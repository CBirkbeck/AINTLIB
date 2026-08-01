#!/usr/bin/env python3
"""Rank over-50 proofs by how cheap their decomposition actually is.

The ranking this replaces counted proof-locals and treated them alike. That
inverted the true difficulty order: `sub_algebraMap_evalFHom_mem_ideal_fSubX`
scored 6 locals and sat third, when four of the six were `have`-bound with
explicit types and the remaining two were merely *their* bound variables.

What a local costs depends entirely on how it was bound:

  have-bound    CHEAP  -- the type is written down in the source, so the local
                          can be PROMOTED to its own lemma and called by name.
  set/let-bound CHEAP  -- the defining term is written down; the `set` line can
                          be carried into the helper verbatim (this is what made
                          `exists_rps_series_limit` a clean lift).
  obtain/rcases EXPENSIVE -- destructuring binds names whose types appear
                          NOWHERE. The extractor has to reconstruct each one as
                          an explicit hypothesis.
  intro-bound   MEDIUM -- the type is recoverable from the goal, but only by
                          reading the statement.

Second thing this gets right: a helper's cost is not its body, it is the
CONTEXT it must re-import. When the `have`s a block depends on are themselves
promotable, promoting them all beats passing them as hypotheses -- five small
lemmas rather than one helper with a 25-line signature.
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from apply_joins import body_span  # noqa: E402
from decompose_common import in_scope, boilerplate, call_cost, fits  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1] / "Adic spaces"
ID = re.compile(r"[^\W\d][\w'ₐ-ₜ₀-₉]*", re.UNICODE)
NOISE = {'rfl', 'this', '_', 'Set', 'Type', 'Prop', 'fun', 'with', 'at', 'in',
         'to', 'and', 'or', 'by', 'from'}
KIND = [('have', re.compile(r"^\s*have\b")),
        ('set', re.compile(r"^\s*(set|let)\b")),
        ('obtain', re.compile(r"^\s*(obtain|rcases|rintro)\b")),
        ('intro', re.compile(r"^\s*intro\b")),
        ('cases', re.compile(r"^\s*(induction|cases)\b"))]
COST = {'have': 0, 'set': 0, 'intro': 1, 'cases': 2, 'obtain': 3}


def ind(s):
    return len(s) - len(s.lstrip())


def binders(body, upto):
    """name -> binder kind, for everything bound above `upto`."""
    out = {}
    for line in body[:upto]:
        for kind, pat in KIND:
            if pat.match(line):
                head = re.split(r":=|:", line.strip())[0]
                for n in ID.findall(head):
                    if n not in NOISE and n not in {k for k, _ in KIND} | {'using', 'generalizing'}:
                        out.setdefault(n, kind)
                break
    return out


def analyse(rec):
    L = (ROOT / rec['file']).read_text().split('\n')
    b, e = body_span(L, rec['line'] - 1)
    body = L[b:e]
    if not body:
        return None
    base = min(ind(l) for l in body if l.strip())
    need = rec['code'] - 50
    best = None
    for i, l in enumerate(body):
        s = l.strip()
        if not (s.startswith('have ') and ind(l) == base and ':' in s):
            continue
        j = i + 1
        while j < len(body) and (not body[j].strip() or ind(body[j]) > base):
            j += 1
        size = sum(1 for x in body[i:j] if x.strip())
        # The helper must also reproduce the instance boilerplate above the
        # block -- `letI`/`haveI` blocks are what make the statements elaborate.
        # Omitting this is how an earlier version of this ranking put an
        # 84-line proof with a 30-line letI preamble at the TOP of the list:
        # the cut it proposed would have produced a 70-line helper.
        boil = 0
        k = 0
        while k < i:
            if body[k].strip().startswith(('letI', 'haveI')):
                bi = ind(body[k])
                boil += 1
                k += 1
                while k < i and body[k].strip() and ind(body[k]) > bi:
                    boil += 1
                    k += 1
            else:
                k += 1
        # `set`/`let`-bound locals are carried INTO the helper as their defining
        # lines (that is what makes them cost 0 to resolve), so they count
        # against the helper's 50-line budget too. Counting the resolution as
        # free but not its lines is how a 49-line block with two carried `set`s
        # ranked top at an actual helper size of 51.
        pre_bnd = binders(body, i)
        used_pre = set()
        for x in body[i:j]:
            used_pre |= set(ID.findall(x))
        carried = 0
        for k2, l2 in enumerate(body[:i]):
            if re.match(r"^\s*(set|let)\b", l2):
                nm = ID.findall(re.split(r":=|:", l2.strip())[0])
                if any(n in used_pre and pre_bnd.get(n) == 'set' for n in nm):
                    bi = ind(l2)
                    carried += 1
                    k3 = k2 + 1
                    while k3 < i and body[k3].strip() and ind(body[k3]) > bi:
                        carried += 1
                        k3 += 1
        # The extracted block is NOT replaced by one line. The call passes every
        # promoted local, so it wraps: about a line per four arguments. Scoring
        # it at 1 put `tateAlgNhd_leftMul_of_principal`'s parent at 47 when it
        # measured 52. (Keeping an explicit type ascription costs ~3 more; the
        # fix there was to drop it and let Lean infer.)
        call = 1 + len(set(binders(body, i)) & used_pre) // 4
        if size - call < need or size + boil + carried > 50:
            continue
        bnd = binders(body, i)
        used = set()
        for x in body[i:j]:
            used |= set(ID.findall(x))
        locs = {n: bnd[n] for n in (set(bnd) & used) - NOISE}
        cost = sum(COST[k] for k in locs.values())
        row = (cost, size, need, rec, s.split(':')[0].strip(), locs)
        if best is None or cost < best[0]:
            best = row
    return best


def main():
    rows = []
    for r in json.load(open('/tmp/over50_code.json')):
        if not in_scope(r):
            continue
        got = analyse(r)
        if got:
            rows.append(got)
    rows.sort(key=lambda x: (x[0], x[3]['code']))
    print("# decompose worklist, ranked by EXTRACTION COST")
    print("# cost = sum over the locals a candidate `have` touches:")
    print("#   have/set-bound 0 (type or term is written down -> promote or carry)")
    print("#   intro 1, cases 2, obtain/rcases 3 (type appears nowhere -> reconstruct)")
    print(f"#\n# {len(rows)} candidates\n")
    print(f"{'cost':>4} {'blk':>4} {'need':>4} {'code':>4}  target :: have")
    for cost, size, need, r, hv, locs in rows:
        print(f"{cost:4d} {size:4d} {need:4d} {r['code']:4d}  {r['file']}::{r['name'].split('.')[-1]} :: {hv}")
        if locs:
            grp = {}
            for n, k in sorted(locs.items()):
                grp.setdefault(k, []).append(n)
            print(f"{'':22}" + "  ".join(f"{k}:{v}" for k, v in sorted(grp.items())))


if __name__ == "__main__":
    sys.exit(main())
