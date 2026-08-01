#!/usr/bin/env python3
"""Rank proofs where PROMOTING A CLUSTER of top-level `have`s clears the parent.

`decompose_rank.py` finds proofs with a single `have` big enough to clear the
parent on its own. That well runs dry fast -- three candidates left out of 159.
This is the generalisation, and it is the shape that actually worked on
`sub_algebraMap_evalFHom_mem_ideal_fSubX`: no single `have` was viable there
(the big one needed the four above it as 25 lines of hypotheses), but promoting
all five to top level let each call the others BY NAME and cost nothing.

The rule that makes a cluster cheap: promote in DEPENDENCY ORDER. A `have` whose
only proof-locals are earlier `have`s in the same cluster becomes a lemma that
calls those lemmas -- zero hypotheses added. A `have` that touches an
`obtain`-bound local needs it reconstructed, so it prices itself out.

Reported per proof:
  cluster   how many leading top-level `have`s are promotable
  frees     lines the parent sheds (their bodies, minus one call line each)
  worst     the largest promoted body -- each must itself land under 50
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from apply_joins import body_span  # noqa: E402
from decompose_common import ID, NOISE, ind, in_scope, boilerplate, fits  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1] / "Adic spaces"
ID = re.compile(r"[^\W\d][\w'ₐ-ₜ₀-₉]*", re.UNICODE)
NOISE = {'rfl', 'this', '_', 'Set', 'Type', 'Prop', 'fun', 'with', 'at', 'in',
         'to', 'and', 'or', 'by', 'from'}
CHEAP = re.compile(r"^\s*(have|set|let)\b")
COSTLY = re.compile(r"^\s*(obtain|rcases|rintro|intro|induction|cases)\b")


def ind(s):
    return len(s) - len(s.lstrip())


def blocks(body, base):
    """Top-level tactic blocks: (start, end, kind, name)."""
    out = []
    i = 0
    while i < len(body):
        l = body[i]
        if l.strip() and ind(l) == base:
            j = i + 1
            while j < len(body) and (not body[j].strip() or ind(body[j]) > base):
                j += 1
            nm = None
            m = re.match(r"\s*have\s+([^\s:]+)\s*:", l)
            if m:
                nm = m.group(1)
            kind = 'have' if m else ('costly' if COSTLY.match(l) else
                                     'cheap' if CHEAP.match(l) else 'other')
            out.append((i, j, kind, nm))
            i = j
        else:
            i += 1
    return out


def analyse(rec):
    L = (ROOT / rec['file']).read_text().split('\n')
    b, e = body_span(L, rec['line'] - 1)
    body = L[b:e]
    if not body:
        return None
    base = min(ind(l) for l in body if l.strip())
    # Instance boilerplate above the cluster has to be reproduced in EVERY
    # promoted lemma, so it multiplies rather than adding. This is the same
    # blind spot decompose_rank had twice; here it is worse, because a 30-line
    # letI preamble times four promotions is 120 lines of duplication.
    boil = 0
    k = 0
    while k < len(body):
        if body[k].strip().startswith(('letI', 'haveI')):
            bi = ind(body[k]); boil += 1; k += 1
            while k < len(body) and body[k].strip() and ind(body[k]) > bi:
                boil += 1; k += 1
        else:
            k += 1
    if boil >= 8:
        return None
    bl = blocks(body, base)
    promoted, freed, worst, names = 0, 0, 0, []
    bound_costly = set()
    for (i, j, kind, nm) in bl:
        if kind == 'costly':
            # everything this binds is unavailable to later promotions
            bound_costly |= set(ID.findall(re.split(r":=|:", body[i].strip())[0])) - NOISE
            continue
        if kind != 'have' or nm is None:
            continue
        used = set()
        for x in body[i:j]:
            used |= set(ID.findall(x))
        if used & bound_costly:
            continue                      # needs a reconstructed hypothesis
        size = sum(1 for x in body[i:j] if x.strip())
        if not fits(size, boil):
            continue
        promoted += 1
        freed += size - 1
        worst = max(worst, size)
        names.append(nm)
    need = rec['code'] - 50
    if promoted and freed >= need:
        return (need - freed, promoted, freed, worst, rec, names)
    return None


def main():
    rows = []
    for r in json.load(open('/tmp/over50_code.json')):
        # Vendored/ is third-party and explicitly out of scope for this campaign.
        # It appeared at rank 5 on the first run of this tool.
        if not in_scope(r):
            continue
        got = analyse(r)
        if got:
            rows.append(got)
    rows.sort(key=lambda x: (x[1], -x[0]))
    print("# promote-cluster worklist: proofs cleared by promoting leading `have`s")
    print("# to top-level lemmas, in dependency order, each calling the previous.")
    print("# A `have` touching an obtain/intro-bound local is skipped -- that is the")
    print("# one that would need a reconstructed hypothesis.")
    print(f"#\n# {len(rows)} candidates\n")
    print(f"{'n':>3} {'frees':>5} {'worst':>5} {'need':>4} {'code':>4}  target")
    for slack, n, freed, worst, r, names in rows:
        print(f"{n:3d} {freed:5d} {worst:5d} {r['code'] - 50:4d} {r['code']:4d}  "
              f"{r['file']}::{r['name'].split('.')[-1]}")
        print(f"{'':22}{names}")


if __name__ == "__main__":
    sys.exit(main())
