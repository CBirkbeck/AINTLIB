#!/usr/bin/env python3
"""Rank over-50 proofs by how much a REPEATED SUBTERM is costing them.

`decompose_rank.py` scores candidates by the `have` blocks they can lift, so a proof
that is long because it repeats itself scores as expensive: there is no big block to
extract. `limitFrobHom_add` went 62 -> 43 with no helper at all -- the same six
continuity proofs were spelled out at seventeen sites -- and it sat at the BOTTOM of
that ranking with `cost 0 / need 12`.

These are the cheapest targets in the campaign and the other ranking cannot see them.
This one finds them: balanced-parenthesis subterms occurring 3+ times in one proof
body, scored by the characters naming them once would remove.

Safety note carried from that target: substituting a name for an inlined term is
mechanical when the term is a PROOF (`Continuous …`, `_ ≤ _`), because proof
irrelevance keeps the surrounding terms definitionally equal and later `rw`s still
match. For a DATA argument the substitution can change what unifies -- check before
applying.
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import decompose_common as dc  # noqa: E402

MINLEN = 18      # shorter than this, naming it saves nothing
MINCOUNT = 3     # two occurrences rarely pay for the naming line
NAMELEN = 5      # a plausible local name, `hck'`-sized


def code_lines(body):
    """Body lines that carry code -- the metric scope_code.py reports."""
    out = []
    for line in body:
        s = line.strip()
        if not s or s.startswith('--'):
            continue
        out.append(line)
    return out


def subterms(text):
    """Every balanced-paren group in `text`, innermost first."""
    stack, found = [], []
    for i, ch in enumerate(text):
        if ch == '(':
            stack.append(i)
        elif ch == ')' and stack:
            j = stack.pop()
            found.append(text[j:i + 1])
    return found


def best_repeat(text):
    """Highest-yield repeated subterm in `text`, or None."""
    counts = {}
    for t in subterms(text):
        flat = re.sub(r"\s+", " ", t)
        if len(flat) < MINLEN or len(flat) > 400:
            continue
        counts[flat] = counts.get(flat, 0) + 1
    best = None
    for t, n in counts.items():
        if n < MINCOUNT:
            continue
        # chars removed by using a name at each site, minus the definition line
        saved = n * (len(t) - NAMELEN) - (len(t) + 14)
        if saved > 0 and (best is None or saved > best[0]):
            best = (saved, n, t)
    return best


def score(body):
    """Code lines that naming repeated subterms would save, applied REPEATEDLY.

    One name is rarely the whole fix: `limitFrobHom_add` needed seven (six continuity
    proofs and the transported section value), and they compound -- naming the outer
    term changes what the inner counts are. So substitute and re-scan until dry,
    exactly as the manual pass does. Scoring only the single best repeat understated
    every target in the first version of this script.
    """
    code = code_lines(body)
    if not code:
        return None
    text = "\n".join(code)
    # Average line fill, measured from this proof -- reflow estimates use its own style.
    fill = max(1, sum(len(l.strip()) for l in code) // len(code))
    total, picks = 0, []
    for _ in range(12):
        b = best_repeat(text)
        if not b:
            break
        saved, n, t = b
        total += saved
        picks.append((n, t))
        # substituting a name is what makes the NEXT repeat visible
        text = re.sub(re.escape(t), 'N' * NAMELEN, re.sub(r"\s+", " ", text))
    if not picks:
        return None
    return (total // fill, picks)


ROOT = pathlib.Path(__file__).resolve().parents[1] / 'Adic spaces'


def main():
    """Reads scope_code.py's output -- the CANONICAL task-2 measure.

    Not `/tmp/scope.py`'s: that one splits the body at the first line containing `:=`,
    so a `:=` inside a binder truncates the signature and the body absorbs it. It
    reports 283 actionable against this campaign's 117, and it lives in a `/tmp` shared
    with other sessions, which is how it came to be a different script than the one this
    campaign started with. Run `scope_code.py` first; it writes the json read here.
    """
    src = pathlib.Path('/tmp/over50_code.json')
    if not src.exists():
        sys.exit('run projects/AdicSpaces/scripts/scope_code.py first')
    rows = [r for r in json.load(open(src))
            if not r['sorry'] and not r['file'].startswith('Vendored/')]
    out = []
    for r in rows:
        path = ROOT / r['file']
        L = path.read_text().split('\n')
        e = r['line'] - 1 + 1
        while e < len(L) and not re.match(
                r'^\s*(?:@\[|/--|/-!|include |omit |(?:private |protected |noncomputable '
                r'|scoped |partial |unsafe )*(?:theorem|lemma|def|abbrev|instance|structure'
                r'|inductive|class|end|section|namespace|variable|open|universe|attribute'
                r'|macro|notation|syntax|elab)\s)', L[e]):
            e += 1
        by = next((k for k in range(r['line'] - 1, e)
                   if L[k].rstrip().endswith(':= by')), None)
        if by is None:
            continue
        body = L[by + 1:e]
        n_code = len(code_lines(body))
        if n_code <= dc.BUDGET:
            continue
        b = score(body)
        if not b:
            continue
        lines, picks = b
        out.append((lines - (n_code - dc.BUDGET), lines, n_code, picks, r))
    out.sort(key=lambda x: -x[0])
    print("# proofs long because they REPEAT subterms -- invisible to decompose_rank")
    print("# slack = lines naming the repeats saves, minus lines that must go")
    print("# slack >= 0 means naming alone finishes it; otherwise it shrinks the lift\n")
    print(f"{'slack':>5} {'saves':>5} {'code':>4} {'n':>2}  target :: top repeats")
    for slack, lines, n_code, picks, r in out[:20]:
        name = r['name'][:34]
        loc = r["file"]
        print(f"{slack:5d} {lines:5d} {n_code:4d} {len(picks):2d}  {loc}::{name}")
        for n, t in picks[:3]:
            print(f"{'':22}x{n:<3} {t[:82]}")


if __name__ == '__main__':
    main()
