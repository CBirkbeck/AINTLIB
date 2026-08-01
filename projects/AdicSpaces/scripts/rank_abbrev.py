#!/usr/bin/env python3
"""Simulate `set X := <repeated term> with hX` + joins + sibs, and report the
net line change.

Abbreviation is the lever I have twice ranked with a proxy and twice got wrong:
"characters saved" and "occurrences on wrap-pressured lines" both score the
cases that worked identically to the cases that did not.  The value of an
abbreviation is almost entirely INDIRECT -- it shortens lines until previously
unjoinable continuations rejoin -- so the only honest ranking is to apply the
substitution and re-run the real joinable()/mergeable() passes over the result.

That is what this does.  It reuses rank_cheap's simulate() so the joins/sibs
half is the same code that produces the committed numbers.
"""
import collections
import importlib.util
import json
import pathlib
import re
import sys

SP = pathlib.Path(__file__).parent
ROOT = pathlib.Path("/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces"
                    "/projects/AdicSpaces/Adic spaces")


def load(name):
    spec = importlib.util.spec_from_file_location(name, SP / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


RC = load("rank_cheap")
AJ = sys.modules["apply_joins"]

TERM = re.compile(r"[A-Za-z_][\w'.₀-₉]*(?:\s+[A-Za-z_(][\w'.₀-₉]*)+")


def balanced(t):
    """A candidate must be a self-contained expression.

    The regex happily returns `Ideal (MvPolynomial (Fin m` -- two opens, no
    closes.  Substituting it textually still *predicts* a line saving, because
    the simulator only counts lines, but the edit it implies is not Lean.  This
    is the abbreviation lever's version of the two-line window: the measurement
    is fine and the thing being measured is nonsense.
    """
    depth = 0
    for ch in t:
        if ch in '([⟨{':
            depth += 1
        elif ch in ')]⟩}':
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


# The regex matches any run of identifiers, so it happily swallows the TACTIC in
# front of a term (`change iteratedPlus_forwardHom P D0 f`) or the binder behind
# it (`ValuativeRel.valuation A with hw_def`).  Abbreviating either produces a
# `set` whose body is not an expression.  Same class as the balance check: the
# line-count prediction is fine, the edit it implies is not Lean.
TACTIC = frozenset("""change exact apply refine rw rwa simp simpa have show intro
    intros set let calc use exists constructor obtain rcases cases induction
    conv unfold delta erw specialize replace suffices by from at with""".split())


def candidates(body, min_len=22, min_count=3):
    c = collections.Counter()
    for line in body:
        for m in TERM.finditer(line):
            t = m.group(0).strip()
            words = t.split()
            if words[0] in TACTIC or any(w in ('with', 'at', 'from') for w in words):
                continue
            if len(t) >= min_len and t.count(' ') >= 2 and balanced(t):
                c[t] += 1
    return [(t, k) for t, k in c.most_common(6) if k >= min_count]


def simulate_with(lines, start, term, alias):
    """Substitute, insert the `set`, then run the real joins+sibs passes."""
    bstart, end = AJ.body_span(lines, start)
    body = lines[:]
    for i in range(bstart, end):
        body[i] = body[i].replace(term, alias)
    indent = ' ' * (len(body[bstart]) - len(body[bstart].lstrip()))
    body.insert(bstart, f"{indent}set {alias} := {term} with h{alias}")
    tmp = SP / "_sim.tmp"
    tmp.write_text('\n'.join(body))
    return RC.simulate(tmp, start + 1)


def main():
    targets = json.load(open('/tmp/over50_code.json'))
    names = set(sys.argv[1:]) if len(sys.argv) > 1 else None
    rows = []
    for t in targets:
        if t["sorry"]:
            continue
        short = t["name"].split('.')[-1]
        if names and short not in names:
            continue
        path = ROOT / t["file"]
        lines = path.read_text().split('\n')
        start = t["line"] - 1
        base = RC.simulate(path, t["line"])
        if base is None:
            continue
        bstart, end = AJ.body_span(lines, start)
        best = None
        for term, count in candidates(lines[bstart:end]):
            alias = 'Q'
            r = simulate_with(lines, start, term, alias)
            if r is None:
                continue
            if best is None or r[2] < best[0][2]:
                best = (r, term, count)
        if best is None:
            continue
        (j, s, after), term, count = best
        if after < base[2]:
            rows.append((after, base[2], t["code"], count, len(term), term, t["file"], short))
    rows.sort()
    print(f"{'after':>5} {'was':>4} {'code':>4} {'x':>3} {'ch':>3}  target / term")
    for after, was, code, count, ln, term, f, n in rows:
        flag = "  <= CLEARS" if after <= 50 else ""
        print(f"{after:5d} {was:4d} {code:4d} {count:3d} {ln:3d}  {f}::{n}{flag}")
        print(f"{'':22}set Q := {term[:60]}")


if __name__ == "__main__":
    sys.exit(main())
