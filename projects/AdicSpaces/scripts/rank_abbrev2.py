#!/usr/bin/env python3
"""Greedy MULTI-round abbreviation: apply the best `set`, re-scan the shortened
text, apply the next best, and keep going while the line count falls.

Single-round abbreviation stalled with several targets sitting at exactly 51-53.
The question this answers is whether abbreviations compound: shortening one term
can pull a line under the join threshold, which changes which OTHER terms sit on
wrap-pressured lines.  Re-scanning after each round is the only way to see that
-- the round-1 candidate table is computed against the original text and cannot
know what round 1 itself will change.

Same discipline as the single-round tool: measure by simulating the real
joinable()/mergeable() passes, and require every candidate term to be a balanced
expression before it is allowed to count.
"""
import importlib.util
import json
import pathlib
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


RA = load("rank_abbrev")
RC = sys.modules["rank_cheap"]
AJ = sys.modules["apply_joins"]
ALIASES = ['Q', 'W', 'Z']


def rounds(lines, start, max_rounds=3):
    """Greedily apply abbreviations; return (applied, final_after)."""
    cur = lines[:]
    cur_start = start
    applied = []
    base = RC.simulate_lines(cur, cur_start) if hasattr(RC, 'simulate_lines') else None
    tmp = SP / "_s2.tmp"
    tmp.write_text('\n'.join(cur))
    best_after = RC.simulate(tmp, cur_start + 1)[2]
    for r in range(max_rounds):
        b, e = AJ.body_span(cur, cur_start)
        alias = ALIASES[r]
        pick = None
        for term, count in RA.candidates(cur[b:e]):
            if alias in term:
                continue
            trial = cur[:]
            for i in range(b, e):
                trial[i] = trial[i].replace(term, alias)
            ind = ' ' * (len(trial[b]) - len(trial[b].lstrip()))
            trial.insert(b, f"{ind}set {alias} := {term} with h{alias}")
            tmp.write_text('\n'.join(trial))
            got = RC.simulate(tmp, cur_start + 1)
            if got is None:
                continue
            if got[2] < best_after and (pick is None or got[2] < pick[0]):
                pick = (got[2], term, count, trial, got)
        if pick is None:
            break
        best_after, term, count, cur, got = pick
        applied.append((alias, term, count, best_after, got[0], got[1]))
    return applied, best_after


def main():
    targets = json.load(open('/tmp/over50_code.json'))
    names = set(sys.argv[1:]) if len(sys.argv) > 1 else None
    out = []
    for t in targets:
        if t["sorry"]:
            continue
        short = t["name"].split('.')[-1]
        if names and short not in names:
            continue
        path = ROOT / t["file"]
        lines = path.read_text().split('\n')
        base = RC.simulate(path, t["line"])
        if base is None:
            continue
        applied, after = rounds(lines, t["line"] - 1)
        if len(applied) >= 1 and after < base[2]:
            out.append((after, base[2], t["code"], t["file"], short, applied))
    out.sort()
    for after, was, code, f, n, applied in out:
        flag = "  <= CLEARS" if after <= 50 else ""
        print(f"{code:4d} -> {after:3d} (1-round: {was}) {f}::{n}{flag}")
        for alias, term, count, aft, j, s in applied:
            print(f"        set {alias} := {term[:52]:52s} {count:3d}x -> {aft} (j{j} s{s})")


if __name__ == "__main__":
    sys.exit(main())
