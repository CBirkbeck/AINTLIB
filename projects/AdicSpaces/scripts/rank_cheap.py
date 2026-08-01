#!/usr/bin/env python3
"""Rank the over-50 proofs by whether joins + sibling-merges alone clear them.

This is the estimator I got wrong three times, so it is now built from the
ACTUAL apply_* tools rather than a re-implementation: it imports joinable()
from apply_joins and mergeable() from apply_sibs, so the count it reports is
by construction the count those tools will deliver.

It also SIMULATES: joins are applied in memory first, then sibs are counted on
the joined text.  Counting them independently on the original text and adding
overstates -- shortening lines removes wrap points (the imgFamily lesson).
"""
import importlib.util
import json
import pathlib
import sys

SP = pathlib.Path(__file__).parent
ROOT = pathlib.Path("/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces")


def load(name):
    spec = importlib.util.spec_from_file_location(name, SP / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


AJ = load("apply_joins")
AS_ = load("apply_sibs")


def code_len(lines):
    """Code lines only -- block comments excluded, matching scope_code.py."""
    depth, n = 0, 0
    for line in lines:
        opens = depth == 0
        i = 0
        stripped = line.strip()
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                depth = max(0, depth - 1)
                i += 2
                continue
            if depth == 0 and line.startswith("--", i):
                break
            i += 1
        if opens and stripped and not stripped.startswith("--"):
            n += 1
    return n


def simulate(path, line):
    lines = path.read_text().split("\n")
    start = line - 1
    bstart, end = AJ.body_span(lines, start)
    # pass 1: joins, applied in memory
    body = lines[:]
    joins = 0
    k = end - 2
    while k >= bstart:
        if AJ.joinable(body, k, end):
            body[k] = body[k].rstrip() + " " + body[k + 1].strip()
            del body[k + 1]
            end -= 1
            joins += 1
        k -= 1
    # pass 2: sibs on the JOINED text
    sibs = 0
    k = end - 2
    while k >= bstart:
        if AS_.mergeable(body[k], body[k + 1], body[k - 1] if k else '',
                         body[max(0, k - 12):k]):
            body[k] = body[k].rstrip() + "; " + body[k + 1].strip()
            del body[k + 1]
            end -= 1
            sibs += 1
            k -= 1  # no chaining
        k -= 1
    after = code_len(body[bstart:end])
    return joins, sibs, after


def main():
    targets = json.load(open("/tmp/over50_code.json"))
    rows = []
    for t in targets:
        if t["sorry"]:
            continue
        p = ROOT / t["file"]
        r = simulate(p, t["line"])
        if r is None:
            continue
        joins, sibs, after = r
        rows.append((after, t["code"], joins, sibs, t["file"], t["name"]))
    rows.sort()
    clear = [r for r in rows if r[0] <= 50]
    print(f"CLEARED by joins+sibs alone: {len(clear)} of {len(rows)}\n")
    for after, code, joins, sibs, f, n in clear:
        print(f"  {code:4d} -> {after:3d}  j{joins:3d} s{sibs:3d}  {f}::{n}")
    print("\nNear misses (1-3 over after both passes):")
    for after, code, joins, sibs, f, n in rows:
        if 50 < after <= 53:
            print(f"  {code:4d} -> {after:3d}  j{joins:3d} s{sibs:3d}  {f}::{n}")


if __name__ == "__main__":
    sys.exit(main())
