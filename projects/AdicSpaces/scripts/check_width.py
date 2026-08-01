#!/usr/bin/env python3
"""Report lines over the 100-column budget, in CHARACTERS.

`awk 'length($0)>100'` counts BYTES. Lean source is Unicode-dense (ρ, ϖ, ε, ≤,
₀), so a 96-character line routinely measures 110+ bytes and awk reports a style
violation that does not exist. This cost me a spurious "I introduced an
over-long line" scare on RestrictionInjective, where the true count was zero
both before and after.

usage: check_width.py <file> [<file> ...]      compares against HEAD if tracked
"""
import pathlib
import subprocess
import sys


def over(lines, n=100):
    return [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > n]


def main():
    bad = 0
    for f in sys.argv[1:]:
        cur = pathlib.Path(f).read_text().split("\n")
        head = subprocess.run(["git", "show", f"HEAD:{f}"],
                              capture_output=True, text=True).stdout.split("\n")
        c, h = over(cur), over(head)
        mark = "" if len(c) <= len(h) else "   <= REGRESSION"
        print(f"{len(c):3d} over-100 (HEAD {len(h)}){mark}  {f}")
        for ln, w in c[:5]:
            print(f"      line {ln}: {w} chars")
        bad += max(0, len(c) - len(h))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
