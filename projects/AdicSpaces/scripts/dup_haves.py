#!/usr/bin/env python3
"""Find duplicated top-level `have` blocks: the same statement AND the same proof,
appearing in two or more places.

Comparator note, learned the expensive way: hash the TYPE together with the body.
Hashing the body alone treats `have h : P := by tac` and `have h : Q := by tac`
as duplicates whenever `tac` coincides, which over-counted this tree by 21
clusters / 125 lines and would have produced merges that do not typecheck.

Indentation is normalised before hashing -- the two copies of `hmax` in
WedhornCechAcyclicity sit at depths 2 and 4, so a raw compare misses them.

Within-file clusters are the tractable half: both copies share a context, so the
hoisted lemma's hypotheses can be read off whichever copy states them
explicitly. Cross-file clusters additionally need an import-closure check for a
common home.
"""
import collections
import hashlib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1] / "Adic spaces"


def ind(s):
    return len(s) - len(s.lstrip())


def main():
    seen = collections.defaultdict(list)
    for f in sorted(ROOT.rglob("*.lean")):
        if "Vendored" in str(f):
            continue
        L = f.read_text().split("\n")
        i = 0
        while i < len(L):
            m = re.match(r"(\s+)have\s+([^\s:]+)\s*:", L[i])
            if m:
                base = len(m.group(1))
                j = i + 1
                while j < len(L) and (not L[j].strip() or ind(L[j]) > base):
                    j += 1
                blk = [x.strip() for x in L[i:j] if x.strip()]
                if len(blk) >= 3:
                    norm = ["have _ :" + blk[0].split(":", 1)[1]] + blk[1:]
                    key = hashlib.md5("\n".join(norm).encode()).hexdigest()
                    seen[key].append((f.relative_to(ROOT), i + 1, m.group(2), len(blk)))
                i = j
            else:
                i += 1
    dups = {k: v for k, v in seen.items() if len(v) > 1}
    within = {k: v for k, v in dups.items() if len({f for f, _, _, _ in v}) == 1}
    total = sum(v[0][3] * (len(v) - 1) for v in dups.values())
    print(f"# {len(dups)} clusters, {total} redundant lines "
          f"({len(within)} within one file, {len(dups) - len(within)} across files)\n")
    for k, v in sorted(dups.items(), key=lambda kv: -kv[1][0][3]):
        tag = "same-file" if k in within else "cross-file"
        print(f"{v[0][3]:3d}L x{len(v)}  [{tag}] {v[0][2]}")
        for f, ln, nm, _ in v:
            print(f"        {f}:{ln}  ({nm})")


if __name__ == "__main__":
    sys.exit(main())

