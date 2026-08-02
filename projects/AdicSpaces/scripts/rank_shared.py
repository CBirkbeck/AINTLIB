#!/usr/bin/env python3
"""Find PAIRS of over-50 proofs that share a long block — one extraction closes both.

The highest-yield targets of this campaign have all been pairs or triples:

  relativePiece_equiv_restrict_square ×3   one script, three targets
  unitCover_overlapQuotEquiv + _symm_mk    five shared lemmas, two targets
  digit_sub_le + valued_sub_sub_PhiHatK_le ~40 shared preamble lines

None of the three existing rankings can see this. `decompose_rank`, `rank_repeats` and
`rank_anon_defs` all score ONE proof at a time; a block that appears once per proof is
invisible to each of them and obvious across the pair.

This scans every pair of over-50 proofs (same file first, then whole tree) for their
longest common contiguous run of normalised lines, and reports the ones where that run is
worth extracting. A hit means: extract the run once, and BOTH proofs shrink by it.

Normalisation strips indentation and collapses whitespace, so a copy that was re-indented
into a different bullet depth still matches — which is precisely how the
`digit_sub_le` / `valued_sub_sub_PhiHatK_le` overlap escaped the other scans.
"""
import json
import pathlib
import re
import sys
from difflib import SequenceMatcher

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import decompose_common as dc  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1] / 'Adic spaces'
MINRUN = 6          # shorter than this, extracting costs more than it saves


def norm(line):
    return re.sub(r'\s+', ' ', line.strip())


def body_of(r):
    L = (ROOT / r['file']).read_text().split('\n')
    by = next((k for k in range(r['line'] - 1, min(r['line'] + 95, len(L)))
               if L[k].rstrip().endswith(':= by')), None)
    if by is None:
        return None
    e = by + 1
    while e < len(L) and (not L[e].strip() or dc.ind(L[e]) > 0):
        e += 1
    return [norm(l) for l in L[by + 1:e] if l.strip() and not l.strip().startswith('--')]


def main():
    src = pathlib.Path('/tmp/over50_code.json')
    if not src.exists():
        sys.exit('run projects/AdicSpaces/scripts/scope_code.py first')
    rows = [r for r in json.load(open(src))
            if not r['sorry'] and not r['file'].startswith('Vendored/')]
    bodies = []
    for r in rows:
        b = body_of(r)
        if b:
            bodies.append((r, b))
    hits = []
    for i in range(len(bodies)):
        ri, bi = bodies[i]
        for j in range(i + 1, len(bodies)):
            rj, bj = bodies[j]
            m = SequenceMatcher(None, bi, bj, autojunk=False).find_longest_match(
                0, len(bi), 0, len(bj))
            if m.size >= MINRUN:
                hits.append((m.size, ri, rj, bi[m.a]))
    hits.sort(key=lambda h: -h[0])
    print('# PAIRS of over-50 proofs sharing a block — extract once, both shrink')
    print('# invisible to the other three rankings: each scores one proof at a time\n')
    print(f"{'run':>4} {'codeA':>5} {'codeB':>5}  pair")
    for size, ri, rj, first in hits[:20]:
        same = 'same file' if ri['file'] == rj['file'] else 'CROSS-FILE'
        print(f"{size:4} {ri['code']:5} {rj['code']:5}  {ri['name'][:34]} + {rj['name'][:34]}"
              f"  ({same})")
        print(f"{'':12}{ri['file']}")
        if ri['file'] != rj['file']:
            print(f"{'':12}{rj['file']}")
        print(f"{'':12}starts: {first[:76]}")


if __name__ == '__main__':
    main()
