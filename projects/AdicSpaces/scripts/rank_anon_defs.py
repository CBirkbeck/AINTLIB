#!/usr/bin/env python3
"""Find proofs that CONSTRUCT something anonymously and then prove lemmas about it.

The third distinct shape in this campaign, and the one neither existing ranking can see:

  decompose_rank  scores liftable `have` blocks -- but every block in such a proof
                  mentions a local, so nothing lifts
  rank_repeats    scores repeated subterms -- but the construction's formula typically
                  appears only twice (definition, then the `change` that restates it),
                  under the 3-occurrence threshold

`lambdaMap_surjective` was the instance that showed it: it built `g`, `h` and a Bézout
witness `c` as anonymous `set` subtype terms, then needed three `have … _val` lemmas whose
entire proof was a `change` back to the formula written above. 76 -> 45 by turning the three
into `private noncomputable def`s with their coefficient lemmas beside them.

The tell this looks for: a `set`/`let` whose value is an anonymous constructor `⟨…⟩` or a
`fun`, together with `have`s that mention the bound name. Score = lines held hostage.

Fix is always the same: name the construction as a top-level definition, and the `have`s
about it become standalone lemmas next to it.
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import decompose_common as dc  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1] / 'Adic spaces'
BIND = re.compile(r"^\s*(?:set|let)\s+([A-Za-z_][\w'₀-₉]*)\s*[:(]?.*?:=\s*(.*)$")


def constructions(body):
    """`set`/`let` bindings whose value is an anonymous constructor or a lambda."""
    out = {}
    for k, line in enumerate(body):
        m = BIND.match(line)
        if not m:
            continue
        name, rest = m.group(1), m.group(2).strip()
        # the value may start on the next line
        if not rest and k + 1 < len(body):
            rest = body[k + 1].strip()
        if rest.startswith('⟨') or rest.startswith('fun ') or rest.startswith('fun('):
            bi = dc.ind(line)
            j = k + 1
            while j < len(body) and body[j].strip() and dc.ind(body[j]) > bi:
                j += 1
            out[name] = j - k
    return out


def main():
    src = pathlib.Path('/tmp/over50_code.json')
    if not src.exists():
        sys.exit('run projects/AdicSpaces/scripts/scope_code.py first')
    rows = [r for r in json.load(open(src))
            if not r['sorry'] and not r['file'].startswith('Vendored/')]
    out = []
    for r in rows:
        L = (ROOT / r['file']).read_text().split('\n')
        by = next((k for k in range(r['line'] - 1, min(r['line'] + 90, len(L)))
                   if L[k].rstrip().endswith(':= by')), None)
        if by is None:
            continue
        e = by + 1
        while e < len(L) and (not L[e].strip() or dc.ind(L[e]) > 0):
            e += 1
        body = L[by + 1:e]
        cons = constructions(body)
        if len(cons) < 2:
            continue
        # lines of `have` blocks that mention a constructed name
        held, k = 0, 0
        while k < len(body):
            s = body[k].strip()
            if s.startswith('have ') and any(n in body[k] for n in cons):
                bi = dc.ind(body[k])
                j = k + 1
                while j < len(body) and body[j].strip() and dc.ind(body[j]) > bi:
                    j += 1
                held += j - k
                k = j
                continue
            k += 1
        if held == 0:
            continue
        out.append((held + sum(cons.values()), held, len(cons), r, cons))
    out.sort(key=lambda x: -x[0])
    print('# proofs that construct anonymously, then prove lemmas about the construction')
    print('# fix: name the construction as a def; the `have`s become lemmas beside it\n')
    print(f"{'score':>5} {'held':>4} {'n':>2} {'code':>4}  target")
    for score, held, n, r, cons in out[:20]:
        print(f"{score:5} {held:4} {n:2} {r['code']:4}  {r['file']}:{r['line']} :: {r['name'][:38]}")
        print(f"{'':16}{', '.join(sorted(cons))[:88]}")


if __name__ == '__main__':
    main()
