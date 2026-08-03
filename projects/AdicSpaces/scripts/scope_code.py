#!/usr/bin/env python3
"""Canonical task-2 measure: proof bodies over 50 lines of CODE.

`scope2.py` counts raw body lines, which makes documentation count as proof length — 39 proofs are
"over 50" purely on comments, one of them 110 raw lines against 8 of code. `/cleanup` forbids
deleting proof comments, so those are not decomposition work. This measure counts non-blank lines
that do not start with `--`.

Both numbers are reported, plus the intersection that is cheapest to act on: proofs where the RAW
count is also barely over, so a couple of removed lines move both metrics at once.
"""
import json, os, re, collections

os.chdir("/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces")
NEXT = re.compile(r'^set_option .* in$|'
                  r'^\s*(?:@\[|/--|/-!|include |omit |(?:private |protected |noncomputable |scoped |partial |unsafe )*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|end|section|namespace|variable|open|universe|attribute|macro|notation|syntax|elab)\s)')
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|partial\s+|unsafe\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s({\[:]+)")
OPEN, CLOSE = '([{⟨', ')]}⟩'
SORRY = re.compile(r'(?<![A-Za-z_])(sorry|admit)(?![A-Za-z_])')

def sig_end(L, start, stop):
    """Index of the line carrying the `:=` that starts the PROOF.

    Bracket depth alone is not enough. A conclusion may itself contain term-mode
    `haveI`/`letI` bindings, whose `:=` sits at depth 0:

        theorem relativePiece_equiv_restrict_square … (y : presheafValue E) :
            haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing… ← not it
            …
            relativePiece_equiv D₀ E' … = … := by                                    ← this one

    Stopping at the first one charged nine lines of STATEMENT to the body and reported
    three of these at 56/60/60 against their actual 47/50/50. So: when the declaration is
    tactic-mode, the proof starts at the first line ending `:= by`; only a term-mode proof
    falls back to the first depth-0 `:=`.
    """
    depth, first = 0, None
    for k in range(start, stop):
        s = re.sub(r'--.*', '', L[k]); i = 0
        while i < len(s):
            c = s[i]
            if c in OPEN: depth += 1
            elif c in CLOSE: depth -= 1
            elif depth == 0 and s.startswith(':=', i):
                if s.rstrip().endswith(':= by'): return k
                if first is None: first = k
            i += 1
    return first if first is not None else stop - 1

rows = []
for root, dirs, fs in os.walk('.'):
    dirs[:] = [d for d in dirs if d != '.lake']
    for fn in sorted(fs):
        if not fn.endswith('.lean'): continue
        p = os.path.join(root, fn)[2:]
        L = open(p).read().split('\n')
        for i, l in enumerate(L):
            m = DECL.match(l)
            if not m: continue
            e = i + 1
            while e < len(L) and not NEXT.match(L[e]): e += 1
            b = sig_end(L, i, e)
            body = L[b + 1:e]
            raw = len(body)
            code = len([x for x in body if x.strip() and not x.strip().startswith('--')])
            if code > 50:
                rows.append({'file': p, 'line': i + 1, 'name': m.group(2), 'raw': raw,
                             'code': code, 'comment': raw - code,
                             'sorry': bool(SORRY.search(re.sub(r'--.*', '', '\n'.join(L[i:e]))))})
rows.sort(key=lambda r: -r['code'])
# ACTIONABLE = sorry-free and not third-party. `Vendored/` is out of scope by directive, and a
# sorry-bearing body is the owning producer's WIP (CLAUDE.md) — never decompose either. The JSON
# is the work queue, so it carries only these; `rows` stays for the summary counts below.
clean = [r for r in rows if not r['sorry'] and not r['file'].startswith('Vendored/')]
json.dump(clean, open('/tmp/over50_code.json', 'w'), indent=1)
print(f'proof bodies over 50 CODE lines: {len(rows)}  ({len(rows)-len(clean)} excluded '
      f'(sorry-bearing or Vendored/), {len(clean)} actionable)')
both = [r for r in clean if r['raw'] <= 55]
print(f'of those, RAW <= 55 as well (cheapest — a few lines move both metrics): {len(both)}\n')
for r in sorted(both, key=lambda z: z['raw'])[:18]:
    print(f'  code {r["code"]:3d} raw {r["raw"]:3d}  {r["name"][:44]:44s} {r["file"]}:{r["line"]}')
c = collections.Counter(r['file'] for r in clean)
print('\nworst files by code-line count:')
for f, n in c.most_common(8): print(f'  {n:3d}  {f}')
