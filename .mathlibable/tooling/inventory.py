#!/usr/bin/env python3
"""Enumerate public declarations in an AINTLIB project + cheap pre-filter (mathlibable B0/B1).

Walks projects/<P>/**/*.lean (excluding .lake), tracks the namespace stack to build qualified
names, matches Lean-4-module-system decl heads, and applies the cheap SKIP filters
(private/local, _aux, test/examples, internal/auxiliary docstring). Writes a worklist JSON
(all public decls, each tagged keep/skip+reason) and prints a triage summary.

Usage: inventory.py <Project>
"""
import re, os, json, sys

ROOT = "/Users/mcu22seu/Documents/GitHub/aintlib-main"
PROJ = sys.argv[1]
PDIR = f"{ROOT}/projects/{PROJ}"

DECL = re.compile(r'^\s*(@\[[^\]]*\]\s*)*(noncomputable\s+)?(protected\s+)?(public\s+)?'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|proposition|corollary)'
                  r'(?:\s+([^\s:({\[]+))?(?=[\s:({\[]|$)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
ENDNS = re.compile(r'^\s*end\s+(\S+)\s*$')
PRIV = re.compile(r'^\s*(private|local)\b')

def strip_comments(text):
    """Remove Lean block comments /- ... -/ (nestable, covers /-- -/) and line comments --.
    Replace removed spans with spaces of equal length so line numbers are preserved."""
    out = []
    i = 0; n = len(text); depth = 0; line_comment = False
    while i < n:
        c = text[i]; nxt = text[i+1] if i+1 < n else ''
        if line_comment:
            if c == '\n':
                line_comment = False; out.append(c)
            else:
                out.append(' ')
            i += 1; continue
        if depth > 0:
            if c == '/' and nxt == '-':
                depth += 1; out.append('  '); i += 2; continue
            if c == '-' and nxt == '/':
                depth -= 1; out.append('  '); i += 2; continue
            out.append(c if c == '\n' else ' '); i += 1; continue
        # depth == 0, not in line comment
        if c == '/' and nxt == '-':
            depth += 1; out.append('  '); i += 2; continue
        if c == '-' and nxt == '-':
            line_comment = True; out.append('  '); i += 2; continue
        out.append(c); i += 1
    return ''.join(out)

def enumerate_file(path, rel):
    out = []
    nsstack = []
    raw = open(path, encoding='utf-8', errors='replace').read()
    lines = strip_comments(raw).splitlines()
    # preserve original lines for docstring detection
    orig = raw.splitlines()
    prev_doc = ""
    for i, ln in enumerate(lines, 1):
        mns = NS.match(ln)
        if mns:
            nsstack.append(mns.group(1)); continue
        mend = ENDNS.match(ln)
        if mend:
            # pop if it matches a namespace (ignore section ends)
            if nsstack and (nsstack[-1] == mend.group(1) or nsstack[-1].endswith('.' + mend.group(1))):
                nsstack.pop()
            continue
        m = DECL.match(ln)
        if m:
            kind = m.group(5)
            name = m.group(6) or f"_anon_{i}"
            ns = ".".join(nsstack)
            qual = f"{ns}.{name}" if ns else name
            skip = None
            if PRIV.match(ln):
                skip = "private/local"
            elif name.endswith("_aux"):
                skip = "_aux name"
            elif "/test/" in rel.lower() or "/examples/" in rel.lower() or rel.lower().startswith(("test/", "examples/")):
                skip = "test/examples"
            elif prev_doc.strip().lower().startswith(("internal", "auxiliary")):
                skip = "internal/auxiliary docstring"
            out.append({"base": name, "qual": qual, "file": rel, "line": i, "kind": kind,
                        "skip": skip})
        # track preceding docstring from the ORIGINAL line (comments are stripped in `lines`)
        os_ = orig[i-1].strip() if i-1 < len(orig) else ""
        if os_.startswith("/--") or os_.startswith("/-!"):
            prev_doc = os_
        elif os_ and not os_.startswith("@["):
            prev_doc = ""
    return out

decls = []
for dirpath, dirnames, filenames in os.walk(PDIR):
    if ".lake" in dirpath.split(os.sep):
        continue
    for fn in filenames:
        if fn.endswith(".lean"):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, ROOT)
            decls.extend(enumerate_file(full, rel))

keep = [d for d in decls if not d["skip"]]
skip = [d for d in decls if d["skip"]]

from collections import Counter
print(f"project={PROJ}")
print(f"  files scanned:        {len(set(d['file'] for d in decls))}")
print(f"  public decls:         {len(decls)}")
print(f"  -> keep (assess):     {len(keep)}")
print(f"  -> skip (pre-filter): {len(skip)}")
print("  skip reasons:", dict(Counter(d['skip'] for d in skip)))
print("  keep by kind:", dict(Counter(d['kind'] for d in keep)))

out = f"{ROOT}/projects/{PROJ}/.mathlib-quality/overview/worklist.json"
os.makedirs(os.path.dirname(out), exist_ok=True)
json.dump({"keep": keep, "skip": skip}, open(out, "w"), ensure_ascii=False, indent=0)
print(f"  wrote {out}")
