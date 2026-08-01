#!/usr/bin/env python3
"""Inline single-use, term-bodied `have`s — the junk-def pattern.

A `have` that is used ONCE and whose body is a TERM earns nothing: it names an
expression that could be written where it is used. The cleanup rules call this a
junk def. It is also, empirically, the cheapest reduction available in this
tree — a scan finds it in 116 of the remaining over-50 proofs, and it cleared
two targets that extraction had twice rejected as too expensive.

WHY THE EXTRACTION RANKING IS BLIND TO IT. `decompose_rank` scores candidates by
extractable block size and by how many locals a block touches. A proof full of
one-use aliases scores as EXPENSIVE, because each alias appears as a local that
a helper would have to thread. The metric points away from the cheapest work.

    extraction  asks "can I lift this out?"    needs every local as a parameter
    inlining    asks "does this binding earn   needs nothing
                      its name?"

Three mechanics, each learned by getting it wrong:

1. ITERATE TO A FIXED POINT. Inlining changes use-counts: a `have` used twice
   becomes single-use once an earlier one is inlined. A single pass caught 3 of
   10 in `ringStalkMap_piYHom_injective`.

2. SPLIT THE BODY ON ALL `:=`, REJOINED — not on the first. A `have` whose TYPE
   contains `:=` would otherwise have its proof term truncated.

3. ONLY TERM BODIES COMPRESS. A tactic-bodied (`:= by`) single-use `have`
   relocates its lines to the call site and saves nothing.

4. THE RESULT MUST FIT 100 COLUMNS. Joining a multi-line term into one line
   "saves" lines while producing an unreadable monster -- a first version of
   this tool produced a 1004-character line and I had to revert two proofs it
   had "cleared". Inlining is only a win for SHORT terms.

usage: inline_junk.py <decl-name> [--dry]
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from decompose_common import ind  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1] / "Adic spaces"
HAVE = re.compile(r"\s*have\s+([^\s:]+)\s*:")


def proof_span(lines, start):
    e = start + 1
    while e < len(lines) and (not lines[e].strip() or ind(lines[e]) > ind(lines[start])):
        e += 1
    return e


def block_span(lines, i):
    b = ind(lines[i])
    e = i + 1
    while e < len(lines) and (not lines[e].strip() or ind(lines[e]) > b):
        e += 1
    return e


def find_one(lines, s, e0):
    """The next inlinable `have`, or None. Re-scans from the top every call so
    that use-counts reflect earlier inlines (mechanic 1)."""
    for i in range(s + 1, e0):
        m = HAVE.match(lines[i])
        if not m:
            continue
        e = block_span(lines, i)
        blk = " ".join(x.strip() for x in lines[i:e])
        n = sum(1 for x in lines[i:e] if x.strip())
        if ":= by" in blk or n < 2:          # mechanic 3
            continue
        parts = blk.split(":=")
        if len(parts) < 2:
            continue
        body = ":=".join(parts[1:]).strip()  # mechanic 2
        name = m.group(1)
        uses = [k for k in range(e, e0)
                if re.search(rf"(?<![\w']){re.escape(name)}(?![\w'])", lines[k])]
        if len(uses) != 1:
            continue
        # MECHANIC 4: the substituted line must still be readable. Joining a
        # multi-line term into one line "saves" lines while producing a 1004-
        # character monster -- optimising the counter by destroying the code.
        # Only inline when the result fits the 100-column budget.
        u = uses[0]
        cand = re.sub(rf"(?<![\w']){re.escape(name)}(?![\w'])", f"({body})", lines[u])
        if len(cand.rstrip()) > 100:
            continue
        return i, e, name, n, body, u
    return None


def main():
    decl = sys.argv[1]
    dry = "--dry" in sys.argv
    rec = next(r for r in json.load(open("/tmp/over50_code.json"))
               if r["name"].split(".")[-1] == decl)
    p = ROOT / rec["file"]
    L = p.read_text().split("\n")
    s = rec["line"] - 1
    e0 = proof_span(L, s)
    done = []
    while True:
        hit = find_one(L, s, e0)
        if hit is None:
            break
        i, e, name, n, body, u = hit
        L[u] = re.sub(rf"(?<![\w']){re.escape(name)}(?![\w'])", f"({body})", L[u])
        del L[i:e]
        e0 -= e - i
        done.append((name, n))
    if not done:
        print(f"{decl}: nothing inlinable")
        return 1
    if dry:
        print(f"{decl}: would inline {done} (-{sum(n - 1 for _, n in done)} lines)")
        return 0
    p.write_text("\n".join(L))
    print(f"ok {decl}: inlined {done}, -{sum(n - 1 for _, n in done)} lines")
    return 0


if __name__ == "__main__":
    sys.exit(main())
