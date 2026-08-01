#!/usr/bin/env python3
"""Lift a top-level `have` out of a proof into a private helper.

Every defect the last three extractions hit is designed out here rather than
written down, because notes did not stop the docstring bug and will not stop
the indent bug:

* RE-DERIVE INDENTATION, never preserve it.  A block moved across an enclosure
  boundary keeps its old columns and they now mean something else — this cost a
  build in `windowTraceHomeomorph` (`refine Equiv.mk`'s arguments stopped being
  continuations) and again in `exists_rps_series_limit` (body at 4, parent at
  2).  The body is dedented to the helper's tactic column on the way out.

* ANCHOR ON THE DOCSTRING, not the declaration.  A declaration's documentation
  lives *above* it, so inserting at the declaration necessarily lands between
  the two and yields `unexpected token '/--'; expected 'lemma'`.  That one
  recurred one commit after being recorded.

* ASSERT THE MATCH BEFORE WRITING.  A file-wide search for a structure-field
  name once hit the wrong instance 200 lines away; the assert is what turned a
  silent corruption into a stopped script.

usage: extract_have.py <file> <decl> <have-name> <helper-name>
       [--sig FILE] [--call "expr"] [--dry]

`--sig` supplies the helper's signature lines (binders + conclusion + ':= by').
Compose it from text already in the file — the lemma the proof rewrites with,
or the `have` that produced the local — rather than typing it out.
"""
import argparse
import pathlib
import sys


def ind(s: str) -> int:
    return len(s) - len(s.lstrip())


def decl_start(lines, name):
    for i, l in enumerate(lines):
        if l.lstrip().startswith(("theorem ", "lemma ", "def ", "private theorem ",
                                  "private lemma ", "noncomputable def ")) and f" {name} " in l + " ":
            if name in l.split(":")[0]:
                return i
    raise SystemExit(f"declaration {name!r} not found")


def doc_anchor(lines, i):
    """First line of the declaration's docstring/attribute block, else the decl."""
    j = i
    while j > 0 and lines[j - 1].strip() and not lines[j - 1].lstrip().startswith("/--"):
        if lines[j - 1].rstrip().endswith("-/"):
            break
        j -= 1
    k = i
    while k > 0:
        prev = lines[k - 1]
        if prev.rstrip().endswith("-/"):
            while k > 0 and not lines[k - 1].lstrip().startswith(("/--", "/-!")):
                k -= 1
            k -= 1
            continue
        if prev.lstrip().startswith("@["):
            k -= 1
            continue
        break
    return min(j, k) if k < i else i


def have_extent(lines, start, have):
    for i in range(start, len(lines)):
        s = lines[i].strip()
        if s.startswith(f"have {have} ") or s.startswith(f"have {have}:"):
            base = ind(lines[i])
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or ind(lines[j]) > base):
                j += 1
            return i, j, base
    raise SystemExit(f"`have {have}` not found in {lines[start][:60]!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file"); ap.add_argument("decl")
    ap.add_argument("have"); ap.add_argument("helper")
    ap.add_argument("--sig", required=True)
    ap.add_argument("--call", required=True)
    ap.add_argument("--carry", default="", help="comma-separated lines to move INTO the helper (e.g. a `set`)")
    ap.add_argument("--dry", action="store_true")
    a = ap.parse_args()

    p = pathlib.Path(a.file)
    L = p.read_text().split("\n")
    d = decl_start(L, a.decl)
    h, j, base = have_extent(L, d, a.have)
    body = L[h + 1:j]
    assert body, "empty have body"

    sig = pathlib.Path(a.sig).read_text().rstrip("\n").split("\n")
    assert sig[-1].rstrip().endswith(":= by"), "signature must end in ':= by'"
    tac = 2                                    # helper's tactic column
    carry = [c for c in a.carry.split("\n") if c.strip()]
    # THE FIX: re-derive indentation relative to the new parent.
    shift = ind(body[0]) - tac
    moved = [(l[shift:] if l.strip() and ind(l) >= shift else l) for l in body]
    helper = sig + [" " * tac + c.strip() for c in carry] + moved

    L[h:j] = [" " * base + x for x in a.call.split("\n")]
    anchor = doc_anchor(L, decl_start(L, a.decl))
    L[anchor:anchor] = helper + [""]

    if a.dry:
        print("\n".join(helper[:6] + ["…"] + helper[-3:]))
        print(f"\n-- would insert at line {anchor + 1}, replacing {j - h} lines with {len(a.call.splitlines())}")
        return
    p.write_text("\n".join(L))
    print(f"ok {a.decl}::{a.have} -> {a.helper}: helper {len(helper)} lines at {anchor + 1}, "
          f"body dedented by {shift}")


if __name__ == "__main__":
    sys.exit(main())
