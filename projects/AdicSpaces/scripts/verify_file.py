#!/usr/bin/env python3
"""Per-file verification for a decompose edit: what MUST be checked before a build.

Written after a range-replace that sliced to end-of-string deleted twelve declarations
from `SheafyBI.lean` (179 lines). The module still built green — nothing inside the file
used them — and only the full-library gate caught it, eleven `Unknown identifier` errors
later in two downstream files. A declaration-name diff against HEAD would have caught it
in under a second.

Usage:  python3 scripts/verify_file.py <path-relative-to-repo-root> [<git-ref>]

Reports, against the given ref (default HEAD):
  * declarations REMOVED   -- the truncation / clobber signal. Never expected.
  * declarations ADDED     -- should be exactly the helpers you meant to add.
  * line-count delta       -- a large negative delta with no removals is also suspect.
  * over-width lines       -- must not increase (byte count, matching the repo's awk check).
"""
import re
import subprocess
import sys
import pathlib

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+"
    r"|partial\s+|unsafe\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)"
    r"\s+([^\s({\[:]+)")


def decls(text):
    return [m.group(1) for m in (DECL.match(l) for l in text.split('\n')) if m]


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    rel = sys.argv[1]
    ref = sys.argv[2] if len(sys.argv) > 2 else 'HEAD'
    root = subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          capture_output=True, text=True).stdout.strip()
    old = subprocess.run(['git', 'show', f'{ref}:{rel}'], capture_output=True, text=True,
                         cwd=root)
    if old.returncode:
        sys.exit(f'cannot read {ref}:{rel}')
    old_text = old.stdout
    new_text = pathlib.Path(root, rel).read_text()

    o, n = decls(old_text), decls(new_text)
    removed = [d for d in o if d not in n]
    added = [d for d in n if d not in o]

    def wide(t):
        # CODEPOINTS, not UTF-8 bytes. mathlib's `longLine` linter tests
        # `maxLineLength < (fm.toPosition line.stopPos).column`, and Lean's Position.column
        # counts characters. Measuring in bytes reports 1610 over-wide lines in this project
        # where the linter's own rule reports 517 -- the difference is entirely ↥ ⟨⟩ ₀ ⁻¹ etc.
        return sum(1 for l in t.split('\n') if len(l) > 100)

    print(f'{rel}  ({ref} -> working tree)')
    print(f'  lines       {len(old_text.split(chr(10))):6d} -> {len(new_text.split(chr(10))):6d}'
          f'   ({len(new_text.split(chr(10))) - len(old_text.split(chr(10))):+d})')
    print(f'  decls       {len(o):6d} -> {len(n):6d}')
    print(f'  over-width  {wide(old_text):6d} -> {wide(new_text):6d}')
    if added:
        print(f'  ADDED   ({len(added)}): {", ".join(added)}')
    if removed:
        print(f'  REMOVED ({len(removed)}): {", ".join(removed)}')
        print('  *** DECLARATIONS REMOVED — a decompose edit must never remove one. ***')
        return 1
    if wide(new_text) > wide(old_text):
        print('  *** over-width lines increased ***')
        return 1
    print('  ok')
    return 0


if __name__ == '__main__':
    sys.exit(main())
