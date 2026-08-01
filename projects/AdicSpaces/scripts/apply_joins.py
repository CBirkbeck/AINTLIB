#!/usr/bin/env python3
"""Rejoin gratuitously-wrapped continuation lines inside a proof BODY.

The joined line holds exactly the tokens of the two it replaces, so no proof can
change meaning. Two guards, both learned from failures on earlier passes:

* LEAF GUARD -- only join when the continuation line has no children of its own
  (nothing below it is indented deeper). Joining a line that has children
  re-anchors the block's column and silently ejects them, which showed up as
  bogus "Fields missing" errors inside structure literals.
* BODY SCOPING -- start after the signature's top-level `:=`. The metric counts
  body lines only, so joins landing in the signature change files without moving
  the number.

Usage: apply_joins.py <decl-name> <n-joins>
"""
import json
import re
import sys

NEXT = re.compile(
    r'^\s*(?:@\[|/--|/-!|include |omit |'
    r'(?:private |protected |noncomputable |scoped |partial |unsafe )*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|end|'
    r'section|namespace|variable|open|universe|attribute|macro|notation|'
    r'syntax|elab)\s)')
OPEN, CLOSE = '([{⟨', ')]}⟩'


def body_span(lines, start):
    """Return (body_start, decl_end): the line after the signature's `:=`."""
    end = start + 1
    while end < len(lines) and not NEXT.match(lines[end]):
        end += 1
    depth = 0
    for k in range(start, end):
        text = re.sub(r'--.*', '', lines[k])
        pos = 0
        while pos < len(text):
            ch = text[pos]
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                depth -= 1
            elif depth == 0 and text.startswith(':=', pos):
                return k + 1, end
            pos += 1
    return end, end


def joinable(lines, k, end):
    """Is `lines[k]` safely joinable with its continuation `lines[k + 1]`?"""
    left, right = lines[k], lines[k + 1]
    if not left.strip() or not right.strip():
        return False
    if '--' in left or '--' in right:
        return False
    if left.lstrip().startswith(('·', '.', '|')):
        return False
    # CALC GUARD. A `calc` step continues with `_ = rhs := proof` on its own line; joining the
    # previous step onto it yields `... := by tac _ = ...`, which is a syntax error
    # ("unexpected token '_'"). The right line being deeper-indented does NOT mean it continues
    # the left one here -- calc steps are siblings that happen to be indented.
    if right.lstrip().startswith('_'):
        return False
    # ALTERNATIVES GUARD. A tactic whose cases follow as `| alt =>` lines does not end at its
    # own line: `induction … with` / `cases … with` / `match … with` / `rcases … with` continue
    # onto the block below. Joining anything onto such a line makes it the tail of a `;` chain
    # and the `|` alternatives stop attaching to it -- "Alternative `insert` has not been
    # provided", reported at the alternatives rather than at the join. Third member of the same
    # family as the calc-step and structure-literal guards: constructs whose parts are indented
    # siblings, which indentation alone cannot distinguish from a continuation.
    if re.search(r'(?<![\w\'])(induction|cases|rcases|obtain|match)\b.*\bwith\s*$', left):
        return False
    for nxt in lines[k + 2:end]:
        if not nxt.strip():
            continue
        if nxt.lstrip().startswith('|'):
            return False
        break
    if left.rstrip().endswith(('by', 'do')):
        return False
    ind_l = len(left) - len(left.lstrip())
    ind_r = len(right) - len(right.lstrip())
    if not (ind_r > ind_l or left.rstrip().endswith((':=', '↦', '=>'))):
        return False
    if len(left.rstrip()) + 1 + len(right.strip()) > 100:
        return False
    # STRUCTURE-LITERAL GUARD. In `{ toFun := f` / `  map_zero' := g` the fields are SIBLINGS,
    # but the `{` line is indented less than them, so the "deeper indent = continuation" test
    # fires and the leaf test passes (the next field is at equal indent). Joining two fields
    # onto one line is a syntax error ("Fields missing"). Refuse when the right line is a field
    # assignment and the left already carries one, or when the left opens an unclosed `{`.
    if left.count('{') > left.count('}'):
        return False
    if re.match(r"^[\w']+\s*:=", right.strip()) and ':=' in left:
        return False
    for j in range(k + 2, end):  # leaf guard
        if not lines[j].strip():
            continue
        return len(lines[j]) - len(lines[j].lstrip()) <= ind_r
    return True


def main():
    name, want = sys.argv[1], int(sys.argv[2])
    record = next(r for r in json.load(open('/tmp/over50_code.json'))
                  if r['name'] == name)
    lines = open(record['file']).read().split('\n')
    body, end = body_span(lines, record['line'] - 1)

    picked, last = [], -10
    for k in range(body, end - 1):
        if len(picked) == want:
            break
        if k > last + 1 and joinable(lines, k, end):
            picked.append(k)
            last = k

    if len(picked) < want:
        print(f'FAIL {name}: only {len(picked)}/{want} safe joins')
        return 1
    for k in sorted(picked, reverse=True):
        lines[k:k + 2] = [lines[k].rstrip() + ' ' + lines[k + 1].strip()]
    open(record['file'], 'w').write('\n'.join(lines))
    print(f'ok  {name}: {want} join(s) at {sorted(p + 1 for p in picked)}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
