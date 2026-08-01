#!/usr/bin/env python3
"""Merge adjacent EQUAL-INDENT tactic lines with `; `.

The join tool only ever joins a deeper-indented *continuation*. Two sibling tactics at the same
indentation are invisible to it, yet merging them is the move that closed several proofs by hand.
This applies that move mechanically, with the same guards plus the ones that bit:

* never merge onto a line whose syntax continues below -- `induction/cases/rcases/obtain/match …
  with` takes `| alt` blocks, and a `;` chain detaches them ("Alternative `insert` has not been
  provided", reported at the alternatives, not at the merge);
* never touch bullets (`·`, `|`), `calc` steps (`_ = …`), or comment-bearing lines;
* never merge onto a line that ends mid-expression (`:=`, `by`, `do`, `=>`, `↦`, `(`, `[`, `,`);
* refuse any merge whose result exceeds 100 characters, checked before writing;
* never merge a line into one that was just merged (no chaining in a single pass).

usage: apply_sibs.py <decl-name> <count>
"""
import json
import re
import sys

sys.path.insert(0, '/private/tmp/claude-540497854/'
                   '-Users-mcu22seu-Documents-GitHub-aintlib-adic-spaces/'
                   'a4df1e2f-1042-4710-99e0-1ffb2e22f89a/scratchpad')
from apply_joins import body_span  # noqa: E402

ALT = re.compile(r"(?<![\w'])(induction|cases|rcases|obtain|match)\b.*\bwith\s*$")
TAIL = (':=', 'by', 'do', '=>', '↦', 'with', '(', '[', ',', '⟨')

# Tactics whose syntax ends in an OPTIONAL trailing tacticSeq.  They parse fine
# alone, so they look like self-contained tactics, but a `;` immediately after
# lands where the parser is still trying to read that optional block:
#     classical; have h : T := by     ->  "unexpected token ';'; expected tactic"
# Same family as ALT above -- the left line's syntax has not actually ended.
OPT_SEQ = re.compile(r"(?<![\w'])(classical|focus|next|case\s+\S+)\s*$")

# The nastiest case, because it produces a SILENT scope change rather than a
# parse error.  A term-level `by` runs to the end of the line, so a `;` appended
# to a line that already contains one lands INSIDE that block:
#     have h : T := by omega          + `; have h2 : U := by omega`
#  -> have h : T := by omega; have h2 : U := by omega
# and now h2 is introduced inside h's proof, not after it.  The symptom is
# "No goals to be solved" plus "Unknown identifier h2" at the USE site -- never
# at the merge.  A line ending in bare `by` is caught by TAIL; this catches the
# far more common line where the by-block is complete on the same line.
TERM_BY = re.compile(r":=\s*by\b|<\|\s*by\b|\bfrom\s+by\b")


OPENER = ('by', 'do', '=>', '↦', 'from')
# a line ending in one of these is mid-expression, so what follows continues it
CONT = (':=', '(', '[', ',', '⟨', '+', '*', '-', '→', 'fun')


def _eff_indent(line: str) -> int:
    """Content indent: a `· tac` bullet's content starts 2 columns in."""
    ind = len(line) - len(line.lstrip())
    return ind + 2 if line.lstrip().startswith(('· ', '. ')) else ind


def starts_a_tactic(prev: str, a: str, above=()) -> bool:
    """Is `a` the START of a tactic, or a CONTINUATION of `prev`'s expression?

    Equal indent between `a` and `c` is not enough: two argument-continuation
    lines of the same application are also equally indented, and `;`-merging
    them produces gibberish --

        exact foo_of_bar (baz qux)
          (quux corge).symm.toRingHom          <- `a`
          (RingEquiv.surjective _)             <- `c`

    Both are arguments of the `exact`, neither is a tactic.  The tell is that
    `a` is indented DEEPER than the content column of the line above it.  The
    exception is a line that opens a block (`by`, `do`, `=>`), whose body is
    legitimately deeper.
    """
    if not prev.strip():
        return True
    if prev.rstrip().endswith(OPENER):
        return True
    if (len(a) - len(a.lstrip())) > _eff_indent(prev):
        return False
    # `prev` may ITSELF be a continuation at the same indent, in which case the
    # one-line comparison above is fooled.  Walk back to the first line strictly
    # LESS indented than `a`: that is the line `a` actually continues (or the
    # tactic it belongs to).  If it does not end a complete tactic, `a` is an
    # argument line, not a tactic.
    #
    #     have hint := f p F ϖ φ hφ            <- indent 4, opens an application
    #       hρσ hσρ zb m hm a k                <- indent 6, continuation
    #       (le_trans (le_max_left _ _) hxw)   <- indent 6, ALSO a continuation
    #
    # Merging the last two with `;` yields `unknown tactic`.  Cost: one build.
    ai = len(a) - len(a.lstrip())
    for line in reversed(above):
        if not line.strip():
            continue
        if (len(line) - len(line.lstrip())) < ai:
            # In Lean a line indented past the tactic column CONTINUES the line
            # above unless that line opened a block (`by`, `do`, `=>`).  The
            # trailing token cannot decide this: `f p F ϖ φ hφ hφb` looks
            # complete but is a partial application continued below.
            return line.rstrip().endswith(OPENER)
    return True


def mergeable(a: str, c: str, prev: str = '', above=()) -> bool:
    if not a.strip() or not c.strip():
        return False
    if not starts_a_tactic(prev, a, above):
        return False
    if '--' in a or '--' in c:
        return False
    if a.lstrip().startswith(('·', '.', '|')) or c.lstrip().startswith(('·', '.', '|', '_')):
        return False
    if (a.rstrip().endswith(TAIL) or ALT.search(a) or OPT_SEQ.search(a)
            or TERM_BY.search(a)):
        return False
    if (len(a) - len(a.lstrip())) != (len(c) - len(c.lstrip())):
        return False
    return len(a.rstrip()) + 2 + len(c.strip()) <= 100


def main() -> int:
    name, want = sys.argv[1], int(sys.argv[2])
    rec = next(r for r in json.load(open('/tmp/over50_code.json'))
               if r['name'].split('.')[-1] == name)
    lines = open(rec['file']).read().split('\n')
    b, e = body_span(lines, rec['line'] - 1)
    picks, k, last = [], b, -10
    while k < e - 1:
        if k > last and mergeable(lines[k], lines[k + 1], lines[k - 1] if k else '', lines[max(0, k - 12):k]):
            picks.append(k)
            last = k + 1
            k += 2
            continue
        k += 1
    if len(picks) < want:
        print(f'FAIL {name}: only {len(picks)}/{want} safe sibling merges')
        return 1
    for k in reversed(picks[:want]):
        lines[k] = lines[k].rstrip() + '; ' + lines[k + 1].strip()
        del lines[k + 1]
    open(rec['file'], 'w').write('\n'.join(lines))
    print(f'ok  {name}: {want} sibling merge(s) at {[k + 1 for k in picks[:want]]}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
