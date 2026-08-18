#!/usr/bin/env python3
"""File GitHub tickets from /overview Step-9 mathlibable verdicts for one AINTLIB project.

Reads projects/<P>/.mathlib-quality/overview/mathlibable_ledger.tsv (qual<TAB>bucket<TAB>rationale)
and the per-decl reports in .../mathlibable/<base>.md. Qualified name + source location are
recovered from each report (H1 backtick + first project path). Dedup-safe by issue title, so
safe to re-run as more verdicts land.

Mapping (same as the first project):
  YES-but-generalise-first        -> generalise            lane:generalise,state:todo,mathlibable
  NO-mathlib-has-it / NO-composable -> cleanup(mathlib-dedup) lane:cleanup,state:todo,mathlibable
  YES-add-as-is                   -> mathlib-PR             mathlibable,mathlib:pr   (tracking)
  BORDERLINE-needs-human          -> mathlib-decision       mathlibable,mathlib:borderline (tracking)

Usage: file_mathlibable_tickets.py <Project> [--dry-run]
"""
import json, subprocess, os, re, sys

GH = "/opt/homebrew/bin/gh"
REPO = "CBirkbeck/AINTLIB"
ROOT = "/Users/mcu22seu/Documents/GitHub/aintlib-main"

if len(sys.argv) < 2:
    sys.exit("usage: file_mathlibable_tickets.py <Project> [--dry-run]")
PROJ = sys.argv[1]
DRY = "--dry-run" in sys.argv[2:]

OVDIR = f"{ROOT}/projects/{PROJ}/.mathlib-quality/overview"
LEDGER = f"{OVDIR}/mathlibable_ledger.tsv"
REPORTDIR_ABS = f"{OVDIR}/mathlibable"
REPORTDIR_REL = f"projects/{PROJ}/.mathlib-quality/overview/mathlibable"

if not os.path.exists(LEDGER):
    sys.exit(f"no ledger at {LEDGER}")

h1pat = re.compile(r'^#\s+.*?`([^`]+)`', re.M)
locpat = re.compile(r'(projects/' + re.escape(PROJ) + r'/[^\s`)]+\.lean:\d+)')

def report_info(base):
    """Return (qual, loc) for a ledger base name.

    The qualified name can come from the filename (projects I name `<qual>.md`) or the
    report H1 (legacy projects with short-name filenames). Pick the best valid candidate:
    reject garbage like `/mathlibable`; prefer the most-qualified (most dots, then longest)."""
    p = f"{REPORTDIR_ABS}/{base}.md"
    candidates = [base]
    loc = ""
    if os.path.exists(p):
        txt = open(p).read()
        m = h1pat.search(txt)
        if m:
            candidates.append(m.group(1).strip())
        m = locpat.search(txt)
        if m:
            loc = m.group(1)
    valid = [q for q in candidates if q and '/' not in q and ' ' not in q and '`' not in q]
    if not valid:
        valid = [base]
    qual = max(valid, key=lambda q: (q.count('.'), len(q)))
    return qual, loc

def plan(bucket):
    if bucket == 'YES-but-generalise-first':
        return ('generalise', ['lane:generalise', 'state:todo', 'mathlibable'])
    if bucket in ('NO-composable-from-mathlib', 'NO-mathlib-has-it'):
        return ('cleanup(mathlib-dedup)', ['lane:cleanup', 'state:todo', 'mathlibable'])
    if bucket == 'YES-add-as-is':
        return ('mathlib-PR', ['mathlibable', 'mathlib:pr'])
    if bucket == 'BORDERLINE-needs-human':
        return ('mathlib-decision', ['mathlibable', 'mathlib:borderline'])
    return (None, None)

# ensure labels exist
if not DRY:
    for lab, color, desc in [('mathlibable', '5319e7', 'from /overview Step-9 mathlibable assessment'),
                             ('mathlib:pr', '0e8a16', 'candidate to PR to mathlib as-is'),
                             ('mathlib:borderline', 'fbca04', 'mathlibable verdict needs a human scope call')]:
        subprocess.run([GH, 'label', 'create', lab, '--repo', REPO, '--color', color,
                        '--description', desc, '--force'], capture_output=True)

# existing mathlibable titles (dedup)
ex = subprocess.run([GH, 'issue', 'list', '--repo', REPO, '--label', 'mathlibable',
                     '--state', 'all', '--limit', '4000', '--json', 'title'],
                    capture_output=True, text=True)
existing = set(d['title'] for d in (json.loads(ex.stdout) if ex.stdout.strip() else []))

from collections import Counter
filed = Counter(); skipped = 0; planned = Counter()
rows = open(LEDGER).read().splitlines()[1:]
for line in rows:
    parts = line.split('\t')
    if len(parts) < 2:
        continue
    base, bucket = parts[0], parts[1]
    rat = parts[2] if len(parts) >= 3 else ""
    pfx, labels = plan(bucket)
    if not pfx:
        continue
    qual, loc = report_info(base)
    title = f"{pfx}: {qual}"
    planned[pfx] += 1
    if title in existing:
        skipped += 1
        continue
    locline = f"**Decl:** `{qual}`" + (f" — `{loc}`" if loc else "") + "\n"
    directive = ""
    if pfx == 'generalise':
        directive = ("\n\n**Worker — finish the work (no lazy bailing).** Re-prove the weakened statement AND "
                     "fix every consumer; that adjustment is the job. Effort / proof length / \"too much work\" "
                     "is NOT a reason to bail or relabel back. DONE = a pushed, building PR — you may NEVER move "
                     "this to `state:review` without one. The only legitimate stop is a `sorry` in the target "
                     "(producer WIP) or a *genuinely* impossible generalisation with the **specific** proof "
                     "obstruction named. See `docs/worker-prompts/generalise-worker.md`.")
    body = (f"**Verdict:** `{bucket}`\n\n{rat}\n\n"
            f"{locline}"
            f"**Evidence:** `{REPORTDIR_REL}/{base}.md`{directive}\n\n"
            f"_From `/overview` Step-9 mathlibable assessment ({PROJ})._")
    if DRY:
        filed[pfx] += 1
        existing.add(title)
        continue
    args = [GH, 'issue', 'create', '--repo', REPO, '--title', title, '--body', body]
    for l in labels:
        args += ['--label', l]
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode == 0:
        filed[pfx] += 1
        existing.add(title)
    else:
        print("ERR", title, '::', r.stderr.strip()[:140])

print(f"project={PROJ} dry_run={DRY}")
print("planned (by type):", dict(planned), "| total planned:", sum(planned.values()))
print("would-file" if DRY else "filed", "(new):", dict(filed), "| total:", sum(filed.values()))
print("skipped (already exist):", skipped)
