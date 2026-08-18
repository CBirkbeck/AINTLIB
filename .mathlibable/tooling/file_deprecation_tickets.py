#!/usr/bin/env python3
"""File cleanup(deprecation) tickets from a bump build log.

Scans a `lake build` log (e.g. build_all.sh output) for mathlib deprecation
warnings ("`X` has been deprecated …" / "'Mathlib.Foo' has been deprecated …"),
groups them by deprecated symbol/import, and files ONE `cleanup(deprecation): <sym>`
ticket per symbol listing every affected file. Dedup-safe by title against the
`deprecation` label, so re-running on the same or a later bump never duplicates —
a deprecation regenerates every build until the fleet fixes it.

  -> lane:cleanup, state:todo, deprecation

Usage: file_deprecation_tickets.py <build_log> [--dry-run]
"""
import json, subprocess, os, re, sys
from collections import defaultdict, Counter

GH = "/opt/homebrew/bin/gh"
REPO = "CBirkbeck/AINTLIB"

if len(sys.argv) < 2:
    sys.exit("usage: file_deprecation_tickets.py <build_log> [--dry-run]")
LOG = sys.argv[1]
DRY = "--dry-run" in sys.argv[2:]
if not os.path.exists(LOG):
    sys.exit(f"no build log at {LOG}")

# warning: <file>.lean:<line>:<col>: `sym` (or 'sym') has been deprecated[.:] <replacement…>
pat = re.compile(
    r"warning:\s+(?P<file>[^:]+\.lean):\d+:\d+:\s+[`'](?P<sym>[^`']+)[`']\s+has been deprecated[.:]?\s*(?P<rep>.*)$")

by_sym = defaultdict(lambda: {"files": set(), "rep": ""})
for line in open(LOG, errors="replace").read().splitlines():
    m = pat.search(line)
    if not m:
        continue
    sym = m.group("sym").strip()
    e = by_sym[sym]
    e["files"].add(m.group("file").strip())
    rep = m.group("rep").strip()
    if rep and len(rep) > len(e["rep"]):
        e["rep"] = rep  # keep the most informative replacement hint seen

if not by_sym:
    print("no deprecation warnings found in", LOG)
    sys.exit(0)

# ensure the dedup label exists
if not DRY:
    subprocess.run([GH, 'label', 'create', 'deprecation', '--repo', REPO, '--color', 'd4c5f9',
                    '--description', 'mathlib deprecation surfaced by the daily bump', '--force'],
                   capture_output=True)

# dedup against existing deprecation-labelled titles
ex = subprocess.run([GH, 'issue', 'list', '--repo', REPO, '--label', 'deprecation',
                     '--state', 'all', '--limit', '4000', '--json', 'title'],
                    capture_output=True, text=True)
existing = set(d['title'] for d in (json.loads(ex.stdout) if ex.stdout.strip() else []))

filed = 0; skipped = 0
for sym in sorted(by_sym):
    e = by_sym[sym]
    files = sorted(e["files"])
    title = f"cleanup(deprecation): {sym}"
    if title in existing:
        skipped += 1
        continue
    rep = e["rep"] or "(see the warning at the site for the suggested replacement)"
    filelist = "\n".join(f"- `{f}`" for f in files)
    body = (f"**Deprecated:** `{sym}`\n\n"
            f"**Replacement:** {rep}\n\n"
            f"Mathlib deprecated this; surfaced by the daily bump build. Mechanical replacement at each "
            f"site below. (`cleanup(deprecation)` regenerates every bump until fixed.) Skip any `sorry`'d decl.\n\n"
            f"**Affected files ({len(files)}):**\n{filelist}\n\n"
            f"_Filed by the daily mathlib bump from the build log._")
    if DRY:
        print(f"WOULD FILE: {title}  ({len(files)} file(s))")
        filed += 1
        existing.add(title)
        continue
    args = [GH, 'issue', 'create', '--repo', REPO, '--title', title, '--body', body,
            '--label', 'lane:cleanup', '--label', 'state:todo', '--label', 'deprecation']
    r = subprocess.run(args, capture_output=True, text=True)
    if r.returncode == 0:
        filed += 1
        existing.add(title)
        print("filed:", title, f"({len(files)} file(s))")
    else:
        print("ERR", title, '::', r.stderr.strip()[:140])

print(f"\ndry_run={DRY} | distinct deprecations={len(by_sym)} | filed(new)={filed} | skipped(existing)={skipped}")
