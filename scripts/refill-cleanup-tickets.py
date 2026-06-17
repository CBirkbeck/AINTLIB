#!/usr/bin/env python3
"""Refill AINTLIB cleanup tickets for the next un-ticketed project.

Files one GitHub issue per *cleanable* .lean file (a file with >=1 substantial,
sorry-free proof), labelled `lane:cleanup` + `state:todo`. Skips any file that
already has a cleanup ticket (exact-title dedup), so it is safe to re-run.

The coordinator cron calls this when the cleanup queue runs low. It is paced:
`--max` caps how many it files per run, and `--next` keeps choosing the first
project in ORDER that still has un-ticketed cleanable files.

Usage:
  refill-cleanup-tickets.py --next   [--dry-run] [--max 60]
  refill-cleanup-tickets.py --project HasseWeil [--dry-run] [--max 60]
"""
import os, re, sys, json, subprocess, argparse

REPO = "CBirkbeck/AINTLIB"
GH   = "/opt/homebrew/bin/gh"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # repo root (scripts/..)

# Projects to ticket, in priority order. PadicLFunctions + AdicSpaces are already
# ticketed; FltRegular is vendored upstream (never cleaned here).
ORDER = ["HasseWeil", "LeanModularForms", "NagellLutz", "Chebotarev", "FltRegularBernoulli"]
SKIP_PROJECTS = {"FltRegular"}

MIN_PROOF_LINES = 20   # only ticket files with a proof at least this long (real golf value)


def strip_comments(s: str) -> str:
    """Remove Lean block comments (nested), line comments, and string literals,
    so a `sorry` inside a comment/string does not count as a real sorry."""
    out = []; i = 0; n = len(s); depth = 0; instr = False
    while i < n:
        c = s[i]; nxt = s[i + 1] if i + 1 < n else ''
        if depth > 0:
            if c == '/' and nxt == '-': depth += 1; i += 2; continue
            if c == '-' and nxt == '/': depth -= 1; i += 2; continue
            i += 1; continue
        if instr:
            if c == '\\': i += 2; continue
            if c == '"': instr = False
            i += 1; continue
        if c == '/' and nxt == '-': depth = 1; i += 2; continue
        if c == '-' and nxt == '-':
            j = s.find('\n', i)
            if j < 0: break
            i = j; continue
        if c == '"': instr = True; i += 1; continue
        out.append(c); i += 1
    return ''.join(out)


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |scoped )*"
    r"(theorem|lemma|def|instance|structure|abbrev|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def cleanable_count(path: str) -> int:
    """Number of theorem/lemma proofs that are substantial (>=MIN_PROOF_LINES) and sorry-free."""
    try:
        lines = open(path, encoding='utf-8', errors='ignore').read().split('\n')
    except Exception:
        return 0
    decls = [(i, m.group(1)) for i, l in enumerate(lines) for m in [DECL.match(l)] if m]
    cnt = 0
    for j, (ln, kind) in enumerate(decls):
        if kind not in ('theorem', 'lemma'):
            continue
        end = decls[j + 1][0] if j + 1 < len(decls) else len(lines)
        if end - ln < MIN_PROOF_LINES:
            continue
        if re.search(r'\bsorry\b', strip_comments('\n'.join(lines[ln:end]))):
            continue
        cnt += 1
    return cnt


def lib_for(project: str) -> str:
    """Resolve the lean_lib name whose srcDir is projects/<project> from lakefile.toml."""
    try:
        txt = open(os.path.join(ROOT, 'lakefile.toml'), encoding='utf-8').read()
    except Exception:
        return project
    for b in re.split(r'\[\[lean_lib\]\]', txt):
        nm = re.search(r'name\s*=\s*"([^"]+)"', b)
        sd = re.search(r'srcDir\s*=\s*"projects/([^"]+)"', b)
        if nm and sd and sd.group(1) == project:
            return nm.group(1)
    return project


def existing_cleanup_titles() -> set:
    out = subprocess.run(
        [GH, "issue", "list", "--repo", REPO, "--label", "lane:cleanup",
         "--state", "all", "--limit", "5000", "--json", "title"],
        capture_output=True, text=True)
    try:
        return {d['title'] for d in json.loads(out.stdout)}
    except Exception:
        return set()


def new_candidates(project: str, titles: set):
    """(lib, [(rel, title, count), ...]) of cleanable files in `project` without a ticket yet."""
    pdir = os.path.join(ROOT, 'projects', project)
    if not os.path.isdir(pdir):
        return project, []
    lib = lib_for(project); cands = []
    for r, _, fs in os.walk(pdir):
        if '.lake' in r:
            continue
        for fn in sorted(fs):
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(r, fn)
            rel = os.path.relpath(p, pdir)               # e.g. "HasseWeil/Foo/Bar.lean"
            title = f"cleanup: {rel}"
            if title in titles:
                continue
            c = cleanable_count(p)
            if c >= 1:
                cands.append((rel, title, c))
    cands.sort()
    return lib, cands


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--next', action='store_true', help='pick the first ORDER project with new cleanable files')
    ap.add_argument('--project', help='ticket a specific project')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--max', type=int, default=60)
    a = ap.parse_args()
    if not (a.next or a.project):
        ap.error("need --next or --project")

    titles = existing_cleanup_titles()
    project = None; lib = None; cands = []
    if a.project:
        if a.project in SKIP_PROJECTS:
            print(f"refill: {a.project} is skipped (vendored)"); return
        project = a.project; lib, cands = new_candidates(project, titles)
    else:  # --next
        for proj in ORDER:
            if proj in SKIP_PROJECTS:
                continue
            lib, cands = new_candidates(proj, titles)
            if cands:
                project = proj; break

    if not project or not cands:
        print("refill: no un-ticketed cleanable files found (nothing to do)"); return

    print(f"refill: project={project} lib={lib} new-cleanable-files={len(cands)} "
          f"max={a.max} dry_run={a.dry_run}")
    filed = 0
    for rel, title, c in cands[:a.max]:
        body = (f"`{lib}` · {c} substantial sorry-free proof(s) in `projects/{project}/{rel}`.\n\n"
                f"Run `/cleanup` on the whole file; skip any declaration whose proof contains a `sorry`.")
        if a.dry_run:
            print(f"  [dry] {title}  ({c})"); filed += 1; continue
        r = subprocess.run(
            [GH, "issue", "create", "--repo", REPO, "--title", title, "--body", body,
             "--label", "lane:cleanup", "--label", "state:todo"],
            capture_output=True, text=True)
        if r.returncode == 0:
            print(f"  filed {title}"); filed += 1
        else:
            print(f"  ERR  {title}: {r.stderr.strip()[:140]}")
    print(f"refill: {'would file' if a.dry_run else 'filed'} {filed} ticket(s) for {project}"
          f"  ({len(cands) - filed} more remain for next run)")


if __name__ == '__main__':
    main()
