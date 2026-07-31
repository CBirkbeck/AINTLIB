#!/usr/bin/env python3
"""Compare `formalisation.yaml` against the actual Lean source, and report drift.

    python3 scripts/check_formalisation.py                  # structural check (fast, no build)
    python3 scripts/check_formalisation.py --group fjp      # scope to one group
    python3 scripts/check_formalisation.py --strict         # warnings are failures too
    python3 scripts/check_formalisation.py --axioms         # also run `#print axioms` (slow)
    python3 scripts/check_formalisation.py --json           # machine-readable report

Exit status is 0 when nothing at ERROR level was found (or nothing at all under `--strict`).

What it catches, and why each matters here:

  RESTATED (error)   the declaration still exists but its STATEMENT changed — the digest in
                     the manifest no longer matches. This project's cleanup rules forbid
                     changing a theorem statement to make something pass, so a restatement
                     that nobody recorded is exactly the thing to fail on.
  MISSING  (error)   a manifest entry names a declaration that no longer exists: renamed or
                     deleted without updating the manifest.
  REGRESSED(error)   a result recorded as `proved` now contains a `sorry`.
  MOVED    (warning) same declaration, different module — the manifest is stale.
  UNLISTED (warning) a declaration in the tree cites a source but is absent from the
                     manifest: new formalised work that was never recorded.
  PROMOTED (warning) recorded as `sorry`, now proved — good news, stale manifest.
  COUNTS   (warning) a module's declaration count moved.

Line numbers are deliberately NOT checked: they move on every cleanup commit, and a checker
that fails on them gets switched off.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from formalisation_lib import citation_id, extract_all, group_of  # noqa: E402
from mini_yaml import load  # noqa: E402

ERROR, WARN, INFO = "error", "warning", "info"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class Report:
    def __init__(self) -> None:
        self.items: list[dict] = []

    def add(self, level: str, kind: str, subject: str, detail: str) -> None:
        self.items.append(
            {"level": level, "kind": kind, "subject": subject, "detail": detail}
        )

    def count(self, level: str) -> int:
        return sum(1 for i in self.items if i["level"] == level)


def structural_check(manifest: dict, decls: list, only: str | None, rep: Report) -> None:
    # Key on (module, name) first. Two modules that are never imported together may declare
    # the same fully-qualified name, and a name-only index would then compare an entry
    # against the wrong declaration and report a phantom RESTATED.
    by_key = {(d.module, d.name): d for d in decls}
    by_name: dict[str, list] = collections.defaultdict(list)
    for d in decls:
        by_name[d.name].append(d)

    listed = {(r["module"], r["decl"]) for r in manifest.get("results") or []}

    for entry in manifest.get("results") or []:
        if only and entry.get("group") != only:
            continue
        name = entry["decl"]
        d = by_key.get((entry["module"], name))
        if d is None:
            elsewhere = by_name.get(name) or []
            if not elsewhere:
                rep.add(ERROR, "MISSING", name,
                        f"listed in {entry['module']} but not found anywhere in the library")
                continue
            d = elsewhere[0]
            rep.add(WARN, "MOVED", name,
                    f"manifest says {entry['module']}, found in "
                    + ", ".join(x.module for x in elsewhere))
        if d.digest != entry.get("digest"):
            rep.add(ERROR, "RESTATED", name,
                    f"statement digest {entry.get('digest')} -> {d.digest}")
        was, now = entry.get("status"), ("sorry" if d.sorry else "proved")
        if was == "proved" and now == "sorry":
            rep.add(ERROR, "REGRESSED", name, "recorded as proved, now contains a sorry")
        elif was == "sorry" and now == "proved":
            rep.add(WARN, "PROMOTED", name, "recorded as sorry, now proved — regenerate")
        want = {citation_id(s) for s in (entry.get("sources") or [])}
        have = {citation_id(s) for s in d.citations}
        if want != have:
            rep.add(WARN, "SOURCES", name,
                    f"citations changed: {sorted(want)} -> {sorted(have)}")

    for d in decls:
        if not d.citations:
            continue
        if only and group_of(d.module) != only:
            continue
        if (d.module, d.name) not in listed:
            cites = ", ".join(citation_id(c) for c in d.citations)
            rep.add(WARN, "UNLISTED", d.name,
                    f"cites {cites} in {d.module} but is not in the manifest")

    # ---- module inventory ---------------------------------------------------
    per_module = collections.Counter(d.module for d in decls)
    listed_modules = {m["name"]: m for m in (manifest.get("modules") or [])}
    for name, m in listed_modules.items():
        if only and m.get("group") != only:
            continue
        if name not in per_module and m.get("declarations", 0) > 0:
            rep.add(ERROR, "MODULE-GONE", name, "module in manifest has no declarations now")
        elif per_module.get(name, 0) != m.get("declarations", 0):
            rep.add(WARN, "COUNTS", name,
                    f"declarations {m.get('declarations')} -> {per_module.get(name, 0)}")
    for name in per_module:
        if only and group_of(name) != only:
            continue
        if name not in listed_modules:
            rep.add(WARN, "MODULE-NEW", name, "module not in the manifest")


def axiom_check(manifest: dict, decls: list, only: str | None, repo: Path,
                rep: Report) -> None:
    """Run `#print axioms` on every non-private listed result and check the axiom set."""
    by_name = {d.name: d for d in decls}
    targets = []
    for entry in manifest.get("results") or []:
        if only and entry.get("group") != only:
            continue
        if entry.get("status") != "proved":
            continue
        d = by_name.get(entry["decl"])
        if d is None or d.private:
            continue           # private names are mangled; #print axioms cannot reach them
        targets.append(d)
    if not targets:
        print("axiom check: nothing to do")
        return

    modules = sorted({d.module for d in targets})
    src = "\n".join(f"import {m}" for m in modules)
    src += "\n" + "\n".join(f"#print axioms {d.name}" for d in targets) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     dir=repo, encoding="utf-8") as fh:
        fh.write(src)
        path = Path(fh.name)
    print(f"axiom check: {len(targets)} declarations across {len(modules)} modules …")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=repo, capture_output=True, text=True,
            env={**__import__("os").environ, "LEAN4_GUARDRAILS_BYPASS": "1"},
        )
    finally:
        path.unlink(missing_ok=True)

    out = proc.stdout + proc.stderr
    seen = set()
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        name, axs = m.group(1), {a.strip() for a in m.group(2).split(",") if a.strip()}
        seen.add(name)
        extra = axs - ALLOWED_AXIOMS
        if extra:
            level = ERROR if "sorryAx" in extra else WARN
            rep.add(level, "AXIOMS", name, f"depends on {sorted(extra)}")
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
        seen.add(m.group(1))
    for d in targets:
        if d.name not in seen:
            rep.add(WARN, "AXIOM-UNKNOWN", d.name, "no #print axioms output (check the name)")
    for m in re.finditer(r"error[:(]", out):
        rep.add(ERROR, "AXIOM-BUILD", "-", "lean reported errors while checking axioms")
        break


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", help="restrict to one group id (fjp / examples / adic-spaces)")
    ap.add_argument("--strict", action="store_true", help="warnings fail too")
    ap.add_argument("--axioms", action="store_true", help="also run #print axioms (slow)")
    ap.add_argument("--json", action="store_true", help="machine-readable report")
    ap.add_argument("--manifest", help="path to formalisation.yaml")
    ap.add_argument("--list", action="store_true",
                    help="print the informal-to-formal table instead of checking")
    args = ap.parse_args()

    project_root = Path(__file__).resolve().parents[1]
    repo_root = project_root.parents[1]
    mpath = Path(args.manifest) if args.manifest else project_root / "formalisation.yaml"
    if not mpath.exists():
        print(f"no manifest at {mpath}; run scripts/gen_formalisation.py", file=sys.stderr)
        return 2

    manifest = load(mpath.read_text())
    rep = Report()
    if manifest.get("schema") != 1:
        rep.add(ERROR, "SCHEMA", str(mpath), f"unsupported schema {manifest.get('schema')}")
        print(json.dumps(rep.items) if args.json else "unsupported schema")
        return 1

    if args.list:
        rows = [r for r in (manifest.get("results") or [])
                if not args.group or r.get("group") == args.group]
        by_source: dict[str, list[dict]] = collections.defaultdict(list)
        for r in rows:
            for s in r.get("sources") or []:
                by_source[citation_id(s)].append(r)
        print(f"{len(rows)} results covering {len(by_source)} source statements"
              + (f" [group={args.group}]" if args.group else ""))
        for cid in sorted(by_source, key=lambda c: (c.split(":")[0], c)):
            entries = by_source[cid]
            kind = next((s.get("kind", "") for r in entries
                         for s in r["sources"] if citation_id(s) == cid), "")
            print(f"\n  {cid}" + (f"   ({kind})" if kind else ""))
            for r in entries:
                flag = " [sorry]" if r["status"] != "proved" else ""
                print(f"      {r['decl']}{flag}")
                print(f"          {r['statement'][:110]}")
        return 0

    decls = extract_all(project_root)
    structural_check(manifest, decls, args.group, rep)
    if args.axioms:
        axiom_check(manifest, decls, args.group, repo_root, rep)

    if args.json:
        print(json.dumps({"items": rep.items,
                          "errors": rep.count(ERROR),
                          "warnings": rep.count(WARN)}, indent=2, ensure_ascii=False))
    else:
        by_kind = collections.Counter(i["kind"] for i in rep.items)
        scope = f" [group={args.group}]" if args.group else ""
        print(f"formalisation check{scope}: "
              f"{len(manifest.get('results') or [])} results, "
              f"{len(manifest.get('modules') or [])} modules in manifest")
        if not rep.items:
            print("  no drift — manifest matches the source")
        for kind, n in by_kind.most_common():
            lvl = next(i["level"] for i in rep.items if i["kind"] == kind)
            print(f"  {lvl.upper():7s} {kind:14s} {n}")
        shown = 0
        for i in rep.items:
            if i["level"] == ERROR or (args.strict and i["level"] == WARN):
                print(f"    {i['kind']}: {i['subject']}\n        {i['detail']}")
                shown += 1
                if shown >= 40:
                    print(f"    … {len(rep.items) - shown} more")
                    break
        print(f"  {rep.count(ERROR)} error(s), {rep.count(WARN)} warning(s)")

    bad = rep.count(ERROR) + (rep.count(WARN) if args.strict else 0)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
