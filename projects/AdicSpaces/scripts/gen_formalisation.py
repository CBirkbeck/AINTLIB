#!/usr/bin/env python3
"""Generate `formalisation.yaml` — the manifest of what this project has formalised.

    python3 scripts/gen_formalisation.py            # write projects/AdicSpaces/formalisation.yaml
    python3 scripts/gen_formalisation.py --stdout    # print instead

The manifest has two levels, because "what is formalised" has two useful granularities:

* `results:` — statement level. One entry per declaration whose docstring cites a source
  (Wedhorn / [FJP] / Huber / Stacks). This is the informal-to-formal correspondence: which
  numbered result in the literature is proved by which Lean declaration.
* `modules:` — the full inventory of every module in the library, so that "all of the adic
  spaces development" is covered rather than only the parts that happen to carry a citation.

Everything is derived from the source; nothing here is hand-maintained. Re-run after any
change and diff. `check_formalisation.py` verifies a committed manifest against the tree.
"""
from __future__ import annotations

import argparse
import collections
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from formalisation_lib import (  # noqa: E402
    GROUPS,
    LIB_NAMESPACE,
    REFERENCES,
    Decl,
    citation_id,
    extract_all,
    group_of,
    lean_files,
    module_name,
)
from mini_yaml import dump  # noqa: E402

SCHEMA = 1


def _git(repo: Path, *args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args], cwd=repo, capture_output=True, text=True, check=True
        ).stdout.strip()
    except Exception:
        return ""


def _toolchain(repo: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    tc = repo / "lean-toolchain"
    if tc.exists():
        out["toolchain"] = tc.read_text().strip()
    lf = repo / "lakefile.toml"
    if lf.exists():
        for line in lf.read_text().split("\n"):
            if line.strip().startswith("rev =") and "mathlib" not in out:
                out["mathlib_rev"] = line.split("=", 1)[1].split("#")[0].strip().strip('"')
                break
    return out


def status_of(d: Decl) -> str:
    return "sorry" if d.sorry else "proved"


def build(project_root: Path, repo_root: Path) -> dict:
    decls = extract_all(project_root)
    cited = [d for d in decls if d.citations]

    # ---- results: statement-level, one entry per cited declaration ----------
    results = []
    for d in sorted(cited, key=lambda x: (group_of(x.module), x.module, x.line)):
        results.append(
            {
                "decl": d.name,
                "kind": d.kind,
                "group": group_of(d.module),
                "module": d.module,
                "file": d.file,
                "line": d.line,
                "status": status_of(d),
                "digest": d.digest,
                "sources": d.citations,
                "statement": d.summary or "(no docstring summary)",
            }
        )

    # ---- modules: full inventory of the development -------------------------
    per_module: dict[str, list[Decl]] = collections.defaultdict(list)
    for d in decls:
        per_module[d.module].append(d)
    modules = []
    for mod in sorted(per_module):
        ds = per_module[mod]
        refs = sorted({citation_id(c) for d in ds for c in d.citations})
        modules.append(
            {
                "name": mod,
                "group": group_of(mod),
                "file": ds[0].file,
                "declarations": len(ds),
                "public": sum(not d.private for d in ds),
                "with_sorry": sum(d.sorry for d in ds),
                "results": sum(bool(d.citations) for d in ds),
                "sources": refs,
            }
        )
    # modules that declare nothing still belong in the inventory
    known = {m["name"] for m in modules}
    for p in lean_files(project_root):
        mod = module_name(project_root, p)
        if mod in known:
            continue
        try:
            rel = str(p.relative_to(repo_root))
        except ValueError:
            rel = str(p)
        modules.append(
            {
                "name": mod,
                "group": group_of(mod),
                "file": rel,
                "declarations": 0,
                "public": 0,
                "with_sorry": 0,
                "results": 0,
                "sources": [],
            }
        )
    modules.sort(key=lambda m: (m["group"], m["name"]))

    # ---- groups + summary ---------------------------------------------------
    groups = []
    for key, desc, _rx in GROUPS:
        gm = [m for m in modules if m["group"] == key]
        gr = [r for r in results if r["group"] == key]
        groups.append(
            {
                "id": key,
                "description": desc,
                "modules": len(gm),
                "declarations": sum(m["declarations"] for m in gm),
                "results": len(gr),
                "source_results": len({citation_id(s) for r in gr for s in r["sources"]}),
                "with_sorry": sum(m["with_sorry"] for m in gm),
            }
        )

    all_ids = {citation_id(s) for r in results for s in r["sources"]}
    # Deliberately no commit sha: it would change on every commit, so `regenerate and
    # diff` — the cheapest way to ask "has the manifest drifted?" — would never come back
    # empty, and a diff that is always dirty is a diff nobody reads. Provenance is the git
    # history of this file. Branch/toolchain/mathlib move rarely enough to be worth keeping.
    meta = {
        "name": "AdicSpaces",
        "library": LIB_NAMESPACE,
        "branch": _git(repo_root, "rev-parse", "--abbrev-ref", "HEAD"),
        **_toolchain(repo_root),
    }

    return {
        "schema": SCHEMA,
        "generated_by": "scripts/gen_formalisation.py",
        "project": meta,
        "references": {
            k: {"title": v["title"]} for k, v in REFERENCES.items()
        },
        "summary": {
            "modules": len(modules),
            "declarations": len(decls),
            "public": sum(not d.private for d in decls),
            "documented": sum(bool(d.docstring) for d in decls),
            "declarations_with_sorry": sum(d.sorry for d in decls),
            "results": len(results),
            "source_results": len(all_ids),
        },
        "groups": groups,
        "results": results,
        "modules": modules,
    }


HEADER = """\
# formalisation.yaml — what the AdicSpaces project has formalised.
#
# GENERATED FILE — do not edit by hand.
#   regenerate:  python3 scripts/gen_formalisation.py
#   verify:      python3 scripts/check_formalisation.py
#
# `results` maps numbered results in the literature to the Lean declarations that prove
# them; `modules` is the full inventory of the development. `digest` is a hash of the
# declaration's STATEMENT (up to the top-level `:=`), so the checker can tell a renamed
# declaration from a restated one.
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stdout", action="store_true", help="print instead of writing the file")
    args = ap.parse_args()

    project_root = Path(__file__).resolve().parents[1]
    repo_root = project_root.parents[1]
    data = build(project_root, repo_root)
    text = HEADER + dump(data) + "\n"

    if args.stdout:
        sys.stdout.write(text)
    else:
        out = project_root / "formalisation.yaml"
        out.write_text(text)
        s = data["summary"]
        print(f"wrote {out.relative_to(repo_root)}  ({len(text.splitlines())} lines)")
        print(
            f"  {s['modules']} modules, {s['declarations']} declarations, "
            f"{s['results']} cited results covering {s['source_results']} source results, "
            f"{s['declarations_with_sorry']} declarations with sorry"
        )
        for g in data["groups"]:
            print(
                f"  - {g['id']:12s} {g['modules']:4d} modules {g['declarations']:5d} decls "
                f"{g['results']:4d} results ({g['source_results']} sources) "
                f"{g['with_sorry']:3d} sorry"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
