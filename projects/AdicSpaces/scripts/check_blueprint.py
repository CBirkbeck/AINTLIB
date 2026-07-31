#!/usr/bin/env python3
"""Verify every `(lean := …)` reference in the blueprint resolves to a real declaration.

    python3 scripts/check_blueprint.py            # exit 1 if any reference dangles
    python3 scripts/check_blueprint.py --json

This checks the opposite direction from `check_formalisation.py`, and that is the whole point.
The manifest checker runs **library → manifest**: it starts from declarations that exist and
asks what the manifest failed to record. It is structurally incapable of noticing a *claim*
about a declaration that does not exist.

Blueprint nodes carry `(lean := "Foo.bar, Foo.baz")` and Verso reads each node's completion
status from those names. When a declaration is renamed or never lands, the reference dangles
silently and the published blueprint reports progress on something that is not there.

That is not hypothetical: this check was written after finding three such references
(`IsRationalSubset.inter`, `IsRationalSubset.isOpen`,
`structurePresheaf_typeLevel_isSheaf`) in a blueprint that otherwise resolved cleanly.

A fully-qualified miss whose final component matches exactly one declaration is reported as
**RENAMED**, not silently resolved. Doing the latter hides the defect: `IsRationalSubset.isOpen`
"resolves" to `HasRationalPresentation.isOpen`, which is indeed the intended declaration — but
under a different namespace, so the blueprint reference is stale and Verso will not find it.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from formalisation_lib import extract_all  # noqa: E402

BLUEPRINT = Path("AdicSpacesBlueprint/Blueprint.lean")
#: `:::theorem "slug" (lean := "A.b, C.d")`
_REF = re.compile(r'\(lean\s*:=\s*"([^"]*)"\)')
_NODE = re.compile(r'^:::(\w+)\s+"([^"]*)"')


def blueprint_refs(path: Path) -> list[dict]:
    """Every `(lean := …)` name, with the node and line it came from."""
    out: list[dict] = []
    node = ("?", "?")
    for i, line in enumerate(path.read_text(errors="replace").split("\n"), 1):
        m = _NODE.match(line)
        if m:
            node = (m.group(1), m.group(2))
        for m in _REF.finditer(line):
            for name in (n.strip() for n in m.group(1).split(",")):
                if name:
                    out.append({"name": name, "kind": node[0], "slug": node[1], "line": i})
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--blueprint", help="path to the blueprint source")
    args = ap.parse_args()

    project_root = Path(__file__).resolve().parents[1]
    bp = Path(args.blueprint) if args.blueprint else project_root / BLUEPRINT
    if not bp.exists():
        print(f"no blueprint at {bp}", file=sys.stderr)
        return 2

    refs = blueprint_refs(bp)
    decls = extract_all(project_root)
    by_full = {d.name: d for d in decls}
    by_last: dict[str, list] = {}
    for d in decls:
        by_last.setdefault(d.name.split(".")[-1], []).append(d)

    dangling, renamed, undocumented = [], [], []
    for r in refs:
        d = by_full.get(r["name"])
        if d is None:
            cand = by_last.get(r["name"].split(".")[-1], [])
            if len(cand) == 1:
                renamed.append({**r, "actual": cand[0].name, "module": cand[0].module})
                d = cand[0]
            else:
                dangling.append({**r, "candidates": [c.name for c in cand]})
                continue
        if not d.docstring:
            undocumented.append({**r, "module": d.module})

    if args.json:
        print(json.dumps({"references": len(refs), "dangling": dangling,
                          "renamed": renamed, "undocumented": undocumented},
                         indent=2, ensure_ascii=False))
    else:
        print(f"blueprint references {len(refs)} declarations in {bp.name}")
        if dangling:
            print(f"\n  DANGLING ({len(dangling)}) — referenced but not in the library:")
            for r in dangling:
                print(f"    {r['name']}")
                if r.get("candidates"):
                    print(f"        ambiguous final component: {r['candidates']}")
                print(f"        {r['kind']} \"{r['slug']}\" at {bp.name}:{r['line']}")
        if renamed:
            print(f"\n  RENAMED ({len(renamed)}) — reference is stale; Verso will not resolve it:")
            for r in renamed:
                print(f"    {r['name']}")
                print(f"        -> {r['actual']}  ({r['module']})")
                print(f"        {r['kind']} \"{r['slug']}\" at {bp.name}:{r['line']}")
        if undocumented:
            print(f"\n  UNDOCUMENTED ({len(undocumented)}) — referenced but no docstring:")
            for r in undocumented:
                print(f"    {r['name']}  ({r['module']})")
        if not dangling and not renamed and not undocumented:
            print("  all references resolve, all documented")
    return 1 if (dangling or renamed) else 0


if __name__ == "__main__":
    sys.exit(main())
