#!/usr/bin/env python3
"""all_modules.py — emit EVERY Lean module name in the AINTLIB workspace.

`lake build <lib>` compiles only modules reachable from that lib's root import,
so orphan / WIP files (imported by nobody) are invisible — the green-gate blind
spot that let bump fallout hide in FLT37 orphans. This enumerates every `.lean`
file under each declared lean_lib's srcDir and derives its module name
(relpath(file, srcDir) with `/`→`.`, minus `.lean`), so `build_all.sh` can build
the whole tree, orphans included.

One module name per line (may contain spaces, e.g. `«Adic spaces».TateAlgebra`).
"""
import os, re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def libs():
    """(name, srcDir) for every [[lean_lib]] in lakefile.toml."""
    out, in_lib, name = [], False, None
    for line in open(os.path.join(ROOT, "lakefile.toml"), encoding="utf-8"):
        s = line.strip()
        if s == "[[lean_lib]]":
            in_lib, name = True, None
            continue
        if s.startswith("[["):
            in_lib = False
        if not in_lib:
            continue
        m = re.match(r'name\s*=\s*"(.*)"', s)
        if m:
            name = m.group(1)
        m = re.match(r'srcDir\s*=\s*"(.*)"', s)
        if m and name:
            out.append((name, m.group(1)))
    return out


def main():
    seen = set()
    for name, src in libs():
        base = os.path.join(ROOT, src)
        if not os.path.isdir(base):
            continue
        for dirpath, _, files in os.walk(base):
            # Skip non-library trees under a lib's srcDir: process artifacts
            # (.mathlib-quality/) and Verso blueprint sources (blueprint dirs /
            # *Blueprint* files) — these are .lean but not declared lake targets.
            low = dirpath.lower()
            if ".mathlib-quality" in low or "blueprint" in low:
                continue
            for f in files:
                if not f.endswith(".lean"):
                    continue
                if "blueprint" in f.lower():
                    continue
                rel = os.path.relpath(os.path.join(dirpath, f), base)
                # module = path components joined by '.'; any component with a
                # space (e.g. the «Adic spaces» lib root) needs Lean «» quoting.
                comps = [c if " " not in c else f"«{c}»" for c in rel[:-5].split(os.sep)]
                mod = ".".join(comps)
                if mod not in seen:
                    seen.add(mod)
                    print(mod)


if __name__ == "__main__":
    main()
