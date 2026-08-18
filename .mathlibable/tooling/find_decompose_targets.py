#!/usr/bin/env python3
"""Find long, sorry-free theorem/lemma proofs that are `/decompose-proof` targets.

Scans projects/ for theorem/lemma blocks longer than the 50-line decompose threshold,
skips any containing `sorry`/`admit` (producer WIP), ranks by length. Prints candidates;
`--file [N]` files the top N as lane:decompose / state:todo tickets (dedup-safe by title).

Usage: find_decompose_targets.py [--min N] [--file K]
"""
import os, re, subprocess, sys, json

GH = "/opt/homebrew/bin/gh"; REPO = "CBirkbeck/AINTLIB"; ROOT = "projects"

# protected paths: never file decompose tickets on files reserved for an active dev-extraction
PROT_FILE = "docs/worker-prompts/protected-paths.txt"
PROTECTED = [l.strip() for l in open(PROT_FILE)] if os.path.exists(PROT_FILE) else []
PROTECTED = [p for p in PROTECTED if p and not p.startswith("#")]
MIN = 50
for i, a in enumerate(sys.argv):
    if a == "--min": MIN = int(sys.argv[i+1])
FILE_K = None
if "--file" in sys.argv:
    k = sys.argv[sys.argv.index("--file")+1] if sys.argv.index("--file")+1 < len(sys.argv) and sys.argv[sys.argv.index("--file")+1].isdigit() else "9999"
    FILE_K = int(k)

# decl-start: optional attrs/modifiers then a decl keyword + name
declpat = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|partial\s+|unsafe\s+)*'
    r'(theorem|lemma|def|instance|abbrev|structure|class|inductive)\b\s*([^\s({\[:]*)')

# the lib target for each project root dir (for the build hint in the ticket)
LIBHINT = {
    "FltRegularBernoulli": "BernoulliRegular", "HasseWeil": "HasseWeil",
    "LeanModularForms": "LeanModularForms", "AdicSpaces": '"«Adic spaces»"',
    "PadicLFunctions": "PadicLFunctions", "NagellLutz": "LutzNagell",
    "Chebotarev": "CebotarevDensity", "FltRegular": "FltRegular",
}
def libhint(path):
    parts = path.split("/")
    return LIBHINT.get(parts[1], parts[1]) if len(parts) > 1 else "<lib>"

cands = []
for dp, dirs, files in os.walk(ROOT):
    if "/.lake" in dp or "/.mathlib-quality" in dp or "/blueprint" in dp:
        continue
    dirs[:] = [d for d in dirs if d not in (".lake", ".mathlib-quality", "blueprint")]
    for fn in files:
        if not fn.endswith(".lean"): continue
        path = os.path.join(dp, fn)
        if any(pp in path for pp in PROTECTED): continue  # dev-extraction in progress
        try:
            lines = open(path, errors="replace").read().split("\n")
        except Exception:
            continue
        starts = [(i, m.group(1), m.group(2)) for i, ln in enumerate(lines)
                  for m in [declpat.match(ln)] if m]
        for j, (i, kind, name) in enumerate(starts):
            if kind not in ("theorem", "lemma") or not name: continue
            end = starts[j+1][0] if j+1 < len(starts) else len(lines)
            block = lines[i:end]
            # trim trailing blank/comment-only lines
            while block and not block[-1].strip(): block.pop()
            span = len(block)
            text = "\n".join(block)
            if re.search(r'\bsorry\b|\badmit\b', text): continue
            if span >= MIN:
                cands.append((span, path, i+1, name))
cands.sort(reverse=True)

# dedup by DECL NAME vs already-filed decompose tickets (open+closed) — line counts drift
existing_names = set()
if FILE_K is not None:
    r = subprocess.run([GH, "issue", "list", "--repo", REPO, "--label", "lane:decompose",
                        "--state", "all", "--limit", "500", "--json", "title"], capture_output=True, text=True)
    for d in (json.loads(r.stdout) if r.stdout.strip() else []):
        m = re.match(r'decompose:\s*(\S+)', d["title"])
        if m: existing_names.add(m.group(1))

print(f"# {len(cands)} sorry-free theorem/lemma proofs >= {MIN} lines")
filed = 0
for rank, (span, path, line, name) in enumerate(cands):
    title = f"decompose: {name} ({span} lines)"
    mark = ""
    if FILE_K is not None and filed < FILE_K and name not in existing_names:
        body = (f"**Target:** `{name}` — `{path}:{line}` — **{span}-line proof** (sorry-free), over the 50-line limit.\n\n"
                f"**Action:** `/decompose-proof`: extract well-named general helpers (search mathlib first for "
                f"anything reusable), leaving the main proof short. Build target: `lake build {libhint(path)}` "
                f"**and** `lake build <Lib>.<Module>` (the file by name — orphans aren't in the lib gate).\n\n"
                f"**Acceptance:** build green · zero new `sorry` · `#print axioms` unchanged · top-level statement "
                f"byte-for-byte identical.\n\n_Filed by find_decompose_targets.py._")
        res = subprocess.run([GH, "issue", "create", "--repo", REPO, "--title", title, "--body", body,
                              "--label", "lane:decompose", "--label", "state:todo"], capture_output=True, text=True)
        if res.returncode == 0:
            filed += 1; existing_names.add(name); mark = " -> FILED"
        else:
            mark = " -> ERR " + res.stderr.strip()[:80]
    if rank < 40 or mark:
        print(f"{span}\t{path}:{line}\t{name}{mark}")
if FILE_K is not None:
    print(f"\nfiled {filed} decompose tickets")
