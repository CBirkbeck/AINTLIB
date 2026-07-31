# `formalisation.yaml` and its comparator

`formalisation.yaml` records **what this project has formalised** — which numbered results
in the literature are proved by which Lean declarations — and the comparator checks that
record against the actual source tree.

The manifest is **generated, never hand-edited**. The library is the source of truth; the
manifest is a snapshot of it, and the comparator's job is to notice when the two disagree.

## Usage

```bash
cd projects/AdicSpaces

python3 scripts/gen_formalisation.py       # regenerate formalisation.yaml
python3 scripts/check_formalisation.py     # verify it against the tree (fast, no build)
```

| Command | What it does |
|---|---|
| `check_formalisation.py` | structural check; exit 1 on any ERROR |
| `check_formalisation.py --strict` | warnings fail too — use when the manifest is meant to be exactly current |
| `check_formalisation.py --group fjp` | scope to one group (`fjp`, `examples`, `adic-spaces`) |
| `check_formalisation.py --list --group fjp` | print the informal→formal table for humans |
| `check_formalisation.py --axioms` | additionally run `#print axioms` on every listed result (needs a built `.lake`; slow) |
| `check_formalisation.py --json` | machine-readable report |

## What the manifest contains

Two levels of granularity, because "what is formalised" means two different things:

* **`results:`** — statement level. One entry per declaration whose docstring cites a
  source (Wedhorn / `[FJP]` / Huber / Stacks). This is the informal↔formal correspondence.
* **`modules:`** — the full inventory of every module in the library, so the manifest
  covers *all* of the adic-spaces development rather than only the cited parts.

Each result entry carries a `digest`: a hash of the declaration's **statement** (everything
up to the top-level `:=`). That is what lets the checker distinguish a declaration that was
renamed from one that was *restated*.

`Vendored/` is excluded throughout — it is third-party code, not this project's
formalisation.

## What the comparator catches

| Level | Kind | Meaning |
|---|---|---|
| ERROR | `RESTATED` | the statement changed — the digest no longer matches |
| ERROR | `MISSING` | a listed declaration no longer exists (renamed or deleted) |
| ERROR | `REGRESSED` | a result recorded as `proved` now contains a `sorry` |
| ERROR | `MODULE-GONE` | a module in the manifest has no declarations any more |
| ERROR | `AXIOMS` | (with `--axioms`) depends on `sorryAx` |
| WARN | `MOVED` | same declaration, different module |
| WARN | `UNLISTED` | a declaration cites a source but is not in the manifest — new work never recorded |
| WARN | `PROMOTED` | recorded as `sorry`, now proved |
| WARN | `SOURCES` | the set of cited sources changed |
| WARN | `COUNTS` / `MODULE-NEW` | module inventory drift |

`RESTATED` is the one that matters most here. The project's cleanup rules forbid changing a
theorem statement to make something pass; a restatement nobody recorded is exactly what
should fail a check.

**Line numbers are deliberately not checked.** They move on every cleanup commit, and a
checker that fails on noise gets switched off.

## Files

| File | Role |
|---|---|
| `formalisation_lib.py` | all extraction: declarations, namespaces, citations, digests |
| `gen_formalisation.py` | writes `formalisation.yaml` |
| `check_formalisation.py` | compares manifest ↔ source |
| `mini_yaml.py` | emitter + loader (uses `pyyaml` if installed, otherwise a strict subset reader) |

The generator and the comparator share `formalisation_lib.py` on purpose: if they read the
source differently, the check would pass on a manifest that does not describe the tree.

## Gotchas encoded here (each one cost a bug)

* **Docstring prose is not code.** Continuation lines in this library start at column 0 with
  things like `theorem is unsound outside ...`, `lemma so the chain assembly ...`,
  `structure presheaf is a sheaf ...`. Parsing without tracking block-comment depth invented
  nine phantom declarations, which then collided with real ones and produced phantom
  `RESTATED` reports. `code_line_mask` handles it; Lean block comments nest, so depth is
  counted rather than toggled.
* **Never split a signature on the first `:=`.** Binders and default arguments contain one
  (`(h : P := by simp)`). `signature_of` tracks bracket depth.
* **Citations wrap.** Docstrings break lines mid-citation (`Wedhorn\nCor 8.32`), so
  whitespace is collapsed before matching — a newline-sensitive pattern loses a large
  fraction of the Wedhorn references.
* **`Wedhorn Lemma 7.31` and a bare `Wedhorn 7.31` are the same result.** Both spellings
  occur; the citation id excludes the kind word so they unify.
* **Private declarations are skipped by `--axioms`** — their real names are mangled
  (`_private.«Adic spaces»…`), so `#print axioms` cannot reach them by source name.
