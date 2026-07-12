# ModularCurves — project docs

Formalising the theory of **modular curves** in AINTLIB.

**Branch:** `dev/modular-curves` · **Worktree:** `../aintlib-modular-curves` · **Lean lib:** `ModularCurves`

## Goal

Build the theory of the modular curves `Y(Γ) = Γ \ ℍ` and their compactifications `X(Γ)`,
for congruence subgroups `Γ ≤ SL₂(ℤ)`:

1. **Analytic** — `X(Γ)` as a compact Riemann surface (quotient, cusps, charts, genus).
2. **Level structures** — the standard families `X(N)`, `X₀(N)`, `X₁(N)`; cusps and widths.
3. **Algebraic / moduli** (longer term) — `X(Γ)` as an algebraic curve; the moduli
   interpretation as elliptic curves with level structure.

Scope will be pinned down once `sources.md` is populated and a blueprint is drafted.

## Layout

```
projects/ModularCurves/
├─ ModularCurves.lean            -- library root (imports the tree)
├─ ModularCurves/
│  └─ Basic.lean                 -- stub: module root + core imports (build me first)
└─ docs/                         -- planning, NOT merged to main (process, not library)
   ├─ README.md                  -- this file
   └─ sources.md                 -- the bibliography — start here
```

- **`docs/`, `.mathlib-quality/`, `blueprint/`, `scripts/` stay on `dev/modular-curves`.** They
  are process, not the cleaned library, and are not merged into `main`. Only the `.lean` files go.
- **Reference PDFs are local-only.** Put them in `refs/ModularCurves/` (reachable via the
  `refs → ../AINTLIB/refs` symlink in this worktree). `*.pdf` and `/refs` are gitignored, so a
  stray PDF can never be pushed.

## Build (in this worktree)

```sh
cd ../aintlib-modular-curves
lake exe cache get          # mathlib oleans (first time in this worktree)
lake build ModularCurves    # builds this project only
```

`ModularCurves` is declared in the root `lakefile.toml` but is **not** a default target yet, so
it will not gate the workspace `lake build` while it is still a stub.

## Workflow (producer rules — from the root `CLAUDE.md`)

- **Prove theorems.** Track the work in this project's dev tickets under `.mathlib-quality/`
  (to be initialised).
- **Reuse, don't duplicate.** Search the whole repo + mathlib before proving anything nontrivial
  (`grep -r`, `import`, `exact?` / `apply?`). Re-proving an existing result is the cardinal sin.
  Start from the "Existing infrastructure" section of `sources.md`.
- **`sorry` is fine** as a WIP marker on this branch. Don't clean, golf, or bump mathlib — that
  happens centrally on `main`.
- **Rebase onto `main` at stable points** (never mid-proof) to absorb the daily mathlib bump.
- **When a dev ticket is done**, open a PR `dev/modular-curves → main`. That hands the sorry-free
  result to the cleanup fleet.

## Next steps

1. Populate `sources.md` (drop PDFs in `refs/ModularCurves/`).
2. Draft a blueprint / roadmap: the dependency graph from `ℍ` and `Γ` up to `X(Γ)` compact.
3. Initialise the dev-ticket system under `.mathlib-quality/` and cut the first tickets
   (e.g. "quotient topology on `Y(Γ)`", "cusps of `Γ`", "chart at a cusp").
