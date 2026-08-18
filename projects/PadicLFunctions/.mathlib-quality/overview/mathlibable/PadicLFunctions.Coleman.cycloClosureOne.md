# Mathlibable assessment: `PadicLFunctions.Coleman.cycloClosureOne`

**Verdict: `NO-composable-from-mathlib`** (a thin definitional `⊓`-wrapper over two
project-specific subgroups; not a standalone mathlib object).

- **Kind:** `def` (returns data — a `Subgroup ℂ_[p]ˣ`), so `lowerCamelCase` is correct.
- **Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:218`
- **Mode:** A (single declaration), full 10-phase workflow with the 9-channel literature search.

```lean
/-- `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}` (RJW TeX 3091). -/
noncomputable def cycloClosureOne (n : ℕ) : Subgroup ℂ_[p]ˣ :=
  cycloClosure p n ⊓ localUnitsOne p n
```

---

## Phase 0 — Doctor / baseline

Per the task's build note, `lake build` was **not** re-run (the build is known stale/slow
here). **Build not re-run; reasoned from source.** The declaration and its full dependency
chain were read directly:

- `cycloClosure p n := (cycloUnits p n).topologicalClosure ⊓ localUnits p n`
  (`CyclotomicUnits.lean:210`)
- `localUnitsOne p n` = principal local units, carrier `{u | u ∈ localUnits p n ∧ ‖(u:ℂ_[p]) − 1‖ < 1}`
  (`LocalUnits.lean:71`)
- `localUnits p n` = units of `O_n` (`LocalUnits.lean:39`)
- `cycloUnits p n := Subgroup.closure (cycloGenSet p n) ⊓ globalUnits p n` (`CyclotomicUnits.lean:182`)

All operands are **project-defined** objects of the RJW (arXiv:2309.15692) §11.3 Iwasawa
cyclotomic-unit tower, living inside `ℂ_[p]`.

## Phase 1 — Comprehend

`cycloClosureOne p n` is `𝒞_{n,1}`: the meet (lattice `⊓` on `Subgroup ℂ_[p]ˣ`) of

1. `cycloClosure p n = 𝒞_n` — the p-adic (topological) closure of the cyclotomic units
   `𝒟_n`, intersected into the local units `𝒰_n`; and
2. `localUnitsOne p n = 𝒰_{n,1}` — the principal local units (`‖u − 1‖ < 1`).

Mathematically it is the principal-unit part of the local closure of the cyclotomic units at
level `n` — one node in the construction of the tower `𝒞_{∞,1}` that receives the Coleman-map
input. It is data (a bundled subgroup), defined as a **single `⊓`** of two project subgroups.

## Phase 2 — Preliminary BIG/SMALL + one-line check

SMALL by construction: the body is one `⊓`. It is **not** a one-liner equal to an existing
mathlib decl (the operands are project-specific), so the one-line exemption does not apply —
it is a *new project definition that happens to be a trivial combination of project objects*.
No `def`/`class`/`instance` diamond concern beyond what `Subgroup`'s `⊓` already carries
(it reuses mathlib's `Lattice (Subgroup G)`; no new instance is introduced here).

## Phase 3 — Exhaustive literature search (9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "cyclotomic units p-adic closure principal local units Iwasawa tower C_{n,1}" | Concepts standard (Iwasawa 1968; Coates–Sujatha, *Cyclotomic Fields and Zeta Values*; local cyclotomic fields). **No standalone "C_{n,1}" object** — flagged as paper-specific notation. |
| 2 | WebSearch | "Rubin Iwasawa cyclotomic units local closure intersection principal units" | Rubin's Euler systems of cyclotomic units, plus-part of class groups; local-unit Λ-modules. Intersection-with-principal-units appears only inside specific proofs, never as a named definition. |
| 3 | WebSearch | "'semi-local units modulo cyclotomic units' projective limit principal units p-adic closure definition" | Sciencedirect (Kim) + JTNB 2024: `U` (proj. limit semi-local units), `C` (proj. limit cyclotomic units), study of `U/C`. Confirms the *operand-level* objects are standard; the per-level principal-unit intersection is bookkeeping. |
| 4 | ChatGPT MCP (historical formulation) | n/a | **n/a: MCP server not configured in this environment.** Substituted by the three WebSearches + local-mathlib reading. |
| 5 | Local refs (`refs/PadicLFunctions/`) | — | **n/a: no `refs/` symlink present** (PDFs are local-only and not linked here). Primary source identified from the docstring: RJW arXiv:2309.15692, §11.3, TeX 3090–3094. |
| 6 | nLab | cyclotomic units / principal units | No page treating this exact per-level intersection as a named object. |
| 7 | nCatLab/Stacks | local units, principal units, Iwasawa | Stacks has valuation/units; no cyclotomic-unit local-closure tower. |
| 8 | MathOverflow | semi-local units modulo cyclotomic units | Matches channel 3 — `U/C` is the studied object, not `𝒞_{n,1}` per se. |
| 9 | arXiv | (covered by 1–3) | Sources above (1907.06437, math/0512015, 1102.4705, JTNB 1284, etc.). |

**Phase 3 conclusion.** The *ingredients* (cyclotomic units, their p-adic/topological
closure, principal/semi-local units, and the quotient/intersection `U/C`) are canonical
Iwasawa theory. The *specific object* `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}` is **not** a named,
reusable definition in the literature — it is one intersection step in a particular tower
construction (RJW). There is therefore no "literature-standard form of `cycloClosureOne`"
to anchor a generalisation against.

## Phase 4 — Generality vs literature-standard form

`cycloClosureOne` is `A ⊓ B`. There is no separate "more general form of the meet" to target.
The only generality questions live on the **operands**, and they are about *those* decls, not
this one:

- `localUnitsOne` (the `‖u − 1‖ < 1` principal units) vs mathlib's general
  `ValuationSubring.principalUnitGroup` (principal-unit group of a valuation subring,
  `Mathlib/RingTheory/Valuation/ValuationSubring.lean:634`).
- `cycloClosure` vs a hypothetical general "topological closure of cyclotomic units in the
  local units."

**Verdict for THIS decl: not separately generalisable.** It inherits whatever generality the
operands have; weakening it means weakening `localUnitsOne` / `cycloClosure`, which is
out of scope for `cycloClosureOne` and is the operands' own assessment.

## Phase 4c — Modern-mathlib-idiom (Bourbaki 2.0) restatement

The meet `⊓` is already the maximally idiomatic mathlib spelling of "intersection of two
subgroups" (`Lattice (Subgroup G)`). A genuine modernisation exists *one level down* —
restating `localUnitsOne` via `ValuationSubring.principalUnitGroup` and giving the local-units
setup a typeclass/valuation-theoretic home — but that is a restatement of the **operand**,
with downstream consequences for `localUnits*`, not for `cycloClosureOne`. There is **no**
modern-idiom restatement of `cycloClosureOne` *itself* with concrete downstream consequences:
once the operands are fixed, the object is forced to be their meet. (Bourbaki-2.0 claim
deliberately **not** asserted for this decl — it would fail the Phase-7 gate's
"downstream consequences" requirement.)

## Phase 5 — Mathlib five-method search

| # | Method | Query | Result |
|---|---|---|---|
| A | Lean-Finder | (semantic) | **n/a: tool not available in-env**; substituted by D + E over the local `.lake/packages/mathlib` checkout. |
| B | Loogle / type | `(n : ℕ) → Subgroup ℂ_[p]ˣ` from project defs | No mathlib hit possible — the return type is built from project-defined subgroups. |
| C | LeanSearch / NL | "p-adic closure of cyclotomic units intersect principal units" | Concept absent from mathlib. |
| D | grep mathlib source | `cyclotomicunit`, `principalUnit`, `localUnits`, `iwasawa`, `topologicalClosure` | `RingTheory/RootsOfUnity/CyclotomicUnits` = generic number-field cyclotomic units (**not** a local-closure object). `ValuationSubring.principalUnitGroup` = general principal-unit group (closest analogue of the **operand** `localUnitsOne`, **not** of this object). `GroupTheory/GroupAction/Iwasawa.lean` = Iwasawa *simplicity criterion* (unrelated). `Subgroup.topologicalClosure` exists generally. **No cyclotomic-unit local-closure tower.** |
| E | name-pattern | `cycloClosure*`, `localUnits*`, `cycloUnits*` | Found **only** in this project. |

`Subgroup.mem_inf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`) confirms the meet API
mathlib supplies. **Phase 5 conclusion: mathlib does NOT have `cycloClosureOne` or any direct
analogue.** It has (a) the generic `⊓`, and (b) `principalUnitGroup` as a *general* sibling of
one operand — but not this object and not the cyclotomic-unit closure operand.

## Phase 6 — Composition check (≤3 mathlib calls?)

The body is `cycloClosure p n ⊓ localUnitsOne p n` — a **single** mathlib `⊓`. But the two
operands are **project-specific** subgroups that are **not in mathlib**. So:

- This is **not** the `NO-composable-from-mathlib` of Case 4 in
  `references/mathlibable-verdicts.md` (that bucket means *mathlib's own* building blocks
  reproduce the object in ≤3 mathlib calls). Here mathlib supplies only the `⊓`; the content
  is the operands, which only exist in the project.
- Equivalently: `cycloClosureOne` is a **thin definitional wrapper internal to the project**,
  riding on the lattice meet. It carries no mathematical content beyond "intersect these two
  project objects." It cannot be reconstructed from mathlib alone (the operands are needed),
  and it is too trivial to be a standalone mathlib definition.

### Phase 6.0 — Call-sites (composability signal)

| Consumer file | Uses | Nature |
|---|---|---|
| `CyclotomicUnits.lean` | `cycloTower1` carrier; `cyclo_mem_cycloTower1`; `zpPow_zetaSys_mem_cycloClosureOne`; `mem_cycloClosureOne_of_pow_mem` | tower assembly + membership lemmas, all `rw [cycloClosureOne, Subgroup.mem_inf]` then work on the factors |
| `IwasawaProof/Generators.lean` | `wGamma_mem_cycloTower1` chain; `cycloClosureOnePlus_le_…` | unfolds to factors |
| `IwasawaProof/Main.lean` | several membership/`≤` steps | unfolds to factors |
| `Coleman/ColContinuity.lean` | `isClosed_cycloClosureOne`, `isClosed_val_cycloClosureOne` | both immediately `rw [cycloClosureOne, cycloClosure]` and prove via the three closed factors |

K ≥ 3 internal uses → it is *real, used* project API. **But** every use unfolds it back to its
factors (`Subgroup.mem_inf`); the two lemmas nominally "about" it
(`isClosed_cycloClosureOne`, `isClosed_val_cycloClosureOne`) are facts about the *intersection
of closed factors*, not new facts about a new object. The call-site signal says "load-bearing
project glue," **not** "standalone abstraction worth exporting."

## Phases 7–8 — Verdict synthesis and gate

Weighing the artifacts:

- Phase 3: object is **not** a named literature definition (only its ingredients are) → no YES anchor.
- Phase 4 / 4c: **not separately generalisable / no modern restatement** of this decl
  (those moves belong to the operands) → not `YES-but-generalise-first`.
- Phase 5: **mathlib lacks it** and lacks both operands → not `NO-mathlib-has-it`.
- Phase 6: it is a **single `⊓` over two project-specific, non-mathlib operands** → a thin
  wrapper, not standalone-novel; cannot live in mathlib without the operands.

The structural facts decide this cleanly, so it is **not** `BORDERLINE` (there is no residual
taste/policy question — a `⊓` of two project subgroups is, by construction, project bookkeeping).
It is **not** any `YES` (not novel as a standalone object; not generalisable as itself; mathlib
PRs do not take `A ⊓ B` wrappers — cf. verdicts-doc audit-item-12 STRUCTURE note that combined
wrappers over separate facts/objects don't go to mathlib). The best fit is:

### Final verdict: `NO-composable-from-mathlib`

with the precise reading: **a trivial definitional `⊓`-wrapper over two project-specific
subgroups.** Mathlib supplies the meet (`Subgroup.mem_inf`); it does not — and should not —
supply this object, because its entire content is the two project operands.

**Recommended action (project-local, not a mathlib PR):**
1. **Keep `cycloClosureOne` as-is in the project.** It is correct, idiomatically named
   (`lowerCamelCase` for data), and is genuinely load-bearing glue for the RJW Iwasawa-tower
   proof. There is nothing to fix.
2. **Do not** propose `cycloClosureOne` to mathlib — a `⊓` of two project subgroups is not a
   mathlib contribution.
3. **If** any mathlib-direction work is wanted from this file, it lives **on the operands**,
   assessed separately:
   - `localUnitsOne` → consider restating against `ValuationSubring.principalUnitGroup`
     (mathlib's general principal-unit group) — a real Bourbaki-2.0 modernisation *for that
     decl*.
   - the cyclotomic-unit closure (`cycloClosure` / `cycloUnits`) → a general "topological
     closure of cyclotomic units in the local units" API would be the contributable object,
     if abstracted away from the bespoke `ℂ_[p]` setup.

---

### Evidence pointers (for the Phase-7 gate)
- Phase 3 table: 9 channels, ≥3 substantive web channels with sources; ChatGPT-MCP and
  local-refs recorded `n/a: <reason>` (not blank).
- Phase 4: explicit "not separately generalisable" with the operand-level alternatives named.
- Phase 4c: Bourbaki-2.0 claim **withheld** for this decl (no downstream consequence) — only
  asserted for the operand `localUnitsOne`.
- Phase 5: five methods, A recorded `n/a` with substitute; mathlib decls cited by qualified
  name (`Subgroup.mem_inf`, `ValuationSubring.principalUnitGroup`, `RootsOfUnity.CyclotomicUnits`,
  `GroupTheory.GroupAction.Iwasawa`).
- Phase 6: composition is one `⊓`; building blocks are project-specific → not Case-4 mathlib-composable;
  call-sites table shows K ≥ 3 but every use unfolds to factors.
- No cost-based reasoning used anywhere (cost is not a verdict factor).
