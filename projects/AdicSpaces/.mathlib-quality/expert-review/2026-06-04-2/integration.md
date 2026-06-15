# Reply integration — 2026-06-04 (round 2: 8.28(b) gluing-half blockers)

Reply received from an adic-spaces + Mathlib expert on 2026-06-04.
Brief: ./brief.md   Reply: ./reply.md

## Interpretation summary

All four questions answered, high confidence, with one decisive correction (Q1):
- **Q1 — CORRECTION**: `A°°` is **NOT an ideal of `A`** for a Tate ring (ℚ_p: `p` is a top-nilp unit ⟹ an `A°°` ideal of `A` would contain `1`). Mathlib's `topologicalNilradical : Ideal A` (under `[IsLinearTopology]`, unsatisfiable for Tate) is the wrong object. Build a project-local `NonarchimedeanAddGroup` API: `A°°` = open additive subgroup + radical ideal of `A°`; the Lemma-7.31 input is `∃ finite T ⊆ A°°, T·A°° open` (via `I²  ⊆ T·A°°`, `I²` open). Local first; do NOT relax `topologicalNilradical : Ideal A` upstream.
- **Q2**: quasi-compactness via Wedhorn 7.35 / spectral `Spv` (continue the parked SpvAI route); the Rmk 7.40(2) finite-union is post-hoc, not foundational.
- **Q3 — confirmed**: 7.54 is whole-space; proper bases via applying it to `O_X(U)`, transport `Spa O_X(U) ≃ U`.
- **Q4 — confirmed**: height-1 lemma false AND unnecessary; Cor 7.32 no-height. Extra caution: no universal inclusion between arbitrary `A₀` and `A⁺` in EITHER direction (only `A°°⊆A⁺⊆A°`); compatibility must be a *chosen* hypothesis (the project's `CompatiblePlusSubring`).

## Changes applied to tickets.md

- **T-MIGRATE-LINTOP-TATE-QC → SUPERSEDED, replaced by T-AOO-NONARCH** (revised target per Q1 correction): project-local `NonarchimedeanAddGroup` `A°°` API in NEW file `TopologicallyNilpotentNonarch.lean` — add/neg/finset-sum closure, mul-by-power-bounded, `A°°` as `AddSubgroup A` + `Ideal A°`, and `exists_finite_Aoo_generators_open_mul_Aoo` (the 7.31 input). Explicitly NOT `A°° : Ideal A`.
- **T-731-NONARCH added**: reprove Wedhorn 7.31 (`exists_zero_nbhd_lt_on_qc`) without `[IsLinearTopology]`, using T-AOO-NONARCH + T-COMPACT-NO-HARCH. Depends: T-AOO-NONARCH, T-COMPACT-NO-HARCH.
- **T-732-NOHEIGHT added**: Cor 7.32 dominating unit, no-height (`exists_dominating_unit_noHArch`, IsLinearTopology-free). Depends: T-731-NONARCH.
- **T-CECH-754-STEP1 re-pointed**: deps now T-732-NOHEIGHT (transitively T-AOO-NONARCH → T-731-NONARCH) + T-COMPACT-NO-HARCH; the 1a per-point proof compiles verbatim once T-732 lands.
- **T-CECH-740-6 → SUPERSEDED (delete the lemma)**: `mulArchimedean_valueGroup_of_stronglyNoetherianTate` is false + unnecessary; `cor_7_32_dominating_unit` re-routes through T-732-NOHEIGHT.
- **T-CECH-PAIR → SUPERSEDED (delete the `A₀⊆A⁺` lemma)**: no universal `A₀`/`A⁺` inclusion; no-height Cor 7.32 doesn't need it; use the chosen `[CompatiblePlusSubring]` where a compatible inclusion is genuinely needed.
- **T-COMPACT-NO-HARCH created** (was referenced but not a formal ticket): no-hArch `Spa A` quasi-compactness via the spectral-`Spv` route (Q2 confirmed); continue SpvAI/Bool-cylinder.
- **T-CECH-754-REL promoted** (was "low priority"): THE route for proper rational bases — apply whole-space `exists_form_a_refinement_coversSpa` to `presheafValue U`, transport `Spa(presheafValue U) ≃ U`. Dep changed T-CECH-754 → T-CECH-754-STEP1.
- **T-754-REROUTE added**: delete the false general-base `exists_form_a_refinement`/`exists_ideal_gen_refinement`; re-route `every_rational_cover_is_OXAcyclic` (general base) through T-CECH-754-REL + Prop A.3(2). Depends: T-CECH-754-REL.

## New dependency spine

T-AOO-NONARCH → T-731-NONARCH → T-732-NOHEIGHT → T-CECH-754-STEP1 → (whole-space 7.54 `exists_form_a_refinement_coversSpa` complete) → T-CECH-754-REL → T-754-REROUTE → `every_rational_cover_is_OXAcyclic`.
Side: T-COMPACT-NO-HARCH feeds T-731-NONARCH + T-CECH-754-STEP1. Retired: T-CECH-740-6, T-CECH-PAIR, T-MIGRATE-LINTOP-TATE-QC.

## Changes rejected by user

(none — "apply all")

## Open questions remaining

(none — all four answered, high confidence.)

## Decisions recorded but not actioned (`.lean` left untouched — `/beastmode` work)

- The actual `.lean` deletions (740-6 lemma, PAIR `A₀⊆A⁺` lemma, the general-base `exists_form_a_refinement` chain) and the new `TopologicallyNilpotentNonarch.lean` are NOT done here — they are the next `/beastmode` cycle, now with a corrected, sound board.
- The existing vacuous `IsTateRing.isOpen_topologicalNilradical` / `isOpen_topologicallyNilpotentElements` (Mathlib `topologicalNilradical`-based) are left in place (harmless under `[IsLinearTopology]`); the 7.31/7.32 chain simply stops routing through them.
