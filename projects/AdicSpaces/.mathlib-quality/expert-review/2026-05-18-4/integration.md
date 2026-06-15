# Reply integration — Round 4 (2026-05-18)

Reply received from the external mathematical reviewer (same as rounds 1-3) on 2026-05-18.

Brief: `./brief.md`
Reply: `./reply.md`

## Interpretation summary

13 substantive reviewer points across Q1-Q8 + overall verdict + methodological note + recommended execution order. All mapped with high confidence (no clarifications needed). See `state.md` for the question-by-question mapping table.

## Changes applied (Session 27, 2026-05-18)

### Code edits

- **A.2** APPLIED: `laurentCover_exact_general` (Wedhorn 8.33, project I2) — added `[IsDomain A]` to hypothesis bundle, updated docstring with scope note explaining the narrower-than-Wedhorn scope and the Krull-intersection rationale (per Q4).
- **A.3** APPLIED: `b2_log.jsonl` entry I2.3 — corrected counterexample computation: `(f)^n = ℚ_p × 0` (not `(0, c)`); intersection = `ℚ_p × 0` (still ≠ ⊥). Reviewer caught coordinate reversal in brief.
- **A.1** NO-OP: L5.1.1 statement already in the simpler base-change form `Nonempty (↥(TateAlgebra A) ≃+* TensorProduct P.A₀ A (AdicCompletion (P.I.map (algebraMap P.A₀ (Polynomial P.A₀))) (Polynomial P.A₀)))`. Brief had misdescribed the actual code. No edit needed.

### Audit document updates (B.1-B.5 — Session 27 deltas)

`adversarial-audit-2026-05-18-3.md` Parts IV-VI superseded by the reviewer-confirmed plan:

- **D12** (Part IV+VI): SCRATCH the "canonical Huber-field valuation" mathlib gap (D12.4 sub-leaf, ~30-50 LOC). New route per reviewer Q1: case-split on `m` open/non-open; open case uses trivial valuation on `A/m` (existing project `exists_spa_point_in_rationalOpen_of_isOpen_prime`); non-open case via Wedhorn 7.45 (D9+D10 chain). This reduces D12 from ~120-150 LOC to ~50-80 LOC and eliminates the mathlib gap.
- **I2** (Part IV+VI): change "either re-add [IsDomain A] OR case-split" → "ADD [IsDomain A] (decided per Q4); document narrower scope". Already applied in A.2.
- **Cor 8.32** (Part V Tier 3+5): SPLIT into two tickets per reviewer Q6:
  - `T-COR832-CLEAN-VIA-FLAT` (MAIN API): consumes `(∀ D ∈ C.covers, Module.Flat (O(C.base)) (O(D)))` + Spec-surjectivity → product faithful flatness. Flatness input from C1 / Prop 8.30.
  - `T-COR832-CLEAN-VIA-LAURENT` (SUBSIDIARY): Laurent-shaped covers only, used inside refinement-tree subproofs.
- **C3 sub-tree** (Part VI): updated with reviewer's 3 concrete sub-lemmas (Q3): `valuation_extends_to_localization_of_rationalOpen`, `valuation_extends_to_completion_of_continuous`, `Spa_comap_image_eq_rationalOpen`.

### New feedback memory (C.1)

`feedback_hypothesis_ledger_v2.md` saved — the 5-column proof-hypothesis ledger from reviewer's methodological note, superseding `feedback_proof_hypothesis_ledger.md` (4-column). Adds the column "literature proof actually uses" which catches implicit blockers like the Krull-intersection reliance in 8.33.

### State file flip (D.1)

`state.md` updated: `Reply received: true (2026-05-18T16:00:00Z)`, `Reply integrated: true (2026-05-18T16:05:00Z)`.

## Changes rejected by user

None.

## Open questions remaining (the reviewer didn't address)

None. All 8 questions answered directly. Methodological note + execution order ranking provided as unprompted additions.

## Decisions recorded but not actioned

- **A1 no-op**: confirmed; no code change needed.
- **Cluster L stays clear**: confirmed; no action.
- **F12 + C3 confirmed as architectural plan**: no code change yet (still pending execution per the Session 26 user decisions D-2, D-3).
- **Stacks 0316 direct route confirmed**: no plan change; AdicCompletionNoetherian.lean skeleton unchanged.

## Recommended execution order (per reviewer)

1. F12 move (4 declarations from LaurentRefinement → TateAcyclicityFinalAssembly)
2. C3 build (Spa_presheafValue_eq_rationalOpen + 3 sub-lemmas)
3. Stacks 0316 direct route (5 sub-leaves in AdicCompletionNoetherian.lean)
4. Define `cor_8_32_clean_via_flat` (NEW main API, replacing `_via_laurent` as headline)
5. Patch 8.33 with `[IsDomain A]` — DONE this session (A.2)
6. Use proven parametric 8.31 replacements (TateAlgebra.lean:2625/2597/2607) — unchanged

Items 1-4 and 6 are pending /beastmode execution. Item 5 is applied.

## Forward pointer

Next /beastmode session can begin from the Tier 1 work (Stacks 0316 L1-L5 in AdicCompletionNoetherian.lean). The F12 move + C3 build are larger architectural items recommended ahead of `cor_8_32_clean_via_flat`.
