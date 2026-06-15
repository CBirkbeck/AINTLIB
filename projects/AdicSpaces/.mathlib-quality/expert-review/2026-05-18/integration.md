# Reply integration — 2026-05-18 (Stage 1 of 2)

Reply received: 2026-05-18.
Brief: ./brief.md
Reply: ./reply.md
Stage 2 (cascading deletes/renames/restatements): NOT YET APPLIED.

## Interpretation summary

Reviewer confirmed all four flagged statements (B2, B3, B4, F2) are mathematically false or scoped wrong. Recommended:
- Restate D15, E1, E2 with proper hypotheses (CompleteSpace; M̂ fg; ContinuousSMul).
- Remove B2/B3/B4 (false derivations of noeth-A₀ / strong noeth) from main path.
- Quarantine G1/G2 (false single-map injectivity/surjectivity) in deprecated namespace.
- Restate F2/F3 over `O(C.base)` not `A`.
- Fix Stacks 00MA → 0316 citation.
- Drop "Wedhorn 7.42" label from D8.
- Keep ratio-tree architecture but make refinement constructions relative.
- Rename IsSheafy or document it captures only sheaf-of-sets (not full acyclicity).

## Stage 1 — changes APPLIED (this turn)

All edits are docstring/hypothesis tightenings that LAND CLEANLY in the build (verified: `lake build` returns no errors).

### Citation fix (1)
- **`_sub_lemma_L5_1_2_adicCompletion_noetherian`** (WedhornStronglyNoetherian.lean:123): docstring updated — Stacks 00MA → Stacks 0316 (Lemma 10.97.6). Statement unchanged.

### FALSE-AS-STATED docstring annotations (4)
- **`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`** (StructureSheaf.lean:1579): docstring updated with ℂ_p counterexample + Stage 2 deletion notice.
- **`isNoetherianRing_A₀_of_stronglyNoetherianTate`** (StructureSheaf.lean:1602): same.
- **`isStronglyNoetherian_of_isNoetherianRing_isTateRing`** (StructureSheaf.lean:1613): docstring updated as NOT-IN-WEDHORN / LIKELY-OPEN + Stage 2 deletion notice.
- **`restrictionMap_isLocalization`** (PresheafTateStructure.lean:2454): EXPERT-REVIEW CONFIRMATION line added; existing strong B2-flag preserved.

### Quarantine annotations (2)
- **`restrictionMapHom_surj`** (PresheafTateStructure.lean:1206): EXPERT-REVIEW DIRECTIVE line added with planned rename to `_DEPRECATED_FALSE_*`.
- **`restrictionMapHom_injective`** (PresheafTateStructure.lean:1412): same.

### Citation correction with rename note (1)
- **`wedhorn_7_42_powerBounded_iff_forall_continuous_vle_one`** (Presheaf.lean:2646): docstring fixed — Wedhorn Remark 7.42 is about vertical generizations, NOT this statement. Combined attribution to Wedhorn 7.41 + non-analytic generization. Lemma name retained for legacy; planned rename in Stage 2.

### Signature tightening (2)
- **`units_eq_union_translates_of_oneAdd_topNilp`** (Presheaf.lean:2508): added `[UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]` to the hypothesis bundle. Resolves b2_log entry 9 counterexample.
- **`wedhorn_6_18_unique`** (WedhornBanachTheorem.lean:608): added `[T2Space M^τ] [ContinuousSMul A M^τ]` on both the existential τ and the universally-quantified τ'. Resolves the ⊕_n ℤ/2ℤ counterexample.

### Reverted (cascade too wide for Stage 1)
- **`_sub_lemma_L3_1a_completion_fg_complete`** (E1): attempted to add `[ContinuousSMul]` + `[UniformContinuousConstSMul]` + replace `Module.Finite A M` with `Module.Finite A (UniformSpace.Completion M)`. Mathlib does not provide `UniformContinuousConstSMul A ↥N` for submodules; downstream `_sub_lemma_L3_1b_fg_submodule_closed` consumer needed updating. Reverted; added Stage 2 SIGNATURE NOTE in the docstring explaining the planned restatement.

## Stage 2 — changes NOT YET APPLIED (require coordinated refactor)

### Deletions (4 declarations, each with 3-8 consumer files)
| Declaration | Consumer files |
|---|---|
| `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` (B2) | StructureSheaf, TateAcyclicity, TateAcyclicityResiduals, WedhornStronglyNoetherian (4) |
| `isNoetherianRing_A₀_of_stronglyNoetherianTate` (B3) | StructureSheaf (1) |
| `isStronglyNoetherian_of_isNoetherianRing_isTateRing` (B4) | StructureSheaf, TateAcyclicity, WedhornStronglyNoetherian (3) |
| `restrictionMap_isLocalization` | PresheafTateStructure, LaurentRefinement, TateAcyclicityFinalAssembly, StructureSheaf, Cor832, RestrictionFlatness (6) |

For each, consumers need to be refactored to take `(P, [IsNoetherianRing P.A₀])` as explicit parameters (when genuinely needed) or use the Wedhorn-honest flatness route directly via Example 6.38 + Prop 8.30 + Cor 8.32.

### Quarantine (2 declarations, each with 3-8 consumer files)
| Declaration | Consumer files |
|---|---|
| `restrictionMapHom_surj` (G1) | PresheafTateStructure, LaurentRefinement, Cor832 (3) |
| `restrictionMapHom_injective` (G2) | PresheafTateStructure, LaurentRefinement, TateAcyclicityFinalAssembly, HubnerSeparation, Cor832, RationalRefinement, GeometricReduction, CompletionLocalization (8) |

Quarantine: move to a `Deprecated` namespace; rename to `_DEPRECATED_FALSE_*`; refactor 8+ consumer call sites onto cover-level Cor 8.32 product-injectivity.

### Restatements (3 declarations, each with cascade)
| Declaration | Notes |
|---|---|
| `_sub_lemma_L3_1a_completion_fg_complete` (E1) | Restate hypothesis as `Module.Finite A (UniformSpace.Completion M)`; requires `[ContinuousSMul] [UniformContinuousConstSMul]`; cascade to L3.1b + 2 downstream Banach OMT consumers. |
| `exists_ideal_generators_refining_cover` (F2) | Restate `S : Finset (presheafValue C.base)` not `Finset A`; cascade through F1, F3 + P3-P8 chain. |
| `exists_standard_cover_refining_via_754` (F3) | Same as F2. |

### Rename (1 typeclass, MASSIVE cascade)
| Declaration | Notes |
|---|---|
| `IsSheafy` | Reviewer suggests renaming to `IsSheafyAtDegreeZero` to clarify scope. Used by AdicSpace, PerfectoidSpace, IntegralStructureSheaf and many supporting files. Likely 20+ call sites. |

### New work (4 items)
- `exists_standard_cover_refining_relative`: Wedhorn-honest relative form of F2 over `O(C.base)`.
- Refactor `flat_over_base_tate` in Cor832 off `restrictionMap_isLocalization` onto `restrictionMap_flat_via_iteratedMinus`.
- Refactor IsSheafy `embedding` algebraic side off the retired `restrictionMapHom_injective` onto cover-level Cor 8.32.
- Document the renamed target / scope clarification.

## Changes rejected by user

None — user approved option 1 (apply all).

## Open questions remaining

None — reviewer answered all 10.

## Decisions recorded

- ℂ_p counterexample confirmed mathematically valid for B2/B3.
- B4 confirmed as not in Wedhorn for general noeth Tate; restrict to completely valued field of height 1 case (BGR 5.2.6) when used.
- F2/F3 confirmed type-misaligned; correct form is `S ⊆ O(C.base)`.
- Sheaf-of-sets vs. full acyclicity: keep current scope; document that IsSheafy captures only degree-zero.
- Stacks tag for completion-noetherianness: use 0316, not 00MA.

## Recommendation for next session

Stage 2 is a substantial coordinated refactor (~30 call-site updates across 10+ files). Recommended sequencing:
1. Quarantine G1/G2 first (most consumer cascade, but each refactor target is well-known — route through Cor 8.32 product injectivity).
2. Delete `restrictionMap_isLocalization` next (refactor Cor832 chain onto the Wedhorn-honest flatness route).
3. Delete B2/B3/B4 last (after the Cor 8.32 chain is verified to work without them — at which point downstream consumers can be safely re-parameterised).
4. Defer F2/F3 restatement, IsSheafy rename, and new work G1-G4 to a separate session.
