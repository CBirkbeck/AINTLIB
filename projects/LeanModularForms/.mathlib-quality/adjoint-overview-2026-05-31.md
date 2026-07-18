# AdjointTheory subtree — structural overview (2026-05-31)

**Scope.** 18,359 LOC across 7 files:

| File | LOC | Decls (total) | Private |
| ---- | --: | ------------: | ------: |
| `AdjointTheory.lean` | 911 | 60 | 28 |
| `AdjointTheoryPetersson.lean` | 1,002 | 53 | 45 |
| `AdjointTheory/FDTransport.lean` | 2,305 | 109 | 16 |
| `AdjointTheory/SummandAdjoint.lean` | 1,938 | 89 | 24 |
| `AdjointTheory/DeltaBSystem.lean` | 3,604 | 134 | 104 |
| `AdjointTheory/TileBridge.lean` | 4,116 | 124 | 66 |
| `AdjointTheory/ConcreteFamily.lean` | 4,483 | 134 | 115 |
| **Total** | **18,359** | **703** | **398** |

**Sorries:** 0 in scope. Build is green. The four protected headlines (`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_constMul`, `strongMultiplicityOne_axiom_clean`) all transitively depend on this subtree.

## Headlining note — the real proof path

`heckeT_p_adjoint` (ConcreteFamily:4476) is proved in **25 lines** by
`petN_heckeT_p_adjoint_via_trace` (ConcreteFamily:4446), the **DIRECT** route, which
composes only:

1. `petN_heckeT_p_LHS_eq_aggregate` (3900),
2. `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` (120),
3. `aggregate_D_petersson_eq_Gamma_p_A_fundDomain` (4101),
4. `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`
   (FDTransport:1641),
5. `traceSlash_T_p_lower_eq_diamond_inv_heckeT_p` (4369),

plus support lemmas. The substrate underneath this DIRECT route is `FDTransport`,
`SummandAdjoint` (just the slash-adjoint substrate `peterssonInner_slash_adjoint`,
`peterssonAdj_*`, `petN_slash_adjoint_GL2`, integrability/measure lemmas, the
diamond/heckeT_p commutation reindex), and a handful of facts in `DeltaBSystem` (the
trace-engine inputs `ds_traceSlash_*` and the **Γ_p(α) ↔ Γ_up bridge**). The DIRECT
trace route does NOT touch the giant Blocker / Family / Balanced / Canonical /
SLTileBalance / PerQSigmaAligned / SigmaQPerm / TileFormIntegralResidual machinery
that occupies most of ConcreteFamily.lean (lines ~30–3900) and most of TileBridge.lean.

**The single external API hook into the heavy chain** is
`petN_heckeT_p_adjoint_on_charSpace_via_sum_chain` (AdjointTheoryPetersson:489),
which is itself **not used anywhere downstream** (`grep` confirms zero external
callers). The hypothesis `h_LHS_dist_eq_RHS_absorbed` is an enormous unfolded
`LHSDistEqRHSAbsorbed` term inlined verbatim into the theorem signature (~60 LOC of
signature). Removing that one hook severs the entire dead chain.

---

## 1. The Family Sprawl

Naming families with ≥2 near-parallel siblings:

### 1A. `MInfty*` / `TpUpper*` data-prop pairs (TileBridge.lean)

For nearly every prop-type definition involving the `M_∞` matrix vs. the
`T_p_upper b` matrix family, there is a `MInfty…` def and a `TpUpper…` def that are
literally the same Prop with `glMap (M_infty …)` replaced by
`glMap (T_p_upper p hp.pos b)` and an extra `∑ b ∈ Finset.range p` wrapper:

| `MInfty…` | `TpUpper…` | Lines |
| --------- | ---------- | ----: |
| `MInftyTileShiftPrefactored` | `TpUpperTileShiftPrefactored` | 119/150 |
| `MInftyFDSlashExchange` | `TpUpperFDSlashExchange` | 183/215 |
| `MInftyBranchBalanced` | `TpUpperBranchBalanced` | 251/285 |
| `MInftySLTileBalance` | `TpUpperBSLTileBalance` | 365/319 |
| `MInftyTilePairwiseAEDisjoint` | (absorbed into `AlphaFamilyPerQTilePairwiseAEDisjoint`) | 384 |
| `MInftyTileNullMeasurable` | (ditto) | 396 |
| `MInftyIntegrableLHS/RHS` | `AlphaIntegrableLHS/RHS` | 406/421 vs 436/450 |
| `MInftyPostAdjSwapBalance` | (no T_p_upper twin — alpha-bundled is `AlphaPostSwapBalance`) | 341 |

**There is already a generic `Alpha*` family for many of these** (`AlphaIntegrableLHS`,
`AlphaIntegrableRHS`, `AlphaFDBalance`, `AlphaPostSwapBalance`, `AlphaSLTileBalance`,
`AlphaBalanced`, `AlphaCanonical`, `AlphaTpLowerFDSlashExchange`) that take a fully
general `α : GL (Fin 2) ℝ`. The `MInfty*`/`TpUpper*` siblings are then just
specialisations at `α := glMap (M_infty …)` and `α := glMap (T_p_upper …)`. The
*existence* of the generic `Alpha*` family proves the unification is mechanical —
**but the project still ships both** because the `MInfty*` form is what the
downstream sum-chain unfolds to.

Verdict: **MInftyTileShiftPrefactored, MInftyFDSlashExchange, MInftyBranchBalanced,
TpUpperTileShiftPrefactored, TpUpperFDSlashExchange, TpUpperBranchBalanced** are all
single-instance specialisations of one common Alpha-form that the generic family
already implements. **The Alpha* family already exists**; the MInfty*/TpUpper*
specialisations could be replaced by abbreviations.

LOC impact: TileBridge `MInfty*`/`TpUpper*` defs alone occupy ~430 LOC (lines 119 –
~525, minus the `Alpha*` block 436–600). The downstream consumer theorems
(`h_M_infty_*` vs. `h_upper_*`) double again on the proof side.

### 1B. `M_infty_branch_*` / `T_p_upper_branch_*` proof-helper pairs (TileBridge.lean)

These are *identical proofs* of identical-up-to-rename statements:

| `M_infty_branch_*` | `T_p_upper_branch_*` | LOC each |
| ------------------ | -------------------- | -------: |
| `M_infty_branch_RHS_unfactor_slot2` (2440) | `T_p_upper_branch_RHS_unfactor_slot2` (2647) | ~35 |
| `M_infty_branch_LHS_sigma_reindex` (2476) | (no twin) | ~45 |
| `M_infty_branch_LHS_normalize_to_diamond` (2520) | `T_p_upper_branch_LHS_normalize_to_diamond` (2685) | ~60 |
| `M_infty_branch_sum_slash_adjoint_reindex_prefactored` (2579) | `T_p_upper_branch_sum_slash_adjoint_reindex_prefactored` (2745) | ~55 |
| `M_infty_branch_hypothesis_via_sum_chain` (2636) | `T_p_upper_branch_hypothesis_via_sum_chain` (2805) | ~10 |
| `peterssonInner_per_tile_match_M_infty_branch` (1912) | `peterssonInner_per_tile_match_T_p_upper_branch` (1957) | ~45 |
| `peterssonInner_per_tile_match_M_infty_branch_closed` (2001) | `peterssonInner_per_tile_match_T_p_upper_branch_closed` (2074) | ~70 |

I read both `M_infty_branch_LHS_normalize_to_diamond` (2520) and
`T_p_upper_branch_LHS_normalize_to_diamond` (2685) in full. They are
**word-for-word identical** modulo the substitution `M_∞ ↔ T_p_upper b` and an
added `∑ b ∈ Finset.range p` on the outside. Same `slash_diamond_inv_M_infty_eq_T_p_lower_epsilon`
vs. `slash_diamond_inv_T_p_upper_eq_T_p_lower_delta` step (the only difference is
which support lemma is invoked).

LOC impact: ~320 LOC of mirror-image proofs that could be one parametric proof.

### 1C. `slash_…_M_infty_…` / `slash_…_T_p_upper_…` lemma pairs (SummandAdjoint.lean)

The slash-action-of-M_∞ vs. slash-action-of-T_p_upper lemmas come in matched pairs:

| M_∞ lemma | T_p_upper lemma | Loc |
| --------- | --------------- | --: |
| `slash_diamond_inv_M_infty_eq_slash_T_p_lower` (508) | (none; T_p_upper-side handled below) | ~25 |
| `slash_diamond_inv_M_infty_eq_slash_T_p_lower_cusp` (543) | (none) | ~8 |
| `slash_M_infty_eq_diamond_slash_T_p_lower_cusp_g` (551) | (similar pattern for T_p_upper exists in TileBridge:746) | ~12 |
| `peterssonInner_slash_M_infty_eq_diamond_T_p_lower_cusp_g` (562) | similar T_p_upper at TileBridge:779 | ~12 |
| `slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower` (1918) | `slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower` (1927) | ~10 each |
| `peterssonAdj_glMap_M_infty_eq` (315) | `peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower` (1879) | ~15 each |
| `peterssonAdj_T_p_upper_eq_shift_mul_lower` (362) | `peterssonAdj_glMap_T_p_lower` (257) | shared substrate |
| (M_∞ branch of `aedisjoint_*`) `aedisjoint_glMap_M_infty_T_p_upper` (1407), `aedisjoint_glMap_M_infty_T_p_upper_fd_per_q` (1645) | (T_p_upper branch) `aedisjoint_glMap_T_p_upper_pair` (1099), `aedisjoint_glMap_T_p_upper_pair_fd_per_q` (1117) | ~20 each |

### 1D. `ds_p_plus_one_family_*_inv_mul_notMem_*` 4-case nested splits (DeltaBSystem.lean)

The `T_p_lower_tile_family_*_inv_mul_notMem_Gamma_up` lemma is split into
`some_some`, `some_none`, `none_some`, `none_none` cases — four near-identical
proofs at lines 2934, 2964, 2985, 3009. Identical pattern for
`ds_p_plus_one_family_Gamma1_factor_*_inv_mul_notMem_Gamma0` at lines 3276, 3311,
3335, 3357. Both 4-tuples are then bundled by `_inv_mul_notMem_Gamma_up` /
`_inv_mul_notMem_Gamma0`. The 4-way `Option (Fin p) × Option (Fin p)` split is
essentially a manual `match` that `fin_cases` + a single proof body would handle.

LOC impact: ~250 LOC for 8 nearly identical case proofs that should be ~50 in one
unified proof.

### 1E. `*_per_q_*` / `*_per_b_*` / `*_per_tile_*` / `*_per_alpha_*` per-index families

| Pattern | Sample count | Locus |
| ------- | -----------: | ----- |
| `*_per_q_*` (per coset) | 27 decls | DeltaBSystem, ConcreteFamily, TileBridge |
| `*_per_b_*` (per upper-tile) | 6 decls | SummandAdjoint, TileBridge |
| `*_per_tile_*` (per tile of canonical SL union) | 8 decls | ConcreteFamily |
| `*_per_alpha_*` / `*_per_α_*` (per Option (Fin p) branch) | 4 decls | DeltaBSystem |

Each of these takes a "per-X" lemma and lifts it to a Σ-X aggregate, often via a
single `Finset.sum_congr rfl` plus a measure-of-iUnion split. The patterns are
mechanical and could be Mathlib-style combinators (`Finset.sum_iUnion_aedisjoint`,
`Pairwise.lift`).

LOC impact: ~600 LOC of essentially uniform per-X → Σ-X lifts.

### 1F. `Gamma_p_α` / `Gamma_p` / `Gamma_up` / `Gamma1` / `Gamma0` subgroup family

The `FDTransport.lean` file is mostly the API for `Gamma_p_α α` (FDTransport:41),
implemented uniformly for **arbitrary** α via `Gamma_p_α α := mapGL ℚ ⁻¹'
(toConjAct α • mapGL ℚ '' Γ_1 ∩ mapGL ℚ '' Γ_1)`. The instantiations are scattered:

- `Gamma_p_α_T_p_lower_eq_inf` (1832) — instantiate α = T_p_lower
- `Gamma_up_eq_conj_Gamma0` (2049) — relate to `Gamma_up p`
- `Gamma_up_sup_Gamma1_eq_top` (2100) — index calculation
- `Gamma1_relIndex_Gamma_up_eq_index` (2186)
- `Gamma_up_relIndex_Gamma1` (2225)
- `relIndex_Gamma_p_α_T_p_lower` (2001)

These are all the **same index-counting computation** done from different angles
(via Goursat / via the Gamma0/Gamma1/Gamma_up triple / via the conjugation
isomorphism). The fact that the level structure `Γ_p(T_p_lower) = Γ_1 ∩
Γ_up^conj` is provable in three different ways suggests an opportunity for
consolidation but the parallel statements probably each pull their weight elsewhere.

### 1G. The "`_via_*`" suffix family in ConcreteFamily (the entry-point sprawl)

`petN_heckeT_p_symmetric_form_from_*` and `petN_heckeT_p_adjoint_standard_form_from_*`
have **many** parallel "from_X" wrappers, each taking a different hypothesis bundle:

- `from_TpHeckeFamilyBlocker` (1168), `from_TpHeckeFamilyBlocker_v2` (1193),
  `from_v2_bundled` (1218),
- `from_uniform` (1234), `from_SL_tile_balances` (1252),
- `from_per_q` (1289), `from_per_q_fd` (1357),
- `from_petN_symmetric_form` (1435), `from_combined_hecke_sum_residual` (1454),
- `from_HeckeFD_swap` (1535), `from_aggregate_hypotheses` (1608),
- `from_two_residuals` (916), `from_two_tile_shift_residuals` (2713),
  `from_two_FD_slash_exchanges` (2726), `from_SL_tile_balances` (2741),
- `from_per_tile_balances` (3216), `from_per_q_fd_balances` (3302),
- `from_canonical_SL_balance` (2822), `from_heckeFD_canonical_SL_tile_balance` (2809),

…each ~30–80 LOC, each chaining through the layer below it.

LOC impact: ~1,500 LOC of "different doors into the same building." The entire
`Blocker` / `Balanced` / `Canonical` / `SLTileBalance` / `PerQSigmaAligned` /
`SigmaQPerm` / `TileFormIntegralResidual` sequence is **dead code** under the
DIRECT trace route now used by `heckeT_p_adjoint`. It exists because the *older*
plan was to use `DSDoubleCosetTileBridge`, which red-team analysis (`plan-adjoint.md`)
showed was circular; the trace route was added later as the actual proof, but the
sum-chain machinery was kept.

---

## 2. Hypothesis sprawl

### 2A. Existing bundles

| Bundle | Lines | Fields |
| ------ | ----- | -----: |
| `TpHeckeFamilyMeasureHypotheses` | ConcreteFamily:462 | 8 (4 each × M_∞/T_p_upper) |
| `TpHeckeFamilyBlocker` | ConcreteFamily:526 | 2 (M_∞-blocker + ∀b T_p_upper-blocker) |
| `TpHeckeFamilyBlocker_v2` | ConcreteFamily:852 | 2 (v2 variant) |
| `heckeFD_canonical_SL_tile_balance` | ConcreteFamily:2769 | 2 (M_∞ + family) |
| `DSDoubleCosetTileBridge` | TileBridge:30 | 1 (giant Prop; itself a 60-LOC unfolded sum equality) |
| `MInftyBranchIUnionEqRHSPrefactored` | ConcreteFamily:986 | 1 |
| `UpperBranchIUnionEqRHSPrefactored` | ConcreteFamily:1019 | 1 |
| `LHSDistEqRHSAbsorbed` | ConcreteFamily:1053 | 1 |

### 2B. Recurring un-bundled hypothesis tuples (≥5 headlines)

Across the ConcreteFamily "from_*" wrappers, these hypothesis 4-tuples appear
repeatedly (raw, un-bundled, retyped in each signature):

**(M_∞ tile-measure 4-tuple)** appears in 7+ signatures as the same 4 lines:
- `hd_M : MInftyTilePairwiseAEDisjoint p hp hpN` (or unfolded `Pairwise (… AEDisjoint …)`)
- `hm_M : MInftyTileNullMeasurable p hp hpN`
- `hint_LHS_M : MInftyIntegrableLHS p hp hpN f g`
- `hint_RHS_M : MInftyIntegrableRHS p hp hpN f g`

**Proposed bundle `MInftyTileMeasure` (4 fields).** Already partially bundled in
`TpHeckeFamilyMeasureHypotheses` but in unfolded form mixed with T_p_upper
hypotheses.

**(T_p_upper family tile-measure 4-tuple)** appears similarly in 7+ signatures:
- `hd_U : ∀ b ∈ Finset.range p, AlphaTilePairwiseAEDisjoint (glMap …)`
- `hm_U : ∀ b ∈ Finset.range p, AlphaTileNullMeasurable (glMap …)`
- `hint_LHS_U : ∀ b ∈ Finset.range p, AlphaIntegrableLHS …`
- `hint_RHS_U : ∀ b ∈ Finset.range p, AlphaIntegrableRHS …`

**Proposed bundle `TpUpperFamilyTileMeasure` (4 fields).** Same shape as the M_∞
one above; could share a single `AlphaTileMeasure α f g` 4-tuple bundle and let the
M_∞ vs. family-of-T_p_upper distinction be expressed as a `∀ α ∈ S, AlphaTileMeasure α f g`
over a finset `S = {M_∞} ∪ image (T_p_upper) (range p)` — or, even cleaner, over
the existing `α_T_p_PSL_R` / `α_T_p_GLPos` / `α_T_p_Q` projective tile family
(ConcreteFamily:30–49) that already unifies M_∞ and T_p_upper as
`α_T_p_Q : Option (Fin p) → GL (Fin 2) ℚ`. The projective `α_T_p_*` family is the
correct abstraction; the `MInfty…`/`TpUpper…` split is legacy.

**(SL-tile-union 3-tuple)** appears in 5+ signatures as the same 3 hypotheses
(disjoint / null-measurable / integrable on `⋃ q, q.out⁻¹ • fd`):
- `hd : SLTilePairwiseAEDisjoint`
- `hm : SLTileNullMeasurable`
- `hint : SLTileIntegrableUnion …`

**Proposed bundle `SLTileUnion` (3 fields).** Often appears unfolded mid-proof,
even though the 3 names exist as separate defs.

**(α-tile-union 3-tuple)** the α-parameterised analogue, in `AlphaTile*` form:
- `hd : AlphaTilePairwiseAEDisjoint (N := N) α`
- `hm : AlphaTileNullMeasurable (N := N) α`
- `hint_LHS / hint_RHS : AlphaIntegrableLHS/RHS … α f g`

**Proposed bundle `AlphaTileUnion α f g` (4 fields).** Or 3 fields if LHS/RHS
integrabilities are combined.

### 2C. The "f, g, p, hp, hpN" prefix

Every theorem in `ConcreteFamily.lean` starts with the same 5-tuple
`(p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (f g : CuspForm (…) k)`.
That is ~700 lines of repeated signature noise across the 134 declarations in the
file. A `variable` block at the top of the file (or `variable` in a `section`)
would eliminate it cleanly.

LOC impact: ~700–900 LOC saving (5 lines × ~150 decls in scope).

### 2D. Inlined unfolded equations in theorem statements

`DSDoubleCosetTileBridge` (TileBridge:30 — a 54-LOC Prop body, an equation of two
giant sums), `LHSDistEqRHSAbsorbed` (ConcreteFamily:1053 — 57 LOC), and the
matching `h_LHS_dist_eq_RHS_absorbed` hypothesis in
`petN_heckeT_p_adjoint_on_charSpace_via_sum_chain` (AdjointTheoryPetersson:493
— 55 LOC) are all the **same** sum equation written out three times. This 165 LOC
of literal duplication is one `def` away from being a 1-line hypothesis.

---

## 3. The redundant "blockers" / "data" structures

| Decl | Lines | Fields | Verdict |
| ---- | ----: | -----: | ------- |
| `TpUpperZeroShiftedFormBlocker` (TileBridge:3798) | 30 | Prop (single eq) | Used by `_from_blocker`, `_eq_uniform`. **Redundant with `TpUniformSigmaPermBlocker`** (ConcreteFamily:533) at α=T_p_lower (see `TpUpperZeroShiftedFormBlocker_v2_eq_uniform`:790). |
| `TpUpperZeroShiftedFormBlocker_v2` (ConcreteFamily:424) | 18 | Prop (eq) | Equal to `TpUniformSigmaPermBlocker … (glMap T_p_lower)` (proven by `_v2_eq_uniform`). **Pure renaming.** |
| `TpUpperBranchDiamondFormBlocker` (TileBridge:3828) | 23 | Prop (eq) | Equal to `TpUniformSigmaPermBlocker … (glMap T_p_lower * gamma_b)` (proven by `_eq_uniform`:819). **Pure renaming.** |
| `TpHeckeFamilyBlocker` (ConcreteFamily:526) | 2 | 2 conjuncts | Just `TpUpperZeroShiftedFormBlocker ∧ ∀ b, TpUpperBranchDiamondFormBlocker`. |
| `TpHeckeFamilyBlocker_v2` (ConcreteFamily:852) | 2 | 2 conjuncts | Variant of above with `_v2` left conjunct. **Pure renaming**, eliminable. |
| `TpHeckeFamilyMeasureHypotheses` (ConcreteFamily:462) | 50 | 8 conjuncts | The only large bundle that genuinely consolidates 8 hypotheses; keep. |
| `TpUniformSigmaPermBlocker` (ConcreteFamily:533) | 17 | Prop (eq parameterised by M) | The **actual** common form; every other Blocker above reduces to this at a specific M. |
| `TpPerQSigmaAlignedBlocker` (ConcreteFamily:551) | 18 | Prop (eq per q) | Per-q form of TpUniformSigmaPermBlocker. |
| `TpPerQSigmaAlignedBlocker_fd` (ConcreteFamily:570) | 20 | Prop (eq per q on FD) | FD-form (no `⋃ q` smul) of above. |
| `heckeFD_canonical_SL_tile_balance` (ConcreteFamily:2769) | 30 | 2-tuple | M_∞ + ∀b T_p_upper SL-tile balance. **Bundleable via existing `Alpha*` family.** |
| `heckeT_p_petN_symmetric_residual` (ConcreteFamily:1447) | 5 | Prop (eq) | Just `petN(T_p f, g) = petN(⟨p⟩f, T_p g)` aliased as a name. **Eliminable.** |
| `LHSDistEqRHSAbsorbed` (ConcreteFamily:1053) | 57 | Prop (eq) | The "irreducible algebraic hypothesis" — a 57-LOC unfolded sum equality. Should be a 1-line `def` referencing `MInftyTileShiftPrefactored + TpUpperTileShiftPrefactored` (which it equals up to algebraic rearrangement). |
| `MInftyBranchIUnionEqRHSPrefactored` (ConcreteFamily:986) | 27 | Prop (eq) | Intermediate-only; used once by `h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion`. **Inlineable.** |
| `UpperBranchIUnionEqRHSPrefactored` (ConcreteFamily:1019) | 27 | Prop (eq) | Twin of above. **Inlineable.** |
| `SigmaQPermResidual_M_infty` (ConcreteFamily:3400) | 33 | Prop (eq) | Used by 3 `_of_*` lemmas. Specialisation of a generic `SigmaQPermResidual α`. |
| `SigmaQPermResidual_upper` (ConcreteFamily:3433) | 33 | Prop (eq) | Mirror of above. **Should be one parametric.** |
| `TileFormIntegralResidual_M_infty` (ConcreteFamily:3466) | 25 | Prop (eq) | Used by 1 `_of_*` lemma. **Inlineable.** |
| `TileFormIntegralResidual_upper` (ConcreteFamily:3491) | 25 | Prop (eq, indexed by b) | Mirror. |
| `TileFormIntegralResidual_M_infty_sigma_p_reduced` (ConcreteFamily:3516) | 31 | Prop (eq) | Used once. |
| `TileFormIntegralResidual_M_infty_per_q` (ConcreteFamily:3633) | 24 | Prop (eq per q) | Used once. |
| `DSDoubleCosetTileBridge` (TileBridge:30) | 54 | Prop (eq) | The T024 entry point. **Dead** — no external callers; the trace route bypasses it. |
| `Hecke_FD_integral_residual` (DeltaBSystem:957) | 12 | Prop | Private helper, single use. |
| `T_p_lower_tile_family` (DeltaBSystem:687) | 5 | def | Used. |
| `Hecke_rep_family` (DeltaBSystem:693) | 5 | def | Used. |
| `ds_p_plus_one_family_Gamma1_factor` (DeltaBSystem:143) | 6 | def | Used. |
| `traceSlash_Gamma_p_α` (FDTransport:1313) | 10 | def | Substrate of the trace engine. **Keep.** |
| `TraceFiberIntegrable` (FDTransport:1325) | 13 | Prop | Substrate. **Keep.** |
| `Gamma_p_α_fundDomain_PSL` (FDTransport:356) | 8 | def | Substrate. **Keep.** |
| `Gamma_p_α_fundDomain_PSL_canonical` (FDTransport:484) | 6 | def | Substrate. **Keep.** |
| `image_Gamma_p_α_PSL` (FDTransport:451) | 4 | def | Substrate. **Keep.** |
| `Gamma_up` (FDTransport:2024) | 17 | subgroup def | Substrate. **Keep.** |
| `α_T_p_Q`, `α_T_p_GLPos`, `α_T_p_PSL_R` (ConcreteFamily:30/38/46) | 5/5/3 | family defs | The **correct** abstraction (Option (Fin p) → GL (…)). **Keep — should be used more.** |
| `peterssonAdj` (AdjointTheory:609) | 6 | def | Core substrate. **Keep.** |

Net: ~12 of the `*_Blocker` / `*_Data` / `*_Residual` structures are pure renamings,
single-use intermediates, or are subsumed by `TpUniformSigmaPermBlocker` or the
existing `Alpha*` family. Eliminating them inlines ~250 LOC of defs plus
~400 LOC of `*_of_*` lemma chains.

---

## 4. Duplicate proof bodies

### 4A. Mirror-image proofs across `_M_infty` ↔ `_upper` (TileBridge)

Verified by reading both bodies in full:

- `M_infty_branch_LHS_normalize_to_diamond` (2520, 27 LOC body) **==**
  `T_p_upper_branch_LHS_normalize_to_diamond` (2685, ~30 LOC body) modulo
  `slash_diamond_inv_M_infty_eq_T_p_lower_epsilon` ↔ `…_T_p_upper_eq_T_p_lower_delta`.

- `M_infty_branch_sum_slash_adjoint_reindex_prefactored` (2579, 55 LOC body) **==**
  `T_p_upper_branch_sum_slash_adjoint_reindex_prefactored` (2745, ~60 LOC body).
  Same `peterssonInner_slash_adj_M_infty_q_summand_eq` ↔
  `peterssonInner_slash_adj_T_p_upper_q_summand_eq` swap.

- `M_infty_branch_RHS_unfactor_slot2` (2440, ~35 LOC) **==**
  `T_p_upper_branch_RHS_unfactor_slot2` (2647, ~30 LOC) using
  `slash_M_infty_eq_diamond_slash_T_p_lower_factor` ↔
  `slash_T_p_upper_eq_diamond_slash_T_p_lower_factor`.

- `peterssonInner_per_tile_match_M_infty_branch{,_closed}` (1912/2001) **==**
  `peterssonInner_per_tile_match_T_p_upper_branch{,_closed}` (1957/2074) with the
  same b-sum wrapping.

- `per_q_M_infty_branch_full_absorb` (795, 40 LOC) **==**
  `per_q_T_p_upper_branch_full_absorb` (835, 40 LOC).

- `heckeFD_canonical_SL_tile_balance_M_infty_from_per_tile_balance` (2894, ~45
  LOC) **==** `heckeFD_canonical_SL_tile_balance_α_branch_from_per_tile_balance`
  (2938, ~40 LOC) — the M_∞ version actually *invokes* the α-branch version (or
  could; they're nearly identical structurally).

**Total mirror-body LOC: ~700 LOC** that one parametric proof (taking
`α : GL (Fin 2) ℝ` and a `gamma_α : SL(2, ℤ)` factorisation as parameters) would
collapse to ~350 LOC. The `Alpha*` family defs already exist, so the unification
is a structural refactor, not a fresh mathematical development.

### 4B. The 4-case `Option (Fin p)`-split in DeltaBSystem

- `T_p_lower_tile_family_some_some_inv_mul_notMem_Gamma_up` (2934, ~30 LOC)
- `T_p_lower_tile_family_some_none_inv_mul_notMem_Gamma_up` (2964, ~22 LOC)
- `T_p_lower_tile_family_none_some_inv_mul_notMem_Gamma_up` (2985, ~25 LOC)
- (none-none is degenerate, handled by `hij : i ≠ j` directly)

All three proof bodies share the same skeleton: extract the matrix entries via
`fin_cases`, show divisibility fails via a `ZMod`-arithmetic check. Identical
pattern reappears in lines 3276–3357 for `ds_p_plus_one_family_Gamma1_factor_…_inv_mul_notMem_Gamma0`.

Estimated saving: 8 × ~25 = 200 LOC → 1 parametric proof of ~40 LOC = **160 LOC saved**.

### 4C. Repeated `let ... in` matrix conversions

The `glMap_T_p_upper_det_pos` proof body (SummandAdjoint:44; **also** TileBridge:1120) is
copied verbatim across the two files (≥30 LOC each). Same pattern of
`show 0 < (... : Matrix _ _ ℝ).det → rw [show ... = (algebraMap …) … from rfl, RingHom.map_det] → simp [T_p_upper, …]`.

The pattern recurs in `glMap_M_infty_det_pos` (SummandAdjoint:1560), and the inv
versions. Could be one helper lemma `glMap_det_pos_of_pos_rat_det`.

**Existing helper:** `glMap_det_pos_of_rat_det_pos` (ConcreteFamily:117 uses it
once). The det-pos lemmas in SummandAdjoint should be one-line wrappers around
this helper.

LOC saving: ~80.

### 4D. `slash_peterssonAdj_glMap_X_eq_slash_T_p_lower` (SummandAdjoint:1879–1927)

Four near-identical lemmas at lines 1879, 1896, 1918, 1927. Each follows the
same pattern: invoke a "shift" lemma then a "diamond" lemma. They share ~70% of
the body.

---

## 5. Cross-file redundancy

### 5A. Duplicate names across files

Confirmed duplicates by `uniq -d`:

- **`glMap_T_p_upper_det_pos`** defined in BOTH `SummandAdjoint:44` (`private`)
  and `TileBridge:1120` (public theorem). Both bodies identical. The
  `TileBridge` version shadows the `SummandAdjoint` private one in callers
  importing `TileBridge`. Should be promoted/moved to one location.

- **`TpHeckeFamilyBlocker_v2`** has two `_of_…` constructors (ConcreteFamily:858
  and 865). Both produce the same type from different inputs. Not strictly a
  duplicate name but a duplication of intent.

### 5B. Cross-file logical duplication

- `peterssonInner_slash_adjoint` (AdjointTheory:776, the master CoV) is invoked
  by `peterssonInner_slash_adjoint_for_heckeRep` (AdjointTheory:805) and
  `peterssonInner_slash_adjoint_for_heckeRep_per_q` (AdjointTheory:814) and
  `peterssonInner_slash_adjoint_coset` (SummandAdjoint:591) and
  `peterssonInner_slash_adjoint_coset_right` (SummandAdjoint:1506) and
  `peterssonInner_slash_adjoint_right` (SummandAdjoint:624) and
  `peterssonInner_slash_adjoint_q_summand_left` (TileBridge:1141). Six trivial
  specialisations of the same theorem.

- `slash_M_infty_eq_diamond_slash_T_p_lower_factor` and
  `slash_T_p_upper_eq_diamond_slash_T_p_lower_factor` (TileBridge:729/746)
  inline-prove M_∞ = (some Γ_0 factor) · T_p_lower, while
  `mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon` (DeltaBSystem:118)
  states the matrix identity directly. These say the same thing at different
  conjugacy levels.

- `aedisjoint_glMap_T_p_upper_pair{,_fd_per_q}` (SummandAdjoint:1099, 1117) and
  `aedisjoint_glMap_M_infty_T_p_upper{,_fd_per_q}` (SummandAdjoint:1407, 1645) and
  `aedisjoint_pairwise_T_p_family` (SummandAdjoint:1425) and
  `aedisjoint_pairwise_T_p_family_PSL_R` (ConcreteFamily:84) — a 5-step ladder
  proving the same disjointness in increasingly bundled forms. Could be 2 lemmas.

### 5C. `peterssonInner_T_p_reps_sum_slashes_eq_aggregate*` triplet

- `peterssonInner_T_p_family_sum_slashes_eq_aggregate` (SummandAdjoint:1455)
- `peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable`
  (SummandAdjoint:1481)
- `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD`
  (ConcreteFamily:120) — uses the previous
- `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R`
  (ConcreteFamily:200) — uses the previous

Four cascading wrappers, each adding one bridge layer (general → integrable →
HeckeFD-specific → PSL_R-specific). The DIRECT route consumes only #3. The first
two are general infrastructure; the fourth is a strictly-typed convenience that
adds little.

### 5D. `FDTransport` ↔ `DeltaBSystem` Gamma_p_α API duplication

`FDTransport.lean` builds the FD/quotient/index theory for `Gamma_p_α α`
*uniformly* for any α. Then `DeltaBSystem.lean` re-builds essentially the same
theory specifically for `α = T_p_lower` via a different angle (the `Gamma_up`
side, lines 2024–2298 of FDTransport, then DeltaBSystem 2553–3200 builds the
`toConjAct_GLPos` ↔ `Gamma_up` bridge). Result: two ways to prove the same FD
identification, both compiled. The FDTransport route is the substrate the
trace-engine actually uses (via `isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R`
at FDTransport:859); the DeltaBSystem `T_p_lower_tile_family` machinery
(DeltaBSystem:687–3186) is used to prove
`isFundamentalDomain_Hecke_tiles_Gamma_p_α` (DeltaBSystem:3186), which is then
invoked once by `aggregate_D_petersson_eq_Gamma_p_A_fundDomain` (ConcreteFamily:4101).

So both routes are live — but the existence of `Gamma_p_α_fundDomain_PSL_canonical`
+ the abstract isFundamentalDomain machinery in FDTransport suggests the
DeltaBSystem `T_p_lower_tile_family` derivation could be subsumed.

---

## 6. The Bloat Diagnosis (≤500 words)

This subtree is 18,359 LOC. With a clean rebuild on the DIRECT trace route it
could be ~4,500 LOC. The 4× bloat factor splits as follows, ranked by LOC
impact:

**(a) Structural family duplication of the `MInfty…` ↔ `TpUpper…` pair —
~2,000 LOC.** Every Prop-type definition has an M_∞-specific copy and a
T_p_upper-specific copy, and every proof has matching mirror-image bodies. A
generic `Alpha*` family already exists alongside (`AlphaFDBalance`,
`AlphaPostSwapBalance`, …); the M_∞/T_p_upper siblings are pure specialisations
that should be `abbrev`-ed or eliminated. The `α_T_p_Q : Option (Fin p) → GL …`
projective family (ConcreteFamily:30) is the correct unifying abstraction and is
already in use by `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R`
(120, 200) — but the older sum-chain machinery (~3,000 LOC of TileBridge +
ConcreteFamily) doesn't use it.

**(b) Hypothesis sprawl in signatures — ~1,500 LOC.** The same 4–8 measure /
integrability / disjointness hypotheses are retyped in dozens of `from_*` wrappers
in ConcreteFamily. Bundles like `AlphaTileMeasure α f g` (4 fields) and
`AlphaFamilyMeasure (α : ℕ → GL …) f g` (4 fields) would consolidate them. The
`f, g, p, hp, hpN` 5-tuple should be a `variable` block.

**(c) Over-specialised data structures — ~600 LOC.** `TpUpperZeroShiftedFormBlocker`,
`TpUpperZeroShiftedFormBlocker_v2`, `TpUpperBranchDiamondFormBlocker`,
`TpHeckeFamilyBlocker`, `TpHeckeFamilyBlocker_v2`, `heckeT_p_petN_symmetric_residual`,
`MInftyBranchIUnionEqRHSPrefactored`, `UpperBranchIUnionEqRHSPrefactored`, and
several `TileFormIntegralResidual_*` are pure renamings or single-use intermediates
that all reduce to `TpUniformSigmaPermBlocker`-at-an-`M` or to a Prop-equality.

**(d) Long unfolded proof bodies — ~500 LOC.** `petN_heckeT_p_adjoint_via_iUnion_residuals`,
`petN_LHS_dist_eq_RHS_absorbed_from_two_residuals`,
`petN_heckeT_p_adjoint_standard_form_from_per_tile_balances` each take ~100 LOC
of hypothesis list followed by a 1-paragraph proof. Mostly hypothesis bloat (b),
not body bloat.

**(e) Missing mathlib search — likely ~200 LOC.** Some FD/index calculations
(`Gamma1_relIndex_Gamma_up_eq_index`, `Gamma_up_relIndex_Gamma1`,
`relIndex_Gamma_p_α_T_p_lower`) re-derive standard index manipulations. The
`peterssonInner_iUnion_finite_aedisjoint` invocation pattern recurs ~15 times.

**(f) Dead chain — ~3,000 LOC.** The strongest single contributor. The entire
`DSDoubleCosetTileBridge` → `LHSDistEqRHSAbsorbed` → `*Blocker` → `*Balance` →
`*PerQ*` → `*TileFormIntegralResidual*` chain (≈3,000 LOC of TileBridge +
ConcreteFamily) was developed for the old T024 route, which the project's own
`plan-adjoint.md` red-team analysis exposed as circular. The new DIRECT trace
route via `petN_heckeT_p_adjoint_via_trace` (ConcreteFamily:4446) bypasses all of
it. The only external user of the chain is `petN_heckeT_p_adjoint_on_charSpace_via_sum_chain`
(AdjointTheoryPetersson:489), which has **zero** callers. Deleting the entire
chain + that one hook would not break anything downstream.

**Total expected saving:** (a)+(b)+(c)+(d)+(f) with overlap ≈ ~10,000 LOC,
landing the subtree at ~8k LOC. With more aggressive bundling and Alpha-family
unification (b)+(a) overlap pushes it lower, ~5k LOC.

---

## 7. The Reduction Plan

### Ticket R1 — Delete the dead `DSDoubleCosetTileBridge` chain
**Files:** TileBridge.lean (lines 30–117, 119–613, 795–2438, 2440–3996, 3798–3868);
ConcreteFamily.lean (lines 327–3399, 3633–3899); AdjointTheoryPetersson.lean
(lines 487–566). **LOC saved:** ~7,000. **Risk:** LOW. The four protected
headlines `heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`,
`strongMultiplicityOne_constMul`, `strongMultiplicityOne_axiom_clean` route
through `petN_heckeT_p_adjoint_via_trace` (ConcreteFamily:4446), which depends
ONLY on FDTransport + the SummandAdjoint slash-adjoint substrate + a small slice
of DeltaBSystem (the `ds_traceSlash_*` chain at DeltaBSystem 3403–3585 and the
matrix-entry support 36–135) + a thin slice of ConcreteFamily (lines 30–253 for
`α_T_p_*` + lines 3900–4030 for `petN_heckeT_p_LHS_eq_aggregate` and aggregate
measure hyps + 4030–4475 for `petN_heckeT_p_RHS_eq_aggregate`, the trace bridge,
and the headline). The `Gamma_p_α` substrate (FDTransport:41–1700) is the load-
bearing API and stays. Verify nothing external uses
`petN_heckeT_p_adjoint_on_charSpace_via_sum_chain` (already confirmed via
`grep`: zero callers). **Order:** First.

### Ticket R2 — Hoist `(p, hp, hpN, f, g)` to a `variable` block
**Files:** ConcreteFamily.lean (most decls), TileBridge.lean (post-R1),
DeltaBSystem.lean (most decls). **LOC saved:** ~700 (signature lines).
**Risk:** LOW. Pure cosmetic refactor.
**Order:** After R1 (so we're not touching dead code).

### Ticket R3 — Unify the `Alpha*` / `MInfty*` / `TpUpper*` Prop family via `α_T_p_*`
**Files:** TileBridge.lean (lines 119–600 + 700–870), ConcreteFamily.lean
(uses of `MInfty…` and `TpUpper…` props). **LOC saved:** ~600 if R1 already
deletes most of TileBridge; ~1,500 if R1 not yet done.
**Risk:** MEDIUM. The `Alpha*` family already exists; this is mostly removing
the M_∞ and T_p_upper instantiations and rewriting callers to `Alpha…
(α := glMap (M_infty …))`. The single substantive headache is the
`MInftyTileShiftPrefactored` vs `TpUpperTileShiftPrefactored` (extra `∑ b ∈ Finset.range p`
wrapper); a single `AlphaFamilyTileShiftPrefactored (α : ι → GL …)`
specialised at `α := α_T_p_Q` works.
**Order:** After R1 (or together with).

### Ticket R4 — Collapse the 4-case `Option (Fin p)` splits in DeltaBSystem
**Files:** DeltaBSystem.lean (lines 2934–3045 + 3276–3357 + 3377–3479).
**LOC saved:** ~160.
**Risk:** LOW. Replace 8 manual case proofs with 2 parametric proofs over
`Option (Fin p) × Option (Fin p)`. The combinatorial content is the same; only
the case-splitting becomes a `fin_cases`/`match` pattern.
**Order:** Independent of R1–R3.

### Ticket R5 — Move `glMap_T_p_upper_det_pos` to a single home; remove duplicate
**Files:** SummandAdjoint.lean (line 44, private — remove), TileBridge.lean
(line 1120, public — keep, or move to SummandAdjoint as public).
**LOC saved:** ~30 (one body deletion).
**Risk:** LOW. Pure name-collision cleanup.
**Order:** Anytime.

### Ticket R6 — Bundle measure hypotheses into `AlphaTileUnion / AlphaFamilyTileUnion`
**Files:** TileBridge.lean (defs `AlphaTilePairwiseAEDisjoint`,
`AlphaTileNullMeasurable`, `AlphaIntegrableLHS`, `AlphaIntegrableRHS`),
DeltaBSystem.lean (`AlphaFamilyPerQ*` 1429–1448), ConcreteFamily.lean (callers).
**LOC saved:** ~500–800 (most after R1).
**Risk:** LOW–MEDIUM. The fields are already separate defs; bundling means
introducing one `structure AlphaTileUnion α f g` and threading it through. The
DIRECT trace route does not need this (it uses `aggregate_HeckeFD_measure_hyps`
which already auto-discharges these), so this only helps the surviving
"hypothesised" API wrappers.
**Order:** After R3.

### Ticket R7 — Consolidate the `peterssonInner_slash_adjoint*` family
**Files:** AdjointTheory.lean (776, 805, 814), SummandAdjoint.lean (591, 624,
1506), TileBridge.lean (1141). **LOC saved:** ~80.
**Risk:** LOW. The 6 specialisations are trivial calls into
`peterssonInner_slash_adjoint`. Most callers should call the master directly,
or one `_coset` wrapper (the most common pattern).
**Order:** Anytime.

### Ticket R8 — Collapse the FDTransport / DeltaBSystem `Gamma_p_α` ↔ `Gamma_up` duplication
**Files:** DeltaBSystem.lean (lines 2553–3200, the
`toConjAct_GLPos_*`/`T_p_lower_tile_family_*` route to FD).
**LOC saved:** ~600 if `isFundamentalDomain_Hecke_tiles_Gamma_p_α`
(DeltaBSystem:3186) can be re-derived from FDTransport's
`Gamma_p_α_fundDomain_PSL_canonical` machinery. Probably partial: ~300 LOC.
**Risk:** MEDIUM–HIGH. This touches the trace-engine substrate. Needs
careful checking that `aggregate_D_petersson_eq_Gamma_p_A_fundDomain`
(ConcreteFamily:4101) still works.
**Order:** After R1; before any cleanup of FDTransport. Independent of R3–R7.

### Ticket R9 — Simplify the cascade of `peterssonInner_T_p_*sum_slashes_eq_aggregate*` wrappers
**Files:** SummandAdjoint.lean (1455, 1481), ConcreteFamily.lean (120, 200).
**LOC saved:** ~200.
**Risk:** LOW. Drop the unused intermediate wrappers; have the trace-route
call go directly to `_of_integrable` (1481).
**Order:** Anytime.

### Ticket R10 — Inline single-use Blocker/Residual defs (if R1 not pursued)
**Files:** ConcreteFamily.lean. **LOC saved:** ~250.
**Risk:** LOW. Only applies if R1 is NOT done (else they're gone). Inline
`MInftyBranchIUnionEqRHSPrefactored`, `UpperBranchIUnionEqRHSPrefactored`,
`TileFormIntegralResidual_M_infty_sigma_p_reduced`,
`TileFormIntegralResidual_M_infty_per_q`, `heckeT_p_petN_symmetric_residual`.
**Order:** Only if R1 declined.

---

### Summary of expected impact

| Ticket | LOC saved | Risk | Depends on |
| ------ | --------: | ---- | ---------- |
| R1 | ~7,000 | LOW | — |
| R2 | ~700 | LOW | R1 (recommended) |
| R3 | ~600 (post-R1) / ~1,500 (no R1) | MEDIUM | R1 (recommended) |
| R4 | ~160 | LOW | — |
| R5 | ~30 | LOW | — |
| R6 | ~500 | LOW–MED | R3 |
| R7 | ~80 | LOW | — |
| R8 | ~300 | MED–HIGH | R1 |
| R9 | ~200 | LOW | — |
| R10 | ~250 | LOW | only if R1 declined |
| **Total (R1+R2+R3+R4+R5+R6+R7+R8+R9)** | **~9,500–10,000** | mixed | — |

Landing target: **~8,000 LOC** with R1+R2+R5+R7+R9 alone (the LOW-risk core),
**~5,000–6,000 LOC** with the full plan including R3 and R6.

R1 alone takes the subtree from 18,359 → ~11,000 LOC at LOW risk.
