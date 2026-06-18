# Inventory: ./HasseWeil/AdditionPullback/Differential.lean

**File purpose**: Differential-pullback witness infrastructure for the `1 − π` isogeny
(`isogOneSub_negFrobenius`). Provides a chain of theorems discharging Witness #1
(omega-pullback coefficient = 1 implies separability) and Witness #2 (finite-dimensionality
of K(E) over the pullback algebra), assembling them into progressively fewer hypotheses
needed to prove `(isogOneSub_negFrobenius W hq).IsSeparable`.

**Imports**: `HasseWeil.AdditionPullback.Frobenius`, `HasseWeil.BridgeFrobenius`,
`HasseWeil.Curves.Differentials`, `HasseWeil.Hasse.HoleE`,
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`

**Total declarations**: 21 theorems, 0 defs, 0 instances. No `sorry` in any body.
No `set_option maxHeartbeats`.

---

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = (1 : ℤ) * omegaPullbackCoeff W (Isogeny.id W.toAffine) + (-1 : ℤ) * omegaPullbackCoeff W (frobeniusIsog W)) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: Given the Silverman III.5.2 additivity hypothesis for `1 − π = 1·id + (−1)·π`, deduces that the omega-pullback coefficient of `isogOneSub_negFrobenius` equals 1.
- **How**: Applies `omegaPullbackCoeff_m_plus_n_frob_of_witness` (BridgeFrobenius.lean) which unconditionally computes `m·a_id + n·a_frob = m` for any integers `m, n`; then `simpa` closes.
- **Hypotheses**: Finite field K with ≥ 2 elements; additivity sum identity (III.5.2 applied to `1·id + (−1)·π`).
- **Uses from project**: `omegaPullbackCoeff_m_plus_n_frob_of_witness` (BridgeFrobenius.lean)
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004` (L143), `isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge` (indirectly via prev)
- **Visibility**: public
- **Lines**: 79–87, proof ~8 lines
- **Notes**: Witness-parametric — leaves `h_add` as an open hypothesis.

---

### `theorem isogOneSub_negFrobenius_toAddMonoidHom_decomposition`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (isogOneSub_negFrobenius W hq).toAddMonoidHom = (Isogeny.id W.toAffine).toAddMonoidHom + (negFrobeniusIsog W).toAddMonoidHom`
- **What**: The rational-point map of `1 − π` decomposes as the sum of the identity hom and the negFrobenius hom at every point.
- **How**: `ext P`, rewrites LHS to `P − π·P` and RHS to `P + (−π·P)` via `Isogeny.id_toAddMonoidHom`, `negFrobeniusIsog_toAddMonoidHom_apply`, then `sub_eq_add_neg`.
- **Hypotheses**: Finite field K with ≥ 2 elements.
- **Uses from project**: `negFrobeniusIsog_toAddMonoidHom_apply` (from Frobenius import)
- **Used by**: `isogOneSub_negFrobenius_fiber_witness_of_sepDegree_eq_pointCount` (L502, `by rfl` check)
- **Visibility**: public
- **Lines**: 102–114, proof ~12 lines
- **Notes**: Structural `ext` proof; provides the morphism-decomposition input for BRIDGE-003.

---

### `theorem isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004`

- **Type**: `(hq) → (h_add : additivity sum) → (h_sep_iff : IsSeparable ↔ omegaPullbackCoeff ≠ 0) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Separability of `1 − π` from the additivity sum hypothesis and the T-II-4-004 iff (separability ↔ nonzero omega-coefficient), without assuming the iff is unconditional.
- **How**: First derives `omegaPullbackCoeff = 1` via `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness`; then feeds into `isogOneSub_negFrobenius_isSeparable_of_witnesses` (HoleE.lean).
- **Hypotheses**: Finite field; additivity sum identity; iff between IsSeparable and nonzero omega-coeff.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness`, `isogOneSub_negFrobenius_isSeparable_of_witnesses` (HoleE.lean)
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge` (L175), `isogOneSub_negFrobenius_isSeparable_of_h_add_only` (L446)
- **Visibility**: public
- **Lines**: 134–145, proof ~11 lines

---

### `theorem isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge`

- **Type**: `(hq) → (h_add) → (h_fin : FiniteDimensional) → (h_bridge : Subsingleton KaehlerDiff ↔ Injective pullbackKaehler) → IsSeparable`
- **What**: Separability of `1 − π` from additivity, finite-dimensionality of K(E) as pullback module, and the Kähler-differential bridge (cotangent-sequence iff).
- **How**: Composes `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004` with `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses` (HoleE.lean) to build the iff from `h_fin` and `h_bridge`.
- **Hypotheses**: Finite field; additivity sum; FiniteDimensional; Kähler bridge iff.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004`, `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses` (HoleE.lean)
- **Used by**: unused in file (leaf witness for future callers)
- **Visibility**: public
- **Lines**: 164–177, proof ~13 lines

---

### `theorem addPullback_x_negFrobenius_algebraicIndependent`

- **Type**: `(hq) → (hxy : AddNonInverse W (negFrobeniusIsog W)) → AlgebraicIndependent K (![addPullback_x W (negFrobeniusIsog W)] : Fin 1 → FunctionField)`
- **What**: The singleton `{addPullback_x_negFrobenius}` is algebraically independent over `K` in the function field.
- **How**: Rewrites via `algebraicIndependent_unique_type_iff` to transcendentality; applies `addPullback_x_transcendental_negFrobenius` (from Frobenius import).
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse` predicate (point image is not an inverse of the original).
- **Uses from project**: `addPullback_x_transcendental_negFrobenius` (Frobenius import)
- **Used by**: `addPullback_x_negFrobenius_isTranscendenceBasis` (L207)
- **Visibility**: public
- **Lines**: 188–195, proof ~7 lines

---

### `theorem addPullback_x_negFrobenius_isTranscendenceBasis`

- **Type**: `(hq) → (hxy) → IsTranscendenceBasis K (![addPullback_x W (negFrobeniusIsog W)] : Fin 1 → FunctionField)`
- **What**: The singleton `{addPullback_x_negFrobenius}` is a transcendence basis of K(E) over K.
- **How**: Applies `AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite` to the algebraic independence result, using `weierstrass_functionField_trdeg_eq_one` (Differentials import) to supply `trdeg = 1`.
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse`.
- **Uses from project**: `addPullback_x_negFrobenius_algebraicIndependent`, `weierstrass_functionField_trdeg_eq_one` (Differentials import)
- **Used by**: `addPullback_x_negFrobenius_isAlgebraic_subalgebra` (L226)
- **Visibility**: public
- **Lines**: 200–209, proof ~9 lines

---

### `theorem addPullback_x_negFrobenius_isAlgebraic_subalgebra`

- **Type**: `(hq) → (hxy) → @Algebra.IsAlgebraic (↥Algebra.adjoin K {addPullback_x W (negFrobeniusIsog W)}) FunctionField _ _ (Subalgebra.toAlgebra _)`
- **What**: K(E) is algebraic over the subalgebra `K[addPullback_x_negFrobenius]`.
- **How**: Directly applies `IsTranscendenceBasis.isAlgebraic` to `addPullback_x_negFrobenius_isTranscendenceBasis`.
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse`.
- **Uses from project**: `addPullback_x_negFrobenius_isTranscendenceBasis`
- **Used by**: `addPullback_x_negFrobenius_isAlgebraic_range_of_witness` (L276)
- **Visibility**: public
- **Lines**: 218–226, proof ~8 lines (term-mode, one-liner)
- **Notes**: Uses `@`-explicit `Subalgebra.toAlgebra` to bypass typeclass synthesis issues on the Weierstrass term.

---

### `theorem addPullback_x_negFrobenius_mem_range`

- **Type**: `(hq : 2 ≤ Fintype.card K) → addPullback_x W (negFrobeniusIsog W) ∈ (isogOneSub_negFrobenius W hq).pullback.range`
- **What**: The x-coordinate of the negFrobenius pullback lies in the range of the `1 − π` pullback algebra map.
- **How**: Shows `addPullbackAlgHom_negFrobenius W hq (x_gen) = addPullback_x W (negFrobeniusIsog W)` by unfolding the hom definitions (`addPullbackAlgHom_negFrobenius`, `addPullbackAlgHom_negFrobenius_of_inj`, `addPullbackAlgHom`), applying `IsFractionRing.liftAlgHom_apply`, `IsFractionRing.lift_algebraMap`, then `AdjoinRoot.lift_mk` + `simp` with `addBaseHom`.
- **Hypotheses**: Finite field ≥ 2.
- **Uses from project**: `addPullbackAlgHom_negFrobenius`, `addPullbackAlgHom_negFrobenius_of_inj`, `addPullbackAlgHom`, `addCoordAlgHom`, `addCoordRingHom`, `negFrobeniusIsog_addNonInverse`, `addBaseHom`, `addPullback_x` (all from Frobenius import)
- **Used by**: `addPullback_x_negFrobenius_isAlgebraic_range` (L292)
- **Visibility**: public
- **Lines**: 231–251, proof ~20 lines
- **Notes**: Heaviest unfolding proof in the file; navigates the fraction ring / adjoin root construction chain.

---

### `theorem addPullback_x_negFrobenius_isAlgebraic_range_of_witness`

- **Type**: `(hq) → (hxy) → (h_mem : addPullback_x ... ∈ α.pullback.range) → @Algebra.IsAlgebraic (↥α.pullback.range) FunctionField _ _ (Subalgebra.toAlgebra _)`
- **What**: K(E) is algebraic over `(isogOneSub_negFrobenius).pullback.range` as a subalgebra, given membership of `addPullback_x` in that range.
- **How**: Establishes `Algebra.adjoin K {addPullback_x} ≤ α.pullback.range` from `h_mem` (via `Algebra.adjoin_le_iff`); lifts element-wise algebraicity from the adjoin subalgebra using `IsAlgebraic.tower_top_of_subalgebra_le`.
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse`; membership witness.
- **Uses from project**: `addPullback_x_negFrobenius_isAlgebraic_subalgebra`
- **Used by**: `addPullback_x_negFrobenius_isAlgebraic_range` (L291)
- **Visibility**: public
- **Lines**: 258–280, proof ~22 lines

---

### `theorem addPullback_x_negFrobenius_isAlgebraic_range`

- **Type**: `(hq) → (hxy) → @Algebra.IsAlgebraic (↥(isogOneSub_negFrobenius W hq).pullback.range) FunctionField _ _ (Subalgebra.toAlgebra _)`
- **What**: K(E) is algebraic over the range subalgebra, unconditionally (no membership witness hypothesis).
- **How**: Composes `addPullback_x_negFrobenius_isAlgebraic_range_of_witness` with `addPullback_x_negFrobenius_mem_range`.
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse`.
- **Uses from project**: `addPullback_x_negFrobenius_isAlgebraic_range_of_witness`, `addPullback_x_negFrobenius_mem_range`
- **Used by**: `isogOneSub_negFrobenius_isAlgebraic_synonym` (L306)
- **Visibility**: public
- **Lines**: 284–292, proof ~8 lines (term-mode)

---

### `theorem isogOneSub_negFrobenius_isAlgebraic_synonym`

- **Type**: `(hq) → (hxy : AddNonInverse W (negFrobeniusIsog W)) → Algebra.IsAlgebraic (IsogenyAlgebraSource W (isogOneSub_negFrobenius W hq)) FunctionField`
- **What**: K(E) is algebraic over the type-synonym `IsogenyAlgebraSource W (isogOneSub_negFrobenius W hq)` (the pullback range with type-synonym wrapper).
- **How**: Uses `addPullback_x_negFrobenius_isAlgebraic_range`; builds the AlgEquiv `e : FunctionField ≃ₐ[K] α.pullback.range` via `AlgEquiv.ofInjective α.pullback α.pullback_injective`; transports element-wise algebraicity from range to synonym by converting the algebra map through `Polynomial.map_ne_zero_iff` and `convert ... using 2` on the aeval computation.
- **Hypotheses**: Finite field ≥ 2; `AddNonInverse`.
- **Uses from project**: `addPullback_x_negFrobenius_isAlgebraic_range`, `IsogenyAlgebraSource` (HoleE/Differentials import)
- **Used by**: `isogOneSub_negFrobenius_finiteDimensional` (L353)
- **Visibility**: public
- **Lines**: 300–332, proof ~32 lines
- **Notes**: LONG PROOF (>30 lines). Most involved proof in the file; requires careful algebra-map transport through the range isomorphism using `convert` and `RingHom.ext`.

---

### `theorem isogOneSub_negFrobenius_finiteDimensional`

- **Type**: `(hq : 2 ≤ Fintype.card K) → @FiniteDimensional FunctionField FunctionField _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule`
- **What**: K(E) is finite-dimensional as a module over the `1 − π` pullback algebra — Witness #2 for the Hasse bound, unconditionally (no extra hypotheses beyond `hq`).
- **How**: Instantiates `isogOneSub_negFrobenius_isAlgebraic_synonym` (discharging `hxy` via `negFrobeniusIsog_addNonInverse W`), then applies `isogeny_finiteDimensional_of_isAlgebraic_synonym` (HoleE.lean).
- **Hypotheses**: Finite field ≥ 2.
- **Uses from project**: `isogOneSub_negFrobenius_isAlgebraic_synonym`, `negFrobeniusIsog_addNonInverse` (Frobenius import), `isogeny_finiteDimensional_of_isAlgebraic_synonym` (HoleE.lean)
- **Used by**: `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero` (L375), `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_sep_and_fiber` (L480)
- **Visibility**: public
- **Lines**: 349–355, proof ~6 lines

---

### `theorem isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (isogOneSub_negFrobenius W hq).IsSeparable ↔ omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ≠ 0`
- **What**: T-II-4-004 fully unconditional for `1 − π`: separability is equivalent to nonzero omega-pullback coefficient, with no further hypotheses.
- **How**: Direct application of `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim` (HoleE.lean) supplying `isogOneSub_negFrobenius_finiteDimensional`.
- **Hypotheses**: Finite field ≥ 2.
- **Uses from project**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim` (HoleE.lean), `isogOneSub_negFrobenius_finiteDimensional`
- **Used by**: `isogOneSub_negFrobenius_isSeparable_of_h_add_only` (L447), `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only` (L461)
- **Visibility**: public
- **Lines**: 369–375, proof ~6 lines (term-mode)

---

### `theorem alpha_star_u_mulByInt_neg_one`

- **Type**: `alpha_star_u W (mulByInt W.toAffine (-1)) = -u_gen W`
- **What**: The negation isogeny `[−1]` pulls back the differential form generator `u_gen = 2y + a₁x + a₃` to its negative.
- **How**: Unfolds `alpha_star_u` to the explicit formula `2·[−1]^*y + a₁·[−1]^*x + a₃`; rewrites via `mulByInt_pullback_y_neg_one` and `mulByInt_pullback_x_neg_one`; closes by `ring`.
- **Hypotheses**: None (no `hq` needed).
- **Uses from project**: `mulByInt_pullback_y_neg_one`, `mulByInt_pullback_x_neg_one` (from Differentials import), `alpha_star_u`, `u_gen` (Differentials import)
- **Used by**: `omegaPullbackCoeff_mulByInt_neg_one` (L407)
- **Visibility**: public
- **Lines**: 382–391, proof ~9 lines

---

### `theorem omegaPullbackCoeff_mulByInt_neg_one`

- **Type**: `omegaPullbackCoeff W (mulByInt W.toAffine (-1)) = -1`
- **What**: The omega-pullback coefficient of the negation isogeny `[−1]` equals `−1`.
- **How**: Applies `omegaPullbackCoeff_unique` by verifying the spec equation `omegaPullbackCoeff_spec`; rewrites `[−1]^*x = x_gen` (via `mulByInt_pullback_x_neg_one`) and `alpha_star_u [−1] = -u_gen` (via `alpha_star_u_mulByInt_neg_one`); simplifies `inv_neg, neg_smul, neg_one_smul` to close.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec` (Differentials import), `alpha_star_u_mulByInt_neg_one`, `mulByInt_pullback_x_neg_one`
- **Used by**: `omegaPullbackCoeff_negFrobeniusIsog` (L422)
- **Visibility**: public
- **Lines**: 400–408, proof ~8 lines
- **Notes**: Explicitly avoids the Wronskian-based `omegaPullbackCoeff_mulByInt` (which carries `sorryAx`); this path is axiom-clean.

---

### `theorem omegaPullbackCoeff_negFrobeniusIsog`

- **Type**: `omegaPullbackCoeff W (negFrobeniusIsog W) = 0`
- **What**: The omega-pullback coefficient of `negFrobeniusIsog = [−1] ∘ π` equals 0.
- **How**: Unfolds `negFrobeniusIsog`; applies the chain rule `omegaPullbackCoeff_comp_of_base` with outer isogeny `[−1]` and inner `frobeniusIsog`, supplying `omegaPullbackCoeff [−1] = -1` (via `omegaPullbackCoeff_mulByInt_neg_one`) and `omegaPullbackCoeff π = 0` (via `omegaPullbackCoeff_frobenius`); closes `(-1) * 0 = 0`.
- **Hypotheses**: None.
- **Uses from project**: `omegaPullbackCoeff_comp_of_base` (BridgeFrobenius/Differentials), `omegaPullbackCoeff_frobenius` (BridgeFrobenius import), `omegaPullbackCoeff_mulByInt_neg_one`
- **Used by**: `isogOneSub_negFrobenius_isSeparable_via_leading_witnesses` (L544)
- **Visibility**: public
- **Lines**: 417–424, proof ~7 lines
- **Notes**: Axiom-clean by using `omegaPullbackCoeff_mulByInt_neg_one` rather than the sorry-carrying `omegaPullbackCoeff_mulByInt`.

---

### `theorem isogOneSub_negFrobenius_isSeparable_of_h_add_only`

- **Type**: `(hq) → (h_add : additivity sum) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Separability of `1 − π` from the additivity sum alone — T-II-4-004 iff is absorbed via the unconditional `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`.
- **How**: Applies `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004` with the unconditional iff.
- **Hypotheses**: Finite field ≥ 2; additivity sum hypothesis.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004`, `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 440–447, proof ~7 lines (term-mode)
- **Notes**: Leaf; only external file could use it.

---

### `theorem isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`

- **Type**: `(hq) → (h_coeff : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Separability of `1 − π` given only the omega-coefficient identity (= 1), with T-II-4-004 absorbed.
- **How**: Applies `isogOneSub_negFrobenius_isSeparable_of_witnesses` (HoleE.lean) with `h_coeff` and the unconditional iff.
- **Hypotheses**: Finite field ≥ 2; omega-coeff = 1.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable_of_witnesses` (HoleE.lean), `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: `isogOneSub_negFrobenius_isSeparable_via_leading_witnesses` (L547)
- **Visibility**: public
- **Lines**: 456–461, proof ~5 lines (term-mode)

---

### `theorem isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_sep_and_fiber`

- **Type**: `[Fintype Point] → (hq) → (h_pc_sep : IsSeparable) → (h_pc_fiber_witness : ∃ P₀, Nat.card fiber = sepDegree) → [Finite kernel] → sepDegree = pointCount W.toAffine`
- **What**: The separability degree of `1 − π` equals the number of K-rational points, given separability, a fiber witness, and finite kernel — Witness #2 (FiniteDimensional) is absorbed.
- **How**: Applies `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses` (HoleE.lean) supplying `isogOneSub_negFrobenius_finiteDimensional`.
- **Hypotheses**: Fintype of points; finite field ≥ 2; IsSeparable; fiber cardinality witness; Finite kernel.
- **Uses from project**: `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses` (HoleE.lean), `isogOneSub_negFrobenius_finiteDimensional`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 468–480, proof ~12 lines

---

### `theorem isogOneSub_negFrobenius_fiber_witness_of_sepDegree_eq_pointCount`

- **Type**: `[Fintype Point] → (hq) → (h_sepDeg : sepDegree = pointCount) → ∃ P₀, Nat.card fiber = sepDegree`
- **What**: Given that sepDegree equals pointCount, produces the fiber witness (∃ P₀ such that the fiber over P₀ has cardinality = sepDegree).
- **How**: Applies `hole_d_of_hom_and_sepDegree` (HoleE.lean) with the identification `(isogOneSub_negFrobenius).toAddMonoidHom = id − frobeniusIsog.toAddMonoidHom` checked by `rfl`.
- **Hypotheses**: Fintype of points; finite field ≥ 2; sepDegree = pointCount.
- **Uses from project**: `hole_d_of_hom_and_sepDegree` (HoleE.lean), `isogOneSub_negFrobenius_toAddMonoidHom_decomposition` (implicitly via `rfl`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 492–504, proof ~12 lines

---

### `theorem isogOneSub_negFrobenius_isSeparable_via_leading_witnesses`

- **Type**: `(hq) → (h_bridge_negFrob : omegaPullbackCoeff negFrob = algMap (formalIsogenySeries coeff 1 negFrob)) → (h_bridge_γ : same for γ) → (h_leading_add : coeff 1 of γ = coeff 1 of id + coeff 1 of negFrob) → IsSeparable`
- **What**: Separability of `1 − π` from three leading-coefficient bridge witnesses: BRIDGE-001 for negFrob and γ, plus formal-series leading-coefficient additivity.
- **How**: First derives `omegaPullbackCoeff γ = omegaPullbackCoeff id + omegaPullbackCoeff negFrob` from the three bridge hypotheses via `omegaPullbackCoeff_add_of_leading_witness` (BridgeFrobenius import); then substitutes `omegaPullbackCoeff_id = 1` and `omegaPullbackCoeff_negFrobeniusIsog = 0`; applies `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`.
- **Hypotheses**: Finite field ≥ 2; two BRIDGE-001 witnesses; leading-coefficient additivity of formal power series.
- **Uses from project**: `omegaPullbackCoeff_add_of_leading_witness` (BridgeFrobenius), `omegaPullbackCoeff_eq_formalIsogenyLeading_id` (BridgeFrobenius), `omegaPullbackCoeff_id` (Differentials), `omegaPullbackCoeff_negFrobeniusIsog`, `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 521–547, proof ~26 lines
- **Notes**: Closest to closing Witness #1 unconditionally; `h_leading_add` remains open.

---

## Summary

- **21 theorems**, 0 defs, 0 instances, 0 sorries.
- **No `set_option maxHeartbeats`** anywhere in the file.
- **Long proofs (>30 lines)**: `isogOneSub_negFrobenius_isAlgebraic_synonym` (~32 lines).
- **Key API** (used by ≥3 declarations in this file):
  - `isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004` (used by 2 directly, ~2 indirectly)
  - `isogOneSub_negFrobenius_finiteDimensional` (used by 3: isSeparable_iff, sepDegree_eq, finiteDim bridge)
  - `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero` (used by 2)
  - `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness` (used by 2)
- **Unused in file** (leaf theorems, likely intended for callers): `isogOneSub_negFrobenius_toAddMonoidHom_decomposition`, `isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge`, `isogOneSub_negFrobenius_isSeparable_of_h_add_only`, `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_sep_and_fiber`, `isogOneSub_negFrobenius_fiber_witness_of_sepDegree_eq_pointCount`, `isogOneSub_negFrobenius_isSeparable_via_leading_witnesses`.
