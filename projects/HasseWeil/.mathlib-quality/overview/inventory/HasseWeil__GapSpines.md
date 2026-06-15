# Inventory: ./HasseWeil/GapSpines.lean

**File summary**: 2233 lines. The central "spine" assembly file connecting pillar B (Verschiebung
dual) with V.1.3 (degree of 1−π = #E(Fq)). Contains: the Verschiebung existence chain,
the L6 tower/Lemma-5/ComputationA cluster, the full V.1.3 proof via embeddings classification
(including the HARD half `emb_le_card_kernel`), and the GAP-QF genuine-isogeny extensionality
and degree-quadratic framework. One `sorry` remains in `genuineIsogSmulSub_degree_eq_signed`.

---

## Declaration Inventory

### `theorem mulByInt_q_pullback_qth_root`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∀ z : FunctionField, ∃ g, g^q = ([q])*z`
- **What**: Every [q]-pullback element is a q-th power — the purely-inseparable content (Pillar B bottom leaf).
- **How**: One-line delegation to `qth_root_witness_general W` (from `Verschiebung.QthRootRouteB`).
- **Hypotheses**: Finite field with at least 2 elements; W elliptic.
- **Uses from project**: `qth_root_witness_general`
- **Used by**: `mulByInt_q_pullback_subset_frobenius`
- **Visibility**: public
- **Lines**: 40–43, proof ~1 line
- **Notes**: pure delegation

---

### `theorem mulByInt_q_pullback_subset_frobenius`
- **Type**: `(hq : 2 ≤ Fintype.card K) → [q]*.range ≤ π*.range`
- **What**: The image of [q]-pullback is contained in the image of Frobenius-pullback (Silverman II.2.11/III.6.2).
- **How**: Applies `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` with the witness from `mulByInt_q_pullback_qth_root`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`, `mulByInt_q_pullback_qth_root`
- **Used by**: `mulByInt_q_factors_through_frobenius`
- **Visibility**: public
- **Lines**: 47–51, proof ~1 line

---

### `theorem mulByInt_q_factors_through_frobenius`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∃ ψ : Isogeny, ψ.comp (frobeniusIsog W) = mulByInt W.toAffine q`
- **What**: [q] factors through Frobenius — Silverman II.2.12.
- **How**: Applies `mulByInt_q_factor_isog_of_subset_witness` with the subset witness from the previous theorem.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_q_factor_isog_of_subset_witness`, `mulByInt_q_pullback_subset_frobenius`
- **Used by**: `verschiebung_dual_exists`
- **Visibility**: public
- **Lines**: 56–59, proof ~1 line

---

### `theorem verschiebung_dual_exists`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∃ V : Isogeny, IsDualOf V (frobeniusIsog W)`
- **What**: GAP-QF keystone: the Verschiebung exists as an isogeny dual to the q-power Frobenius (Silverman III.6.1 Case 2).
- **How**: Applies `verschiebungIsog_isDualOf_frobenius_of_factor` with the factorization from `mulByInt_q_factors_through_frobenius`.
- **Hypotheses**: Same as above.
- **Uses from project**: `verschiebungIsog_isDualOf_frobenius_of_factor`, `mulByInt_q_factors_through_frobenius`
- **Used by**: unused in file (top-level output)
- **Visibility**: public
- **Lines**: 64–67, proof ~2 lines

---

### `theorem l6_B3_tower`
- **Type**: `(hq : 2 ≤ Fintype.card K) → Module.finrank (IntermediateField.adjoin K {γ.pullback x_gen}) FunctionField = 2 * γ.degree`
  where `γ = isogOneSub_negFrobenius W hq`
- **What**: GAP-L6 sub-leaf B3: the function field has degree 2·deg(1−π) over K⟮(1−π)*x⟯ (Silverman V.1.1 tower step).
- **How**: Tower identity via `Module.finrank_mul_finrank`: upper factor `[K(E):γ.pullback.fieldRange] = γ.degree` via `finrank_pullback_fieldRange_eq_degree`; lower factor `[γ.pullback.fieldRange : K⟮γ*x⟯] = 2` via `Algebra.finrank_eq_of_equiv_equiv` using the pair (e_f, gammaBar) of algebra equivalences threaded through `RatFunc.algEquivOfTranscendental` and `AlgEquiv.ofInjectiveField`. AlgHom equality proved via `IsLocalization.algHom_ext` + `Polynomial.algHom_ext`.
- **Hypotheses**: `2 ≤ #K`; `[Fintype W.toAffine.Point]` omitted (inner use).
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen_transcendental`, `finrank_pullback_fieldRange_eq_degree`, `finrank_functionField_eq_two`
- **Used by**: `moduleFinite_linfAt_gamma_pullback_x`, `isogOneSub_negFrobenius_pointCount_le_degree`, `Sinf_finrank_witness_via_B3_tower`
- **Visibility**: public
- **Lines**: 69–202 (set_option block at 69–71; proof 84–202), proof ~119 lines
- **Notes**: `set_option backward.isDefEq.respectTransparency false`, `set_option synthInstance.maxHeartbeats 800000`, `set_option maxHeartbeats 800000` (no justifying comment in the `set_option` line, but docstring explains the opaque instance issue). Proof >30 lines.

---

### `theorem moduleFinite_linfAt_gamma_pullback_x`
- **Type**: `(hq : 2 ≤ Fintype.card K) [Fact (Transcendental K ((1−π)*x)⁻¹)] → @Module.Finite (FractionRing K[X]) (LinfAt ((1−π)*x)) ...`
- **What**: K(E) is module-finite over FractionRing K[X] in the LinfAt framing — the last HYPS hypothesis for `Sinf.ofIntegralClosure`.
- **How**: Builds the finrank > 0 via `Conditional.finrank_adjoin_eq_finrank_LinfAt` + `l6_B3_tower` (giving 2·γ.degree > 0 since `isogOneSub_negFrobenius_finiteDimensional` implies degree > 0 via `Module.finrank_pos`), then concludes `Module.finite_of_finrank_pos`.
- **Hypotheses**: `2 ≤ #K`; `Fact (Transcendental K ((1−π)*x)⁻¹)` must be in scope.
- **Uses from project**: `l6_B3_tower`, `Conditional.finrank_adjoin_eq_finrank_LinfAt`, `isogOneSub_negFrobenius_finiteDimensional`
- **Used by**: `l6_computationA`, `isogOneSub_negFrobenius_pointCount_le_degree`, `Sinf_finrank_witness_via_B3_tower`
- **Visibility**: public
- **Lines**: 210–242, proof ~32 lines
- **Notes**: Proof >30 lines. Relies on `@Module.Free.of_divisionRing` to get the free module needed for `Module.finrank_pos`.

---

### `theorem projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness`
- **Type**: `(hq : ...) (h_two_torsion_witness : ...) (P : ProjectiveSmoothPoint) → (projectiveDivisorOf ((1−π)*x)) P = -2`
- **What**: The projective divisor of (1−π)*x takes value −2 at every projective smooth point, given a 2-torsion witness for the affine 2-torsion case.
- **How**: Three-way `rcases P`: infinity case uses `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`; affine non-2-tor uses `lemma3_pole_at_T_unconditional`; affine 2-tor uses the provided `h_two_torsion_witness`.
- **Hypotheses**: `2 ≤ #K`; 2-torsion witness for affine 2-tor points.
- **Uses from project**: `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`, `Conditional.lemma3_pole_at_T_unconditional`
- **Used by**: `l6_pole_orders_of_two_torsion_witness`
- **Visibility**: public
- **Lines**: 252–268, proof ~16 lines

---

### `theorem l6_pole_orders_of_two_torsion_witness`
- **Type**: `(hq : ...) (h_two_torsion_witness : ...) → ∀ P ∈ support, (D P).toNat = 0 ∧ (−D P).toNat = 2`
- **What**: Witness-parametric version: every point in the pole-divisor support of (1−π)*x has zero-part 0 and pole-part 2.
- **How**: Applies `projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness` and uses `rfl` after rewriting.
- **Hypotheses**: Same as above with 2-torsion witness.
- **Uses from project**: `projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness`
- **Used by**: `l6_pole_orders`
- **Visibility**: public
- **Lines**: 276–291, proof ~6 lines

---

### `theorem l6_pole_orders`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∀ P ∈ support, (D P).toNat = 0 ∧ (−D P).toNat = 2`
- **What**: GAP-L6 Lemma-5 witness (a): uniform pole orders at every support point; discharges the 2-torsion case via the shipped `lemma3_pole_at_T_at_2tor`.
- **How**: Applies `l6_pole_orders_of_two_torsion_witness` with the concrete 2-tor witness `lemma3_pole_at_T_at_2tor`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `l6_pole_orders_of_two_torsion_witness`, `lemma3_pole_at_T_at_2tor`
- **Used by**: `l6_lemma5`
- **Visibility**: public
- **Lines**: 306–315, proof ~4 lines (term-mode)

---

### `theorem l6_support_card`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (support of projectiveDivisorOf ((1−π)*x)).card = pointCount W.toAffine`
- **What**: GAP-L6 Lemma-5 witness (b): the pole-divisor support has exactly #E(Fq) elements.
- **How**: Applies `Conditional.l6_support_card_of_two_torsion_witness` with `lemma3_pole_at_T_at_2tor`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `Conditional.l6_support_card_of_two_torsion_witness`, `lemma3_pole_at_T_at_2tor`
- **Used by**: `l6_lemma5`
- **Visibility**: public
- **Lines**: 322–328, proof ~3 lines (term-mode)

---

### `theorem l6_lemma5`
- **Type**: `(hq : 2 ≤ Fintype.card K) → support.sum (fun P => (−D P).toNat) = 2 * pointCount W.toAffine`
- **What**: GAP-L6 sub-leaf Lemma 5: the pole-divisor sum equals 2·#E(Fq).
- **How**: One-line application of `Conditional.lemma5_of_pole_orders_and_support_card` using `l6_pole_orders` and `l6_support_card`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `Conditional.lemma5_of_pole_orders_and_support_card`, `l6_pole_orders`, `l6_support_card`
- **Used by**: `l6_computationA`
- **Visibility**: public
- **Lines**: 332–339, proof ~4 lines (term-mode)

---

### `theorem l6_computationA`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ComputationA_bridge_pullback_x_gen W hq`
- **What**: V.1.3 ComputationA bridge: [K(E):K((1−π)*x)] = degreePoleDivisor. Reduces `finrank K(E) over K⟮γ*x⟯ = Σ e·f` to 2·pointCount via Lemma 5.
- **How**: Assembles `Sinf.ofIntegralClosure` data (using `fact_transcendental_gamma_pullback_x_inv`, `moduleFinite_linfAt_gamma_pullback_x`, `K_E_separable_over_LinfAt_gamma_pullback_x_gen`), then applies `finrank_gamma_pullback_x_eq_weightedPoleDegree` and `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount` with three inline witnesses: `bridge_Bii_mem_primesOverFinset_v2` (surjectivity of kernel-to-prime map), `bridge_Biii_ord_eq_neg_two_v2` (each kernel prime contributes ord = −2), `bridge_Biv_inertia_eq_one_v2` (inertiaDeg = 1), and `Sinf_kernelToPrime_v2_injective` (injectivity). Closes with `l6_lemma5`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `moduleFinite_linfAt_gamma_pullback_x`, `Conditional.fact_transcendental_gamma_pullback_x_inv`, `Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen`, `Conditional.finrank_adjoin_eq_finrank_LinfAt`, `Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree`, `Conditional.weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount`, `bridge_Bi_kernelToPrime_v2`, `bridge_Bii_mem_primesOverFinset_v2`, `bridge_Biii_ord_eq_neg_two_v2`, `bridge_Biv_inertia_eq_one_v2`, `Sinf_kernelToPrime_v2_injective`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `l6_lemma5`
- **Used by**: unused in file (final output)
- **Visibility**: public
- **Lines**: 347–412, proof ~65 lines
- **Notes**: Proof >30 lines.

---

### `theorem isogOneSub_negFrobenius_pointCount_le_degree`
- **Type**: `(hq : 2 ≤ Fintype.card K) → pointCount W.toAffine ≤ (isogOneSub_negFrobenius W hq).degree`
- **What**: Easy half of V.1.3: #E(Fq) ≤ deg(1−π) via monotonicity of the Σ ef sum over the kernel-prime image. Axiom-clean.
- **How**: Builds `Sinf` data; computes TOTAL sum = 2·deg via `finrank_gamma_pullback_x_eq_weightedPoleDegree` + `finrank_adjoin_eq_finrank_LinfAt` + `l6_B3_tower`; computes IMAGE sum = 2·pointCount using `bridge_Biii/Biv` (each kernel prime contributes ef = 2) and `kernel_eq_top_of_hom_eq_id_sub_frobenius`; concludes by `Finset.sum_le_sum_of_subset_of_nonneg` (monotonicity) and `omega`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `l6_B3_tower`, `moduleFinite_linfAt_gamma_pullback_x`, `Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree`, `Conditional.finrank_adjoin_eq_finrank_LinfAt`, `bridge_Bi_kernelToPrime_v2`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `bridge_Biii_ord_eq_neg_two_v2`, `bridge_Biv_inertia_eq_one_v2`, `Sinf_kernelToPrime_v2_injective`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`
- **Used by**: `isogOneSub_negFrobenius_card_kernel_le_sepDegree`
- **Visibility**: public
- **Lines**: 447–523, proof ~76 lines
- **Notes**: Proof >30 lines. The "easy monotonicity" direction of V.1.3, axiom-clean.

---

### `theorem isogOneSub_negFrobenius_sepDegree_eq_card_emb`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (1−π).sepDegree = Nat.card (K(E) →ₐ[K(E)] AlgClosure K(E))`
- **What**: Explicit embedding form: sepDegree of 1−π equals the number of γ*K(E)-algebra embeddings — definitional unfold of `Isogeny.sepDegree_eq_card_emb`.
- **How**: One-line application of `Isogeny.sepDegree_eq_card_emb`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `Isogeny.sepDegree_eq_card_emb`, `isogOneSub_negFrobenius`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 663–668, proof ~1 line

---

### `theorem isogOneSub_negFrobenius_card_kernel_le_sepDegree`
- **Type**: `(hq : 2 ≤ Fintype.card K) → Nat.card (1−π).kernel ≤ (1−π).sepDegree`
- **What**: EASY half of the embedding↔kernel count: #ker ≤ #Emb = sepDegree, axiom-clean.
- **How**: Uses `kernel_eq_top_of_hom_eq_id_sub_frobenius` to get #ker = pointCount, `isSeparable_iff_sepDegree_eq_degree` to get sepDegree = deg, then applies `isogOneSub_negFrobenius_pointCount_le_degree`.
- **Hypotheses**: `2 ≤ #K`; `Fact p.Prime` for char p.
- **Uses from project**: `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `Isogeny.isSeparable_iff_sepDegree_eq_degree`, `isogOneSub_negFrobenius_finiteDimensional`, `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_pointCount_le_degree`
- **Used by**: `isogOneSub_negFrobenius_sepDegree_eq_card_kernel`
- **Visibility**: public
- **Lines**: 681–700, proof ~20 lines

---

### `noncomputable def isogOneSub_negFrobenius_embToPointOmega`
- **Type**: `(hq : 2 ≤ Fintype.card K) (σ : K(E) →ₐ[K] Ω) → ((W_KE W).map σ).toAffine.Point`
- **What**: For each K-algebra embedding σ, the Ω-point of E with coordinates (σ x_gen, σ y_gen) — the forward map of the embeddings↔points classification dictionary.
- **How**: `Affine.Point.map σ.toRingHom σ.toRingHom.injective (genericPoint W)`.
- **Hypotheses**: `2 ≤ #K`; σ a K-algebra embedding.
- **Uses from project**: `genericPoint`
- **Used by**: (docstring brick; simp lemma `isogOneSub_negFrobenius_embToPointOmega_eq` follows immediately)
- **Visibility**: public
- **Lines**: 714–717, def body ~1 line

---

### `theorem isogOneSub_negFrobenius_embToPointOmega_eq`
- **Type**: `@[simp]` — `isogOneSub_negFrobenius_embToPointOmega W hq σ = Affine.Point.some (σ x_gen) (σ y_gen) ...`
- **What**: Computes the embedding-to-point map explicitly as `some (σ x_gen) (σ y_gen)`.
- **How**: `rfl`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `isogOneSub_negFrobenius_embToPointOmega`, `generic_nonsingular`
- **Used by**: unused in file (simp lemma for external use)
- **Visibility**: public
- **Lines**: 719–725, proof 1 line (`rfl`)

---

### `theorem frobenius_fixedPoint_iff_mem_baseField_gen`
- **Type**: `{L : Type*} [Field L] [Algebra K L] (a : L) → a^q = a ↔ a ∈ Set.range (algebraMap K L)`
- **What**: Brick (E): over any field extension L/K of finite K, a^q = a iff a is in the image of K. Generalises the AlgClosed version to arbitrary extensions.
- **How**: Polynomial count argument: the roots of X^q − X form a finset of size q; the image of K is also a finset of size q; the image lies inside the roots; by equal cardinality they are equal. Uses `FiniteField.X_pow_card_sub_X_ne_zero`, `FiniteField.pow_card`, `Polynomial.card_roots'`, `Finset.eq_of_subset_of_card_le`.
- **Hypotheses**: `K` finite field; `[Algebra K L]` field L.
- **Uses from project**: (none from project — pure mathlib)
- **Used by**: `geomFrobOmega_fixed_iff_mem_range`
- **Visibility**: public
- **Lines**: 751–780, proof ~30 lines
- **Notes**: Proof ~30 lines; uses classical decidability.

---

### `theorem algHom_ext_x_y_gen_omega`
- **Type**: `{Ω : Type*} [Field Ω] [Algebra K Ω] {ψ₁ ψ₂ : K(E) →ₐ[K] Ω} → ψ₁ x_gen = ψ₂ x_gen → ψ₁ y_gen = ψ₂ y_gen → ψ₁ = ψ₂`
- **What**: Brick (A): two K-algebra embeddings into an arbitrary Ω field agreeing on x_gen and y_gen are equal. Injectivity of the classification forward map.
- **How**: `IsLocalization.algHom_ext` → `AdjoinRoot.algHom_ext'` → `Polynomial.algHom_ext`.
- **Hypotheses**: `K` finite; field Ω with `Algebra K Ω`.
- **Uses from project**: `x_gen`, `y_gen`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 788–800, proof ~13 lines

---

### `theorem embCurveBaseChange`
- **Type**: `{Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω] (σ : K(E) →ₐ[K] Ω) → (W_KE W).map σ.toRingHom = W.baseChange Ω`
- **What**: Brick (B-base): mapping W_KE along σ returns W.baseChange Ω — all Q_σ land in the common group E(Ω).
- **How**: `WeierstrassCurve.map_map` + `σ.commutes` (showing the algebra maps compose).
- **Hypotheses**: K finite; field Ω with `Algebra K Ω`.
- **Uses from project**: `W_KE`
- **Used by**: (brick for external use; not called within file)
- **Visibility**: public
- **Lines**: 809–819, proof ~11 lines

---

### `theorem embFixesPullbackRange`
- **Type**: `(hq : 2 ≤ Fintype.card K) (σ : M-algebra embedding) (z : K(E)) → σ (γ.pullback z) = algebraMap z`
- **What**: Brick (C): every M-embedding fixes the pullback range — the fibre precondition of the classification. Free from commutative diagram reasoning, just `σ.commutes`.
- **How**: `exact σ.commutes z`.
- **Hypotheses**: `2 ≤ #K`; M-algebra embedding σ.
- **Uses from project**: `isogOneSub_negFrobenius`
- **Used by**: `embAgreeOnPullbackRange`
- **Visibility**: public
- **Lines**: 828–837, proof ~2 lines

---

### `theorem embAgreeOnPullbackRange`
- **Type**: `(hq : 2 ≤ Fintype.card K) (σ₁ σ₂ : M-embeddings) (z : K(E)) → σ₁ (γ.pullback z) = σ₂ (γ.pullback z)`
- **What**: Brick (C, agreement form): all M-embeddings agree on M = γ*K(E).
- **How**: `(σ₁.commutes z).trans (σ₂.commutes z).symm`.
- **Hypotheses**: Same as above.
- **Uses from project**: `isogOneSub_negFrobenius`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 843–851, proof ~3 lines

---

### `noncomputable def embRestrictScalarsK`
- **Type**: `(hq : 2 ≤ Fintype.card K) (σ : M-embedding) → K(E) →ₐ[K] Ω`
- **What**: Brick (A→K view): restricts an M-algebra embedding to a K-algebra hom, using the scalar tower K → M → Ω.
- **How**: Builds explicitly using `σ.toRingHom` with `commutes'` verified by computing `σ (algebraMap K K(E) c)` via `AlgHom.commutes` and `σ.commutes`.
- **Hypotheses**: `2 ≤ #K`; M-embedding σ.
- **Uses from project**: `isogOneSub_negFrobenius`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 859–875, body ~17 lines

---

### `def isogOneSub_negFrobenius_emb_le_card_kernel_gap`
- **Type**: `(hq : 2 ≤ Fintype.card K) → Prop` (= `(1−π).sepDegree ≤ Nat.card (1−π).kernel`)
- **What**: Records the HARD half gap (`#Emb ≤ #ker`, surjectivity of the classification) as an explicit hypothesis-free `Prop` to make the residual's content explicit and unfabricated.
- **How**: Definitional.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `isogOneSub_negFrobenius`
- **Used by**: (documentation/gap marker; not called in file)
- **Visibility**: public
- **Lines**: 912–914, def body ~2 lines

---

### `noncomputable def includePtOmega`
- **Type**: `[DecidableEq Ω] → W.toAffine.Point → (W.baseChange Ω).toAffine.Point`
- **What**: Includes K-rational points into E(Ω) via `Affine.Point.map (algebraMap K Ω)`.
- **How**: Definitional application of `HasseWeil.Affine.Point.map`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `Affine.Point.map`
- **Used by**: `includePtOmega_injective`, `includePtOmega_some`, `geomFrobOmega_fixed_iff_mem_range`, `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 931–933, def body ~2 lines

---

### `theorem includePtOmega_injective`
- **Type**: `[DecidableEq Ω] → Function.Injective (includePtOmega W)`
- **What**: The inclusion of K-points into E(Ω) is injective.
- **How**: Case analysis on both arguments (zero/some); uses `FaithfulSMul.algebraMap_injective` and `Affine.Point.map_some` to read off injectivity from coordinates.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `includePtOmega`, `HasseWeil.Affine.Point.map_some`
- **Used by**: (unused in file — building block)
- **Visibility**: public
- **Lines**: 936–951, proof ~15 lines

---

### `theorem includePtOmega_some`
- **Type**: `@[simp]` — `includePtOmega W (.some x y h) = .some (algebraMap K Ω x) (algebraMap K Ω y) ...`
- **What**: Simp lemma: includePtOmega at an affine point acts coordinate-wise.
- **How**: `rfl`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `includePtOmega`
- **Used by**: `geomFrobOmega_fixed_iff_mem_range`
- **Visibility**: public
- **Lines**: 953–957, proof 1 line

---

### `noncomputable def geomFrobOmega`
- **Type**: `[DecidableEq Ω] → (W.baseChange Ω).toAffine.Point →+ (W.baseChange Ω).toAffine.Point`
- **What**: Geometric Frobenius on E(Ω): the q-power Frobenius algebra hom `frobeniusAlgHom K Ω` applied pointwise as an AddMonoidHom.
- **How**: `WeierstrassCurve.Affine.Point.map (FiniteField.frobeniusAlgHom K Ω)`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: (none from project; uses mathlib `frobeniusAlgHom`)
- **Used by**: `geomFrobOmega_some`, `geomFrobOmega_fixed_iff_mem_range`, `map_sigma_frob_comm`, `Qσ_sub_frob_eq_map`, `map_emb_generic_sub_frob_eq_of_agree`, `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 959–961, def body ~2 lines

---

### `theorem geomFrobOmega_some`
- **Type**: `[DecidableEq Ω] {x y : Ω} (h : Nonsingular) → geomFrobOmega W (.some x y h) = .some (frob x) (frob y) ...`
- **What**: Computes geomFrobOmega at an affine point.
- **How**: Unfolds `geomFrobOmega` and applies `WeierstrassCurve.Affine.Point.map_some`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `geomFrobOmega`
- **Used by**: `geomFrobOmega_fixed_iff_mem_range`
- **Visibility**: public
- **Lines**: 963–972, proof ~9 lines

---

### `theorem geomFrobOmega_fixed_iff_mem_range`
- **Type**: `[DecidableEq Ω] (P : E(Ω)) → geomFrobOmega W P = P ↔ P ∈ Set.range (includePtOmega W)`
- **What**: A point of E(Ω) is fixed by the geometric Frobenius iff it lies in the image of K-points — the key descent criterion.
- **How**: Case analysis on P; affine case splits into x and y coordinates, applies `frobenius_fixedPoint_iff_mem_baseField_gen` twice, then combines with `includePtOmega_some` and `WeierstrassCurve.Affine.map_nonsingular`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `geomFrobOmega`, `geomFrobOmega_some`, `includePtOmega`, `includePtOmega_some`, `frobenius_fixedPoint_iff_mem_baseField_gen`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 974–996, proof ~22 lines

---

### `theorem map_sigma_frob_comm`
- **Type**: `[DecidableEq Ω] (σ : K(E) →ₐ[K] Ω) (P : W_KE.Point) → Affine.Point.map σ (frobeniusW_KE P) = geomFrobOmega W (Affine.Point.map σ P)`
- **What**: The K-algebra embedding σ commutes with Frobenius (σ ∘ frob_KE = geomFrob_Ω ∘ σ) at the point level.
- **How**: Shows the ring hom composition `σ ∘ frobeniusAlgHom K K(E) = frobeniusAlgHom K Ω ∘ σ` via `map_pow`; then uses `WeierstrassCurve.Affine.Point.map_map` twice.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `geomFrobOmega`, `frobeniusW_KE`
- **Used by**: `Qσ_sub_frob_eq_map`
- **Visibility**: public
- **Lines**: 998–1020, proof ~22 lines

---

### `theorem Qσ_sub_frob_eq_map`
- **Type**: `[DecidableEq Ω] (σ : K(E) →ₐ[K] Ω) → σ(P_gen) − geomFrob(σ(P_gen)) = σ(P_gen − frob(P_gen))`
- **What**: The difference Q_σ − Frob(Q_σ) equals σ applied to the σ-independent constant genericPoint − frob(genericPoint).
- **How**: `map_sigma_frob_comm` + `map_sub`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `map_sigma_frob_comm`, `genericPoint`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 1022–1029, proof ~7 lines

---

### `theorem map_emb_generic_sub_frob_eq_of_agree`
- **Type**: `(hq : 2 ≤ Fintype.card K) [DecidableEq Ω] (σ τ : K(E) →ₐ[K] Ω) (hx : σ(γ*x) = τ(γ*x)) (hy : σ(γ*y) = τ(γ*y)) → σ(P_gen − frob P_gen) = τ(P_gen − frob P_gen)`
- **What**: If σ and τ agree on (1−π)*x_gen and (1−π)*y_gen, their images of (genericPoint − frobeniusW_KE genericPoint) coincide.
- **How**: Rewrites via `genericPoint_sub_frobeniusW_KE_apply` to get explicit affine coordinates; matches them using `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x/y_gen_eq`.
- **Hypotheses**: `2 ≤ #K`; `DecidableEq Ω`; σ,τ K-algebra embeddings.
- **Uses from project**: `genericPoint_sub_frobeniusW_KE_apply`, `isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`, `addPullbackAlgHom_negFrobenius_y_gen_eq`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 1031–1053, proof ~22 lines

---

### `theorem map_genericPoint_eq_some`
- **Type**: `[DecidableEq Ω] (σ : K(E) →ₐ[K] Ω) → Affine.Point.map σ (genericPoint W) = .some (σ x_gen) (σ y_gen) ...`
- **What**: Computing Affine.Point.map σ at the generic point gives the affine point with coordinates (σ x_gen, σ y_gen).
- **How**: Rewrites via `genericPoint_xOf_some` and `WeierstrassCurve.Affine.Point.map_some`.
- **Hypotheses**: `DecidableEq Ω`.
- **Uses from project**: `genericPoint`, `genericPoint_xOf_some`, `generic_nonsingular`
- **Used by**: `emb_le_card_kernel`
- **Visibility**: public
- **Lines**: 1056–1063, proof ~7 lines

---

### `theorem emb_le_card_kernel`
- **Type**: `(hq : 2 ≤ Fintype.card K) [DecidableEq Ω] → (1−π).sepDegree ≤ Nat.card (1−π).kernel`
- **What**: HARD half `#Emb ≤ #ker γ` — the classification's surjectivity (Silverman III.4.10c), proved by the point-level torsor assembly. Every M-embedding σ gives Q_σ ∈ E(Ω); differences Q_σ − Q_{σ₀} are geometric-Frobenius-fixed (brick C), descend to K-points (brick E), and σ ↦ Q_σ − Q_{σ₀} is injective (brick A); kernel = ⊤ lands descended points in ker γ.
- **How**: Rewrites via `isogOneSub_negFrobenius_sepDegree_eq_card_emb`; constructs injection `Φ : Emb → ker γ` using `embRestrictScalarsK`, `embAgreeOnPullbackRange`, `Qσ_sub_frob_eq_map`, `map_emb_generic_sub_frob_eq_of_agree`, `geomFrobOmega_fixed_iff_mem_range` (Frob-fixed ↔ K-rational), `algHom_ext_x_y_gen_omega`; concludes by `Nat.card_le_card_of_injective`.
- **Hypotheses**: `2 ≤ #K`; `DecidableEq Ω`; `Fact p.Prime` internally for char.
- **Uses from project**: `isogOneSub_negFrobenius_sepDegree_eq_card_emb`, `embRestrictScalarsK`, `embAgreeOnPullbackRange`, `Qσ_sub_frob_eq_map`, `map_emb_generic_sub_frob_eq_of_agree`, `geomFrobOmega_fixed_iff_mem_range`, `algHom_ext_x_y_gen_omega`, `map_genericPoint_eq_some`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `isogOneSub_negFrobenius_toAddMonoidHom`
- **Used by**: `isogOneSub_negFrobenius_sepDegree_eq_card_kernel`
- **Visibility**: public
- **Lines**: 1068–1134 (with `set_option maxHeartbeats 1600000 in` at 1068), proof ~66 lines
- **Notes**: `set_option maxHeartbeats 1600000` (comment at 1065–1067 explains: "threads several Affine.Point / γ.toAlgebra / Ore-localization instance layers"). Proof >30 lines.

---

### `theorem isogOneSub_negFrobenius_sepDegree_eq_card_kernel`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (1−π).sepDegree = Nat.card (1−π).kernel`
- **What**: The sepDegree of 1−π equals the kernel size — the embedding↔kernel count identity that gates V.1.3.
- **How**: Combines easy half `isogOneSub_negFrobenius_card_kernel_le_sepDegree` and hard half `emb_le_card_kernel` (called with `classical` for `DecidableEq`), concludes by `le_antisymm`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `isogOneSub_negFrobenius_card_kernel_le_sepDegree`, `emb_le_card_kernel`
- **Used by**: `isogOneSub_negFrobenius_degree_eq_pointCount`
- **Visibility**: public
- **Lines**: 1136–1150, proof ~15 lines

---

### `theorem isogOneSub_negFrobenius_degree_eq_pointCount`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (1−π).degree = pointCount W.toAffine`
- **What**: V.1.3 sharp residual (Silverman III.4.10c): deg(1−π) = #E(Fq). The key theorem gates all of V.1.3. Axiom-clean.
- **How**: From `isogOneSub_negFrobenius_sepDegree_eq_card_kernel` + separability (`isSeparable_iff_sepDegree_eq_degree`) + `Isogeny.card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, yields #ker = deg; combines with `degree_eq_pointCount_of_card_kernel_eq_degree` (ker = ⊤).
- **Hypotheses**: `2 ≤ #K`; `Fact p.Prime`.
- **Uses from project**: `isogOneSub_negFrobenius_sepDegree_eq_card_kernel`, `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_finiteDimensional`, `Isogeny.card_kernel_eq_degree_of_sepDegree_eq_card_kernel`, `isogOneSub_negFrobenius_toAddMonoidHom`, `degree_eq_pointCount_of_card_kernel_eq_degree`
- **Used by**: `sepDegree_oneSub_eq_pointCount`, `ker_deg_skeleton`, `Sinf_finrank_witness_via_B3_tower`
- **Visibility**: public
- **Lines**: 1183–1201, proof ~18 lines

---

### `theorem sepDegree_oneSub_eq_pointCount`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (1−π).sepDegree = pointCount W.toAffine`
- **What**: GAP-L6 keystone (Silverman V.1.1): sepDeg(1−π) = #E(Fq). Axiom-clean.
- **How**: `isSeparable_iff_sepDegree_eq_degree` + `isogOneSub_negFrobenius_degree_eq_pointCount`.
- **Hypotheses**: `2 ≤ #K`; `Fact p.Prime`.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_finiteDimensional`, `isogOneSub_negFrobenius_degree_eq_pointCount`
- **Used by**: unused in file (top-level output)
- **Visibility**: public
- **Lines**: 1211–1220, proof ~9 lines

---

### `theorem ker_deg_skeleton`
- **Type**: `(hq : 2 ≤ Fintype.card K) → Nat.card (1−π).kernel = (1−π).degree`
- **What**: GAP-L6 top leaf: #ker(1−π) = deg(1−π). Axiom-clean.
- **How**: `kernel_eq_top_of_hom_eq_id_sub_frobenius` + `AddSubgroup.card_top` + `isogOneSub_negFrobenius_degree_eq_pointCount`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `isogOneSub_negFrobenius_degree_eq_pointCount`
- **Used by**: unused in file (top-level output)
- **Visibility**: public
- **Lines**: 1231–1242, proof ~12 lines

---

### `theorem Sinf_finrank_witness_via_B3_tower`
- **Type**: `(hq : ...) (data : Sinf ...) → Σ e_P · f_P = 2 * pointCount W.toAffine`
- **What**: Phase B V.1.3 LHS finrank witness: combining l6_B3_tower with the sharp residual to give `Σ e·f = 2·pointCount`.
- **How**: Rewrites via `finrank_gamma_pullback_x_eq_weightedPoleDegree` + `finrank_adjoin_eq_finrank_LinfAt` + `l6_B3_tower` + `isogOneSub_negFrobenius_degree_eq_pointCount`.
- **Hypotheses**: `2 ≤ #K`; `Sinf data` in scope.
- **Uses from project**: `l6_B3_tower`, `moduleFinite_linfAt_gamma_pullback_x`, `Conditional.finrank_gamma_pullback_x_eq_weightedPoleDegree`, `Conditional.finrank_adjoin_eq_finrank_LinfAt`, `isogOneSub_negFrobenius_degree_eq_pointCount`
- **Used by**: `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower`
- **Visibility**: public
- **Lines**: 1251–1273, proof ~23 lines

---

### `theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower`
- **Type**: `(hq : ...) (data : Sinf ...) → Σ (inertiaDeg P) = pointCount W.toAffine`
- **What**: Axiom-clean closure of the L6Witnesses sorry `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount` via the squeeze composer.
- **How**: One-line application of `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness` with `Sinf_finrank_witness_via_B3_tower`.
- **Hypotheses**: `2 ≤ #K`; `Sinf data`.
- **Uses from project**: `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness`, `Sinf_finrank_witness_via_B3_tower`
- **Used by**: unused in file (top-level output)
- **Visibility**: public
- **Lines**: 1286–1297, proof ~2 lines

---

### `theorem genuine_dual_comp_toAddMonoidHom_eq_mulByInt`
- **Type**: `(hq : ...) (r s : ℤ) (hr hs hrK hsK) (V β_dual : Isogeny) (h_isDual h_sum_trace h_beta_dual_hom) → (β_dual.comp (genuineIsogSmulSub W r s ...)).toAddMonoidHom = (mulByInt N).toAddMonoidHom`
  where N = q·r² − t·r·s + s²
- **What**: AddMonoidHom-level Cayley–Hamilton: the dual composition at the AddMonoidHom level equals [N]. SUB-PIV-C2 piece.
- **How**: Extracts the dual composition property from `h_isDual` and sum trace; uses `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` + `genuineIsogSmulSub_toAddMonoidHom` + `frobeniusIsog_degree`.
- **Hypotheses**: All standard genuineness witnesses.
- **Uses from project**: `genuineIsogSmulSub`, `genuineIsogSmulSub_toAddMonoidHom`, `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`, `frobeniusIsog_degree`
- **Used by**: `genuine_dual_comp_eq_mulByInt_of_components`, `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`, `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1309–1348, proof ~39 lines
- **Notes**: Proof >30 lines.

---

### `def IsGenuineWith`
- **Type**: `(φ : Isogeny) (g : E(K(E)) →+ E(K(E))) → Prop`
- **What**: An isogeny φ is "genuine with geometric action g" if g carries the generic point to an affine point whose coordinates are exactly (φ.pullback x_gen, φ.pullback y_gen). Non-vacuous definition enforcing pullback↔geometric-action coherence.
- **How**: Definitional.
- **Hypotheses**: (definition — no proof obligations)
- **Uses from project**: `W_KE`, `genericPoint`, `x_gen`, `y_gen`
- **Used by**: `IsGenuine`, `genuine_isogeny_ext_pullback`, `genuine_isogeny_ext`, `mulByInt_isGenuineWith`, `frobeniusIsog_isGenuineWith`, `zsmul_frobeniusIsog_isGenuineWith`, `addIsog_isGenuineWith`, `genuineIsogSmulSub_isGenuineWith`, `FunctorialAtImage`, `genuine_comp_isGenuineWith_of_functorial`, `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`, `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`
- **Visibility**: public
- **Lines**: 1388–1392, def body ~4 lines
- **Notes**: Key API — used by 10+ declarations.

---

### `def IsGenuine`
- **Type**: `(φ : Isogeny) → Prop`
- **What**: An isogeny is "genuine" if there exists some geometric action g making it genuine in the sense of `IsGenuineWith`.
- **How**: Existential over g.
- **Hypotheses**: (definition)
- **Uses from project**: `IsGenuineWith`, `W_KE`
- **Used by**: `mulByInt_isGenuine`, `genuineIsogSmulSub_isGenuine`
- **Visibility**: public
- **Lines**: 1396–1397, def body ~2 lines

---

### `theorem genuine_isogeny_ext_pullback`
- **Type**: `{φ ψ : Isogeny} {g : E(K(E)) →+ E(K(E))} → IsGenuineWith W φ g → IsGenuineWith W ψ g → φ.pullback = ψ.pullback`
- **What**: Wall-B killer (pullback form): two isogenies genuine with the same geometric action have equal pullbacks.
- **How**: Both pullbacks agree on x_gen and y_gen by the genuineness equalities; `algHom_ext_x_y_gen` upgrades to full pullback equality.
- **Hypotheses**: Both isogenies genuine with same g.
- **Uses from project**: `algHom_ext_x_y_gen`, `IsGenuineWith`
- **Used by**: `genuine_isogeny_ext`, `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`
- **Visibility**: public
- **Lines**: 1405–1419, proof ~14 lines

---

### `theorem genuine_isogeny_ext`
- **Type**: `{φ ψ : Isogeny} {g} → IsGenuineWith W φ g → IsGenuineWith W ψ g → φ.toAddMonoidHom = ψ.toAddMonoidHom → φ = ψ`
- **What**: Wall-B killer (full isogeny form): genuine isogenies with same geometric action and same point map are equal.
- **How**: `Isogeny.eq_of_components` + `genuine_isogeny_ext_pullback`.
- **Hypotheses**: Both genuine with same g; same AddMonoidHom.
- **Uses from project**: `genuine_isogeny_ext_pullback`, `IsGenuineWith`
- **Used by**: (unused in file — building block for Wall-B killing)
- **Visibility**: public
- **Lines**: 1425–1431, proof ~4 lines

---

### `noncomputable abbrev zsmulPointHom`
- **Type**: `(N : ℤ) → (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point`
- **What**: The geometric action of [N]: the zsmul-by-N group homomorphism on E(K(E)).
- **How**: `zsmulAddGroupHom N`.
- **Hypotheses**: (none beyond ambient variables)
- **Uses from project**: `W_KE`
- **Used by**: `zsmulPointHom_apply`, `mulByInt_isGenuineWith`, `mulByInt_isGenuine`, `zsmul_frobeniusIsog_isGenuineWith`, `genuineIsogSmulSub_isGenuineWith`, `genuine_comp_isGenuineWith_of_functorial`, `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`, `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1438–1440, abbrev body ~1 line
- **Notes**: Key API — used by 10+ declarations.

---

### `theorem zsmulPointHom_apply`
- **Type**: `(N : ℤ) (P : W_KE.Point) → zsmulPointHom W N P = N • P`
- **What**: Definitional unfolding of `zsmulPointHom`.
- **How**: `rfl`.
- **Hypotheses**: (none)
- **Uses from project**: `zsmulPointHom`
- **Used by**: (unused in file explicitly; conceptual)
- **Visibility**: public
- **Lines**: 1442–1443, proof `rfl`

---

### `theorem mulByInt_isGenuineWith`
- **Type**: `(N : ℤ) (hN : N ≠ 0) → IsGenuineWith W (mulByInt W.toAffine N) (zsmulPointHom W N)`
- **What**: [N] is genuine with the N·(−) action: the pullback of [N] on generators equals the coordinates of N·P_gen.
- **How**: `zsmul_genericPoint_eq W N hN` gives the geometric image; `mulByInt_pullback_x/y` gives the pullback values; a `DecidableEq` instance alignment is needed.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: `IsGenuineWith`, `zsmulPointHom`, `mulByInt_x`, `mulByInt_y`, `zsmul_genericPoint_eq`, `mulByInt_pullback_x`, `mulByInt_pullback_y`
- **Used by**: `mulByInt_isGenuine`, `genuineIsogSmulSub_isGenuineWith`, `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`
- **Visibility**: public
- **Lines**: 1445–1462 (`set_option maxHeartbeats 4000000 in` at 1445), proof ~18 lines
- **Notes**: `set_option maxHeartbeats 4000000` (comment: "basic non-vacuity check" — no specific justification for the large budget).

---

### `theorem mulByInt_isGenuine`
- **Type**: `(N : ℤ) (hN : N ≠ 0) → IsGenuine W (mulByInt W.toAffine N)`
- **What**: [N] is genuine (existential form).
- **How**: `⟨zsmulPointHom W N, mulByInt_isGenuineWith W N hN⟩`.
- **Hypotheses**: `N ≠ 0`.
- **Uses from project**: `IsGenuine`, `zsmulPointHom`, `mulByInt_isGenuineWith`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1465–1467, proof ~1 line

---

### `theorem frobeniusIsog_isGenuineWith`
- **Type**: `IsGenuineWith W (frobeniusIsog W) (frobeniusW_KE W)`
- **What**: The Frobenius isogeny is genuine with geometric action frobeniusW_KE.
- **How**: `frobeniusW_KE_some` + `frobeniusIsog_pullback_apply` + `FiniteField.coe_frobeniusAlgHom`.
- **Hypotheses**: Ambient variables.
- **Uses from project**: `IsGenuineWith`, `frobeniusW_KE`, `genericPoint`, `frobeniusW_KE_some`, `frobeniusIsog_pullback_apply`, `generic_nonsingular`
- **Used by**: `zsmul_frobeniusIsog_isGenuineWith` (indirectly)
- **Visibility**: public
- **Lines**: 1473–1488, proof ~16 lines

---

### `theorem zsmul_frobeniusIsog_isGenuineWith`
- **Type**: `(r : ℤ) (hr : r ≠ 0) → IsGenuineWith W ((frobeniusIsog W).zsmul r) ((zsmulPointHom W r).comp (frobeniusW_KE W))`
- **What**: r·π is genuine with geometric action r·frobeniusW_KE.
- **How**: `zsmul_genericPoint_eq` + `frobeniusW_KE_some` + `Isogeny.zsmul, Isogeny.comp_algebraMap_eq, frobeniusIsog_pullback_apply, mulByInt_pullback_x/y`.
- **Hypotheses**: `r ≠ 0`.
- **Uses from project**: `IsGenuineWith`, `zsmulPointHom`, `frobeniusW_KE`, `zsmul_genericPoint_eq`, `mulByInt_x`, `mulByInt_y`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `frobeniusIsog_pullback_apply`
- **Used by**: `genuineIsogSmulSub_isGenuineWith`
- **Visibility**: public
- **Lines**: 1490–1536 (`set_option maxHeartbeats 4000000 in` at 1490), proof ~46 lines
- **Notes**: `set_option maxHeartbeats 4000000` (no comment in set_option itself; docstring explains the multi-layer pullback computation). Proof >30 lines.

---

### `theorem addIsog_isGenuineWith`
- **Type**: `{α₁ α₂ : Isogeny} (hxy : AddNonInversePair α₁ α₂) (hinj : Injective ...) {g₁ g₂} (h₁ : IsGenuineWith W α₁ g₁) (h₂ : IsGenuineWith W α₂ g₂) → IsGenuineWith W (addIsog hxy hinj) (g₁ + g₂)`
- **What**: Genuineness is closed under addIsog (the genuine sum): addIsog of two genuine isogenies is genuine with the sum action.
- **How**: Computes the sum of geometric images via `WeierstrassCurve.Affine.Point.add_some`; matches pullback via `addIsog_pullback` + `addPullbackAlgHomPair_x/y_gen_eq`; unfolds `addPullback_x/y_pair` and `addSlopePair`.
- **Hypotheses**: Both components genuine; non-inverse hypothesis; injectivity of addCoord map.
- **Uses from project**: `IsGenuineWith`, `addIsog`, `addIsog_pullback`, `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq`, `OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq`, `addPullback_x_pair`, `addPullback_y_pair`, `addSlopePair`
- **Used by**: `genuineIsogSmulSub_isGenuineWith`
- **Visibility**: public
- **Lines**: 1546–1572, proof ~26 lines

---

### `theorem genuineIsogSmulSub_isGenuineWith`
- **Type**: `(r s : ℤ) (hr hs hrK hsK) → IsGenuineWith W (genuineIsogSmulSub W r s ...) (((zsmulPointHom W r).comp (frobeniusW_KE W)) + zsmulPointHom W (-s))`
- **What**: The genuine r·π − s isogeny is genuine (with explicit action). Non-vacuity confirmation.
- **How**: Unfolds `genuineIsogSmulSub`; applies `addIsog_isGenuineWith` with `zsmul_frobeniusIsog_isGenuineWith` and `mulByInt_isGenuineWith`.
- **Hypotheses**: All four nonvanishing conditions.
- **Uses from project**: `IsGenuineWith`, `genuineIsogSmulSub`, `addIsog_isGenuineWith`, `zsmul_frobeniusIsog_isGenuineWith`, `mulByInt_isGenuineWith`, `zsmulPointHom`
- **Used by**: `genuineIsogSmulSub_isGenuine`, `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`, `genuine_dual_comp_eq_mulByInt_of_V_functorial`, `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1582–1592, proof ~10 lines

---

### `theorem genuineIsogSmulSub_isGenuine`
- **Type**: `(r s : ℤ) (hr hs hrK hsK) → IsGenuine W (genuineIsogSmulSub W r s ...)`
- **What**: The genuine r·π − s isogeny is genuine (existential form).
- **How**: `⟨_, genuineIsogSmulSub_isGenuineWith ...⟩`.
- **Hypotheses**: All four nonvanishing conditions.
- **Uses from project**: `IsGenuine`, `genuineIsogSmulSub_isGenuineWith`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1595–1598, proof ~2 lines

---

### `theorem genuineIsogSmulSub_omegaPullbackCoeff`
- **Type**: `(r s : ℤ) (hr hs hrK hsK) → omegaPullbackCoeff W (genuineIsogSmulSub W r s ...) = algebraMap K K(E) (-s)`
- **What**: The omega-pullback coefficient of r·π − s is (−s : K) — Silverman III.5.2/3/5.
- **How**: `omegaPullbackCoeff_addIsog_pair` for general-pair additivity; `omegaPullbackCoeff_comp_of_base` + `omegaPullbackCoeff_frobenius = 0` gives a_{r·π} = 0; `omegaPullbackCoeff_mulByInt_routeB` gives a_{[−s]} = −s.
- **Hypotheses**: All four nonvanishing conditions.
- **Uses from project**: `genuineIsogSmulSub`, `omegaPullbackCoeff_addIsog_pair`, `omegaPullbackCoeff_comp_of_base`, `omegaPullbackCoeff_frobenius`, `omegaPullbackCoeff_mulByInt_routeB`, `zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x`
- **Used by**: `genuineIsogSmulSub_isSeparable`
- **Visibility**: public
- **Lines**: 1614–1633, proof ~20 lines

---

### `theorem genuineIsogSmulSub_isSeparable`
- **Type**: `(r s : ℤ) (hr hs hrK hsK) → (genuineIsogSmulSub W r s ...).IsSeparable`
- **What**: The genuine r·π − s isogeny is separable when p ∤ s (Silverman III.5.5).
- **How**: `isSeparable_iff_omegaPullbackCoeff_ne_zero` + `genuineIsogSmulSub_omegaPullbackCoeff` + `map_eq_zero` (`algebraMap` is injective) + `neg_ne_zero.mpr hsK`.
- **Hypotheses**: `(s : K) ≠ 0` (i.e. p ∤ s).
- **Uses from project**: `genuineIsogSmulSub_omegaPullbackCoeff`, `isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: unused in file (shipped as standalone output)
- **Visibility**: public
- **Lines**: 1640–1647, proof ~8 lines

---

### `def FunctorialAtImage`
- **Type**: `(φ ψ : Isogeny) (g_ψ : E(K(E)) →+ E(K(E))) → Prop`
- **What**: "g_ψ is functorial at the image point of φ" — the second-order generic-point functoriality needed for composition-genuineness. Records that g_ψ sends the image of P_gen under φ to the composite-pullback coordinates.
- **How**: Definitional.
- **Hypotheses**: (definition)
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `IsGenuineWith`
- **Used by**: `genuine_comp_isGenuineWith_of_functorial`, `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`, `genuine_dual_comp_eq_mulByInt_of_V_functorial`, `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1679–1688, def body ~9 lines

---

### `theorem genuine_comp_isGenuineWith_of_functorial`
- **Type**: `(omit [Fintype K] [Fintype W.toAffine.Point]) (N : ℤ) (hφ : IsGenuineWith φ g_φ) (h_func : FunctorialAtImage φ ψ g_ψ) (h_end : g_ψ (g_φ P_gen) = N • P_gen) → IsGenuineWith W (ψ.comp φ) (zsmulPointHom W N)`
- **What**: Composition-genuineness (general form): if φ genuine with g_φ, g_ψ functorial at image, and g_ψ∘g_φ(P_gen) = N·P_gen, then ψ∘φ is genuine with [N]-action.
- **How**: Obtains the image coordinates from `hφ`, applies `h_func`, assembles via `rfl`.
- **Hypotheses**: As above.
- **Uses from project**: `IsGenuineWith`, `FunctorialAtImage`, `zsmulPointHom`
- **Used by**: `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`
- **Visibility**: public
- **Lines**: 1700–1715 (`omit [...] in` at 1689), proof ~15 lines

---

### `theorem genuineIsogSmulSub_comp_isGenuineWith_mulByInt`
- **Type**: `(hq : ...) ... (β_dual : Isogeny) (g_V : ...) (h_V_func : FunctorialAtImage ...) (h_end : ...) → IsGenuineWith W (β_dual.comp (genuineIsogSmulSub W r s ...)) (zsmulPointHom W N)`
- **What**: Composition-genuineness for the genuine r·π − s family (witness-parametric on the V-side). Specialises the general form to φ = r·π − s.
- **How**: `genuine_comp_isGenuineWith_of_functorial` with `genuineIsogSmulSub_isGenuineWith`.
- **Hypotheses**: V-side functoriality + end relation.
- **Uses from project**: `genuine_comp_isGenuineWith_of_functorial`, `genuineIsogSmulSub_isGenuineWith`, `IsGenuineWith`, `FunctorialAtImage`, `zsmulPointHom`
- **Used by**: `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, `genuine_dual_comp_eq_mulByInt_of_V_functorial`
- **Visibility**: public
- **Lines**: 1733–1749, proof ~3 lines

---

### `theorem genuine_dual_comp_eq_mulByInt_of_components`
- **Type**: `... (h_pullback_eq : (β_dual.comp β).pullback = (mulByInt N).pullback) → β_dual.comp β = mulByInt N`
- **What**: Pivot lift: given AddMonoidHom-level Cayley–Hamilton plus a pullback identity, concludes full isogeny equality β_dual∘β = [N].
- **How**: `Isogeny.eq_of_components h_pullback_eq` with `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`.
- **Hypotheses**: All standard genuineness witnesses plus the pullback identity.
- **Uses from project**: `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`
- **Used by**: `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`
- **Visibility**: public
- **Lines**: 1760–1782, proof ~4 lines

---

### `theorem genuine_dual_comp_eq_mulByInt_of_isGenuineWith`
- **Type**: `... (hN_ne : N ≠ 0) (h_comp_genuine : IsGenuineWith W (β_dual.comp β) (zsmulPointHom W N)) → β_dual.comp β = mulByInt N`
- **What**: Wall-B killer (geometric action form): replaces the raw pullback identity with the structural hypothesis that the composition is genuine with the [N]-action.
- **How**: `Isogeny.eq_of_components` where the pullback side uses `genuine_isogeny_ext_pullback` (comparing `h_comp_genuine` with `mulByInt_isGenuineWith`), and the AddMonoidHom side uses `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`.
- **Hypotheses**: All genuineness witnesses; `N ≠ 0`; composition is genuine with [N]-action.
- **Uses from project**: `genuine_isogeny_ext_pullback`, `mulByInt_isGenuineWith`, `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, `IsGenuineWith`, `zsmulPointHom`
- **Used by**: `genuine_dual_comp_eq_mulByInt_of_V_functorial`
- **Visibility**: public
- **Lines**: 1798–1824, proof ~26 lines

---

### `theorem genuine_dual_comp_eq_mulByInt_of_V_functorial`
- **Type**: `... (g_V : ...) (h_V_func : FunctorialAtImage ...) (h_end : ...) → β_dual.comp (r·π − s) = mulByInt N`
- **What**: Wall-B killer fully wired from V-side residue: produces the composition equality from the honest V-side inputs (functoriality + end relation) without assuming the composition is genuine directly.
- **How**: Calls `genuine_dual_comp_eq_mulByInt_of_isGenuineWith` with `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`.
- **Hypotheses**: All genuineness witnesses; V-side functoriality; end relation.
- **Uses from project**: `genuine_dual_comp_eq_mulByInt_of_isGenuineWith`, `genuineIsogSmulSub_comp_isGenuineWith_mulByInt`
- **Used by**: `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1839–1865, proof ~6 lines

---

### `theorem genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`
- **Type**: `... (h_pullback_eq : ...) (h_isDual_pair : IsDualOf β_dual (r·π−s)) (h_beta_pos) (h_N_ne) → ((r·π−s).degree : ℤ) = N`
- **What**: GAP-QF SIGNED L1 from pivot components (composer): from the full witnesses yields the signed III.6.3 degree identity.
- **How**: `genuine_dual_comp_eq_mulByInt_of_components` + `signed_degree_of_genuine_dual_pair`.
- **Hypotheses**: All witnesses including the raw pullback identity.
- **Uses from project**: `genuine_dual_comp_eq_mulByInt_of_components`, `signed_degree_of_genuine_dual_pair`
- **Used by**: unused in file (standalone output)
- **Visibility**: public
- **Lines**: 1879–1905, proof ~3 lines

---

### `theorem genuineIsogSmulSub_degree_pos`
- **Type**: `(r s : ℤ) (hr hs hrK hsK) → 0 < (genuineIsogSmulSub W r s ...).degree`
- **What**: Nonconstancy of r·π − s: its degree is positive, axiom-clean.
- **How**: `isogeny_degree_pos W`.
- **Hypotheses**: All four nonvanishing conditions.
- **Uses from project**: `genuineIsogSmulSub`, `isogeny_degree_pos`
- **Used by**: `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1914–1917, proof ~1 line

---

### `theorem genuineIsogSmulSub_degree_eq_signed_of_pivot_witness`
- **Type**: `... (h_isDual : IsDualOf β_dual (r·π−s)) (h_beta_pos) (h_N_ne) (h_comp_eq : β_dual.comp (r·π−s) = mulByInt N) → ((r·π−s).degree : ℤ) = N`
- **What**: GAP-QF non-circular III.6.3 from pivot witness: takes the dual relation + composition equality as hypotheses.
- **How**: `signed_degree_of_genuine_dual_pair`.
- **Hypotheses**: Dual relation; positivity; N ≠ 0; composition equality.
- **Uses from project**: `signed_degree_of_genuine_dual_pair`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1927–1940, proof ~2 lines

---

### `theorem genuineIsogSmulSub_degree_eq_signed_via_walls`
- **Type**: `... (g_V : ...) (h_isDual_V_pi : IsDualOf V π) (h_sum_trace : ...) (h_beta_dual_hom : ...) (hN_ne) (h_V_func : FunctorialAtImage ...) (h_end : ...) (h_isDual : IsDualOf β_dual (r·π−s)) (h_beta_pos) → ((r·π−s).degree : ℤ) = N`
- **What**: GAP-QF SIGNED L1 via Wall-A bridge: derives the signed degree identity from the Wall-A/B/C chain of witnesses (consolidating to a single deep gap on Wall-A/BRIDGE-003).
- **How**: `genuine_dual_comp_eq_mulByInt_of_V_functorial` to get composition equality; `signed_degree_of_genuine_dual_pair` to extract degree.
- **Hypotheses**: All V-side witnesses (dual+trace+hom for V-π side) + V-side functoriality/end + the β_dual-side dual relation + positivity.
- **Uses from project**: `genuine_dual_comp_eq_mulByInt_of_V_functorial`, `signed_degree_of_genuine_dual_pair`, `FunctorialAtImage`
- **Used by**: `genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Visibility**: public
- **Lines**: 1969–1998, proof ~29 lines

---

### `theorem genuineIsogSmulSub_degree_eq_signed_via_walls'`
- **Type**: Same as `_via_walls` but drops `h_beta_pos` (supplied internally via `genuineIsogSmulSub_degree_pos`).
- **What**: Wall-A-routed signed degree with nonconstancy discharged internally.
- **How**: Calls `genuineIsogSmulSub_degree_eq_signed_via_walls` with `genuineIsogSmulSub_degree_pos`.
- **Hypotheses**: All except `h_beta_pos`.
- **Uses from project**: `genuineIsogSmulSub_degree_eq_signed_via_walls`, `genuineIsogSmulSub_degree_pos`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2012–2036, proof ~5 lines

---

### `theorem genuineIsogSmulSub_degree_eq_signed`
- **Type**: `(hq : 2 ≤ Fintype.card K) (r s : ℤ) (hr hs hrK hsK) → ((genuineIsogSmulSub W r s ...).degree : ℤ) = q·r² − t·r·s + s²`
- **What**: GAP-QF non-circular III.6.3, generic case, unconditional. Intended live form.
- **How**: `sorry` — the unconditional form does not yet have the Wall-A witnesses supplied.
- **Hypotheses**: All four nonvanishing conditions.
- **Uses from project**: (sorry body — no uses)
- **Used by**: `degree_quadratic_exists_skeleton_nonzero`
- **Visibility**: public
- **Lines**: 2057–2062, proof = `sorry`
- **Notes**: **Contains `sorry`**. The docstring explains the gap clearly: the witness-parametric routes (`_via_walls`, `_of_pivot_witness`) are available; the unconditional form waits for Wall-A/BRIDGE-003.

---

### `theorem degree_quadratic_exists_edge_of_witness`
- **Type**: `(hq : ...) (r s : ℤ) (β : Isogeny) (h_beta_deg : ...) → ∃ β', (β'.degree : ℤ) = q·r²−t·r·s+s²`
- **What**: Witness-parametric edge case: given an explicit β with the right degree, yields the existence statement.
- **How**: `⟨β, h_beta_deg⟩`.
- **Hypotheses**: An explicit isogeny β with the correct degree.
- **Uses from project**: (none)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2071–2078, proof ~1 line

---

### `theorem degree_quadratic_exists_edge_r_int_zero`
- **Type**: `(hq : ...) (s : ℤ) (hs : s ≠ 0) → ∃ β, (β.degree : ℤ) = 0−0+s²`
- **What**: L2 easy: r=0∈ℤ case; takes β = [s] with degree s².
- **How**: `mulByInt_degree` + arithmetic.
- **Hypotheses**: `s ≠ 0 ∈ ℤ`.
- **Uses from project**: `mulByInt_degree`
- **Used by**: `degree_quadratic_exists_edge`, `degree_quadratic_exists_skeleton_nonzero`
- **Visibility**: public
- **Lines**: 2092–2102, proof ~10 lines

---

### `theorem degree_quadratic_exists_edge_s_int_zero`
- **Type**: `(hq : ...) (r : ℤ) (hr : r ≠ 0) → ∃ β, (β.degree : ℤ) = q·r²−t·r·0+0`
- **What**: L2 easy: s=0∈ℤ case; takes β = π∘[r] with degree r²·q.
- **How**: `Isogeny.comp_degree` + `mulByInt_degree` + `frobeniusIsog_degree` + arithmetic.
- **Hypotheses**: `r ≠ 0 ∈ ℤ`.
- **Uses from project**: `mulByInt_degree`, `frobeniusIsog_degree`
- **Used by**: `degree_quadratic_exists_edge`, `degree_quadratic_exists_skeleton_nonzero`
- **Visibility**: public
- **Lines**: 2109–2120, proof ~11 lines

---

### `theorem degree_quadratic_exists_edge`
- **Type**: `(hq : ...) (r s : ℤ) (h_nz : ¬(r=0∧s=0)) (h_edge : (r:K)=0 ∨ (s:K)=0) → ∃ β, (β.degree:ℤ) = q·r²−t·r·s+s²`
- **What**: GAP-QF edge case (III.6.3 at degenerate (r,s)): trivial integer-zero sub-cases closed directly; char-divisible sub-case dispatched to named conditional residuals.
- **How**: Case split `hr0 : r=0` / `hs0 : s=0`; integer-zero cases via `_r_int_zero/_s_int_zero`; char-divisible cases via `Conditional.degree_quadratic_exists_edge_r/s_char_divisible`.
- **Hypotheses**: `¬(r=0∧s=0)`; `(r:K)=0 ∨ (s:K)=0`.
- **Uses from project**: `degree_quadratic_exists_edge_r_int_zero`, `degree_quadratic_exists_edge_s_int_zero`, `Conditional.degree_quadratic_exists_edge_r_char_divisible`, `Conditional.degree_quadratic_exists_edge_s_char_divisible`
- **Used by**: `degree_quadratic_exists_skeleton_nonzero`
- **Visibility**: public
- **Lines**: 2132–2155, proof ~23 lines

---

### `theorem degree_quadratic_exists_skeleton_nonzero`
- **Type**: `(hq : ...) (r s : ℤ) (h_nz : ¬(r=0∧s=0)) → ∃ β, (β.degree:ℤ) = q·r²−t·r·s+s²`
- **What**: GAP-QF non-zero existence: for every (r,s)≠(0,0) an isogeny realizes the QF value. Routes to the sorry-carrying `genuineIsogSmulSub_degree_eq_signed` in the generic case.
- **How**: Four-way case split (r=0, s=0, (r:K)=0, (s:K)=0, generic); integer-zero via shipped lemmas; char-divisible via `degree_quadratic_exists_edge`; generic via `genuineIsogSmulSub_degree_eq_signed`.
- **Hypotheses**: `¬(r=0∧s=0)`.
- **Uses from project**: `degree_quadratic_exists_edge_r_int_zero`, `degree_quadratic_exists_edge_s_int_zero`, `degree_quadratic_exists_edge`, `genuineIsogSmulSub`, `genuineIsogSmulSub_degree_eq_signed`
- **Used by**: `qf_nonneg_skeleton`
- **Visibility**: public
- **Lines**: 2167–2184, proof ~17 lines
- **Notes**: Sorries inherited from `genuineIsogSmulSub_degree_eq_signed` in the generic case.

---

### `theorem qf_nonneg_skeleton`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∀ r s : ℤ, 0 ≤ q·r²−t·r·s+s²`
- **What**: GAP-QF top leaf: the degree quadratic form is non-negative (Silverman III.6.3). Carries sorry via `degree_quadratic_exists_skeleton_nonzero`.
- **How**: (r,s)=(0,0) case by `simp`; otherwise via `degree_quadratic_exists_skeleton_nonzero` + `Int.natCast_nonneg`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `degree_quadratic_exists_skeleton_nonzero`
- **Used by**: unused in file (top-level output)
- **Visibility**: public
- **Lines**: 2191–2201, proof ~11 lines
- **Notes**: sorryAx inherited from the generic case.

---

### `theorem qf_nonneg_skeleton_of_pivot_chain`
- **Type**: `(hq : ...) (h_realization : ∀ r s ≠ (0,0), ∃ β, deg=...) → ∀ r s, 0 ≤ q·r²−t·r·s+s²`
- **What**: All-witness-parametric form of qf_nonneg_skeleton: given a full realization hypothesis for all (r,s), concludes non-negativity. Axiom-clean conditioned on its parameter.
- **How**: (r,s)=(0,0) by `simp`; otherwise from `h_realization` + `Int.natCast_nonneg`.
- **Hypotheses**: `h_realization` assumed.
- **Uses from project**: (none from project)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2215–2231, proof ~17 lines

---

## Notes

1. The file uses `set_option maxHeartbeats` at three places: `l6_B3_tower` (800000, for the tower computation with opaque instances), `emb_le_card_kernel` (1600000, for the multi-layer Ore-localization/γ.toAlgebra instance threading), and `mulByInt_isGenuineWith` / `zsmul_frobeniusIsog_isGenuineWith` (4000000 each, for the pullback-at-generic-point computation).

2. The sole `sorry` is in `genuineIsogSmulSub_degree_eq_signed` (line 2062): the unconditional signed degree identity waits for Wall-A/BRIDGE-003. Witness-parametric alternatives (`_via_walls`, `_of_pivot_witness`) are axiom-clean.

3. The file contains extensive prose documentation (block comments totalling ~400 lines) explaining the V.1.3 residual analysis, the R2 route, and the Wall-A gap.
