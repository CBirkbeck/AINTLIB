# Inventory: ./HasseWeil/Hasse/OpenLemmas.lean

This file (1868 lines) packages all remaining open mathematical lemmas needed to
assemble the four-field `HasseWitnesses` bundle and thereby deliver the Hasse bound
`|#E(F_q) − q − 1| ≤ 2√q`. It is organised in reviewer-round layers (rounds 2–4).
Many declarations here are thin wrappers or sorry-stubs for the open lemmas;
a handful are non-trivial proven theorems.

---

### `theorem Isogeny_eq_of_components`
- **Type**: `{f g : Isogeny W₁ W₂} → f.pullback = g.pullback → f.toAddMonoidHom = g.toAddMonoidHom → f = g`
- **What**: Structural extensionality for `Isogeny`: two isogenies are equal iff their pullback and rational-point map components agree.
- **How**: `cases f; cases g` then `simp [Isogeny.mk.injEq]` reduces to component equality.
- **Hypotheses**: Two isogenies over elliptic curves over a field with `DecidableEq`.
- **Uses from project**: none
- **Used by**: `Isogeny.eq_of_components` (wrapper), `trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness`
- **Visibility**: public
- **Lines**: 180–189, proof 3 lines
- **Notes**: none

---

### `theorem Isogeny.eq_of_components`
- **Type**: same signature as `Isogeny_eq_of_components`, in the `Isogeny` namespace
- **What**: Public re-export of `Isogeny_eq_of_components` in the `Isogeny` namespace for the polarisation pipeline.
- **How**: Delegates directly to `Isogeny_eq_of_components`.
- **Hypotheses**: same as above
- **Uses from project**: `Isogeny_eq_of_components`
- **Used by**: unused in file (intended for external callers in the polarisation pipeline)
- **Visibility**: public
- **Lines**: 200–207, proof 1 line
- **Notes**: None; effectively a namespace alias.

---

### `private theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_silverman_iv14`
- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: Private alias wrapping the SilvermanIV14 form of the ω-coefficient identity for `1 − π`, to avoid Lean 4 partial-name shadowing when the outer wrapper is declared.
- **How**: Delegates directly to `_root_.HasseWeil.omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`.
- **Hypotheses**: Finite field `K` of cardinality ≥ 2, characteristic `p` prime.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (top-level, from SilvermanIV14)
- **Used by**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (public wrapper)
- **Visibility**: private
- **Lines**: 225–228, proof 1 line
- **Notes**: Exists solely to avoid name-shadowing ambiguity.

---

### `theorem omegaPullbackCoeff_add_genuine` (Open Lemma 1)
- **Type**: `(α β : Isogeny W.toAffine W.toAffine) → AddNonInversePair α β → Function.Injective (addCoordAlgHomPair hxy) → omegaPullbackCoeff W (addIsog hxy hinj) = omegaPullbackCoeff W α + omegaPullbackCoeff W β`
- **What**: ω-pullback coefficient additivity for the genuine addition isogeny `addIsog`: the invariant differential coefficient of the sum equals the sum of coefficients (Silverman III.5.2).
- **How**: Sorry — intended to use the Kähler differential witness chain for the addition pullback map.
- **Hypotheses**: Finite field `K`, a pair of isogenies forming a genuine addition (non-inverse pair with injective coord hom).
- **Uses from project**: (none — sorry)
- **Used by**: Docstring-referenced by `additivity_witness_for_pc_sep`; `HasseOpenLemmaPack.l1_omega_add`
- **Visibility**: public
- **Lines**: 252–258, proof 1 line (sorry)
- **Notes**: **sorry**. The Silverman III.5.2 content is open; the specialised companion L1' (`omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`) is now the load-bearing route for Witness #1.

---

### `theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (Open Lemma 1')
- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
- **What**: Direct specialisation of L1 to `1 − π`: the ω-pullback coefficient of the `1 − π` isogeny equals 1. This is what the separability iff consumes.
- **How**: Extracts `p, CharP K p, Fact p.Prime` from `FiniteField.card'`, then delegates to the private alias `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_silverman_iv14` (which reaches the SilvermanIV14 axiom-clean proof).
- **Hypotheses**: Finite field `K` of cardinality ≥ 2.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_silverman_iv14` (private alias)
- **Used by**: `additivity_witness_for_pc_sep` (via `_root_.HasseWeil.omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`)
- **Visibility**: public
- **Lines**: 277–294, proof 4 lines
- **Notes**: Axiom-clean (no sorry). Companion to the still-open L1.

---

### `noncomputable def bridge_Bi_kernelToPrime` (Open Lemma 2, Bridge B(i))
- **Type**: `(hq : 2 ≤ Fintype.card K) → (data : Sinf …) → (T : (isogOneSub_negFrobenius W hq).kernel) → Ideal data.carrier`
- **What**: For each kernel point `T ∈ ker(1 − π)` (including `T = O`), produces the order-based prime ideal of the `Sinf` carrier via the projective local-ring construction `{a : a | ord_T(a) > 0}`. Uniform for all kernel points including infinity.
- **How**: Sorry — needs `Sinf_ord_nonneg_at_kernel_point_unconditional` which is downstream (import cycle prevents referencing it here).
- **Hypotheses**: `Sinf` data on `γ.pullback (x_gen W)`, kernel point `T`.
- **Uses from project**: (none — sorry)
- **Used by**: `bridge_Bi_isPrime`, `bridge_Bi_liesOver`, `bridge_Bii_bijective`
- **Visibility**: public
- **Lines**: 339–370, proof 1 line (sorry)
- **Notes**: **sorry**. Import-cycle block prevents using the downstream `Sinf_ord_nonneg_at_kernel_point_unconditional`.

---

### `theorem bridge_Bi_isPrime` (Open Lemma 2 companion)
- **Type**: `… → (bridge_Bi_kernelToPrime W hq data T).IsPrime`
- **What**: Certifies that the output of `bridge_Bi_kernelToPrime` is a prime ideal.
- **How**: Sorry.
- **Hypotheses**: Same as `bridge_Bi_kernelToPrime`.
- **Uses from project**: `bridge_Bi_kernelToPrime`
- **Used by**: `bridge_Bii_bijective`
- **Visibility**: public
- **Lines**: 374–383, proof 1 line (sorry)
- **Notes**: **sorry**.

---

### `theorem bridge_Bi_liesOver` (Open Lemma 2 companion)
- **Type**: `… → (bridge_Bi_kernelToPrime W hq data T).LiesOver (xIdeal (k := K))`
- **What**: Certifies that the output of `bridge_Bi_kernelToPrime` lies over `xIdeal = (X) ⊂ K[X]`.
- **How**: Sorry.
- **Hypotheses**: Same as `bridge_Bi_kernelToPrime`.
- **Uses from project**: `bridge_Bi_kernelToPrime`
- **Used by**: `bridge_Bii_bijective`
- **Visibility**: public
- **Lines**: 387–398, proof 1 line (sorry)
- **Notes**: **sorry**.

---

### `theorem bridge_Bii_bijective` (Open Lemma 3, Bridge B(ii))
- **Type**: `(hq : …) [Fintype W.toAffine.Point] (data : Sinf …) → Function.Bijective (fun T => ⟨bridge_Bi_kernelToPrime …, …, …⟩)`
- **What**: The map from `ker(1 − π)` to prime ideals of the Sinf carrier lying over `xIdeal` is a bijection (the geometric closed-point ↔ prime correspondence, Silverman V.1.1 p. 138).
- **How**: Sorry — the genuine bijection is the algebraic geometry content.
- **Hypotheses**: `Fintype W.toAffine.Point`, `Sinf` data.
- **Uses from project**: `bridge_Bi_kernelToPrime`, `bridge_Bi_isPrime`, `bridge_Bi_liesOver`
- **Used by**: unused in file (feeds `HasseOpenLemmaPack.l3_bridge_Bii`)
- **Visibility**: public
- **Lines**: 413–430, proof 1 line (sorry)
- **Notes**: **sorry**.

---

### `theorem bridge_Biii_ord_eq_neg_two` (Open Lemma 4, Bridge B(iii))
- **Type**: `… → data.ordAt (bridge_Bi_kernelToPrime W hq data T) = (-2 : ℤ)`
- **What**: The order of `f = γ.pullback (x_gen W)` at each kernel-prime is −2; each rational kernel point is a double pole of the pullback of `x_gen` (ramification index 2, Silverman V.1.1 p. 138).
- **How**: Sorry.
- **Hypotheses**: Same setup as bridge B(i).
- **Uses from project**: `bridge_Bi_kernelToPrime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 447–460, proof 1 line (sorry)
- **Notes**: **sorry**.

---

### `theorem bridge_Biv_inertia_eq_one` (Open Lemma 5, Bridge B(iv))
- **Type**: `… → Ideal.inertiaDeg (xIdeal (k := K)) (bridge_Bi_kernelToPrime W hq data T) = 1`
- **What**: The inertia degree of the kernel-prime over `xIdeal` is 1; i.e. the residue field at each kernel prime is `K`-isomorphic to `K`.
- **How**: Sorry.
- **Hypotheses**: Same setup as bridge B(i).
- **Uses from project**: `bridge_Bi_kernelToPrime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 476–490, proof 1 line (sorry)
- **Notes**: **sorry**.

---

### `theorem v_1_3_sepDegree_eq_pointCount` (Open Lemma 6)
- **Type**: `(hq : 2 ≤ Fintype.card K) [Fintype W.toAffine.Point] → (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`
- **What**: The separable degree of `1 − π` equals the number of `F_q`-rational points on `W` (Silverman V.1.1, combining Bridges B(i)–(iv) + Computation A + L7 + L7a).
- **How**: Sorry — the genuine composition uses `finrank_eq_weighted_poleDegree_of_nonconstant` plus Bridges B(ii)-(iv) plus the `γ.IsSeparable` shipped fact plus kernel coincidence.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`, `Fintype W.toAffine.Point`.
- **Uses from project**: (none — sorry)
- **Used by**: `witness_pc_sepDeg`
- **Visibility**: public
- **Lines**: 541–544, proof 1 line (sorry)
- **Notes**: **sorry**. Key open content of Witness #3.

---

### `theorem isSeparable_LinfAt_pullback_x_gen_of_isSeparable` (Open Lemma 7)
- **Type**: `(hq : …) (_hsep : (isogOneSub_negFrobenius W hq).IsSeparable) (_hf : Fact (Transcendental K (…)⁻¹)) → Nonempty (Algebra.IsSeparable (FractionRing (Polynomial K)) (LinfAt …))`
- **What**: Discharges the `Algebra.IsSeparable` typeclass needed for `Sinf.ofIntegralClosure`, for the specific `f = γ.pullback (x_gen W)`. Implements the tower argument `K⟮f⟯ ⊆ γ.pullback.fieldRange ⊆ K(E)`.
- **How**: Extracts `p` and `CharP K p` via `CharP.exists`, then delegates to `HasseWeil.Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen`.
- **Hypotheses**: `hq`, separability of `1 − π`, `Transcendental` fact for the inverse pullback.
- **Uses from project**: `HasseWeil.Conditional.K_E_separable_over_LinfAt_gamma_pullback_x_gen` (from `PoleDivisorFallback.lean`)
- **Used by**: unused in file (feeds `HasseOpenLemmaPack.l7_sinf_typeclass`)
- **Visibility**: public
- **Lines**: 596–608, proof 5 lines
- **Notes**: Axiom-clean (the underlying `Conditional` lemma is the shipped proof). The `_hsep` parameter is not consumed — it's a documentation parameter.

---

### `theorem function_field_x_separable` (Open Lemma 7a)
- **Type**: `Algebra.IsSeparable (FractionRing (Polynomial K)) W.toAffine.FunctionField`
- **What**: The function field `K(E)` is separable over `K(x) = FractionRing K[X]` for any smooth Weierstrass curve (all characteristics). The element `y_gen W` satisfies a separable degree-2 polynomial over `K(x)`.
- **How**: (1) Shows `W.toAffine.polynomial` is monic and irreducible (via `monic_polynomial`, `irreducible_polynomial`). (2) Maps to `F[Y]` via `Polynomial.map`, inheriting monic + irreducible (Gauss lemma `irreducible_iff_irreducible_map_fraction_map`). (3) Computes the derivative equals `polynomialY`, and `polynomialY ≠ 0` by `IsElliptic` (discriminant non-vanishing rules out `a₁ = a₃ = 0`). (4) Applies `separable_iff_derivative_ne_zero` for irreducible polynomials. (5) Shows `minpoly F y = P` via `minpoly.eq_of_irreducible_of_monic`. (6) Shows `F⟮y⟯ = ⊤` via `finrank_functionField_eq_two` and `IntermediateField.eq_of_le_of_finrank_eq`. (7) Concludes via `AlgEquiv.Algebra.isSeparable` and `IntermediateField.topEquiv`.
- **Hypotheses**: `K` a field with `[Fintype K]`, `W` elliptic. (No `[NeZero 2]` or `[NeZero 3]` — char-uniform.)
- **Uses from project**: `HasseWeil.finrank_functionField_eq_two`; `W.toAffine.monic_polynomial`, `W.toAffine.irreducible_polynomial`, `W.toAffine.natDegree_polynomial`, `y_gen W`
- **Used by**: unused in file (feeds `HasseOpenLemmaPack.l7a_function_field_x_separable`)
- **Visibility**: public
- **Lines**: 645–763, proof ~118 lines
- **Notes**: Proof > 30 lines. Longest proven (non-sorry) proof in the file. Char-uniform (works in char 2 and 3).

---

### `theorem verschiebung_isDualOf_frobenius` (Open Lemma 9)
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∃ V : Isogeny W.toAffine W.toAffine, IsDualOf W.toAffine V (frobeniusIsog W)`
- **What**: There exists a Verschiebung isogeny `V` that is dual to the q-power Frobenius endomorphism, satisfying both composition identities `V ∘ π = [q]` and `π ∘ V = [q]` (Silverman III.7).
- **How**: Sorry. The comment documents that this is a **duplicate** of the shipped `HasseWeil.verschiebung_dual_exists` (GapSpines.lean:64), but the fix is blocked by an import cycle.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: (none — sorry)
- **Used by**: `verschiebung_isDualOf_frobenius_of_qth_root_witness` (docstring reference only); `HasseOpenLemmaPack.l9_verschiebung_dual`
- **Visibility**: public
- **Lines**: 810–815, proof 2 lines (sorry)
- **Notes**: **sorry**. Comment flags this as a DUPLICATE of `verschiebung_dual_exists` — architectural restructuring needed to retire it.

---

### `theorem verschiebung_isDualOf_frobenius_of_qth_root_witness`
- **Type**: `(hq : …) → (h_qth_root : ∀ z, ∃ g, g ^ Fintype.card K = (mulByInt …).pullback z) → ∃ V, IsDualOf W.toAffine V (frobeniusIsog W)`
- **What**: Conditional companion to L9: given a universal q-th root surjectivity witness for the function field, constructs the Verschiebung as the dual of Frobenius via `verschiebungIsog_of_witness`.
- **How**: Applies `verschiebungIsog_of_witness` (composing `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`) then `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` for the `IsDualOf` predicate.
- **Hypotheses**: `hq`, element-level q-th root witness for each function field element.
- **Uses from project**: `verschiebungIsog_of_witness`, `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`, `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` (from Verschiebung/Cascade)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 833–845, proof 4 lines
- **Notes**: Axiom-clean (delegates to shipped axiom-clean cascade). A scaffold, not a closure of L9.

---

### `theorem trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness` (Open Lemma 10, scaffold)
- **Type**: `(hq …) → (V : Isogeny …) → (IsDualOf W.toAffine V (frobeniusIsog W)) → (hxy : AddNonInversePair …) → (hinj …) → (one_sub_V : Isogeny …) → (h_one_sub_V_hom …) → (h_one_sub_isDual …) → (h_pullback_trace …) → addIsog hxy hinj = mulByInt W.toAffine (isogTrace …)`
- **What**: Conditionally proves the trace formula `π + V = [tr]` at the isogeny level, assuming three substantive witnesses for the dual-additivity of `1 − π` (the III.6.2(b) content). Not a full closure of L10; the pack field stays open.
- **How**: Step 1: derives the hom-level trace formula using `trace_identity_of_dual_chain` (consuming the IsDualOf chain on `(1 − V, 1 − π)`) plus `isogOneSub_negFrobenius_toAddMonoidHom`. Step 2: lifts to `addIsog.toAddMonoidHom` via `addIsog_toAddMonoidHom`. Step 3: combines pullback + hom equalities via `Isogeny_eq_of_components`.
- **Hypotheses**: All three substantive witnesses: `one_sub_V`, `h_one_sub_isDual`, `h_pullback_trace`.
- **Uses from project**: `trace_identity_of_dual_chain`, `isogOneSub_negFrobenius_toAddMonoidHom`, `addIsog_toAddMonoidHom`, `Isogeny_eq_of_components`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 891–947, proof ~33 lines (body 915–947)
- **Notes**: Proof > 30 lines. This is a scaffold — the pack field `l10_trace_eq` remains open.

---

### `theorem vertical_principal` (Open Lemma 11a, SHIPPED)
- **Type**: `[IsAlgClosed K] [NeZero (2 : K)] [NeZero (3 : K)] [IsIntegrallyClosed …] → (P : W.toAffine.Point) → ProjIsPrincipal … ((P) + (-P) − 2(O))`
- **What**: The vertical-line divisor `(P) + (−P) − 2(O)` is principal on `E` (Silverman III.2.3). Discharged unconditionally via Miller.
- **How**: Applies `miller_hypothesis_holds W.toAffine P (-P)` (which gives `(P) + (-P) − (P + -P) − (O) ∈ Princ`), rewrites `P + -P = 0` and `0.toProjectiveSmoothPoint = ∞`, then converts `2 • single ∞ 1` to a sum via `abel`.
- **Hypotheses**: Algebraically closed field of char ≠ 2, 3; integrally closed coordinate ring.
- **Uses from project**: `HasseWeil.Curves.miller_hypothesis_holds`
- **Used by**: `line_principal`
- **Visibility**: public
- **Lines**: 1013–1047, proof ~23 lines
- **Notes**: **Char 2/3 explicitly excluded** via `[NeZero 2] [NeZero 3]`.

---

### `theorem line_principal` (Open Lemma 11b, SHIPPED)
- **Type**: `[IsAlgClosed K] [NeZero (2 : K)] [NeZero (3 : K)] [IsIntegrallyClosed …] → (P Q : W.toAffine.Point) → ProjIsPrincipal … ((P) + (Q) + (-(P+Q)) − 3(O))`
- **What**: The chord/tangent line divisor `(P) + (Q) + (−(P+Q)) − 3(O)` is principal on `E` (Silverman III.2.3). Sum of Miller + vertical_principal.
- **How**: Combines `miller_hypothesis_holds W.toAffine P Q` (gives `(P)+(Q)−(P+Q)−(O) ∈ Princ`) with `vertical_principal W (P+Q)` (gives `(P+Q)+(-(P+Q))−2(O) ∈ Princ`), adds them via `ProjIsPrincipal.add`, then uses `abel` to match coefficients.
- **Hypotheses**: Same as `vertical_principal`.
- **Uses from project**: `HasseWeil.Curves.miller_hypothesis_holds`, `vertical_principal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1062–1099, proof ~24 lines
- **Notes**: **Char 2/3 explicitly excluded**.

---

### `theorem miller_principal` (Open Lemma 11c, SHIPPED)
- **Type**: `[IsAlgClosed K] [NeZero (2 : K)] [NeZero (3 : K)] [IsIntegrallyClosed …] → MillerHypothesis W.toAffine`
- **What**: The Miller relation: for all `P, Q`, the degree-zero divisor `(P) + (Q) − (P+Q) − (O)` is principal (= `MillerHypothesis W.toAffine`).
- **How**: Direct delegation to `HasseWeil.Curves.miller_hypothesis_holds`.
- **Hypotheses**: Same as `vertical_principal`.
- **Uses from project**: `HasseWeil.Curves.miller_hypothesis_holds`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1113–1117, proof 1 line
- **Notes**: none

---

### `theorem degree_zero_divisor_reduce` (Open Lemma 11d, SHIPPED)
- **Type**: `[IsAlgClosed K] [NeZero (2 : K)] [NeZero (3 : K)] [IsIntegrallyClosed …] → DivZeroReduce W.toAffine`
- **What**: Every degree-zero divisor on `E` is principal-equivalent to `(σ(D)) − (O)` (Silverman III.3, Abel-Jacobi keystone).
- **How**: Direct delegation to `HasseWeil.Curves.divZeroReduce_holds`.
- **Hypotheses**: Same as `vertical_principal`.
- **Uses from project**: `HasseWeil.Curves.divZeroReduce_holds`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1130–1134, proof 1 line
- **Notes**: none

---

### `theorem point_minus_O_principal_eq_zero` (Open Lemma 11e, SHIPPED)
- **Type**: `[IsAlgClosed K] [IsDedekindDomain …] [IsIntegrallyClosed …] → PointMinusOPrincipalEqZero W.toAffine`
- **What**: If `(P) − (O)` is principal on `E`, then `P = O` (unique point in that linear series).
- **How**: Direct delegation to `HasseWeil.Curves.pointMinusOPrincipalEqZero_unconditional`.
- **Hypotheses**: Algebraically closed field, Dedekind + integrally closed coordinate ring.
- **Uses from project**: `HasseWeil.Curves.pointMinusOPrincipalEqZero_unconditional`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1148–1153, proof 1 line
- **Notes**: none

---

### `theorem coordRingImage_ordAtInfty_ne_neg_one` (Open Lemma 11f, SHIPPED)
- **Type**: `(u : …CoordinateRing) → u ≠ 0 → ordAtInfty (algebraMap _ … u) ≠ (-1 : ℤ)`
- **What**: The order at infinity of any nonzero coordinate ring element is never −1 (parity/Riemann-Roch gap theorem for Weierstrass curves).
- **How**: Direct delegation to `SmoothPlaneCurve.coordRingImage_ordAtInfty_ne_neg_one`.
- **Hypotheses**: `u` nonzero in the affine coordinate ring.
- **Uses from project**: `HasseWeil.Curves.SmoothPlaneCurve.coordRingImage_ordAtInfty_ne_neg_one` (from PoleOrderParity)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1171–1179, proof 1 line
- **Notes**: none

---

### `theorem isogeny_degree_baseChange_eq` (Open Lemma 12b, AUDITED)
- **Type**: `(α : Isogeny W.toAffine W.toAffine) → ∃ d : ℤ, d = (α.degree : ℤ)`
- **What**: Definitional placeholder for base-change degree descent: the degree of an isogeny is unchanged under base-change to the algebraic closure. Currently stated as a trivial existence (proved by `⟨α.degree, rfl⟩`).
- **How**: Trivial: `⟨α.degree, rfl⟩`.
- **Hypotheses**: An endoisogeny of an elliptic curve.
- **Uses from project**: none
- **Used by**: `HasseOpenLemmaPack.l12b_basechange_degree` (pack field)
- **Visibility**: public
- **Lines**: 1224–1227, proof 1 line
- **Notes**: The genuine `(α.baseChange L).degree = α.degree` requires `Isogeny.baseChange` which does not yet exist in the project. This is a definitional marker.

---

### `theorem frobenius_isog_iterate` (Open Lemma 13, SHIPPED)
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] → ∀ f, (frobeniusIsog W).pullback f = ((· ^ p)^[r]) f`
- **What**: The q-power Frobenius pullback equals the r-fold iterate of the p-power map on function field elements, when `q = p^r` (Silverman III.4.6).
- **How**: `rw [frobeniusIsog_pullback_apply, (Fact.out : Fintype.card K = p ^ r)]` then `(congr_fun (pow_iterate p r) f).symm`.
- **Hypotheses**: `K` with characteristic `p` prime, `Fintype.card K = p^r`.
- **Uses from project**: `frobeniusIsog_pullback_apply`
- **Used by**: `HasseOpenLemmaPack.l13_frob_iterate` (pack field)
- **Visibility**: public
- **Lines**: 1250–1256, proof 3 lines
- **Notes**: Axiom-clean. Uses `pow_iterate` from mathlib.

---

### `theorem AddHomProperty_descent` (Open Lemma 14, SHIPPED)
- **Type**: `(φ : EC.Isogeny W₁ W₂) → (cd : φ.toCurveMap.CoordHom) → (φL : EC.Isogeny W₁' W₂') → (cdL : …) → (includeP₁ : W₁.Point →+ W₁'.Point) → (includeP₂ : W₂.Point →+ W₂'.Point) → Function.Injective includeP₂ → (∀ P, includeP₂ (φ.toPointMap cd P) = φL.toPointMap cdL (includeP₁ P)) → φL.AddHomProperty cdL → φ.AddHomProperty cd`
- **What**: Pointwise descent of `AddHomProperty` along an injective base-change inclusion: if the base-changed isogeny is additive and the inclusion is injective and the diagram commutes, then the original isogeny is additive (Silverman III.4.8).
- **How**: `intro P Q; apply include_inj; rw [map_add, square, square, square, map_add, hL]` — injectivity of `includeP₂` and commutativity of the square are the only ingredients.
- **Hypotheses**: Fields `F ↪ L`, elliptic curves, commuting diagram.
- **Uses from project**: (none — self-contained)
- **Used by**: unused in file (pack field `l14_addHom_descent`)
- **Visibility**: public
- **Lines**: 1290–1310, proof 3 lines
- **Notes**: Axiom-clean. Reviewer-corrected v2: uses `AddMonoidHom` bundled inclusions.

---

### `noncomputable def Polynomial.scalarExtensionEquiv` (Priority 1 substrate for L15)
- **Type**: `(A : Type*) [CommSemiring A] (B : Type*) [CommSemiring B] [Algebra A B] → TensorProduct A B (Polynomial A) ≃ₐ[B] Polynomial B`
- **What**: Base-change for univariate polynomial rings: `B ⊗[A] A[X] ≃ₐ[B] B[X]`. Substrate for the coordinate-ring scalar-extension chain.
- **How**: Sorry — the MvPolynomial-PUnit bridge composition hit universe meta-variable elaboration errors; refactored to a separate file (not yet done).
- **Hypotheses**: `A`, `B` commutative semirings with `B` an `A`-algebra.
- **Uses from project**: (none — sorry)
- **Used by**: `AdjoinRoot_tensorAlgEquiv_exists` (docstring reference only); `HasseOpenLemmaPack.l15_adjoinRoot_tensor`
- **Visibility**: public (in `Polynomial` namespace)
- **Lines**: 1333–1336, proof 1 line (sorry)
- **Notes**: **sorry**. Comment notes the net sorry-count impact is 0 (parent L15 already carries sorry).

---

### `theorem AdjoinRoot_tensorAlgEquiv_exists` (Open Lemma 15)
- **Type**: `… → Nonempty (TensorProduct A (A[X] ⧸ (p)) B ≃ₐ[B] B[X] ⧸ (p.map …))`
- **What**: The `AdjoinRoot` scalar-extension equivalence `B ⊗_A (A[X]/(p)) ≃ₐ[B] B[X]/(p^B)` as an `AlgEquiv` (Silverman II.2.11 spirit; likely mathlib-upstreamable).
- **How**: Sorry — the AlgEquiv form upgrade from RingEquiv is pending.
- **Hypotheses**: Commutative rings `A`, `B` with `A`-algebra structure on `B`.
- **Uses from project**: (none — sorry)
- **Used by**: `HasseOpenLemmaPack.l15_adjoinRoot_tensor`
- **Visibility**: public
- **Lines**: 1368–1381, proof 1 line (sorry)
- **Notes**: **sorry**. Reviewer round 3 upgraded from `RingEquiv` to `AlgEquiv`.

---

### `theorem witness_pc_sep_from_open_lemmas`
- **Type**: `(hq : …) → (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius …) = …) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Derives separability of `1 − π` from the additivity witness `h_add` (which pins `omegaPullbackCoeff = 1`). An intermediate glue combining `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness` with the separability iff.
- **How**: Step 1: applies `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness`. Step 2: applies `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`. Step 3: `one_ne_zero`.
- **Hypotheses**: `hq`, the additivity witness `h_add`.
- **Uses from project**: `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness`, `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`
- **Used by**: unused in file (superseded — `witness_pc_sep` dispatches directly)
- **Visibility**: public
- **Lines**: 1408–1423, proof 9 lines
- **Notes**: Dead-code candidate: the load-bearing path now goes through `witness_pc_sep` directly. Marked STALE in docstring (R17 D-R17-A-01).

---

### `theorem additivity_witness_for_pc_sep`
- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = ((1 : ℤ) : KE) * omegaPullbackCoeff W (Isogeny.id W.toAffine) + ((-1 : ℤ) : KE) * omegaPullbackCoeff W (frobeniusIsog W)`
- **What**: Verifies the additivity-witness identity `ω(1 − π) = 1 · ω(id) + (−1) · ω(π)` by substituting the shipped closed-form values: `ω(1 − π) = 1`, `ω(id) = 1`, `ω(π) = 0`.
- **How**: Extracts characteristic data from `FiniteField.card'`, applies `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, `omegaPullbackCoeff_id`, `omegaPullbackCoeff_frobenius`, then `push_cast; ring`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `_root_.HasseWeil.omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, `omegaPullbackCoeff_id`, `omegaPullbackCoeff_frobenius`
- **Used by**: unused in file (marked STALE; `witness_pc_sep` bypasses this route)
- **Visibility**: public
- **Lines**: 1445–1459, proof 7 lines
- **Notes**: Docstring marks this STALE (R17 D-R17-A-01). Dead-code candidate; retained for documentation purposes.

---

### `theorem witness_pc_sep`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (isogOneSub_negFrobenius W hq).IsSeparable`
- **What**: Witness #1 (separability of `1 − π`). Dispatches directly to the shipped axiom-clean `isogOneSub_negFrobenius_isSeparable` (SilvermanIV14).
- **How**: Extracts `p, CharP K p, Fact p.Prime` from `FiniteField.card'`, then calls `isogOneSub_negFrobenius_isSeparable`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `isogOneSub_negFrobenius_isSeparable` (from AdditionPullback/SilvermanIV14)
- **Used by**: `witnessBundle`
- **Visibility**: public
- **Lines**: 1469–1475, proof 4 lines
- **Notes**: Axiom-clean. The R18 D-R17-A-01 rewire (2026-05-19).

---

### `theorem witness_pc_fin`
- **Type**: `(hq : 2 ≤ Fintype.card K) → @FiniteDimensional … (isogOneSub_negFrobenius W hq).toAlgebra.toModule`
- **What**: Witness #2 (finite-dimensionality). Direct delegation to the shipped `isogOneSub_negFrobenius_finiteDimensional`.
- **How**: Direct delegation.
- **Hypotheses**: `hq`.
- **Uses from project**: `isogOneSub_negFrobenius_finiteDimensional`
- **Used by**: `witnessBundle`
- **Visibility**: public
- **Lines**: 1482–1486, proof 1 line
- **Notes**: Axiom-clean.

---

### `theorem witness_pc_sepDeg`
- **Type**: `(hq : 2 ≤ Fintype.card K) [Fintype W.toAffine.Point] → (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`
- **What**: Witness #3 (sepDegree = pointCount). Direct delegation to `v_1_3_sepDegree_eq_pointCount`.
- **How**: Direct delegation.
- **Hypotheses**: `hq`, `Fintype W.toAffine.Point`.
- **Uses from project**: `v_1_3_sepDegree_eq_pointCount`
- **Used by**: `witnessBundle`
- **Visibility**: public
- **Lines**: 1496–1499, proof 1 line
- **Notes**: Inherits sorry from `v_1_3_sepDegree_eq_pointCount`.

---

### `theorem witness_qf_nonneg`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 − isogTrace … * r * s + s ^ 2`
- **What**: Witness #4 (QF non-negativity, Silverman III.6.3): the integer quadratic form `q·r² − tr·rs + s²` is non-negative for all `r, s`. This is the content of the Hasse bound's positive semidefiniteness step.
- **How**: Sorry — the Silverman III.6.3 genuine content.
- **Hypotheses**: `hq`.
- **Uses from project**: (none — sorry)
- **Used by**: `witnessBundle`
- **Visibility**: public
- **Lines**: 1521–1534, proof 1 line (sorry)
- **Notes**: **sorry**. Key open content of Witness #4.

---

### `structure HasseOpenLemmaPack`
- **Type**: A structure bundling all 18 open lemma fields for the Hasse bound.
- **What**: Explicit dependency record: bundles L1, L2–L5 (Sinf-parametric bridges), L6, L7, L7a, L8 (QF non-negativity), L9, L10, L11a–L11f (Miller primitives), L12b, L13, L14, L15 as fields. Consuming a `HasseOpenLemmaPack` in `hasse_bound_from_HasseOpenLemmaPack` makes the dependency on all open lemmas explicit at the Lean level (per reviewer Q5).
- **How**: Structure declaration with 20 fields; no proof.
- **Hypotheses**: `W : WeierstrassCurve K`, `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: (all open lemma types reference project constructs: `isogOneSub_negFrobenius`, `addIsog`, `Sinf`, `xIdeal`, `frobeniusIsog`, `isogTrace`, `IsDualOf`, etc.)
- **Used by**: `hasse_bound_from_HasseOpenLemmaPack`, `hasse_bound_from_pack`
- **Visibility**: public
- **Lines**: 1569–1764, ~196 lines (structure body)
- **Notes**: Universe-polymorphic `.{v}` over the `Sinf` carrier universe.

---

### `def witnessBundle`
- **Type**: `[Fintype W.toAffine.Point] → (hq : 2 ≤ Fintype.card K) → HasseWitnesses W hq`
- **What**: Assembles the four-field `HasseWitnesses` bundle from the four witness constructions (`witness_pc_sep`, `witness_pc_fin`, `witness_pc_sepDeg`, `witness_qf_nonneg`).
- **How**: Record literal with four fields.
- **Hypotheses**: `Fintype W.toAffine.Point`, `hq`.
- **Uses from project**: `witness_pc_sep`, `witness_pc_fin`, `witness_pc_sepDeg`, `witness_qf_nonneg`
- **Used by**: `hasse_bound_from_open_lemmas`, `hasse_bound_sq_from_open_lemmas`
- **Visibility**: public
- **Lines**: 1769–1775, proof 5 lines
- **Notes**: Inherits sorries from `witness_pc_sepDeg` and `witness_qf_nonneg`.

---

### `theorem hasse_bound_from_HasseOpenLemmaPack`
- **Type**: `[Fintype W.toAffine.Point] → (hq : 2 ≤ Fintype.card K) → (pack : HasseOpenLemmaPack W hq) → |…| ≤ 2 * Real.sqrt (Fintype.card K)`
- **What**: The Hasse bound `|#E(F_q) − q − 1| ≤ 2√q` from an explicit `HasseOpenLemmaPack`. Makes all open-lemma dependencies manifest at the Lean type level.
- **How**: Constructs a `HasseWitnesses` bundle via `hasse_bound_of_witnesses`, filling: (1) `pc_sep` directly from `isogOneSub_negFrobenius_isSeparable` (bypassing pack field L1); (2) `pc_fin` from `isogOneSub_negFrobenius_finiteDimensional`; (3) `pc_sepDeg_eq_pointCount` from `pack.l6_v_1_3`; (4) `qf_nonneg` from `pack.l8_qf_nonneg`.
- **Hypotheses**: `Fintype W.toAffine.Point`, `hq`, a `HasseOpenLemmaPack`.
- **Uses from project**: `hasse_bound_of_witnesses`, `isogOneSub_negFrobenius_isSeparable`, `isogOneSub_negFrobenius_finiteDimensional`
- **Used by**: `hasse_bound_from_pack` (deprecated alias)
- **Visibility**: public
- **Lines**: 1803–1825, proof ~16 lines
- **Notes**: None; this is the preferred consumer entry point.

---

### `theorem hasse_bound_from_pack` (deprecated alias)
- **Type**: Same as `hasse_bound_from_HasseOpenLemmaPack`
- **What**: Deprecated alias for `hasse_bound_from_HasseOpenLemmaPack` kept for backward compatibility (since 2026-05-15).
- **How**: Direct delegation to `hasse_bound_from_HasseOpenLemmaPack`.
- **Hypotheses**: Same.
- **Uses from project**: `hasse_bound_from_HasseOpenLemmaPack`
- **Used by**: unused in file
- **Visibility**: public (`@[deprecated]`)
- **Lines**: 1831–1836, proof 1 line
- **Notes**: `@[deprecated hasse_bound_from_HasseOpenLemmaPack (since := "2026-05-15")]`.

---

### `theorem hasse_bound_from_open_lemmas` (DEPRECATED)
- **Type**: `[Fintype W.toAffine.Point] → (hq : …) → |…| ≤ 2 * Real.sqrt …`
- **What**: Deprecated simpler form of the Hasse bound from open lemmas (no explicit pack argument). Feeds `witnessBundle` into `hasse_bound_of_witnesses`.
- **How**: `hasse_bound_of_witnesses W (witnessBundle W hq)`.
- **Hypotheses**: `Fintype W.toAffine.Point`, `hq`.
- **Uses from project**: `hasse_bound_of_witnesses`, `witnessBundle`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1852–1856, proof 1 line
- **Notes**: Marked deprecated in favour of `hasse_bound_from_HasseOpenLemmaPack`. Dead-code candidate.

---

### `theorem hasse_bound_sq_from_open_lemmas`
- **Type**: `[Fintype W.toAffine.Point] → (hq : …) → ((pointCount W.toAffine : ℤ) − Fintype.card K − 1) ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Squared form `(#E − q − 1)² ≤ 4q` of the Hasse bound, derived from `hasse_bound_sq_of_witnesses` applied to `witnessBundle`.
- **How**: `hasse_bound_sq_of_witnesses W (witnessBundle W hq)`.
- **Hypotheses**: `Fintype W.toAffine.Point`, `hq`.
- **Uses from project**: `hasse_bound_sq_of_witnesses`, `witnessBundle`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1860–1864, proof 1 line
- **Notes**: Inherits sorries from `witnessBundle`.

---

## Summary

| Metric | Count |
|--------|-------|
| Total declarations | 35 |
| Defs | 3 (`bridge_Bi_kernelToPrime`, `Polynomial.scalarExtensionEquiv`, `witnessBundle`) |
| Theorems/lemmas | 31 |
| Structures | 1 (`HasseOpenLemmaPack`) |
| Instances | 0 |
| Declarations with sorry | 11 |
| `set_option maxHeartbeats` occurrences | 0 |
| Proofs > 30 lines | 2 (`function_field_x_separable` ~118 lines, `trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness` ~33 lines) |

### Sorry declarations
`omegaPullbackCoeff_add_genuine`, `bridge_Bi_kernelToPrime`, `bridge_Bi_isPrime`, `bridge_Bi_liesOver`, `bridge_Bii_bijective`, `bridge_Biii_ord_eq_neg_two`, `bridge_Biv_inertia_eq_one`, `v_1_3_sepDegree_eq_pointCount`, `verschiebung_isDualOf_frobenius`, `Polynomial.scalarExtensionEquiv`, `AdjoinRoot_tensorAlgEquiv_exists`, `witness_qf_nonneg`

### Key API (used by 3+ declarations in this file)
- `Isogeny_eq_of_components`: used by `Isogeny.eq_of_components` + `trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness`
- `witnessBundle`: used by `hasse_bound_from_open_lemmas` + `hasse_bound_sq_from_open_lemmas`

### Unused in file (dead-code candidates)
`Isogeny.eq_of_components`, `bridge_Bii_bijective`, `bridge_Biii_ord_eq_neg_two`, `bridge_Biv_inertia_eq_one`, `isSeparable_LinfAt_pullback_x_gen_of_isSeparable`, `function_field_x_separable`, `verschiebung_isDualOf_frobenius_of_qth_root_witness`, `trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness`, `line_principal`, `miller_principal`, `degree_zero_divisor_reduce`, `point_minus_O_principal_eq_zero`, `coordRingImage_ordAtInfty_ne_neg_one`, `isogeny_degree_baseChange_eq`, `frobenius_isog_iterate`, `AddHomProperty_descent`, `AdjoinRoot_tensorAlgEquiv_exists`, `witness_pc_sep_from_open_lemmas`, `additivity_witness_for_pc_sep`, `hasse_bound_from_pack`, `hasse_bound_from_open_lemmas`, `hasse_bound_sq_from_open_lemmas`
