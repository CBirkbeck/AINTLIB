# Inventory: ./HasseWeil/Curves/NormValuation.lean

File path: `HasseWeil/Curves/NormValuation.lean`
Total lines: 2441
Import: `HasseWeil.Curves.ProjectiveDivisor` plus several Mathlib modules (RelNorm, Jacobson, AdjoinRoot, DedekindDomain.Ideal.Lemmas, etc.)

**Purpose**: Builds the norm-valuation bridge (Silverman II.3.1(b), "Helper B") for smooth Weierstrass curves — the identity `(divisorOf f).degree = intDegree(normAsRatFunc f)`. The foundation is `F[C] ⧸ maximalIdealAt P ≃ₐ[F] F` (inertia-degree-1 at every smooth point), which leads through Dedekind factorization machinery to the full theorem `helperB` and ultimately `projectiveDivisorOf_degree_eq_zero`.

---

## `SmoothPlaneCurve` namespace (lines 40–1250, 2390–2439)

---

### `noncomputable def quotientMaximalIdealAtEquiv`
- **Type**: `(P : C.SmoothPoint) → (C.CoordinateRing ⧸ C.maximalIdealAt P) ≃ₐ[F] F`
- **What**: Constructs the F-algebra isomorphism between the quotient of the coordinate ring by the maximal ideal at P and the base field F.
- **How**: Direct application of mathlib's `WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv` with the nonsingularity datum `P.nonsingular.1`.
- **Hypotheses**: `P` is a smooth point of C; no extra hypotheses.
- **Uses from project**: `C.maximalIdealAt`, `C.CoordinateRing`, `C.toAffine`
- **Used by**: `finrank_quotientMaximalIdealAt`, `algebraMap_quotient_maximalIdealAt_surjective`
- **Visibility**: public
- **Lines**: 52–56; proof length: 2 lines (body)
- **Notes**: None.

---

### `theorem finrank_quotientMaximalIdealAt`
- **Type**: `(P : C.SmoothPoint) → Module.finrank F (C.CoordinateRing ⧸ C.maximalIdealAt P) = 1`
- **What**: The residue field at any smooth point of a smooth plane curve is one-dimensional over F.
- **How**: Uses `quotientMaximalIdealAtEquiv P` to transport finrank via `.toLinearEquiv.finrank_eq`, then `Module.finrank_self`.
- **Hypotheses**: None beyond F field and P smooth.
- **Uses from project**: `C.quotientMaximalIdealAtEquiv`
- **Used by**: unused in file (downstream consumers likely in other files)
- **Visibility**: public
- **Lines**: 60–63; proof length: 2 lines
- **Notes**: None.

---

### `theorem xClass_mem_maximalIdealAt`
- **Type**: `(P : C.SmoothPoint) → XClass C.toAffine P.x ∈ C.maximalIdealAt P`
- **What**: The X-class element (image of X − P.x) lies in the maximal ideal at P.
- **How**: Unfolds `maximalIdealAt` and `XYIdeal`, then `Ideal.subset_span` with membership in the generating set.
- **Hypotheses**: None beyond P smooth.
- **Uses from project**: `C.maximalIdealAt`
- **Used by**: `algebraMap_X_sub_C_mem_maximalIdealAt`, `maximalIdealAt_injective`
- **Visibility**: public
- **Lines**: 68–73; proof length: 3 lines
- **Notes**: None.

---

### `theorem algebraMap_X_sub_C_mem_maximalIdealAt`
- **Type**: `(P : C.SmoothPoint) → algebraMap (Polynomial F) C.CoordinateRing (X - C P.x) ∈ C.maximalIdealAt P`
- **What**: The image of X − P.x under the algebra map F[X] → F[C] belongs to the maximal ideal at P.
- **How**: Shows this image equals `XClass C.toAffine P.x` using `unfold` and `simp` on `mk`/`C_sub`/`AdjoinRoot.mk`, then applies `xClass_mem_maximalIdealAt`.
- **Hypotheses**: None beyond P smooth.
- **Uses from project**: `C.xClass_mem_maximalIdealAt`, `C.maximalIdealAt`
- **Used by**: `maximalIdealAt_liesOver`, `algebraMap_quotient_maximalIdealAt_surjective`, `X_sub_C_pow_two_le_relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 76–88; proof length: 11 lines
- **Notes**: None.

---

### `theorem maximalIdealAt_liesOver`
- **Type**: `(P : C.SmoothPoint) → (C.maximalIdealAt P).LiesOver (Ideal.span {X - C P.x})`
- **What**: The maximal ideal `maximalIdealAt P` lies over the principal ideal `(X − P.x)` in F[X].
- **How**: Shows `span {X − P.x} ≤ comap alg (maximalIdealAt P)` via `algebraMap_X_sub_C_mem_maximalIdealAt`, then invokes maximality of `(X − P.x)` plus non-topness of the comap to use `IsMaximal.eq_of_le`.
- **Hypotheses**: None beyond P smooth.
- **Uses from project**: `C.algebraMap_X_sub_C_mem_maximalIdealAt`, `C.maximalIdealAt_isMaximal`
- **Used by**: `algebraMap_quotient_maximalIdealAt_surjective`, `inertiaDeg_maximalIdealAt`, `exists_relNorm_maximalIdealAt_eq_pow`, `relNorm_maximalIdealAt_le_X_sub_C`, `maximalIdealAt_mem_primesOver`, `ramificationIdx_maximalIdealAt_ne_zero`, `maximalIdealAt_liesOver_of_eq_x`, `sum_ramificationIdx_over_fiber`, `relNorm_eq_X_sub_C_of_primesOver`, `count_relNorm_singleton_eq_sum_count_fiber`
- **Visibility**: public
- **Lines**: 94–119; proof length: 24 lines
- **Notes**: This is a key API lemma — used by 10+ other declarations in this file.

---

### `theorem finrank_quotientSpanXSubC`
- **Type**: `(a : F) → Module.finrank F (Polynomial F ⧸ Ideal.span {X - C a}) = 1`
- **What**: The quotient F[X]/(X−a) has F-dimension 1.
- **How**: Via `Polynomial.quotientSpanXSubCAlgEquiv` and `Module.finrank_self`.
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 122–126; proof length: 3 lines
- **Notes**: Suspected duplication with a mathlib lemma (this is a trivial fact about quotients of polynomial rings by linear factors). Dead code within this file.

---

### `theorem algebraMap_quotient_maximalIdealAt_surjective`
- **Type**: `(P : C.SmoothPoint) → Function.Surjective (algebraMap (F[X] ⧸ (X-P.x)) (F[C] ⧸ maximalIdealAt P))`
- **What**: The induced algebra map from F[X]/(X−P.x) to F[C]/(maximalIdealAt P) is surjective.
- **How**: Given any w in the quotient, lifts to F via `quotientMaximalIdealAtEquiv`, then traces back through the scalar tower `F → F[X] → F[C]` (using `IsScalarTower.algebraMap_apply`, `Ideal.quotientMap_mk`) to produce a preimage. Final equality uses the symm of `quotientMaximalIdealAtEquiv`.
- **Hypotheses**: `maximalIdealAt_liesOver P` for the LiesOver instance.
- **Uses from project**: `C.quotientMaximalIdealAtEquiv`, `C.maximalIdealAt_liesOver`, `C.algebraMap_X_sub_C_mem_maximalIdealAt`
- **Used by**: `inertiaDeg_maximalIdealAt`
- **Visibility**: public
- **Lines**: 133–177; proof length: 43 lines
- **Notes**: Proof > 30 lines.

---

### `theorem inertiaDeg_maximalIdealAt`
- **Type**: `(P : C.SmoothPoint) → Ideal.inertiaDeg (span {X - C P.x}) (C.maximalIdealAt P) = 1`
- **What**: The inertia degree at every smooth point is 1 — the residue field extension is trivial.
- **How**: Unfolds `inertiaDeg_algebraMap`. Upper bound via `finrank_le_one` (using `algebraMap_quotient_maximalIdealAt_surjective`), lower bound via `Module.finrank_pos` (nontriviality of the quotient). Uses `Module.IsTorsionFree` inferInstance since base is a field.
- **Hypotheses**: `maximalIdealAt_liesOver P` for the instance.
- **Uses from project**: `C.maximalIdealAt_liesOver`, `C.algebraMap_quotient_maximalIdealAt_surjective`, `C.maximalIdealAt_isMaximal`
- **Used by**: `sum_ramificationIdx_eq_finrank`
- **Visibility**: public
- **Lines**: 182–223; proof length: 40 lines
- **Notes**: Proof > 30 lines.

---

### `instance coordinateRing_finiteType`
- **Type**: `Algebra.FiniteType F C.CoordinateRing`
- **What**: The coordinate ring F[C] is a finite-type F-algebra.
- **How**: Uses `Algebra.FiniteType.trans` with the chain `F → F[X] → AdjoinRoot(W.polynomial)`, the latter via `AdjoinRoot.finiteType`.
- **Hypotheses**: None.
- **Uses from project**: `C.toAffine.polynomial`
- **Used by**: `module_finite_quotient_of_maximal`
- **Visibility**: public
- **Lines**: 229–232; proof length: 2 lines
- **Notes**: None.

---

### `theorem module_finite_quotient_of_maximal`
- **Type**: `(hM : M.IsMaximal) → Module.Finite F (C.CoordinateRing ⧸ M)` (where `letI : Field (F[C] ⧸ M)`)
- **What**: For any maximal ideal M of F[C], the quotient is a finite F-module (Zariski's lemma).
- **How**: Gets `Algebra.FiniteType` via surjectivity of `Quotient.mkₐ`, then applies `finite_of_finite_type_of_isJacobsonRing` (Zariski's lemma), which applies since F is a field hence Jacobson.
- **Hypotheses**: M maximal in F[C].
- **Uses from project**: `coordinateRing_finiteType`
- **Used by**: `algebraMap_bijective_quotient_of_maximal`
- **Visibility**: public
- **Lines**: 237–245; proof length: 7 lines
- **Notes**: None.

---

### `theorem algebraMap_bijective_quotient_of_maximal`
- **Type**: `[IsAlgClosed F] → (hM : M.IsMaximal) → Function.Bijective (algebraMap F (F[C] ⧸ M))`
- **What**: Under an algebraically closed base field, for any maximal ideal M, the structure map F → F[C]⧸M is bijective.
- **How**: Gets finite module from `module_finite_quotient_of_maximal`, gets integrality from `Algebra.IsIntegral.of_finite`, then applies `IsAlgClosed.algebraMap_bijective_of_isIntegral`.
- **Hypotheses**: F algebraically closed, M maximal.
- **Uses from project**: `C.module_finite_quotient_of_maximal`
- **Used by**: `exists_coordinates_of_isMaximal`, `exists_smoothPoint_of_isMaximal`
- **Visibility**: public
- **Lines**: 251–259; proof length: 8 lines
- **Notes**: None.

---

### `theorem exists_coordinates_of_isMaximal`
- **Type**: `[IsAlgClosed F] → (hM : M.IsMaximal) → ∃ a b : F, algebraMap F (F[C]⧸M) a = mk M (mk C.toAffine (C X)) ∧ algebraMap F (F[C]⧸M) b = mk M (mk C.toAffine Y)`
- **What**: Under IsAlgClosed, every maximal ideal yields F-rational coordinate witnesses (the candidate point).
- **How**: Uses surjectivity of `algebraMap_bijective_quotient_of_maximal` to lift the X-class and Y-class images.
- **Hypotheses**: F algebraically closed, M maximal.
- **Uses from project**: `C.algebraMap_bijective_quotient_of_maximal`
- **Used by**: unused in file (superseded by `exists_coordinates_of_isMaximal_of_surjective`)
- **Visibility**: public
- **Lines**: 268–282; proof length: 12 lines
- **Notes**: Largely superseded within this file by the de-IsAlgClosed version; may be dead code within this file.

---

### `theorem equation_of_coordinates`
- **Type**: `[IsAlgClosed F] → (hM : M.IsMaximal) → (ha, hb) → C.toAffine.Equation a b`
- **What**: The coordinate witnesses from a maximal ideal satisfy the Weierstrass equation.
- **How**: Uses `AdjoinRoot.mk_self` to get `mk W.polynomial = 0` in F[C], projects to the quotient, expands via `map_*` simp lemmas and rewrites using `ha`/`hb`, then injectivity of `algebraMap F (F[C]⧸M)` closes the goal.
- **Hypotheses**: F algebraically closed, M maximal, coordinate witnesses ha, hb.
- **Uses from project**: none (only project types)
- **Used by**: unused in file (superseded by `equation_of_coordinates_of_field`)
- **Visibility**: public
- **Lines**: 293–360; proof length: 66 lines
- **Notes**: Proof > 30 lines. Superseded by `equation_of_coordinates_of_field` (which drops `[IsAlgClosed]`); the remark in the docstring says the proof never used `IsAlgClosed` beyond the hypothesis carrier.

---

### `theorem exists_coordinates_of_isMaximal_of_surjective`
- **Type**: `(hM : M.IsMaximal) → (h_surj : Surjective (algebraMap F (F[C]⧸M))) → ∃ a b : F, ...`
- **What**: IsAlgClosed-free version: under surjectivity of algebraMap F (F[C]⧸M), yields coordinate witnesses.
- **How**: Direct `obtain` using `h_surj` on the X-class and Y-class images.
- **Hypotheses**: M maximal, algebraMap surjective.
- **Uses from project**: none (only project types)
- **Used by**: `exists_smoothPoint_of_isMaximal_of_surjective`
- **Visibility**: public
- **Lines**: 372–387; proof length: 13 lines
- **Notes**: V.1.3 deep-pass decoupling.

---

### `theorem equation_of_coordinates_of_field`
- **Type**: `(hM : M.IsMaximal) → (ha, hb) → C.toAffine.Equation a b`
- **What**: IsAlgClosed-free version: coordinate witnesses satisfy the Weierstrass equation (identical proof to `equation_of_coordinates`, `IsAlgClosed` was not actually used there).
- **How**: Identical to `equation_of_coordinates` — `AdjoinRoot.mk_self`, `map_*` simp, injectivity.
- **Hypotheses**: M maximal, coordinate witnesses.
- **Uses from project**: none (only project types)
- **Used by**: `exists_smoothPoint_of_isMaximal_of_surjective`
- **Visibility**: public
- **Lines**: 394–441; proof length: 46 lines
- **Notes**: Proof > 30 lines. Near-verbatim duplicate of `equation_of_coordinates` with `[IsAlgClosed]` dropped.

---

### `theorem exists_smoothPoint_of_isMaximal_of_surjective`
- **Type**: `[C.toAffine.IsElliptic] → (hM : M.IsMaximal) → (h_surj) → ∃ P : C.SmoothPoint, C.maximalIdealAt P = M`
- **What**: IsAlgClosed-free version of the MaxSpec surjection: any maximal ideal with F-rational residue field is `maximalIdealAt P` for some smooth F-rational point P.
- **How**: Extracts coordinates via `exists_coordinates_of_isMaximal_of_surjective`, proves Equation via `equation_of_coordinates_of_field`, Nonsingular via `equation_iff_nonsingular`, then shows `maximalIdealAt ⊆ M` using XClass/YClass generators and the coordinate equations, concludes by maximality equality.
- **Hypotheses**: C elliptic, M maximal, algebraMap F (F[C]⧸M) surjective.
- **Uses from project**: `C.exists_coordinates_of_isMaximal_of_surjective`, `C.equation_of_coordinates_of_field`, `C.maximalIdealAt_isMaximal`, `C.maximalIdealAt`
- **Used by**: `exists_smoothPoint_of_isMaximal`, `smoothPoint_fiber_eq_primesOver`, `relNorm_eq_X_sub_C_of_primesOver`, `count_relNorm_singleton_eq_sum_count_fiber`, `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 451–490; proof length: 38 lines
- **Notes**: Proof > 30 lines.

---

### `theorem exists_smoothPoint_of_isMaximal`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] → (hM : M.IsMaximal) → ∃ P : C.SmoothPoint, C.maximalIdealAt P = M`
- **What**: Under IsAlgClosed + IsElliptic, every maximal ideal of F[C] is of the form `maximalIdealAt P`.
- **How**: Thin specialisation of `exists_smoothPoint_of_isMaximal_of_surjective`, supplying surjectivity from `algebraMap_bijective_quotient_of_maximal`.
- **Hypotheses**: F algebraically closed, C elliptic, M maximal.
- **Uses from project**: `C.exists_smoothPoint_of_isMaximal_of_surjective`, `C.algebraMap_bijective_quotient_of_maximal`
- **Used by**: `smoothPointEquivMaxIdeal`, `smoothPointEquivMaxIdeal_apply`, `maximalIdealAt_range`, `smoothPoint_fiber_eq_primesOver`, `sum_ramificationIdx_eq_finrank`, `exists_relNorm_maximalIdealAt_eq_pow_bracketed` (indirectly), `relNorm_eq_X_sub_C_of_primesOver`, `count_relNorm_singleton_eq_sum_count_fiber`, `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 500–504; proof length: 2 lines
- **Notes**: None.

---

### `theorem maximalIdealAt_injective`
- **Type**: `Function.Injective (C.maximalIdealAt)`
- **What**: Distinct smooth points give distinct maximal ideals.
- **How**: From P.x = Q.x (via XClass membership in `maximalIdealAt Q` using `mem_maximalIdealAt_iff_eval_zero` and simp), then P.y = Q.y similarly from YClass membership. Concludes with `SmoothPoint.ext`.
- **Hypotheses**: None.
- **Uses from project**: `C.xClass_mem_maximalIdealAt`, `C.mem_maximalIdealAt_iff_eval_zero`
- **Used by**: `smoothPointEquivMaxIdeal`, `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 508–553; proof length: 44 lines
- **Notes**: Proof > 30 lines.

---

### `noncomputable def smoothPointEquivMaxIdeal`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] → C.SmoothPoint ≃ {M : Ideal C.CoordinateRing // M.IsMaximal}`
- **What**: Packages the bijection between smooth F-rational points and maximal ideals of F[C].
- **How**: `toFun = maximalIdealAt`, `invFun = choose` from `exists_smoothPoint_of_isMaximal`. `left_inv` via `maximalIdealAt_injective` + `choose_spec`, `right_inv` via `choose_spec`.
- **Hypotheses**: F algebraically closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_isMaximal`, `C.exists_smoothPoint_of_isMaximal`, `C.maximalIdealAt_injective`
- **Used by**: `smoothPointEquivMaxIdeal_apply`
- **Visibility**: public
- **Lines**: 561–572; proof length: 10 lines
- **Notes**: None.

---

### `@[simp] theorem smoothPointEquivMaxIdeal_apply`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] → (P : C.SmoothPoint) → (C.smoothPointEquivMaxIdeal P : Ideal C.CoordinateRing) = C.maximalIdealAt P`
- **What**: The Equiv's forward function is definitionally `maximalIdealAt`.
- **How**: `rfl`.
- **Hypotheses**: F algebraically closed, C elliptic.
- **Uses from project**: `C.smoothPointEquivMaxIdeal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 574–577; proof length: 1 line
- **Notes**: None.

---

### `theorem maximalIdealAt_range`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] → Set.range C.maximalIdealAt = {M : Ideal C.CoordinateRing | M.IsMaximal}`
- **What**: The image of `maximalIdealAt` is exactly the set of all maximal ideals of F[C].
- **How**: Both directions: surjection from `exists_smoothPoint_of_isMaximal`, injection trivially.
- **Hypotheses**: F algebraically closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_isMaximal`, `C.exists_smoothPoint_of_isMaximal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 582–589; proof length: 7 lines
- **Notes**: Dead code within this file.

---

### `theorem maximalIdealAt_liesOver_of_eq_x`
- **Type**: `(P : C.SmoothPoint) → (h : P.x = a) → (C.maximalIdealAt P).LiesOver (span {X - C a})`
- **What**: If P.x = a, then maximalIdealAt P lies over (X − a).
- **How**: Substitutes h and delegates to `maximalIdealAt_liesOver`.
- **Hypotheses**: P smooth, P.x = a.
- **Uses from project**: `C.maximalIdealAt_liesOver`
- **Used by**: `smoothPoint_fiber_eq_primesOver`, `sum_ramificationIdx_eq_finrank`, `count_relNorm_singleton_eq_sum_count_fiber`, `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 593–597; proof length: 3 lines
- **Notes**: None.

---

### `theorem sum_ramificationIdx_over_fiber`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] → (a : F) → Σ_{M ∈ primesOverFinset (X-a) F[C]} e_M · f_M = [F(C) : F(X)]`
- **What**: The standard Σ e·f = deg identity for the fiber over (X−a) in F[C]/F[X] — the ramification-inertia formula.
- **How**: Direct application of `Ideal.sum_ramification_inertia` with `p ≠ ⊥` (since X−a ≠ 0).
- **Hypotheses**: F algebraically closed, C elliptic, F[C] integrally closed (for Dedekind hypothesis).
- **Uses from project**: `C.CoordinateRing`, `C.FunctionField`
- **Used by**: `sum_ramificationIdx_eq_finrank`
- **Visibility**: public
- **Lines**: 602–627; proof length: 24 lines
- **Notes**: `[IsIntegrallyClosed C.CoordinateRing]` appears twice in the signature (duplicate hypothesis, likely a copy-paste artifact).

---

### `theorem sum_ramificationIdx_eq_finrank`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] → (a : F) → Σ_{M ∈ primesOverFinset (X-a) F[C]} e_M = [F(C) : F(X)]`
- **What**: The sum of ramification indices over all primes above (X−a) equals the degree [F(C):F(X)] = 2, since each inertia degree equals 1.
- **How**: Applies `sum_ramificationIdx_over_fiber`, then per prime rewrites `inertiaDeg = 1` via `inertiaDeg_maximalIdealAt` (after extracting the smooth point from `exists_smoothPoint_of_isMaximal` and showing P.x = a by comparing two LiesOver relations via `Ideal.span_singleton_eq_span_singleton` and `Polynomial.eq_of_monic_of_associated`).
- **Hypotheses**: F algebraically closed, C elliptic, F[C] integrally closed.
- **Uses from project**: `C.sum_ramificationIdx_over_fiber`, `C.finrank_functionField_over_fracPolynomialX`, `C.exists_smoothPoint_of_isMaximal`, `C.maximalIdealAt_liesOver`, `C.inertiaDeg_maximalIdealAt`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 634–706; proof length: 71 lines
- **Notes**: Proof > 30 lines. Duplicate `[IsIntegrallyClosed]` in signature. The longest proof in the SmoothPlaneCurve section.

---

### `theorem smoothPoint_fiber_eq_primesOver`
- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] → (a : F) → C.maximalIdealAt '' {P | P.x = a} = {M | M.IsMaximal ∧ M.LiesOver (span {X-Ca})}`
- **What**: The fiber of maximalIdealAt over smooth points with x-coordinate a equals the set of maximal ideals lying over (X−a).
- **How**: Both inclusions use `maximalIdealAt_isMaximal`, `maximalIdealAt_liesOver_of_eq_x`, and `exists_smoothPoint_of_isMaximal` plus the span-singleton equality argument (Associated → monic-equality → C.injectivity) to recover P.x = a.
- **Hypotheses**: F algebraically closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_isMaximal`, `C.maximalIdealAt_liesOver_of_eq_x`, `C.exists_smoothPoint_of_isMaximal`, `C.maximalIdealAt_liesOver`
- **Used by**: unused in file (mentioned in summary comment)
- **Visibility**: public
- **Lines**: 743–788; proof length: 44 lines
- **Notes**: Proof > 30 lines. Dead code within this file (mentioned only in the summary block comment).

---

### `theorem exists_relNorm_maximalIdealAt_eq_pow`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → (P : C.SmoothPoint) → ∃ s : ℕ, Ideal.relNorm (Polynomial F) (C.maximalIdealAt P) = (span {X - C P.x})^s`
- **What**: The relative norm of the maximal ideal at P is a power of the ideal (X − P.x).
- **How**: Direct application of `Ideal.exists_relNorm_eq_pow_of_isPrime` using `maximalIdealAt_liesOver` and `Polynomial.prime_X_sub_C`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_liesOver`
- **Used by**: `exists_relNorm_maximalIdealAt_eq_pow_bracketed`
- **Visibility**: public
- **Lines**: 832–843; proof length: 10 lines
- **Notes**: None.

---

### `theorem relNorm_algebraMap_X_sub_C_eq_pow_two`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → (a : F) → relNorm F[X] ((span {X-Ca}).map alg) = (span {X-Ca})^2`
- **What**: The relative norm of the pushed-forward ideal (X−a)·F[C] equals (X−a)^2, reflecting [F(C):F(X)] = 2.
- **How**: Direct application of `Ideal.relNorm_algebraMap` and `C.finrank_functionField_over_fracPolynomialX`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.finrank_functionField_over_fracPolynomialX`
- **Used by**: `X_sub_C_pow_two_le_relNorm_maximalIdealAt`, `prod_relNorm_pow_primesOver_eq_X_sub_C_pow_two`, `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 849–856; proof length: 2 lines
- **Notes**: None.

---

### `theorem X_sub_C_pow_two_le_relNorm_maximalIdealAt`
- **Type**: `... → (P : C.SmoothPoint) → (span {X-CP.x})^2 ≤ relNorm F[X] (C.maximalIdealAt P)`
- **What**: Upper bound on the exponent: the square of the ideal (X−P.x) divides the relative norm of maximalIdealAt P.
- **How**: `algebraMap_X_sub_C_mem_maximalIdealAt` gives the map inclusion, then `Ideal.relNorm_mono` + `relNorm_algebraMap_X_sub_C_eq_pow_two` give the bound.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.algebraMap_X_sub_C_mem_maximalIdealAt`, `C.relNorm_algebraMap_X_sub_C_eq_pow_two`
- **Used by**: `exists_relNorm_maximalIdealAt_eq_pow_bracketed`
- **Visibility**: public
- **Lines**: 863–875; proof length: 11 lines
- **Notes**: None.

---

### `theorem map_algebraMap_X_sub_C_eq_prod_primesOver_pow`
- **Type**: `... → (a : F) → (span {X-Ca}).map alg = ∏_{P ∈ primesOver (X-Ca) F[C]} P^{e_P}`
- **What**: Dedekind factorization of the pushed-forward ideal (X−a)·F[C] as a product of prime powers.
- **How**: Direct application of `Ideal.map_algebraMap_eq_finset_prod_pow` (after establishing p ≠ 0).
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: none
- **Used by**: `prod_relNorm_pow_primesOver_eq_X_sub_C_pow_two`
- **Visibility**: public
- **Lines**: 881–902; proof length: 20 lines
- **Notes**: None.

---

### `theorem prod_relNorm_pow_primesOver_eq_X_sub_C_pow_two`
- **Type**: `... → (a : F) → ∏_{P ∈ primesOver (X-Ca)} (relNorm P)^{e_P} = (span {X-Ca})^2`
- **What**: After applying relNorm to the Dedekind factorization, the product equals (X−a)^2.
- **How**: Applies relNorm to `map_algebraMap_X_sub_C_eq_prod_primesOver_pow` via `congr_arg`, rewrites with `relNorm_algebraMap_X_sub_C_eq_pow_two`, distributes `map_prod` and `map_pow`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.map_algebraMap_X_sub_C_eq_prod_primesOver_pow`, `C.relNorm_algebraMap_X_sub_C_eq_pow_two`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 911–934; proof length: 22 lines
- **Notes**: None.

---

### `theorem relNorm_maximalIdealAt_le_X_sub_C`
- **Type**: `... → (P : C.SmoothPoint) → relNorm F[X] (C.maximalIdealAt P) ≤ span {X-CP.x}`
- **What**: Lower bound: the relative norm of maximalIdealAt P divides (X−P.x) (exponent ≥ 1).
- **How**: Uses `Ideal.relNorm_le_comap` with `comap alg (maximalIdealAt P) = span {X-CP.x}` from `maximalIdealAt_liesOver`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_liesOver`
- **Used by**: `exists_relNorm_maximalIdealAt_eq_pow_bracketed`
- **Visibility**: public
- **Lines**: 941–953; proof length: 11 lines
- **Notes**: None.

---

### `theorem exists_relNorm_pow_of_primesOver`
- **Type**: `... → (a : F) → (hQ : Q ∈ primesOver (X-Ca) F[C]) → ∃ s_Q : ℕ, 1 ≤ s_Q ∧ relNorm F[X] Q = (span {X-Ca})^s_Q`
- **What**: For any prime Q over (X−a), its relative norm is a power of (X−a) with exponent ≥ 1.
- **How**: `Ideal.exists_relNorm_eq_pow_of_isPrime` gives the power, then `Ideal.relNorm_le_comap` + `pow_dvd_pow_iff` (for the non-unit prime X-C a) gives s ≥ 1.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: none
- **Used by**: `primesOverExp`, `one_le_primesOverExp`, `relNorm_eq_pow_primesOverExp`
- **Visibility**: public
- **Lines**: 958–989; proof length: 30 lines
- **Notes**: Proof exactly 30 lines (boundary case).

---

### `noncomputable def primesOverExp`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → (a : F) → (Q : Ideal C.CoordinateRing) → (hQ : Q ∈ primesOver (X-Ca) F[C]) → ℕ`
- **What**: The exponent s_Q such that `relNorm Q = (span {X-Ca})^s_Q`, extracted via Classical.choose.
- **How**: `(C.exists_relNorm_pow_of_primesOver a hQ).choose`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_relNorm_pow_of_primesOver`
- **Used by**: `one_le_primesOverExp`, `relNorm_eq_pow_primesOverExp`, `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 994–999; proof length: 1 line
- **Notes**: None.

---

### `theorem one_le_primesOverExp`
- **Type**: `... → 1 ≤ C.primesOverExp a Q hQ`
- **What**: The exponent is at least 1.
- **How**: `choose_spec.1` from `exists_relNorm_pow_of_primesOver`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_relNorm_pow_of_primesOver`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1001–1006; proof length: 1 line
- **Notes**: None.

---

### `theorem relNorm_eq_pow_primesOverExp`
- **Type**: `... → relNorm F[X] Q = (span {X-Ca})^(C.primesOverExp a Q hQ)`
- **What**: Witness that relNorm Q equals the exponent power.
- **How**: `choose_spec.2` from `exists_relNorm_pow_of_primesOver`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_relNorm_pow_of_primesOver`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1008–1016; proof length: 1 line
- **Notes**: None.

---

### `theorem exists_relNorm_maximalIdealAt_eq_pow_bracketed`
- **Type**: `... → (P : C.SmoothPoint) → ∃ s : ℕ, 1 ≤ s ∧ s ≤ 2 ∧ relNorm F[X] (C.maximalIdealAt P) = (span {X-CP.x})^s`
- **What**: Brackets the exponent s in `relNorm maximalIdealAt P = (X-P.x)^s` to {1,2}.
- **How**: Gets s from `exists_relNorm_maximalIdealAt_eq_pow`, s ≥ 1 from `relNorm_maximalIdealAt_le_X_sub_C` + `pow_dvd_pow_iff`, s ≤ 2 from `X_sub_C_pow_two_le_relNorm_maximalIdealAt` + `pow_dvd_pow_iff`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_relNorm_maximalIdealAt_eq_pow`, `C.relNorm_maximalIdealAt_le_X_sub_C`, `C.X_sub_C_pow_two_le_relNorm_maximalIdealAt`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1021–1046; proof length: 24 lines
- **Notes**: None.

---

### `theorem maximalIdealAt_mem_primesOver`
- **Type**: `... → (P : C.SmoothPoint) → C.maximalIdealAt P ∈ (span {X-CP.x}).primesOver C.CoordinateRing`
- **What**: The maximal ideal at P lies in the primesOver set over (X−P.x).
- **How**: `⟨inferInstance, C.maximalIdealAt_liesOver P⟩`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_liesOver`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1051–1057; proof length: 1 line
- **Notes**: None.

---

### `theorem ramificationIdx_maximalIdealAt_ne_zero`
- **Type**: `... → (P : C.SmoothPoint) → ramificationIdx alg (span {X-CP.x}) (C.maximalIdealAt P) ≠ 0`
- **What**: The ramification index of maximalIdealAt P over (X−P.x) is nonzero.
- **How**: `Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver` with `maximalIdealAt_liesOver`, and the proof that (X−P.x) ≠ 0.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.maximalIdealAt_liesOver`
- **Used by**: `relNorm_maximalIdealAt`
- **Visibility**: public
- **Lines**: 1062–1072; proof length: 9 lines
- **Notes**: None.

---

### `theorem relNorm_maximalIdealAt`
- **Type**: `... → (P : C.SmoothPoint) → relNorm F[X] (C.maximalIdealAt P) = span {X - C P.x}`
- **What**: The relative norm of `maximalIdealAt P` equals the ideal (X − P.x) — the keystone Helper B identity, showing the exponent is exactly 1.
- **How**: Uses `interval_cases s` on the bracketed exponent from `exists_relNorm_maximalIdealAt_eq_pow_bracketed`. For s=1 trivial; for s=2: derives contradiction by showing all prime exponents in the fiber must satisfy `s_Q · e_Q = e_Q` (via `Finset.sum_eq_sum_iff_of_le` comparing Σ s·e = Σ e = 2), forcing e_{M_P} = 0, contradicting `ramificationIdx_maximalIdealAt_ne_zero`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_relNorm_maximalIdealAt_eq_pow_bracketed`, `C.relNorm_maximalIdealAt_le_X_sub_C`, `C.X_sub_C_pow_two_le_relNorm_maximalIdealAt`, `C.prod_relNorm_pow_primesOver_eq_X_sub_C_pow_two`, `C.sum_ramificationIdx_eq_finrank`, `C.finrank_functionField_over_fracPolynomialX`, `C.primesOverExp`, `C.one_le_primesOverExp`, `C.relNorm_eq_pow_primesOverExp`, `C.maximalIdealAt_mem_primesOver`, `C.ramificationIdx_maximalIdealAt_ne_zero`
- **Used by**: `relNorm_eq_X_sub_C_of_primesOver`, `count_relNorm_singleton_eq_sum_count_fiber`
- **Visibility**: public
- **Lines**: 1089–1194; proof length: 105 lines
- **Notes**: Proof > 30 lines. This is the main technical payoff of the relNorm machinery.

---

### `theorem relNorm_eq_X_sub_C_of_primesOver`
- **Type**: `... → {a : F} → {Q : Ideal C.CoordinateRing} → (hQ : Q ∈ primesOver (X-Ca) F[C]) → relNorm F[X] Q = span {X - C a}`
- **What**: Extends `relNorm_maximalIdealAt` from M_P to all primes in the fiber over (X−a): every prime Q over (X−a) has relNorm Q = (X−a).
- **How**: Shows Q is maximal, lifts to a smooth point P' via `exists_smoothPoint_of_isMaximal`, proves P'.x = a by comparing two LiesOver relations (span-singleton equality argument), then applies `relNorm_maximalIdealAt`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.exists_smoothPoint_of_isMaximal`, `C.maximalIdealAt_liesOver`, `C.relNorm_maximalIdealAt`
- **Used by**: `relNorm_pow_of_mem_primesOverFinset`
- **Visibility**: public
- **Lines**: 1201–1249; proof length: 47 lines
- **Notes**: Proof > 30 lines.

---

## Top-level declarations (lines 1253–1578)

---

### `theorem map_eq_top_of_ne_localization`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (v : HeightOneSpectrum A) → v.asIdeal ≠ M → Ideal.map alg v.asIdeal = ⊤`
- **What**: In a Dedekind domain, a height-one prime different from M becomes the unit ideal in the localization at M.
- **How**: Non-containment `v ⊄ M` gives x ∈ v.asIdeal, x ∉ M; `IsLocalization.AtPrime.isUnit_to_map_iff` shows alg(x) is a unit in the localization; `Ideal.eq_top_of_isUnit_mem` concludes.
- **Hypotheses**: A Dedekind domain, M maximal, v ≠ M (as ideals).
- **Uses from project**: none
- **Used by**: `map_eq_top_of_ne_heightOneSpectrum`, `map_eq_localRing_max_pow_count`
- **Visibility**: public
- **Lines**: 1258–1279; proof length: 20 lines
- **Notes**: None.

---

### `theorem map_eq_top_of_ne_heightOneSpectrum`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → (v : HeightOneSpectrum A) → (hv_ne : v ≠ ⟨M, _, _⟩) → Ideal.map alg v.asIdeal = ⊤`
- **What**: Special-case packaging of `map_eq_top_of_ne_localization` when M is wrapped as a HeightOneSpectrum element.
- **How**: Reduces to `map_eq_top_of_ne_localization` via `HeightOneSpectrum.ext`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom, v ≠ ⟨M,...⟩.
- **Uses from project**: none (calls `map_eq_top_of_ne_localization`)
- **Used by**: `map_eq_localRing_max_pow_count`
- **Visibility**: public
- **Lines**: 1283–1292; proof length: 8 lines
- **Notes**: None.

---

### `theorem map_M_pow_eq_localRing_max_pow`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (n : ℕ) → Ideal.map alg (M^n) = (IsLocalRing.maximalIdeal (Localization.AtPrime M))^n`
- **What**: The map of M^n to the localization equals the n-th power of the local maximal ideal.
- **How**: `Ideal.map_pow` + `Localization.AtPrime.map_eq_maximalIdeal`.
- **Hypotheses**: A Dedekind domain, M maximal.
- **Uses from project**: none
- **Used by**: `count_preservation_M_pow`, `map_eq_localRing_max_pow_count`
- **Visibility**: public
- **Lines**: 1297–1302; proof length: 1 line
- **Notes**: None.

---

### `def Ideal.mapMonoidHom`
- **Type**: `(f : A →+* B) → Ideal A →* Ideal B`
- **What**: Packages `Ideal.map f` as a monoid homomorphism for use with `map_prod`.
- **How**: Structure with `map_one'` via `Ideal.map_top` and `map_mul'` via `Ideal.map_mul f`.
- **Hypotheses**: f a ring homomorphism.
- **Uses from project**: none
- **Used by**: `Ideal.mapMonoidHom_apply`, `Ideal.map_finset_prod`, `map_eq_localRing_max_pow_count`
- **Visibility**: public
- **Lines**: 1306–1311; proof length: 4 lines
- **Notes**: Likely a mathlib candidate; simple packaging lemma.

---

### `@[simp] theorem Ideal.mapMonoidHom_apply`
- **Type**: `(f : A →+* B) → (I : Ideal A) → Ideal.mapMonoidHom f I = Ideal.map f I`
- **What**: The monoid hom evaluates to `Ideal.map`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `Ideal.mapMonoidHom`
- **Used by**: `Ideal.map_finset_prod`
- **Visibility**: public
- **Lines**: 1312–1314; proof length: 1 line
- **Notes**: None.

---

### `theorem Ideal.map_finset_prod`
- **Type**: `(f : A →+* B) → (s : Finset ι) → (g : ι → Ideal A) → Ideal.map f (∏ i ∈ s, g i) = ∏ i ∈ s, Ideal.map f (g i)`
- **What**: `Ideal.map f` distributes over finite products.
- **How**: Routes through `Ideal.mapMonoidHom` and applies `map_prod`.
- **Hypotheses**: None.
- **Uses from project**: `Ideal.mapMonoidHom`, `Ideal.mapMonoidHom_apply`
- **Used by**: `map_eq_localRing_max_pow_count`
- **Visibility**: public
- **Lines**: 1317–1321; proof length: 3 lines
- **Notes**: Likely a mathlib candidate.

---

### `theorem count_self_pow_heightOneSpectrum`
- **Type**: `[IsDedekindDomain R] → (v : HeightOneSpectrum R) → (n : ℕ) → (Associates.mk v.asIdeal).count (Associates.mk (v.asIdeal^n)).factors = n`
- **What**: The count of a height-one prime v in its own n-th power is n.
- **How**: `Associates.mk_pow` + `Associates.count_pow` + `Associates.count_self`.
- **Hypotheses**: R Dedekind domain.
- **Uses from project**: none
- **Used by**: `count_localRing_max_pow`, `count_preservation_M_pow`, `count_relNorm_pow_of_mem_primesOverFinset`
- **Visibility**: public
- **Lines**: 1326–1336; proof length: 9 lines
- **Notes**: Likely a mathlib candidate.

---

### `theorem count_localRing_max_pow`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → (n : ℕ) → count_{local_max} ((local_max)^n).factors = n`
- **What**: The local maximal ideal's self-count in its n-th power is n.
- **How**: Uses `IsLocalization.AtPrime.isDedekindDomain` and `IsDiscreteValuationRing.maximalIdeal` to get a HeightOneSpectrum, then delegates to `count_self_pow_heightOneSpectrum`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom.
- **Uses from project**: `count_self_pow_heightOneSpectrum`
- **Used by**: `Conditional.count_preservation_of_structural_witness`, `count_preservation_M_pow`
- **Visibility**: public
- **Lines**: 1341–1356; proof length: 14 lines
- **Notes**: None.

---

### `Conditional.theorem count_preservation_of_structural_witness`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → (I : Ideal A) → (h_witness : Ideal.map alg I = local_max^(count_M I)) → count_{map alg M} (map alg I).factors = count_M I.factors`
- **What**: Given a structural witness that map alg I = local_max^count_M_I, count preservation follows mechanically.
- **How**: Rewrites using `h_witness`, `Localization.AtPrime.map_eq_maximalIdeal`, `count_localRing_max_pow`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom, structural witness h_witness.
- **Uses from project**: `count_localRing_max_pow`
- **Used by**: `count_preservation_map_localization`
- **Visibility**: public (in `Conditional` namespace)
- **Lines**: 1367–1379; proof length: 9 lines
- **Notes**: In `Conditional` namespace — a scaffold for the unconditional form.

---

### `theorem count_preservation_M_pow`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → (n : ℕ) → count_{map alg M} (map alg (M^n)).factors = count_M (M^n).factors`
- **What**: Count preservation holds unconditionally for I = M^n.
- **How**: `map_M_pow_eq_localRing_max_pow` + `Localization.AtPrime.map_eq_maximalIdeal` + `count_localRing_max_pow` + `count_self_pow_heightOneSpectrum`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom.
- **Uses from project**: `map_M_pow_eq_localRing_max_pow`, `count_localRing_max_pow`, `count_self_pow_heightOneSpectrum`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1385–1399; proof length: 13 lines
- **Notes**: Dead code within this file.

---

### `theorem localization_max_count_eq_map_count`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (u : A) → count_{local_max} (span {alg u}).factors = count_{map alg M} (map alg (span {u})).factors`
- **What**: Rewrites the local-ring count of span{alg u} to the count of the mapped ideals.
- **How**: `Localization.AtPrime.map_eq_maximalIdeal` + `Ideal.map_span` + `Set.image_singleton`.
- **Hypotheses**: A Dedekind domain, M maximal.
- **Uses from project**: none
- **Used by**: `Conditional.count_preservation_localization_of_witness`, `count_preservation_localization`
- **Visibility**: public
- **Lines**: 1416–1432; proof length: 14 lines
- **Notes**: None.

---

### `Conditional.theorem count_preservation_localization_of_witness`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (u : A) → (h_count_pres : ...) → count_{local_max} (span {alg u}).factors = count_M (span {u}).factors`
- **What**: Witness-parametric form: given count preservation for the mapped ideal, derives the local-ring count identity.
- **How**: `localization_max_count_eq_map_count` + `h_count_pres`.
- **Hypotheses**: A Dedekind domain, M maximal, count-preservation witness.
- **Uses from project**: `localization_max_count_eq_map_count`
- **Used by**: unused in file (superseded by the unconditional form)
- **Visibility**: public (in `Conditional` namespace)
- **Lines**: 1447–1462; proof length: 13 lines
- **Notes**: Dead code within this file (superseded).

---

### `theorem map_eq_localRing_max_pow_count`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → {I : Ideal A} → (hI : I ≠ ⊥) → Ideal.map alg I = local_max^(count_M I)`
- **What**: Structural witness: `Ideal.map alg I = local_max^{count_M I}` for any nonzero ideal I. This is the core localization structural content.
- **How**: Factors I as `∏ᶠ v, v.maxPowDividing I` via `Ideal.finprod_heightOneSpectrum_factorization`, converts to a Finset.prod over a superset S, distributes `Ideal.map` (via `Ideal.map_finset_prod`), for v ≠ M applies `map_eq_top_of_ne_heightOneSpectrum` to collapse the term to ⊤ = 1, for v = M uses `Ideal.map_pow` + `Localization.AtPrime.map_eq_maximalIdeal`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom, I nonzero.
- **Uses from project**: `Ideal.map_finset_prod`, `map_eq_top_of_ne_heightOneSpectrum`, `map_M_pow_eq_localRing_max_pow`
- **Used by**: `count_preservation_map_localization`
- **Visibility**: public
- **Lines**: 1485–1524; proof length: 38 lines
- **Notes**: Proof > 30 lines. This is the mathematical heart of the localization count-preservation chain.

---

### `theorem count_preservation_map_localization`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → {I : Ideal A} → (hI : I ≠ ⊥) → count_{map alg M} (map alg I).factors = count_M I.factors`
- **What**: Count preservation under the localization map: the M-adic multiplicity is preserved by `Ideal.map alg`.
- **How**: Discharges `Conditional.count_preservation_of_structural_witness` using `map_eq_localRing_max_pow_count`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom, I nonzero.
- **Uses from project**: `Conditional.count_preservation_of_structural_witness`, `map_eq_localRing_max_pow_count`
- **Used by**: `count_preservation_localization`
- **Visibility**: public
- **Lines**: 1531–1538; proof length: 3 lines
- **Notes**: None.

---

### `theorem count_preservation_localization`
- **Type**: `[IsDedekindDomain A] → (M : Ideal A) [M.IsMaximal] → (hM_ne : M ≠ ⊥) → (u : A) → count_{local_max} (span {alg u}).factors = count_M (span {u}).factors`
- **What**: Unconditional: the local-ring count of span{alg u} at the local maximal ideal equals the M-adic count of span{u} in A.
- **How**: `u = 0` case: both reduce to `count _ ⊤ = 0` via `Associates.factors_zero`. `u ≠ 0` case: `Ideal.span {u} ≠ ⊥`, apply `localization_max_count_eq_map_count` + `count_preservation_map_localization`.
- **Hypotheses**: A Dedekind domain, M maximal and non-bottom.
- **Uses from project**: `localization_max_count_eq_map_count`, `count_preservation_map_localization`
- **Used by**: `SmoothPlaneCurve.pointValuation_algebraMap_eq_exp_count`
- **Visibility**: public
- **Lines**: 1548–1578; proof length: 29 lines
- **Notes**: None.

---

## `SmoothPlaneCurve` namespace continued (lines 1589–1710)

---

### `theorem pointValuation_algebraMap_eq_exp_count`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (P : C.SmoothPoint) → (hu : u ≠ 0) → C.pointValuation P (alg u) = WithZero.exp(-(count_{M_P} (span{u}).factors : ℤ))`
- **What**: The multiplicative valuation `pointValuation P` of alg u equals `exp(-count_{M_P})` where M_P = maximalIdealAt P.
- **How**: Factors alg u through the localization via `IsScalarTower`, applies `HeightOneSpectrum.valuation_of_algebraMap` to relate valuation to intValuation, expands intValuation via `intValuation_if_neg`, then uses `count_preservation_localization` (of the top-level section) to transport the count from the localization back to F[C].
- **Hypotheses**: F[C] integrally closed, P smooth, u ≠ 0.
- **Uses from project**: `C.maximalIdealAt_isMaximal`, `C.maximalIdealAt_ne_bot`, `C.localRingAt`, `C.pointValuation`, `count_preservation_localization`
- **Used by**: `ord_P_algebraMap_eq_count`
- **Visibility**: public
- **Lines**: 1604–1648; proof length: 43 lines
- **Notes**: Proof > 30 lines.

---

### `theorem ord_P_algebraMap_eq_count`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (P : C.SmoothPoint) → (hu : u ≠ 0) → C.ord_P P (alg u) = (count_{M_P} (span{u}).factors : ℤ) : WithTop ℤ`
- **What**: The additive order `ord_P P (alg u)` equals the M_P-adic count of the principal ideal span{u}.
- **How**: Unfolds `ord_P`, uses `dif_neg` (valuation ≠ 0 since u ≠ 0), applies `pointValuation_algebraMap_eq_exp_count`, then `WithZero.coe_unzero` + `toAdd_ofAdd` + `neg_neg` to recover the count.
- **Hypotheses**: F[C] integrally closed, P smooth, u ≠ 0.
- **Uses from project**: `C.pointValuation`, `C.ord_P`, `C.pointValuation_algebraMap_eq_exp_count`
- **Used by**: `divisorOf_algebraMap_apply_eq_count`
- **Visibility**: public
- **Lines**: 1659–1684; proof length: 24 lines
- **Notes**: None.

---

### `theorem divisorOf_algebraMap_apply_eq_count`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (P : C.SmoothPoint) → (hu : u ≠ 0) → C.divisorOf (alg u) P = (count_{M_P} (span{u}).factors : ℤ)`
- **What**: The affine divisor value at P of alg u equals the M_P-adic count.
- **How**: `SmoothPlaneCurve.divisorOf_apply` + `ord_P_algebraMap_eq_count` + `WithTop.untopD_coe`.
- **Hypotheses**: F[C] integrally closed, P smooth, u ≠ 0.
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `C.ord_P_algebraMap_eq_count`
- **Used by**: `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 1690–1697; proof length: 4 lines
- **Notes**: None.

---

### `theorem relNorm_span_singleton_eq_norm_span`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (u : C.CoordinateRing) → relNorm F[X] (span {u}) = span {Algebra.norm F[X] u}`
- **What**: The relative norm of the principal ideal span{u} is the principal ideal generated by the algebra norm.
- **How**: `Ideal.relNorm_singleton` + `Algebra.intNorm_eq_norm`.
- **Hypotheses**: F[C] integrally closed.
- **Uses from project**: none
- **Used by**: `count_relNorm_singleton_eq_sum_count_fiber`
- **Visibility**: public
- **Lines**: 1704–1708; proof length: 1 line
- **Notes**: None.

---

## Top-level again (lines 1720–2030)

---

### `theorem count_finset_prod_factors`
- **Type**: `[UniqueFactorizationMonoid α] → (hf : ∀ i ∈ s, f i ≠ 0) → (hp : Irreducible p) → p.count (∏ i ∈ s, f i).factors = ∑ i ∈ s, p.count (f i).factors`
- **What**: The multiplicity of an irreducible p at a finite product equals the sum of multiplicities at each factor.
- **How**: Induction on the finset using `Finset.induction_on`, base case `Associates.count_zero`, step case `Associates.count_mul` + inductive hypothesis.
- **Hypotheses**: UFM with nontrivial, all factors nonzero, p irreducible.
- **Uses from project**: none
- **Used by**: `count_relNorm_singleton_eq_sum_count_fiber`
- **Visibility**: public
- **Lines**: 1720–1735; proof length: 14 lines
- **Notes**: Likely a mathlib candidate.

---

### `theorem relNorm_pow_of_mem_primesOverFinset`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → {a : F} → {Q} → (hQ : Q ∈ primesOverFinset (span {X-Ca}) F[C]) → (n : ℕ) → relNorm F[X] (Q^n) = (span {X-Ca})^n`
- **What**: For any prime Q over (X−a), the relNorm of Q^n is (X−a)^n.
- **How**: `map_pow` (relNorm is a monoid-hom) + `relNorm_eq_X_sub_C_of_primesOver`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.relNorm_eq_X_sub_C_of_primesOver`
- **Used by**: `count_relNorm_pow_of_mem_primesOverFinset`
- **Visibility**: public
- **Lines**: 1745–1761; proof length: 15 lines
- **Notes**: Duplicate `[IsIntegrallyClosed]` in signature.

---

### `theorem count_relNorm_pow_of_mem_primesOverFinset`
- **Type**: `... → {Q} → (hQ : Q ∈ primesOverFinset (span {X-Ca}) F[C]) → (n : ℕ) → count_{span {X-Ca}} (relNorm (Q^n)).factors = n`
- **What**: The (X−a)-count of relNorm(Q^n) is exactly n for Q over (X−a).
- **How**: `relNorm_pow_of_mem_primesOverFinset` to get `relNorm(Q^n) = (X-Ca)^n`, then `count_self_pow_heightOneSpectrum`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.relNorm_pow_of_mem_primesOverFinset`, `count_self_pow_heightOneSpectrum`
- **Used by**: `count_relNorm_singleton_eq_sum_count_fiber`
- **Visibility**: public
- **Lines**: 1767–1788; proof length: 20 lines
- **Notes**: Duplicate `[IsIntegrallyClosed]` in signature.

---

### `theorem count_relNorm_singleton_eq_sum_count_fiber`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → {u : C.CoordinateRing} → (hu : u ≠ 0) → (a : F) → count_{(X-Ca)} (span {Algebra.norm F[X] u}).factors = ∑_{Q ∈ primesOverFinset (X-Ca) F[C]} count_Q (span {u}).factors`
- **What**: The (X−a)-adic count of span{N(u)} in F[X] equals the sum over fiber primes Q of the Q-adic counts of span{u} in F[C].
- **How**: Converts N(u) to relNorm via `relNorm_span_singleton_eq_norm_span`, factors span{u} via `Ideal.finprod_heightOneSpectrum_factorization`, distributes relNorm and count, applies `count_relNorm_pow_of_mem_primesOverFinset` (in-fiber contribution = n) and `Associates.count_eq_zero_of_ne` (out-of-fiber contribution = 0, using `relNorm_maximalIdealAt` to identify the prime), then re-indexes via `Finset.sum_bij'`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, u ≠ 0.
- **Uses from project**: `C.relNorm_span_singleton_eq_norm_span`, `C.count_relNorm_pow_of_mem_primesOverFinset`, `C.exists_smoothPoint_of_isMaximal`, `C.relNorm_maximalIdealAt`, `C.maximalIdealAt_liesOver_of_eq_x`, `count_finset_prod_factors`
- **Used by**: `fiber_sum_divisorOf_algMap_eq_count_norm`
- **Visibility**: public
- **Lines**: 1806–2022; proof length: 215 lines
- **Notes**: Proof > 30 lines. This is the longest proof in the file and the technical core of the per-fiber count identity.

---

### `theorem count_X_sub_C_eq_rootMultiplicity`
- **Type**: `{p : Polynomial F} → (hp : p ≠ 0) → (a : F) → count_{span {X-Ca}} (span {p}).factors = p.rootMultiplicity a`
- **What**: The (X−a)-adic count of the principal ideal span{p} equals the root multiplicity of a in p.
- **How**: Decomposes `p = (X−a)^k * q` via `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, splits the ideal product, applies `Associates.count_mul`, `count_pow`, `count_self` for the (X−a)^k part, and `Associates.count_eq_zero_of_ne` (using irreducibility and non-divisibility of (X−a) in q) for the q part.
- **Hypotheses**: p ≠ 0.
- **Uses from project**: none
- **Used by**: `sum_count_X_sub_C_eq_natDegree`
- **Visibility**: public (but in `SmoothPlaneCurve` namespace — actually declared at top level outside namespace according to the file)
- **Lines**: 2032–2089; proof length: 56 lines
- **Notes**: Proof > 30 lines. Likely a mathlib candidate.

---

### `theorem sum_count_X_sub_C_eq_natDegree`
- **Type**: `[IsAlgClosed F] [DecidableEq F] → {p : Polynomial F} → (hp : p ≠ 0) → ∑_{a ∈ p.roots.toFinset} count_{(X-Ca)} (span {p}).factors = p.natDegree`
- **What**: Under IsAlgClosed, the sum of (X−a)-adic counts of span{p} over all roots of p equals natDegree p.
- **How**: Rewrites each count to `rootMultiplicity` via `count_X_sub_C_eq_rootMultiplicity`, then applies `Polynomial.sum_rootMultiplicity_eq_natDegree`.
- **Hypotheses**: F algebraically closed, p ≠ 0.
- **Uses from project**: `SmoothPlaneCurve.count_X_sub_C_eq_rootMultiplicity`
- **Used by**: `SmoothPlaneCurve.divisorOf_algMap_degree_eq_natDegree_norm`
- **Visibility**: public
- **Lines**: 2098–2107; proof length: 8 lines
- **Notes**: None.

---

## `SmoothPlaneCurve` namespace (lines 2118–2439)

---

### `theorem fiber_sum_divisorOf_algMap_eq_count_norm`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] → {u : C.CoordinateRing} → (hu : u ≠ 0) → (a : F) → ∑_{P ∈ {P | P.x = a}.toFinset} C.divisorOf (alg u) P = count_{(X-Ca)} (span {N(u)}).factors`
- **What**: The per-fiber sum of divisor values of alg u over smooth points with x-coordinate a equals the (X−a)-count of the norm ideal.
- **How**: Rewrites each `divisorOf` to count via `divisorOf_algebraMap_apply_eq_count`, applies `count_relNorm_singleton_eq_sum_count_fiber`, then re-indexes the sum from smooth points to primes via `Finset.sum_bij'` using `exists_smoothPoint_of_isMaximal` and `maximalIdealAt_injective`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, u ≠ 0.
- **Uses from project**: `C.divisorOf_algebraMap_apply_eq_count`, `C.count_relNorm_singleton_eq_sum_count_fiber`, `C.smoothPoint_x_preimage_finite`, `C.maximalIdealAt_liesOver_of_eq_x`, `C.exists_smoothPoint_of_isMaximal`, `C.maximalIdealAt_injective`, `C.maximalIdealAt_isMaximal`
- **Used by**: `divisorOf_algMap_degree_eq_natDegree_norm`
- **Visibility**: public
- **Lines**: 2118–2213; proof length: 94 lines
- **Notes**: Proof > 30 lines.

---

### `theorem normAsRatFunc_algebraMap_eq`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (u : C.CoordinateRing) → C.normAsRatFunc (alg u) = algebraMap (Polynomial F) (RatFunc F) (Algebra.norm (Polynomial F) u)`
- **What**: The rational function normAsRatFunc of alg u is the algebraMap of the polynomial norm of u.
- **How**: Unfolds `normAsRatFunc`/`fieldNorm`, uses `Algebra.intNorm_eq_norm`, `Algebra.algebraMap_intNorm_fractionRing`, and `RatFunc.ofFractionRing_algebraMap`.
- **Hypotheses**: F[C] integrally closed.
- **Uses from project**: `C.normAsRatFunc`, `C.fieldNorm`
- **Used by**: `intDegree_normAsRatFunc_algebraMap`
- **Visibility**: public
- **Lines**: 2220–2231; proof length: 9 lines
- **Notes**: None.

---

### `theorem intDegree_normAsRatFunc_algebraMap`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (u : C.CoordinateRing) → (C.normAsRatFunc (alg u)).intDegree = (Algebra.norm (Polynomial F) u).natDegree`
- **What**: The integer degree of normAsRatFunc(alg u) equals the natDegree of the algebra norm polynomial.
- **How**: `normAsRatFunc_algebraMap_eq` + `RatFunc.intDegree_polynomial`.
- **Hypotheses**: F[C] integrally closed.
- **Uses from project**: `C.normAsRatFunc_algebraMap_eq`
- **Used by**: `divisorOf_algMap_degree_eq_natDegree_norm`, `helperB`
- **Visibility**: public
- **Lines**: 2235–2239; proof length: 2 lines
- **Notes**: None.

---

### `theorem divisorOf_algMap_degree_eq_natDegree_norm`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → {u : C.CoordinateRing} → (hu : u ≠ 0) → (C.divisorOf (alg u)).degree = (Algebra.norm F[X] u).natDegree`
- **What**: The degree of the affine divisor of alg u equals the natDegree of the algebra norm N(u).
- **How**: Builds the enclosing finset S as the biUnion of fiber-finsets over roots of N(u). Support of divisorOf lies in S (using `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` + `norm_eval_at_x_of_zero_at_smoothPoint`). Applies `Finsupp.sum_of_support_subset`, `Finset.sum_biUnion`, `fiber_sum_divisorOf_algMap_eq_count_norm`, and `sum_count_X_sub_C_eq_natDegree`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, u ≠ 0.
- **Uses from project**: `C.smoothPoint_x_preimage_finite`, `C.divisorOf`, `C.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`, `C.mem_maximalIdealAt_iff_eval_zero`, `WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq`, `C.norm_eval_at_x_of_zero_at_smoothPoint`, `C.fiber_sum_divisorOf_algMap_eq_count_norm`, `SmoothPlaneCurve.sum_count_X_sub_C_eq_natDegree`
- **Used by**: `helperB`
- **Visibility**: public
- **Lines**: 2256–2316; proof length: 59 lines
- **Notes**: Proof > 30 lines.

---

### `theorem helperB`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → (f : C.FunctionField) → (C.divisorOf f).degree = (C.normAsRatFunc f).intDegree`
- **What**: Helper B (Silverman II.3.1(b)) for arbitrary f ∈ F(C): the degree of the affine divisor equals the integer degree of the norm rational function.
- **How**: `f = 0`: both sides 0. `f ≠ 0`: writes f = alg u / alg v via `IsFractionRing.div_surjective`, applies `divisorOf_mul`, `divisorOf_inv`, `normAsRatFunc_mul`, `normAsRatFunc_inv`, `RatFunc.intDegree_mul`, `intDegree_inv`, then closes using `divisorOf_algMap_degree_eq_natDegree_norm` and `intDegree_normAsRatFunc_algebraMap`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.divisorOf_zero`, `C.normAsRatFunc_zero`, `C.divisorOf_mul`, `C.divisorOf_inv`, `C.normAsRatFunc_mul`, `C.normAsRatFunc_inv`, `C.normAsRatFunc_eq_zero_iff`, `C.divisorOf_algMap_degree_eq_natDegree_norm`, `C.intDegree_normAsRatFunc_algebraMap`
- **Used by**: `projectiveDivisorOf_degree_eq_zero`, `toProjective_eq_projectiveDivisorOf`, `toProjective_eq_projectiveDivisorOf_witness`, `principal_mem_degZero`
- **Visibility**: public
- **Lines**: 2331–2376; proof length: 44 lines
- **Notes**: Proof > 30 lines. The top-level mathematical theorem of the file.

---

### `theorem projectiveDivisorOf_degree_eq_zero`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → (f : C.FunctionField) → (C.projectiveDivisorOf f).degree = 0`
- **What**: Silverman II.3.1(b) unconditional: for any f ∈ F(C), the projective divisor has degree 0.
- **How**: `f = 0`: `projectiveDivisorOf_zero` + `degree_zero`. `f ≠ 0`: `projectiveDivisorOf_degree_eq_zero_of_helperB` + `helperB`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic.
- **Uses from project**: `C.projectiveDivisorOf_zero`, `C.projectiveDivisorOf_degree_eq_zero_of_helperB`, `C.helperB`
- **Used by**: `toProjective_eq_projectiveDivisorOf`, `principal_mem_degZero`
- **Visibility**: public
- **Lines**: 2391–2399; proof length: 7 lines
- **Notes**: None.

---

### `theorem toProjective_eq_projectiveDivisorOf`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → (hf : f ≠ 0) → (hdivZero : (C.divisorOf f).degree = 0) → (C.divisorOf f).toProjective = C.projectiveDivisorOf f`
- **What**: An affine principal divisor of degree zero becomes the projective divisor under `toProjective`.
- **How**: Delegates to `toProjective_eq_projectiveDivisorOf_of_helperB` with `helperB`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, f ≠ 0, affine divisor degree 0.
- **Uses from project**: `C.toProjective_eq_projectiveDivisorOf_of_helperB`, `C.helperB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2405–2410; proof length: 2 lines
- **Notes**: Dead code within this file.

---

### `theorem toProjective_eq_projectiveDivisorOf_witness`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → (hD_aff_principal : C.IsPrincipal D) → (hD_degZero : D.degree = 0) → ∃ g : C.FunctionField, g ≠ 0 ∧ C.projectiveDivisorOf g = D.toProjective`
- **What**: An affine principal divisor of degree 0 is `projectiveDivisorOf g` for some nonzero g.
- **How**: Delegates to `toProjective_eq_projectiveDivisorOf_witness_of_helperB` supplying `helperB` universally.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, D affine-principal and degree-zero.
- **Uses from project**: `C.toProjective_eq_projectiveDivisorOf_witness_of_helperB`, `C.helperB`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2417–2423; proof length: 3 lines
- **Notes**: Dead code within this file.

---

### `theorem principal_mem_degZero`
- **Type**: `[IsAlgClosed F] [IsIntegrallyClosed C.CoordinateRing] [C.toAffine.IsElliptic] [DecidableEq F] → (hD : D ∈ C.projPrincipalSubgroup) → D ∈ ProjectiveDivisor.degZero C`
- **What**: Principal projective divisors lie in the degree-zero sublattice.
- **How**: Gets f from hD, applies `projectiveDivisorOf_degree_eq_zero`.
- **Hypotheses**: F algebraically closed, F[C] integrally closed, C elliptic, D projective-principal.
- **Uses from project**: `C.projPrincipalSubgroup`, `C.projectiveDivisorOf_degree_eq_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2430–2437; proof length: 6 lines
- **Notes**: Dead code within this file (likely consumed by other files).
