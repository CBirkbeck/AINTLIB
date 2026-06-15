# Inventory: ./HasseWeil/Curves/MillerAllChar.lean

**File**: `HasseWeil/Curves/MillerAllChar.lean`
**Import**: `HasseWeil.Curves.Miller` only
**Namespaces**: `HasseWeil.Curves.SmoothPlaneCurve` (lines 44–456), `HasseWeil.Curves` (lines 460–845)
**Lines**: 845 total
**Purpose**: Re-proves the Miller divisor chain (Silverman III.3.4(e)) without `[NeZero (2 : F)]` / `[NeZero (3 : F)]` typeclasses, then derives `miller_hypothesis_holds_allChar`, a witness-parametric κ-reduction, and char-uniform `Pic⁰(E) ≅ E`.

---

## Declarations

### `theorem divisorOf_coordX_sub_const_apply_eq_finsupp_allChar`
- **Type**: `[C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F] (P Q : C.SmoothPoint) : C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) Q = (Finsupp.single P 1 + Finsupp.single P.neg 1 : C.SmoothPoint →₀ ℤ) Q`
- **What**: Pointwise Finsupp identity for the affine divisor of the vertical line `X − P.x` at a smooth point `Q`; char-uniform version of `divisorOf_coordX_sub_const_apply_eq_finsupp` from `Miller.lean:413`.
- **How**: Unfolds the count of `span{XClass P.x}` as a product using `C.span_XClass_eq_maximalIdealAt_neg_mul` + `Associates.count_mul`, then evaluates the count at `P` and `P.neg` via `C.count_maximalIdealAt_self` and `C.count_maximalIdealAt_eq_zero_of_ne`, finishing with `split_ifs; ring`.
- **Hypotheses**: `C` smooth elliptic Weierstrass curve over `F` (field), `CoordinateRing` integrally closed, `DecidableEq F`.
- **Uses from project**: `C.span_XClass_eq_maximalIdealAt_neg_mul`, `C.divisorOf_coordX_sub_const_apply`, `C.count_maximalIdealAt_self`, `C.count_maximalIdealAt_eq_zero_of_ne`, `C.maximalIdealAt_ne_bot`, `C.maximalIdealAt_isMaximal`
- **Used by**: `divisorOf_coordX_sub_const_allChar` (line 116), `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar` (line 336)
- **Visibility**: public
- **Lines**: 60–107 (proof: ~48 lines)
- **Notes**: Proof >30 lines. Reproduces the proof of `Miller.lean:413` with identical structure; `[NeZero 2/3]` were inert in the original.

---

### `theorem divisorOf_coordX_sub_const_allChar`
- **Type**: `[C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F] (P : C.SmoothPoint) : C.divisorOf (C.coordX - algebraMap F C.FunctionField P.x) = Finsupp.single P 1 + Finsupp.single P.neg 1`
- **What**: Full Finsupp equality for the affine divisor of the vertical line; derived from the pointwise version by `Finsupp.ext`.
- **How**: One-liner: `Finsupp.ext fun Q => C.divisorOf_coordX_sub_const_apply_eq_finsupp_allChar P Q`.
- **Hypotheses**: Same as pointwise version.
- **Uses from project**: `divisorOf_coordX_sub_const_apply_eq_finsupp_allChar` (this file)
- **Used by**: `projectiveDivisorOf_coordX_sub_const_allChar` (line 129)
- **Visibility**: public
- **Lines**: 110–116 (proof: 1 line)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_coordX_sub_const_allChar`
- **Type**: `[C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F] (P : C.SmoothPoint) : C.projectiveDivisorOf (C.coordX - algebraMap F C.FunctionField P.x) = Finsupp.single (ProjectiveSmoothPoint.affine P) 1 + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1 − (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1`
- **What**: Full projective divisor of the vertical line function is `(P) + (P.neg) − 2·(∞)`, char-uniformly.
- **How**: Unfolds `projectiveDivisorOf`, rewrites with `divisorOf_coordX_sub_const_allChar`, `ordAtInfty_coordX_sub_const`, `Divisor.toProjective_add`, `Finsupp.mapDomain_single` for individual summands, then closes with `abel`.
- **Hypotheses**: Same as previous.
- **Uses from project**: `divisorOf_coordX_sub_const_allChar` (this file), `C.ordAtInfty_coordX_sub_const`, `Divisor.toProjective_add`, `Divisor.toProjective`
- **Used by**: `vertical_line_principal_allChar` (line 167), `miller_at_addSmoothPoint_principal_allChar` (line 450)
- **Visibility**: public
- **Lines**: 120–153 (proof: ~34 lines)
- **Notes**: Proof >30 lines.

---

### `theorem vertical_line_principal_allChar`
- **Type**: `[C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F] (P : C.SmoothPoint) : SmoothPlaneCurve.ProjIsPrincipal C (Finsupp.single (ProjectiveSmoothPoint.affine P) 1 + Finsupp.single (ProjectiveSmoothPoint.affine P.neg) 1 − (2 : ℤ) • Finsupp.single ProjectiveSmoothPoint.infinity 1)`
- **What**: The projective divisor `(P) + (P.neg) − 2(∞)` is principal on the projective curve (i.e., is the divisor of `coordX − P.x`), in any characteristic.
- **How**: Constructs the witness `⟨C.coordX − algebraMap F C.FunctionField P.x, ne_zero, projective_div_eq⟩` directly, invoking `coordX_sub_const_ne_zero` and `projectiveDivisorOf_coordX_sub_const_allChar`.
- **Hypotheses**: Same as previous.
- **Uses from project**: `C.coordX_sub_const_ne_zero`, `projectiveDivisorOf_coordX_sub_const_allChar` (this file)
- **Used by**: `miller_at_neg_of_some_allChar` (line 488), `miller_at_some_some_degen_allChar` (line 554)
- **Visibility**: public
- **Lines**: 156–167 (proof: 3 lines)
- **Notes**: None.

---

### `theorem count_YClass_linePolynomial_eq_allChar`
- **Type**: `[C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] [DecidableEq F] (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) (Q' : C.SmoothPoint) : (count of YClass · linePoly at Q') + (count of maxIdeal(P+Q) at Q') = (count of XClass · (P+Q).x at Q') + (count of maxIdeal P at Q') + (count of maxIdeal Q at Q')`
- **What**: Pointwise count identity expressing that the chord/tangent ideal factorisation `span{YClass·L} · m_{P+Q} = span{XClass·(P+Q).x} · m_P · m_Q` holds count-wise at every smooth point `Q'`; char-uniform version of `count_YClass_linePolynomial_eq` (`Miller.lean:791`).
- **How**: Uses `C.span_XClass_addSmoothPoint_mul_eq` for the structural ideal equality, then applies `Associates.count_mul` three times (LHS split, RHS split, and structural equality) to expand each product count, finishing with `linarith`.
- **Hypotheses**: `C` smooth elliptic, `CoordinateRing` integrally closed, `DecidableEq F`, `(SP, SQ)` non-degenerate pair (`hxy`).
- **Uses from project**: `C.span_XClass_addSmoothPoint_mul_eq`, `C.maximalIdealAt_ne_bot`, `C.maximalIdealAt_isMaximal`, `WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero`, `WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar` (line 326)
- **Visibility**: public
- **Lines**: 184–309 (proof: ~126 lines)
- **Notes**: Proof >30 lines (longest in file). The proof is a large but entirely mechanical Associates.count_mul expansion; no mathematical novelty beyond `Miller.lean:791`.

---

### `theorem divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar`
- **Type**: `[...] (SP SQ : C.SmoothPoint) (hxy : ...) (Q' : C.SmoothPoint) : C.divisorOf (C.coordY − algebraMap (Polynomial F) ... (linePolynomial SP.x SP.y slope)) Q' = (Finsupp.single SP 1 + Finsupp.single SQ 1 + Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1 : C.SmoothPoint →₀ ℤ) Q'`
- **What**: Pointwise Finsupp identity for the divisor of the chord/tangent line function at a smooth point `Q'`; char-uniform version of `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp` (`Miller.lean:943`).
- **How**: Rewrites via `divisorOf_coordY_sub_algMap_linePolynomial_apply` (from `Miller.lean`), then applies `count_YClass_linePolynomial_eq_allChar` plus the vertical-line identity `divisorOf_coordX_sub_const_apply_eq_finsupp_allChar` for the `XClass` term, with `count_maximalIdealAt_eq_single` for individual point counts, closing with `linarith`.
- **Hypotheses**: Same; `hxy` non-degenerate.
- **Uses from project**: `C.divisorOf_coordY_sub_algMap_linePolynomial_apply`, `count_YClass_linePolynomial_eq_allChar` (this file), `divisorOf_coordX_sub_const_apply_eq_finsupp_allChar` (this file), `C.count_maximalIdealAt_eq_single`
- **Used by**: `divisorOf_coordY_sub_algMap_linePolynomial_allChar` (line 358)
- **Visibility**: public
- **Lines**: 312–343 (proof: ~32 lines)
- **Notes**: Proof >30 lines (borderline).

---

### `theorem divisorOf_coordY_sub_algMap_linePolynomial_allChar`
- **Type**: `[...] (SP SQ : C.SmoothPoint) (hxy : ...) : C.divisorOf (C.coordY − algebraMap ... (linePolynomial ...)) = Finsupp.single SP 1 + Finsupp.single SQ 1 + Finsupp.single (C.addSmoothPoint SP SQ hxy).neg 1`
- **What**: Full Finsupp equality for the divisor of the chord/tangent line function; char-uniform.
- **How**: `Finsupp.ext` applied to the pointwise version.
- **Hypotheses**: Same as pointwise version.
- **Uses from project**: `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar` (this file)
- **Used by**: `projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar` (line 378)
- **Visibility**: public
- **Lines**: 346–359 (proof: 3 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar`
- **Type**: `[...] (SP SQ : C.SmoothPoint) (hxy : ...) : C.projectiveDivisorOf (C.coordY − algebraMap ... (linePolynomial ...)) = Finsupp.single (affine SP) 1 + Finsupp.single (affine SQ) 1 + Finsupp.single (affine (C.addSmoothPoint SP SQ hxy).neg) 1 − (3 : ℤ) • Finsupp.single infinity 1`
- **What**: Full projective divisor of the chord/tangent line function is `(SP) + (SQ) + (SR.neg) − 3(∞)`, char-uniformly.
- **How**: Unfolds `projectiveDivisorOf`, rewrites with `divisorOf_coordY_sub_algMap_linePolynomial_allChar` and `ordAtInfty_coordY_sub_algMap_linePolynomial`, applies `Divisor.toProjective_add` and `Finsupp.mapDomain_single` for each summand, closes with `abel`.
- **Hypotheses**: Same.
- **Uses from project**: `divisorOf_coordY_sub_algMap_linePolynomial_allChar` (this file), `C.ordAtInfty_coordY_sub_algMap_linePolynomial`, `Divisor.toProjective_add`, `Divisor.toProjective`
- **Used by**: `miller_at_addSmoothPoint_principal_allChar` (line 443)
- **Visibility**: public
- **Lines**: 363–410 (proof: ~48 lines)
- **Notes**: Proof >30 lines.

---

### `theorem miller_at_addSmoothPoint_principal_allChar`
- **Type**: `[...] (SP SQ : C.SmoothPoint) (hxy : ¬(SP.x = SQ.x ∧ SP.y = C.toAffine.negY SQ.x SQ.y)) : SmoothPlaneCurve.ProjIsPrincipal C (Finsupp.single (affine SP) 1 + Finsupp.single (affine SQ) 1 − Finsupp.single (affine (C.addSmoothPoint SP SQ hxy)) 1 − Finsupp.single infinity 1)`
- **What**: Miller divisor `(SP) + (SQ) − (SP + SQ) − (∞)` is principal when `(SP, SQ)` is non-degenerate, in any characteristic.
- **How**: Constructs the witness as `f * g⁻¹` where `f` = chord line and `g` = vertical through `SP + SQ`; rewrites using `projectiveDivisorOf_mul`, `projectiveDivisorOf_inv`, `projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar`, and `projectiveDivisorOf_coordX_sub_const_allChar`, then closes with `ring` on the divisor equality.
- **Hypotheses**: Smooth elliptic curve, integrally closed, `DecidableEq F`, non-degenerate pair.
- **Uses from project**: `C.coordY_sub_algMap_linePolynomial_ne_zero`, `C.coordX_sub_const_ne_zero`, `C.projectiveDivisorOf_mul`, `C.projectiveDivisorOf_inv`, `projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar` (this file), `projectiveDivisorOf_coordX_sub_const_allChar` (this file)
- **Used by**: `miller_at_some_some_nondegen_allChar` (line 513)
- **Visibility**: public
- **Lines**: 414–454 (proof: ~41 lines)
- **Notes**: Proof >30 lines. This is the geometric heart of the Miller relation for the non-degenerate case.

---

### `theorem miller_at_neg_of_some_allChar`
- **Type**: `[IsIntegrallyClosed ...] {x y : F} (h_ns : W.Nonsingular x y) : SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩) (Finsupp.single (some x y h_ns).toProjectiveSmoothPoint 1 + Finsupp.single (-some x y h_ns).toProjectiveSmoothPoint 1 − Finsupp.single ((some x y h_ns) + (-some x y h_ns)).toProjectiveSmoothPoint 1 − Finsupp.single infinity 1)`
- **What**: Miller divisor `(P) + (−P) − (P + (−P)) − (∞)` is principal at a concrete `some x y` affine point, in any characteristic.
- **How**: Applies `miller_of_neg_of_vertical_principal` (from `Miller`), converts projective representations via `neg_some_toProjectiveSmoothPoint`, and delegates to `vertical_line_principal_allChar`.
- **Hypotheses**: `W` elliptic, `CoordinateRing` integrally closed, nonsingular point `(x, y)`.
- **Uses from project**: `miller_of_neg_of_vertical_principal`, `WeierstrassCurve.Affine.Point.neg_some_toProjectiveSmoothPoint`, `vertical_line_principal_allChar` (this file)
- **Used by**: **unused in file** (not called by `miller_hypothesis_holds_allChar` or anything else in this file)
- **Visibility**: public
- **Lines**: 468–488 (proof: ~21 lines)
- **Notes**: Dead code within this file. `miller_hypothesis_holds_allChar` handles the `some + zero` case directly via `miller_of_zero_right`, not via this lemma.

---

### `theorem miller_at_some_some_nondegen_allChar`
- **Type**: `[IsIntegrallyClosed ...] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : SmoothPlaneCurve.ProjIsPrincipal ... (Miller divisor (some P) + (some Q) − (P + Q) − ∞)`
- **What**: Miller divisor for two non-degenerate concrete affine points is principal, in any characteristic.
- **How**: Converts `toProjectiveSmoothPoint` via `add_some_some_toProjectiveSmoothPoint` and `rfl` coercions, then delegates to `miller_at_addSmoothPoint_principal_allChar`.
- **Hypotheses**: `W` elliptic, integrally closed, two nonsingular affine points with non-degenerate pair condition.
- **Uses from project**: `WeierstrassCurve.Affine.Point.add_some_some_toProjectiveSmoothPoint`, `miller_at_addSmoothPoint_principal_allChar` (this file)
- **Used by**: `miller_hypothesis_holds_allChar` (line 590)
- **Visibility**: public
- **Lines**: 491–514 (proof: ~24 lines)
- **Notes**: None.

---

### `theorem miller_at_some_some_degen_allChar`
- **Type**: `[IsIntegrallyClosed ...] {x₁ x₂ y₁ y₂ : F} (h₁) (h₂) (hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) : SmoothPlaneCurve.ProjIsPrincipal ... (Miller divisor for P + (−P) = 0)`
- **What**: Miller divisor for the degenerate case `P + Q = 0` (i.e., `Q = -P`) is principal, in any characteristic.
- **How**: Rewrites `P + Q = 0` via `add_of_Y_eq`, converts `0.toProjectiveSmoothPoint = infinity`, identifies `Q.toProjectiveSmoothPoint = affine P.neg` using `SmoothPoint.ext` + `negY_negY`, delegates to `vertical_line_principal_allChar`, and adjusts `2 • infinity` to `infinity + infinity` with `abel`.
- **Hypotheses**: `W` elliptic, integrally closed, nonsingular points with the degenerate condition.
- **Uses from project**: `WeierstrassCurve.Affine.Point.add_of_Y_eq`, `WeierstrassCurve.Affine.negY_negY`, `HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext`, `vertical_line_principal_allChar` (this file)
- **Used by**: `miller_hypothesis_holds_allChar` (line 589)
- **Visibility**: public
- **Lines**: 517–564 (proof: ~48 lines)
- **Notes**: Proof >30 lines. The degenerate case is the most intricate instantiation of the vertical-line result; requires careful SmoothPoint equality via `SmoothPoint.ext`.

---

### `theorem miller_hypothesis_holds_allChar`
- **Type**: `[IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing] : MillerHypothesis W`
- **What**: `MillerHypothesis W` holds in any characteristic (no `[NeZero 2]` / `[NeZero 3]` required): for every `P, Q : W.Point`, the divisor `(P) + (Q) − (P + Q) − (O)` is principal.
- **How**: Case-splits on `P` and `Q` (zero vs. some): zero cases handled by `miller_of_zero_left` / `miller_of_zero_right`; `some + some` split by `by_cases hxy` between degenerate (`miller_at_some_some_degen_allChar`) and non-degenerate (`miller_at_some_some_nondegen_allChar`).
- **Hypotheses**: `W` elliptic affine Weierstrass curve over `F` (field, `DecidableEq F`), `CoordinateRing` integrally closed.
- **Uses from project**: `miller_of_zero_left`, `miller_of_zero_right`, `miller_at_some_some_degen_allChar` (this file), `miller_at_some_some_nondegen_allChar` (this file)
- **Used by**: `divZeroReduce_holds_allChar` (line 727), `afInputs_allChar` (line 775)
- **Visibility**: public
- **Lines**: 570–591 (proof: ~22 lines)
- **Notes**: Main theorem. The proof structure is a standard pattern-match + case analysis.

---

### `theorem general_kappa_reduce_of_miller`
- **Type**: `[IsIntegrallyClosed ...] (h_miller : MillerHypothesis W) (D : ProjectiveDivisor ...) : SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩) D (kappaDivisor W (projectiveDivisorSum W D) + (ProjectiveDivisor.degree D) • Finsupp.single infinity 1)`
- **What**: Witness-parametric form of `general_kappa_reduce` (`Miller.lean:1306`): any projective divisor `D` is linearly equivalent to `κ(Σ D) + (deg D)·(∞)`, where `κ : W.Point → ProjectiveDivisor` is the standard section; takes `MillerHypothesis W` as hypothesis instead of `[NeZero 2/3]`.
- **How**: Induction on `D` as a Finsupp using `Finsupp.induction`; the zero case uses `ProjLinearlyEquiv.refl`; the inductive step rewrites via `projectiveDivisorSum_add/single`, `ProjectiveDivisor.degree_add`, reduces to `single_minus_inf_eq_kappaDivisor` for the single summand, calls `kappaDivisor_zsmul_linEquiv_of_miller` and `kappaDivisor_add_linEquiv_of_miller` for the κ-linearity, then combines pieces via `projPrincipalSubgroup.add_mem`.
- **Hypotheses**: `W` elliptic, `CoordinateRing` integrally closed, `h_miller : MillerHypothesis W`.
- **Uses from project**: `projectiveDivisorSum_zero`, `kappaDivisor_zero`, `ProjectiveDivisor.degree_zero`, `projectiveDivisorSum_add`, `projectiveDivisorSum_single`, `ProjectiveDivisor.degree_add`, `single_minus_inf_eq_kappaDivisor`, `kappaDivisor_zsmul_linEquiv_of_miller`, `kappaDivisor_add_linEquiv_of_miller`, `SmoothPlaneCurve.ProjLinearlyEquiv.refl`, `projPrincipalSubgroup.add_mem`, `projPrincipalSubgroup.neg_mem`
- **Used by**: `divZeroReduce_holds_allChar` (line 726)
- **Visibility**: public
- **Lines**: 604–716 (proof: ~113 lines)
- **Notes**: Proof >30 lines (longest proof in file at ~113 lines). This is a non-trivial inductive argument; the logic precisely mirrors `Miller.lean:1306` but is now parametric on `h_miller`.

---

### `theorem divZeroReduce_holds_allChar`
- **Type**: `[IsIntegrallyClosed ...] : DivZeroReduce W`
- **What**: `DivZeroReduce W` holds in any characteristic: every degree-zero principal divisor is principal via the κ-reduction; char-uniform version of `divZeroReduce_holds`.
- **How**: Applies `general_kappa_reduce_of_miller` with `miller_hypothesis_holds_allChar`, then uses `degree D = 0` (from `ProjectiveDivisor.mem_degZero`) to simplify `0 • ... = 0` and `add_zero`.
- **Hypotheses**: `W` elliptic, `CoordinateRing` integrally closed, `DecidableEq F`.
- **Uses from project**: `general_kappa_reduce_of_miller` (this file), `miller_hypothesis_holds_allChar` (this file), `ProjectiveDivisor.mem_degZero`
- **Used by**: `afInputs_allChar` (line 776)
- **Visibility**: public
- **Lines**: 720–729 (proof: ~10 lines)
- **Notes**: None.

---

### `noncomputable def picZeroIsoE_of_AFInputs_allChar`
- **Type**: `[IsAlgClosed F] [IsDedekindDomain (⟨W⟩).CoordinateRing] [IsIntegrallyClosed ...] (a : AFInputs W) : SmoothPlaneCurve.PicProj₀ (⟨W⟩) ≃+ W.Point`
- **What**: Char-uniform version of `picZeroIsoE_of_AFInputs` (`NoFinitePolesBridge.lean:335`): constructs the `Pic⁰(E) ≅ E` additive equivalence from `AFInputs W`, without `[NeZero 2/3]` hypotheses.
- **How**: Constructs `sigmaBar` via `picZeroSumOfWitness` using `a.h_van` and `principal_mem_degZero`, sets the inverse as `picZeroOfPoint`, proves left/right inverses via `h_inj_of_divZeroReduce` and `picZeroSumOfWitness_picZeroOfPoint`.
- **Hypotheses**: `W` elliptic, algebraically closed `F`, `CoordinateRing` Dedekind + integrally closed; `AFInputs W` bundle.
- **Uses from project**: `SmoothPlaneCurve.principal_mem_degZero`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness`, `picZeroOfPoint`, `h_inj_of_divZeroReduce`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint`
- **Used by**: `picZeroIsoE_allChar` (line 785)
- **Visibility**: public
- **Lines**: 748–766 (definition body: ~18 lines)
- **Notes**: The comment at line 789 claims this still carries `[NeZero 2/3]` but this is stale (the round-2 refactor removed them per line 739–742).

---

### `noncomputable def afInputs_allChar`
- **Type**: `[IsAlgClosed F] [IsDedekindDomain ...] [IsIntegrallyClosed ...] : AFInputs W`
- **What**: Unconditional (all-char) `AFInputs W` bundle: packages `miller_hypothesis_holds_allChar`, `divZeroReduce_holds_allChar`, and `noFinitePolesBridge_unconditional`.
- **How**: Structure literal with the three fields filled by the three char-uniform results.
- **Hypotheses**: `W` elliptic, algebraically closed `F`, Dedekind + integrally closed `CoordinateRing`, `DecidableEq F`.
- **Uses from project**: `miller_hypothesis_holds_allChar` (this file), `divZeroReduce_holds_allChar` (this file), `noFinitePolesBridge_unconditional`
- **Used by**: `picZeroIsoE_allChar` (line 785)
- **Visibility**: public
- **Lines**: 770–778 (definition body: ~8 lines)
- **Notes**: None.

---

### `noncomputable def picZeroIsoE_allChar`
- **Type**: `[IsAlgClosed F] [IsDedekindDomain ...] [IsIntegrallyClosed ...] : SmoothPlaneCurve.PicProj₀ (⟨W⟩) ≃+ W.Point`
- **What**: Unconditional `Pic⁰(E) ≅ E` additive equivalence in any characteristic, assembled from `afInputs_allChar` and `picZeroIsoE_of_AFInputs_allChar`.
- **How**: One-liner applying `picZeroIsoE_of_AFInputs_allChar` to `afInputs_allChar`.
- **Hypotheses**: `W` elliptic, algebraically closed `F`, Dedekind + integrally closed, `DecidableEq F`.
- **Uses from project**: `picZeroIsoE_of_AFInputs_allChar` (this file), `afInputs_allChar` (this file)
- **Used by**: **unused in file** (exported API endpoint)
- **Visibility**: public
- **Lines**: 780–785 (definition body: 1 line)
- **Notes**: Primary export of this file; the main char-uniform Pic⁰ ≅ E result.

---

### `noncomputable def picZeroIsoE_of_AFInputs_witness_pdz_allChar`
- **Type**: `[IsAlgClosed F] [IsDedekindDomain ...] [IsIntegrallyClosed ...] (a : AFInputs W) (h_pdz : ∀ D ∈ projPrincipalSubgroup, D ∈ ProjectiveDivisor.degZero ...) : SmoothPlaneCurve.PicProj₀ (⟨W⟩) ≃+ W.Point`
- **What**: Witness-parametric form of `picZeroIsoE_of_AFInputs` that takes `PrincipalImpliesDegZero W` as an explicit hypothesis (`h_pdz`); intended to be fully char-uniform once `T10-SUB-PRINCIPAL-DEGZERO-ALLCHAR` is closed.
- **How**: Identical construction to `picZeroIsoE_of_AFInputs_allChar` but uses `h_pdz` directly instead of calling `principal_mem_degZero`.
- **Hypotheses**: Same as `picZeroIsoE_of_AFInputs_allChar`, plus explicit `h_pdz`.
- **Uses from project**: `HasseWeil.EC.Isogeny.picZeroSumOfWitness`, `picZeroOfPoint`, `h_inj_of_divZeroReduce`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint`
- **Used by**: **unused in file** (parked/future-use declaration)
- **Visibility**: public
- **Lines**: 822–843 (definition body: ~22 lines)
- **Notes**: Parked/experimental: exists to factor out the `principal_mem_degZero` obstruction for the sub-ticket `T10-SUB-PRINCIPAL-DEGZERO-ALLCHAR`. Nearly identical body to `picZeroIsoE_of_AFInputs_allChar`; potential duplication if the sub-ticket is closed by weakening `NormValuation.lean` instead.

---

## Summary

| Declaration | Kind | Lines | Proof length |
|---|---|---|---|
| `divisorOf_coordX_sub_const_apply_eq_finsupp_allChar` | theorem | 60–107 | ~48 |
| `divisorOf_coordX_sub_const_allChar` | theorem | 110–116 | 1 |
| `projectiveDivisorOf_coordX_sub_const_allChar` | theorem | 120–153 | ~34 |
| `vertical_line_principal_allChar` | theorem | 156–167 | 3 |
| `count_YClass_linePolynomial_eq_allChar` | theorem | 184–309 | ~126 |
| `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp_allChar` | theorem | 312–343 | ~32 |
| `divisorOf_coordY_sub_algMap_linePolynomial_allChar` | theorem | 346–359 | 3 |
| `projectiveDivisorOf_coordY_sub_algMap_linePolynomial_allChar` | theorem | 363–410 | ~48 |
| `miller_at_addSmoothPoint_principal_allChar` | theorem | 414–454 | ~41 |
| `miller_at_neg_of_some_allChar` | theorem | 468–488 | ~21 |
| `miller_at_some_some_nondegen_allChar` | theorem | 491–514 | ~24 |
| `miller_at_some_some_degen_allChar` | theorem | 517–564 | ~48 |
| `miller_hypothesis_holds_allChar` | theorem | 570–591 | ~22 |
| `general_kappa_reduce_of_miller` | theorem | 604–716 | ~113 |
| `divZeroReduce_holds_allChar` | theorem | 720–729 | ~10 |
| `picZeroIsoE_of_AFInputs_allChar` | noncomputable def | 748–766 | ~18 |
| `afInputs_allChar` | noncomputable def | 770–778 | ~8 |
| `picZeroIsoE_allChar` | noncomputable def | 780–785 | 1 |
| `picZeroIsoE_of_AFInputs_witness_pdz_allChar` | noncomputable def | 822–843 | ~22 |

**Total declarations**: 19 (15 theorems, 4 noncomputable defs, 0 instances)
**Sorries**: none
**set_option maxHeartbeats**: none
