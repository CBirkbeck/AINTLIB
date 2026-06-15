# Inventory: ./HasseWeil/Pic0/ToClassSurjective.lean

**File purpose:** Proves surjectivity of `WeierstrassCurve.Affine.Point.toClass` and the group isomorphism `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)` for `[W.IsElliptic]`, unconditionally and axiom-clean. The proof proceeds via genus-1 Riemann–Roch: every nonzero ideal class has a codimension-≤1 representative, codimension-1 ideals are point ideals, and codimension additivity closes the loop.

**Imports:** `Mathlib`, `HasseWeil.Ramification`

**Namespace:** `WeierstrassCurve.Affine.Point`

---

## Declarations

### `def ClassRepresentableByPoints`
- **Type**: `(W : WeierstrassCurve.Affine F) : Prop` — every element of `ClassGroup W.CoordinateRing` is trivial or equals `ClassGroup.mk (XYIdeal' h)` for a nonsingular affine point.
- **What**: The divisor-reduction predicate for genus-1: every degree-0 class is of the form `[(P) − (O)]`.
- **How**: Pure definition (no proof).
- **Hypotheses**: `[Field F]`, `W : WeierstrassCurve.Affine F`
- **Uses from project**: None
- **Used by**: `mem_range_toClass_of_classRep`, `toClass_surjective_of_classRepresentableByPoints`, `classRepresentableByPoints_of_toClass_surjective`, `toClass_surjective_iff_classRepresentableByPoints`, `classRepresentableByPoints_of_integralIdealRep`, `toClass_surjective`, `toClassEquiv`, `toClassEquiv_apply`
- **Visibility**: public
- **Lines**: 102–105 (3 lines, definition)
- **Notes**: Central predicate; heavily used.

---

### `theorem mem_range_toClass_of_classRep`
- **Type**: `(g : ClassGroup W.CoordinateRing) → (g = 1 ∨ ∃ x y h, g = ClassGroup.mk (XYIdeal' h)) → Additive.ofMul g ∈ Set.range (toClass)`
- **What**: Any class representable by a point or trivial lies in the range of `toClass`; uses `toClass_zero` and `toClass_some`.
- **How**: Case split on the disjunction; applies `toClass_zero` / `toClass_some` directly.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `W : WeierstrassCurve.Affine F`
- **Uses from project**: None (uses mathlib `toClass_zero`, `toClass_some`)
- **Used by**: `toClass_surjective_of_classRepresentableByPoints`
- **Visibility**: public
- **Lines**: 109–115 (7 lines)
- **Notes**: None.

---

### `theorem toClass_surjective_of_classRepresentableByPoints`
- **Type**: `ClassRepresentableByPoints W → Function.Surjective (toClass (W := W))`
- **What**: The easy half: the divisor-reduction predicate implies surjectivity of `toClass`.
- **How**: Applies `mem_range_toClass_of_classRep` after unfolding `ClassRepresentableByPoints`; uses `ofMul_toMul`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `mem_range_toClass_of_classRep`, `ClassRepresentableByPoints`
- **Used by**: `toClass_surjective_iff_classRepresentableByPoints`, `toClass_surjective_of_integralIdealRep`, `toClass_surjective`
- **Visibility**: public
- **Lines**: 118–123 (6 lines)
- **Notes**: None.

---

### `theorem classRepresentableByPoints_of_toClass_surjective`
- **Type**: `Function.Surjective (toClass (W := W)) → ClassRepresentableByPoints W`
- **What**: The converse: surjectivity of `toClass` implies the divisor-reduction predicate. Together with the previous lemma gives an iff.
- **How**: For each `g`, lifts a preimage `P` of `Additive.ofMul g`, cases on `P : W.Point`, uses `toClass_zero`/`toClass_some` and injectivity of `Additive.ofMul`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `ClassRepresentableByPoints`
- **Used by**: `toClass_surjective_iff_classRepresentableByPoints`
- **Visibility**: public
- **Lines**: 127–141 (15 lines)
- **Notes**: None.

---

### `theorem toClass_surjective_iff_classRepresentableByPoints`
- **Type**: `Function.Surjective (toClass (W := W)) ↔ ClassRepresentableByPoints W`
- **What**: Records the equivalence between surjectivity of `toClass` and the genus-1 reduction predicate.
- **How**: Pairs the two preceding lemmas.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `classRepresentableByPoints_of_toClass_surjective`, `toClass_surjective_of_classRepresentableByPoints`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 146–149 (4 lines)
- **Notes**: Exposed iff for external use; internally unused.

---

### `noncomputable def toClassEquiv_of_surjective`
- **Type**: `Function.Surjective (toClass (W := W)) → W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`
- **What**: Packages surjectivity plus mathlib's injectivity `toClass_injective` into the AddEquiv via `AddEquiv.ofBijective`.
- **How**: Single call to `AddEquiv.ofBijective toClass ⟨toClass_injective, hsurj⟩`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: None (uses mathlib `toClass_injective`)
- **Used by**: `toClassEquiv_of_surjective_apply`, `toClassEquiv`, `toClassEquiv'`
- **Visibility**: public
- **Lines**: 154–157 (4 lines)
- **Notes**: Core constructor for all three isomorphism variants (`toClassEquiv`, `toClassEquiv'`).

---

### `theorem toClassEquiv_of_surjective_apply`
- **Type**: `toClassEquiv_of_surjective hsurj P = toClass P`
- **What**: Simp lemma: the equiv computes as `toClass`.
- **How**: `rfl`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `toClassEquiv_of_surjective`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 159–163 (5 lines)
- **Notes**: None.

---

### `def IntegralIdealRepresentableByPoints`
- **Type**: `(W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] : Prop` — every nonzero integral ideal `I` has class `1` or `ClassGroup.mk (XYIdeal' h)`.
- **What**: The intermediate reduction predicate: Riemann–Roch step at the level of integral ideals.
- **How**: Pure definition.
- **Hypotheses**: `[Field F]`, `[IsDedekindDomain W.CoordinateRing]`
- **Uses from project**: None
- **Used by**: `classRepresentableByPoints_of_integralIdealRep`, `toClass_surjective_of_integralIdealRep`, `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne`
- **Visibility**: public
- **Lines**: 180–184 (5 lines)
- **Notes**: None.

---

### `theorem classRepresentableByPoints_of_integralIdealRep`
- **Type**: `[IsDedekindDomain W.CoordinateRing] → IntegralIdealRepresentableByPoints W → ClassRepresentableByPoints W`
- **What**: The Dedekind ingredient: every class has an integral representative (`ClassGroup.mk0_surjective`), so the integral reduction gives the full predicate.
- **How**: For any class `g`, obtains an integral representative `I` via `ClassGroup.mk0_surjective`, then applies `hred I`.
- **Hypotheses**: `[Field F]`, `[IsDedekindDomain W.CoordinateRing]` (no `[DecidableEq F]`)
- **Uses from project**: `IntegralIdealRepresentableByPoints`, `ClassRepresentableByPoints`
- **Used by**: `toClass_surjective_of_integralIdealRep`
- **Visibility**: public
- **Lines**: 190–196 (7 lines)
- **Notes**: `omit [DecidableEq F]` annotation present.

---

### `theorem toClass_surjective_of_integralIdealRep`
- **Type**: `[IsDedekindDomain W.CoordinateRing] → IntegralIdealRepresentableByPoints W → Function.Surjective (toClass (W := W))`
- **What**: Surjectivity from the Dedekind instance plus integral reduction — combines the two structural ingredients.
- **How**: Composes `classRepresentableByPoints_of_integralIdealRep` with `toClass_surjective_of_classRepresentableByPoints`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[IsDedekindDomain W.CoordinateRing]`
- **Uses from project**: `classRepresentableByPoints_of_integralIdealRep`, `toClass_surjective_of_classRepresentableByPoints`
- **Used by**: `toClass_surjective_of_classReducesToCodimLEOne`
- **Visibility**: public
- **Lines**: 202–207 (6 lines)
- **Notes**: None.

---

### `theorem finrank_quotient_XYIdeal_eq_one`
- **Type**: `{x y : F} → W.Equation x y → Module.finrank F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) = 1`
- **What**: The quotient of `R` by the point ideal at `(x, y)` is 1-dimensional over `F` (isomorphic to `F`).
- **How**: Uses `CoordinateRing.quotientXYIdealEquiv` (the `R/(X−x, Y−y) ≃ F` isomorphism) and `Module.finrank_self`.
- **Hypotheses**: `[Field F]` (no `DecidableEq`), `W.Equation x y`
- **Uses from project**: None (uses mathlib `CoordinateRing.quotientXYIdealEquiv`)
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 229–232 (4 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem finiteDimensional_quotient_XYIdeal`
- **Type**: `{x y : F} → W.Equation x y → FiniteDimensional F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y))`
- **What**: The quotient by a point ideal is finite-dimensional over `F`.
- **How**: From the `quotientXYIdealEquiv` linear equiv.
- **Hypotheses**: `[Field F]`, `W.Equation x y`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 236–239 (4 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem eq_of_le_of_finrank_quotient_eq`
- **Type**: `J ≤ I → [FiniteDimensional F (R ⧸ J)] → [FiniteDimensional F (R ⧸ I)] → finrank F (R ⧸ J) = finrank F (R ⧸ I) → I = J`
- **What**: Two ideals with the same finite codimension and one contained in the other must be equal — "no room to grow."
- **How**: Constructs the surjection `R/J → R/I` from `J ≤ I`, shows it is injective by `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` (equal finite dimensions), then deduces `I = J` from injectivity.
- **Hypotheses**: `[Field F]`, `J ≤ I`, both quotients finite-dimensional with equal `finrank`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 245–264 (20 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem exists_algHom_ker_eq_of_finrank_quotient_eq_one`
- **Type**: `(I : Ideal W.CoordinateRing) → [Nontrivial (R ⧸ I)] → finrank F (R ⧸ I) = 1 → ∃ φ : R →ₐ[F] F, ∀ r, r ∈ I ↔ φ r = 0`
- **What**: A codimension-1 quotient gives an `F`-algebra map `R → F` whose kernel is exactly `I`; the quotient is a 1-dimensional `F`-algebra hence isomorphic to `F`.
- **How**: Uses `Subalgebra.bot_eq_top_iff_finrank_eq_one` to show `algebraMap F (R⧸I)` is bijective, then forms `AlgEquiv.ofBijective` and composes with the quotient map.
- **Hypotheses**: `[Field F]`, `[Nontrivial (R⧸I)]`, `finrank = 1`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 271–282 (12 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem equation_of_algHom`
- **Type**: `(φ : W.CoordinateRing →ₐ[F] F) → W.Equation (φ X̄) (φ Ȳ)`
- **What**: Any `F`-algebra map `R → F` sends `(X̄, Ȳ)` to a point on the curve.
- **How**: Compares the two ring homomorphisms `φ ∘ mk W` and `evalEval (φ X̄)(φ Ȳ)` using `Polynomial.ringHom_ext'`; both send constants to themselves (via `φ.commutes`) and `X,Y` to the point coordinates. Uses `AdjoinRoot.mk_self = 0`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 289–313 (25 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem algHom_XClass_eq_zero`
- **Type**: `(φ : W.CoordinateRing →ₐ[F] F) → φ (CoordinateRing.XClass W (φ X̄)) = 0`
- **What**: The image of `X̄ − φ(X̄)` under `φ` is zero; shows `XClass` lies in the kernel.
- **How**: Rewrites `XClass` as `mk W (C X) − algebraMap F R x`, then applies `φ.commutes`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 318–327 (10 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem algHom_YClass_eq_zero`
- **Type**: `(φ : W.CoordinateRing →ₐ[F] F) → φ (CoordinateRing.YClass W (C (φ Ȳ))) = 0`
- **What**: The image of `Ȳ − φ(Ȳ)` under `φ` is zero; shows `YClass` lies in the kernel.
- **How**: Same pattern as `algHom_XClass_eq_zero` for the `Y` generator.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `eq_XYIdeal_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 331–339 (9 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem eq_XYIdeal_of_finrank_quotient_eq_one`
- **Type**: `[W.IsElliptic] → (I : Ideal R) → [Nontrivial (R⧸I)] → finrank F (R⧸I) = 1 → ∃ x y (_ : W.Nonsingular x y), I = CoordinateRing.XYIdeal W x (C y)`
- **What**: Every codimension-1 ideal is a point ideal; this is the surjectivity counterpart of mathlib's `natDegree_norm_ne_one`.
- **How**: Extracts an algebra map `φ : R → F` from `exists_algHom_ker_eq_of_finrank_quotient_eq_one`, obtains the point `(x,y)` from `equation_of_algHom`, shows `XYIdeal ≤ I` via `algHom_XClass_eq_zero`/`algHom_YClass_eq_zero`, then uses `eq_of_le_of_finrank_quotient_eq` (both have codimension 1). Under `[W.IsElliptic]` the point is nonsingular via `equation_iff_nonsingular`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `[Nontrivial (R⧸I)]`, `finrank = 1`
- **Uses from project**: `exists_algHom_ker_eq_of_finrank_quotient_eq_one`, `equation_of_algHom`, `algHom_XClass_eq_zero`, `algHom_YClass_eq_zero`, `finiteDimensional_quotient_XYIdeal`, `finrank_quotient_XYIdeal_eq_one`, `eq_of_le_of_finrank_quotient_eq`
- **Used by**: `mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 346–369 (24 lines)
- **Notes**: `omit [DecidableEq F]`. Key capstone of the norm-degree dictionary.

---

### `theorem finiteDimensional_quotient_of_ne_bot`
- **Type**: `[W.IsElliptic] → (I : Ideal W.CoordinateRing) → I ≠ ⊥ → FiniteDimensional F (W.CoordinateRing ⧸ I)`
- **What**: Every nonzero ideal of the coordinate ring has a finite-dimensional quotient over `F`, field-agnostically (no `[Fintype F]`).
- **How**: Uses `Ideal.quotientEquivDirectSum F (CoordinateRing.basis W) hI` (Smith normal form decomposition, each factor `F[X]/(dᵢ)` finite-dimensional) with `Module.Finite.equiv`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ≠ ⊥`
- **Uses from project**: None (uses `CoordinateRing.basis` from mathlib/project)
- **Used by**: `finrank_quotient_smul`, `finrank_quotient_mul`, `exists_mem_norm_natDegree_le`, `exists_codimLEOne_inv`, `classReducesToCodimLEOne_holds` (×7 call sites)
- **Visibility**: public
- **Lines**: 399–402 (4 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 80000` at line 463 covers `finrank_quotient_eq_sum_smithCoeffs` not this one. `omit [DecidableEq F]`. Most-used utility in the file (7 call sites).

---

### `noncomputable def idealNatDegree`
- **Type**: `(J : Ideal F[X]) : ℕ`
- **What**: The natural degree of the (monic) generator of a principal ideal `J` of `F[X]`; packages `finrank F (F[X]⧸J)` polynomially.
- **How**: `(Submodule.IsPrincipal.generator J).natDegree`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `idealNatDegree_span`, `idealNatDegree_mul`, `idealNatDegree_relNorm_mul`, `idealNatDegree_relNorm_span_singleton`
- **Visibility**: public
- **Lines**: 407–408 (2 lines)
- **Notes**: None.

---

### `theorem idealNatDegree_span`
- **Type**: `(g : F[X]) → idealNatDegree (Ideal.span {g}) = g.natDegree`
- **What**: The degree of `⟨g⟩` is `g.natDegree`; the generator of `⟨g⟩` is associated to `g`.
- **How**: Uses `Associated` of `IsPrincipal.generator` with `g`, then `natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ...)`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: `idealNatDegree`
- **Used by**: `idealNatDegree_mul`, `idealNatDegree_relNorm_span_singleton`
- **Visibility**: public
- **Lines**: 413–417 (5 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem idealNatDegree_mul`
- **Type**: `{A B : Ideal F[X]} → A ≠ ⊥ → B ≠ ⊥ → idealNatDegree (A * B) = idealNatDegree A + idealNatDegree B`
- **What**: `idealNatDegree` is additive over products of nonzero ideals.
- **How**: Rewrites `A = ⟨gₐ⟩`, `B = ⟨g_B⟩`, uses `Ideal.span_singleton_mul_span_singleton`, then `idealNatDegree_span` and `natDegree_mul`.
- **Hypotheses**: `[Field F]`, `A ≠ ⊥`, `B ≠ ⊥`
- **Uses from project**: `idealNatDegree`, `idealNatDegree_span`
- **Used by**: `idealNatDegree_relNorm_mul`
- **Visibility**: public
- **Lines**: 423–439 (17 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem idealNatDegree_relNorm_mul`
- **Type**: `[W.IsElliptic] → I ≠ ⊥ → J ≠ ⊥ → idealNatDegree (relNorm F[X] (I * J)) = idealNatDegree (relNorm F[X] I) + idealNatDegree (relNorm F[X] J)`
- **What**: The relative-norm degree invariant is additive over products of nonzero coordinate-ring ideals.
- **How**: Uses `map_mul (Ideal.relNorm F[X])` then `idealNatDegree_mul`, converting nonzero conditions via `Ideal.relNorm_eq_bot_iff`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, both ideals nonzero
- **Uses from project**: `idealNatDegree_mul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 446–452 (7 lines)
- **Notes**: `omit [DecidableEq F]`. Unused within this file (potential dead code, may be used by other files).

---

### `theorem idealNatDegree_relNorm_span_singleton`
- **Type**: `[W.IsElliptic] → {a : W.CoordinateRing} → a ≠ 0 → idealNatDegree (relNorm F[X] ⟨a⟩) = (Algebra.norm F[X] a).natDegree`
- **What**: The relative-norm degree of the principal ideal `⟨a⟩` is the norm degree of `a`.
- **How**: Rewrites via `Ideal.relNorm_singleton`, `Algebra.intNorm_eq_norm`, and `idealNatDegree_span`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `a ≠ 0`
- **Uses from project**: `idealNatDegree_span`, `idealNatDegree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 459–461 (3 lines)
- **Notes**: `omit [DecidableEq F]`. Unused within this file.

---

### `theorem finrank_quotient_eq_sum_smithCoeffs`
- **Type**: `[W.IsElliptic] → (I : Ideal R) → I ≠ ⊥ → finrank F (R ⧸ I) = ∑ i, (Ideal.smithCoeffs (CoordinateRing.basis W) I hI i).natDegree`
- **What**: The `F`-codimension of `R⧸I` equals the sum of Smith-coefficient degrees (from the Smith decomposition of `I`).
- **How**: Uses `Ideal.finrank_quotient_eq_sum` and `finrank_quotient_span_eq_natDegree` for each summand.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ≠ ⊥`
- **Uses from project**: None
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 470–482 (13 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 80000 in` at line 463 (comment: instance search for Smith summands). `omit [DecidableEq F]`. Unused within this file.

---

### `theorem smul_ideal_eq_span_mul`
- **Type**: `(a : W.CoordinateRing) → (I : Ideal R) → a • I = Ideal.span {a} * I`
- **What**: Pointwise scalar multiplication of an ideal by `a` equals multiplication by the principal ideal `⟨a⟩`.
- **How**: Direct element-wise rewriting using `Submodule.mem_smul_pointwise_iff_exists` and `Ideal.mem_span_singleton_mul`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `finrank_quotient_smul`
- **Visibility**: public
- **Lines**: 487–493 (7 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem finrank_quotient_smul`
- **Type**: `[W.IsElliptic] → {a : R} → a ≠ 0 → (I : Ideal R) → I ≠ ⊥ → finrank F (R ⧸ (a • I)) = finrank F (R ⧸ I) + finrank F (R ⧸ ⟨a⟩)`
- **What**: Codimension additivity for multiplication by a principal ideal factor; the short exact sequence `R⧸I → R⧸(a•I) → R⧸⟨a⟩` gives the sum.
- **How**: Uses `Ideal.mulQuot`, `Ideal.quotOfMul`, `Ideal.exact_mulQuot_quotOfMul` to set up the SES, then applies `Module.length_eq_add_of_exact` and converts `Module.length` to `finrank`. Also uses `smul_ideal_eq_span_mul` and `finiteDimensional_quotient_of_ne_bot`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `a ≠ 0`, `I ≠ ⊥`
- **Uses from project**: `smul_ideal_eq_span_mul`, `finiteDimensional_quotient_of_ne_bot`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 502–523 (22 lines)
- **Notes**: `omit [DecidableEq F]`. Unused within this file (superseded by `finrank_quotient_mul`).

---

### `noncomputable def quotIdealMulEquiv`
- **Type**: `[W.IsElliptic] → {I J : Ideal R} → I ≠ ⊥ → J ≠ ⊥ → ((I : Submodule R R) ⧸ comap I.subtype (I*J)) ≃ₗ[R] (R ⧸ J)`
- **What**: The invertible-ideal quotient isomorphism `I/(I·J) ≃ R/J` in a Dedekind domain, the kernel identification for the codimension SES.
- **How**: Constructs transport isomorphisms `μ : I ≃ₗ ↑I` and `ν : R ≃ₗ 1` (via `Submodule.equivMapOfInjective` and `LinearEquiv.ofInjective` applied to the injective `algebraMap R K`), then applies `FractionalIdeal.quotientEquiv` for the invertible-ideal case (with `↑I · ↑J = 1 · ↑(I·J)`), and composes the three transport isomorphisms.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ≠ ⊥`, `J ≠ ⊥`
- **Uses from project**: None (uses `W.FunctionField`, `FaithfulSMul.algebraMap_injective`)
- **Used by**: `finrank_quotient_mul`
- **Visibility**: public
- **Lines**: 558–647 (90 lines)
- **Notes**: `set_option maxHeartbeats 1200000 in` at line 544 (comment: large fractional ideal terms need raised budget). Proof is **90 lines**, the longest in the file.

---

### `theorem finrank_quotient_mul`
- **Type**: `[W.IsElliptic] → {I J : Ideal R} → I ≠ ⊥ → J ≠ ⊥ → finrank F (R ⧸ (I*J)) = finrank F (R ⧸ I) + finrank F (R ⧸ J)`
- **What**: General codimension additivity for products of nonzero ideals.
- **How**: Applies Noether's third isomorphism `Submodule.quotientQuotientEquivQuotient` for the outer quotient, `quotIdealMulEquiv` for the kernel `I/(I·J) ≃ R/J`, then `Submodule.finrank_quotient_add_finrank` for the SES; uses `finiteDimensional_quotient_of_ne_bot` for all three finite-dimensional instances.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ≠ ⊥`, `J ≠ ⊥`
- **Uses from project**: `finiteDimensional_quotient_of_ne_bot`, `quotIdealMulEquiv`
- **Used by**: `exists_codimLEOne_inv`
- **Visibility**: public
- **Lines**: 661–703 (43 lines)
- **Notes**: `set_option maxHeartbeats 800000 in` at line 649 (comment: quotient/restrictScalars defeq checking). Proof >30 lines.

---

### `theorem mk0_eq_mk_XYIdeal'`
- **Type**: `[W.IsElliptic] → {x y : F} → (h : W.Nonsingular x y) → (hmem : XYIdeal W x (C y) ∈ (Ideal R)⁰) → ClassGroup.mk0 ⟨XYIdeal W x (C y), hmem⟩ = ClassGroup.mk (XYIdeal' h)`
- **What**: Equates two notations for the class of a point ideal: `mk0` of the integral ideal equals `mk` of the fractional ideal `XYIdeal'`.
- **How**: Unfolds via `ClassGroup.mk_mk0 W.FunctionField`, then `Units.ext`, `FractionalIdeal.coe_mk0`, `CoordinateRing.XYIdeal'_eq h`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, nonsingularity `h`, membership `hmem`
- **Uses from project**: None
- **Used by**: `mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one`
- **Visibility**: public
- **Lines**: 717–724 (8 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem mk0_eq_one_of_finrank_quotient_eq_zero`
- **Type**: `[W.IsElliptic] → (I : Ideal R) → I ∈ (Ideal R)⁰ → [FiniteDimensional F (R⧸I)] → finrank F (R⧸I) = 0 → ClassGroup.mk0 ⟨I, hmem⟩ = 1`
- **What**: Codimension-0 endpoint: the quotient `R⧸I` being trivial forces `I = ⊤`, which is principal, giving the trivial class.
- **How**: `Module.finrank_zero_iff` gives `Subsingleton (R⧸I)`; `Ideal.Quotient.subsingleton_iff` gives `I = ⊤`; `top_isPrincipal` closes `ClassGroup.mk0_eq_one_iff`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ∈ (Ideal R)⁰`, `finrank = 0`
- **Uses from project**: None
- **Used by**: `classReducesToCodimLEOne_holds`
- **Visibility**: public
- **Lines**: 729–737 (9 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one`
- **Type**: `[W.IsElliptic] → (J : Ideal R) → J ∈ (Ideal R)⁰ → finrank F (R⧸J) = 1 → ∃ x y (h : W.Nonsingular x y), ClassGroup.mk0 ⟨J, hmem⟩ = ClassGroup.mk (XYIdeal' h)`
- **What**: Codimension-1 endpoint: a codimension-1 integral ideal has class equal to that of a point ideal.
- **How**: Uses `eq_XYIdeal_of_finrank_quotient_eq_one` to identify `J` as a point ideal, then `mk0_eq_mk_XYIdeal'` for the class equality.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `J ∈ (Ideal R)⁰`, `finrank = 1`
- **Uses from project**: `eq_XYIdeal_of_finrank_quotient_eq_one`, `mk0_eq_mk_XYIdeal'`
- **Used by**: `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne`
- **Visibility**: public
- **Lines**: 743–753 (11 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `def ClassReducesToCodimLEOne`
- **Type**: `(W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] : Prop` — every `I ∈ (Ideal R)⁰` has `mk0 I = 1` or has a codimension-≤1 class-equivalent representative.
- **What**: The genus-1 Riemann–Roch core predicate: every integral ideal class has a codimension-≤1 representative.
- **How**: Pure definition.
- **Hypotheses**: `[Field F]`, `[IsDedekindDomain W.CoordinateRing]`
- **Uses from project**: None
- **Used by**: `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne`, `toClass_surjective_of_classReducesToCodimLEOne`, `classReducesToCodimLEOne_holds`
- **Visibility**: public
- **Lines**: 761–767 (7 lines)
- **Notes**: None.

---

### `theorem integralIdealRepresentableByPoints_of_classReducesToCodimLEOne`
- **Type**: `[W.IsElliptic] → ClassReducesToCodimLEOne W → IntegralIdealRepresentableByPoints W`
- **What**: The genus-1 reduction predicate implies the integral-ideal representability.
- **How**: For each integral ideal, uses `hred` to get a codimension-≤1 representative; if codimension 0 or 1, applies `mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one` for the codimension-1 case.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`
- **Uses from project**: `IntegralIdealRepresentableByPoints`, `ClassReducesToCodimLEOne`, `mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one`
- **Used by**: `toClass_surjective_of_classReducesToCodimLEOne`
- **Visibility**: public
- **Lines**: 774–781 (8 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem toClass_surjective_of_classReducesToCodimLEOne`
- **Type**: `[W.IsElliptic] → ClassReducesToCodimLEOne W → Function.Surjective (toClass (W := W))`
- **What**: Surjectivity from the genus-1 codimension reduction alone.
- **How**: Composes `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne` with `toClass_surjective_of_integralIdealRep`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[W.IsElliptic]`
- **Uses from project**: `toClass_surjective_of_integralIdealRep`, `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne`
- **Used by**: `toClass_surjective'`
- **Visibility**: public
- **Lines**: 787–791 (5 lines)
- **Notes**: None.

---

### `private theorem two_nsmul_degree_le'`
- **Type**: `{p : F[X]} → {n : ℕ} → p.degree < n → 2 • p.degree ≤ ((2*(n-1) : ℕ) : WithBot ℕ)`
- **What**: Auxiliary degree bound: for `p` of degree less than `n`, `2 deg p ≤ 2(n−1)` in `WithBot ℕ`.
- **How**: Cases on `p = 0`; otherwise converts to `natDegree` and applies `omega`.
- **Hypotheses**: `[Field F]`
- **Uses from project**: None
- **Used by**: `natDegree_norm_basisComb_le`
- **Visibility**: private
- **Lines**: 811–820 (10 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `noncomputable def basisCombMap`
- **Type**: `(W : WeierstrassCurve.Affine F) (a b : ℕ) : (degreeLT F a × degreeLT F b) →ₗ[F] W.CoordinateRing`
- **What**: The linear map `(p, q) ↦ p · 1 + q · Ȳ` from bounded-degree pairs into the coordinate ring; its image is the space used for the Riemann–Roch dimension count.
- **How**: Direct definition of `toFun`; `map_add'` and `map_smul'` proved by `simp/abel/rw`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `CoordinateRing.basis` (via `CoordinateRing.basis W 1`)
- **Used by**: `basisCombMap_ne_zero`, `exists_mem_norm_natDegree_le`, `natDegree_norm_basisComb_le`
- **Visibility**: public
- **Lines**: 826–833 (8 lines)
- **Notes**: None.

---

### `theorem natDegree_norm_basisComb_le`
- **Type**: `{p q : F[X]} → {da db : ℕ} → p.degree < da → q.degree < db → (Algebra.norm F[X] (p • 1 + q • basis W 1)).natDegree ≤ max (2*(da−1)) (2*db+1)`
- **What**: Upper bound on the norm degree of a basis combination `p·1 + q·Ȳ` given degree bounds on `p` and `q`.
- **How**: Uses `CoordinateRing.degree_norm_smul_basis` (the formula `max(2 deg p)(2 deg q + 3)`), then applies `two_nsmul_degree_le'` for the first term and an `omega` argument for the second.
- **Hypotheses**: `[Field F]`, degree bounds on `p` and `q`
- **Uses from project**: `basisCombMap` (implicitly, via `basis W 1`), `two_nsmul_degree_le'`
- **Used by**: `exists_mem_norm_natDegree_le`
- **Visibility**: public
- **Lines**: 840–863 (24 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem basisCombMap_ne_zero`
- **Type**: `{a b : ℕ} → (pq : degreeLT F a × degreeLT F b) → pq ≠ 0 → basisCombMap W a b pq ≠ 0`
- **What**: The map `basisCombMap` sends nonzero inputs to nonzero outputs (injectivity).
- **How**: Via `CoordinateRing.smul_basis_eq_zero` (linear independence of `{1, Ȳ}` over `F[X]`), showing both components must be zero if the sum is zero.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `basisCombMap`
- **Used by**: `exists_mem_norm_natDegree_le`
- **Visibility**: public
- **Lines**: 868–876 (9 lines)
- **Notes**: None.

---

### `theorem exists_mem_norm_natDegree_le`
- **Type**: `[W.IsElliptic] → (I : Ideal R) → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (Algebra.norm F[X] a).natDegree ≤ finrank F (R⧸I) + 1`
- **What**: The genus-1 Riemann–Roch inequality: every nonzero ideal contains a nonzero element of norm degree ≤ codimension + 1. Proved by a dimension-count (subspace of dimension ℓ+1 maps into ℓ-dimensional quotient, kernel nonempty).
- **How**: Sets `da = (ℓ+1)/2 + 1`, `db = ℓ/2`, computes dimension of `degreeLT da × degreeLT db` via `degreeLTEquiv.finrank_eq`, applies rank–nullity `LinearMap.finrank_range_add_finrank_ker` to the composite map `ψ` into `R⧸I`; extracts a nonzero kernel element, verifies its membership and norm bound using `natDegree_norm_basisComb_le`.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`, `I ≠ ⊥`
- **Uses from project**: `finiteDimensional_quotient_of_ne_bot`, `basisCombMap`, `basisCombMap_ne_zero`, `natDegree_norm_basisComb_le`
- **Used by**: `exists_codimLEOne_inv`
- **Visibility**: public
- **Lines**: 887–925 (39 lines)
- **Notes**: `set_option maxHeartbeats 800000 in` at line 878 (comment: rank-nullity dimension count needs raised budget). Proof >30 lines.

---

### `theorem exists_codimLEOne_inv`
- **Type**: `[W.IsElliptic] → (I' : (Ideal R)⁰) → ∃ (J : Ideal R) (hmem : J ∈ (Ideal R)⁰), finrank F (R⧸J) ≤ 1 ∧ ClassGroup.mk0 ⟨J, hmem⟩ = (ClassGroup.mk0 I')⁻¹`
- **What**: For any nonzero integral ideal `I'`, there exists a codimension-≤1 ideal `J` representing the inverse class. The Dedekind factorisation `⟨a⟩ = I' · J` from a small-norm element `a ∈ I'` gives `[J] = [I']⁻¹` and codimension additivity bounds `finrank J ≤ 1`.
- **How**: Applies `exists_mem_norm_natDegree_le` to get `a ∈ I'` with small norm, uses `Ideal.dvd_iff_le.mpr` to factor `⟨a⟩ = I' · J`, verifies `J ≠ ⊥`, then applies `finrank_quotient_mul` and `finrank_quotient_span_eq_natDegree_norm` to bound `finrank J`, and `ClassGroup.mk0` multiplicativity for the class identity.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`
- **Uses from project**: `exists_mem_norm_natDegree_le`, `finrank_quotient_mul`
- **Used by**: `classReducesToCodimLEOne_holds`
- **Visibility**: public
- **Lines**: 943–969 (27 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 80000 in` at line 935 (comment: `(Ideal R)⁰` / class-group coercions need raised instance budget).

---

### `theorem classReducesToCodimLEOne_holds`
- **Type**: `[W.IsElliptic] → ClassReducesToCodimLEOne W`
- **What**: The genus-1 codimension reduction holds unconditionally for an elliptic curve.
- **How**: For each `I`, applies `exists_codimLEOne_inv` to a representative of `(mk0 I)⁻¹`; the resulting codimension-≤1 ideal `J` satisfies `[J] = mk0 I`. Cases on codimension 0 (uses `mk0_eq_one_of_finrank_quotient_eq_zero` and `finiteDimensional_quotient_of_ne_bot`) vs codimension 1.
- **Hypotheses**: `[Field F]`, `[W.IsElliptic]`
- **Uses from project**: `exists_codimLEOne_inv`, `mk0_eq_one_of_finrank_quotient_eq_zero`, `finiteDimensional_quotient_of_ne_bot`, `ClassReducesToCodimLEOne`
- **Used by**: `toClass_surjective'`
- **Visibility**: public
- **Lines**: 976–990 (15 lines)
- **Notes**: `omit [DecidableEq F]`.

---

### `theorem toClass_surjective`
- **Type**: `ClassRepresentableByPoints W → Function.Surjective (toClass (W := W))`
- **What**: Conditional surjectivity — the original form, parametrised by the divisor-reduction hypothesis.
- **How**: Direct call to `toClass_surjective_of_classRepresentableByPoints hrep`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `toClass_surjective_of_classRepresentableByPoints`, `ClassRepresentableByPoints`
- **Used by**: `toClassEquiv`
- **Visibility**: public
- **Lines**: 1001–1003 (3 lines)
- **Notes**: Redundant alias for `toClass_surjective_of_classRepresentableByPoints`.

---

### `noncomputable def toClassEquiv`
- **Type**: `ClassRepresentableByPoints W → W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`
- **What**: Conditional isomorphism `E ≅ Pic⁰(E)`, parametrised by `ClassRepresentableByPoints W`.
- **How**: Applies `toClassEquiv_of_surjective (toClass_surjective hrep)`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `toClassEquiv_of_surjective`, `toClass_surjective`, `ClassRepresentableByPoints`
- **Used by**: `toClassEquiv_apply`
- **Visibility**: public
- **Lines**: 1008–1010 (3 lines)
- **Notes**: Conditional variant; the unconditional `toClassEquiv'` is the main result.

---

### `theorem toClassEquiv_apply`
- **Type**: `toClassEquiv hrep P = toClass P`
- **What**: Simp lemma: the conditional equiv computes as `toClass`.
- **How**: `rfl`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`
- **Uses from project**: `toClassEquiv`, `ClassRepresentableByPoints`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 1013–1015 (3 lines)
- **Notes**: None.

---

### `theorem toClass_surjective'`
- **Type**: `[W.IsElliptic] → Function.Surjective (toClass (W := W))`
- **What**: **Unconditional surjectivity** of `toClass` for an elliptic curve; combines `classReducesToCodimLEOne_holds` with `toClass_surjective_of_classReducesToCodimLEOne`.
- **How**: One-liner: `toClass_surjective_of_classReducesToCodimLEOne classReducesToCodimLEOne_holds`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[W.IsElliptic]`
- **Uses from project**: `toClass_surjective_of_classReducesToCodimLEOne`, `classReducesToCodimLEOne_holds`
- **Used by**: `toClassEquiv'`
- **Visibility**: public
- **Lines**: 1021–1023 (3 lines)
- **Notes**: The main headline theorem of the file.

---

### `noncomputable def toClassEquiv'`
- **Type**: `[W.IsElliptic] → W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`
- **What**: **Unconditional isomorphism** `E ≅ Pic⁰(E)` for an elliptic curve.
- **How**: Applies `toClassEquiv_of_surjective toClass_surjective'`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[W.IsElliptic]`
- **Uses from project**: `toClassEquiv_of_surjective`, `toClass_surjective'`
- **Used by**: `toClassEquiv'_apply`
- **Visibility**: public
- **Lines**: 1028–1030 (3 lines)
- **Notes**: The main headline definition of the file.

---

### `theorem toClassEquiv'_apply`
- **Type**: `[W.IsElliptic] → (P : W.Point) → toClassEquiv' P = toClass P`
- **What**: Simp lemma: the unconditional equiv computes as `toClass`.
- **How**: `rfl`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[W.IsElliptic]`
- **Uses from project**: `toClassEquiv'`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 1033–1035 (3 lines)
- **Notes**: None.

---

## Summary statistics

- **Total declarations**: 41 (3 `def`, 3 `noncomputable def`, 32 `theorem`, 1 `private theorem`, 2 `def` for predicates)
- **Sorries**: none
- **set_option maxHeartbeats**:
  - Line 463: `synthInstance.maxHeartbeats 80000` [instance search for Smith summands]
  - Line 544: `maxHeartbeats 1200000` [large fractional ideal terms]
  - Line 649: `maxHeartbeats 800000` [quotient/restrictScalars defeq]
  - Line 878: `maxHeartbeats 800000` [rank-nullity dimension count]
  - Line 935: `synthInstance.maxHeartbeats 80000` [class-group coercion instance search]
- **Long proofs (>30 lines)**: `quotIdealMulEquiv` (90 lines), `finrank_quotient_mul` (43 lines), `exists_mem_norm_natDegree_le` (39 lines)
- **Key API** (used by 3+ declarations in file): `finiteDimensional_quotient_of_ne_bot` (7 sites), `ClassRepresentableByPoints` (8+ sites), `idealNatDegree` (4 sites), `basisCombMap` (3 sites), `toClassEquiv_of_surjective` (3 sites)
- **Unused in file**: `toClass_surjective_iff_classRepresentableByPoints`, `toClassEquiv_of_surjective_apply`, `idealNatDegree_relNorm_mul`, `idealNatDegree_relNorm_span_singleton`, `finrank_quotient_eq_sum_smithCoeffs`, `finrank_quotient_smul`, `toClassEquiv_apply`, `toClassEquiv'_apply`
