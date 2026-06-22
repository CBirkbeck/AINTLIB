import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

import HasseWeil.MulByIntPullback

/-!
# Isogenies between Elliptic Curves

We define isogenies between elliptic curves and their basic properties,
following Silverman III.4.

## Design

An `Isogeny` carries two pieces of data:
1. **Pullback** `φ* : K(E₂) →ₐ[F] K(E₁)` on function fields.
2. **Group homomorphism** `E₁(F) →+ E₂(F)` on rational points.

The **degree** is *computed* from the pullback as `[K(E₁) : φ*K(E₂)]`
(via `Module.finrank`), not carried as free data. This eliminates circularity
in the Hasse bound proof, where the old axiomatic degree made the argument
self-referential.

The multiplication-by-`n` endomorphism `[n]` gets its pullback from the division-polynomial
construction in `MulByIntPullback.lean`; `mulByInt_degree` proves `deg [n] = n²`.

## Main Definitions

* `HasseWeil.Isogeny`: An isogeny from `W₁` to `W₂`.
* `HasseWeil.Isogeny.degree`: The degree `[K(E₁) : φ*K(E₂)]`.
* `HasseWeil.Isogeny.comp`: Composition of isogenies.
* `HasseWeil.mulByInt`: The multiplication-by-n endomorphism.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4
* [Sutherland, *18.783 Elliptic Curves*], Lecture 7
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

/-- An isogeny `φ : E₁ → E₂` between elliptic curves over a field `F`.

    An isogeny has two components:
    - The **pullback** `φ* : K(E₂) →ₐ[F] K(E₁)` on function fields.
    - The **group homomorphism** `φ : E₁(F) →+ E₂(F)` on rational points.

    Injectivity of the pullback is derived automatically (see `Isogeny.pullback_injective`),
    since any algebra homomorphism from a field is injective.

    The degree is *computed* from the pullback via `Module.finrank`, not stored.

    In the full algebraic-geometric theory, these two components are derived from
    a single morphism of varieties. Here we carry both as data, since constructing
    one from the other requires substantial algebraic geometry not yet in mathlib. -/
structure Isogeny {F : Type*} [Field F] [DecidableEq F]
    (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic] where
  /-- The pullback `φ* : K(E₂) →ₐ[F] K(E₁)` on function fields. -/
  pullback : W₂.FunctionField →ₐ[F] W₁.FunctionField
  /-- The underlying group homomorphism on rational points. -/
  toAddMonoidHom : W₁.Point →+ W₂.Point

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The pullback of an isogeny is injective: any algebra homomorphism from a field
    is injective because the kernel of a ring homomorphism from a field is trivial. -/
theorem pullback_injective (φ : Isogeny W₁ W₂) :
    Function.Injective φ.pullback :=
  φ.pullback.toRingHom.injective

/-- An isogeny `φ : E₁ → E₂` makes `K(E₁)` into a `K(E₂)`-algebra via pullback. -/
@[reducible]
noncomputable def toAlgebra (φ : Isogeny W₁ W₂) :
    Algebra W₂.FunctionField W₁.FunctionField :=
  φ.pullback.toRingHom.toAlgebra

/-- The degree of an isogeny, defined as `[K(E₁) : K(E₂)]` where `K(E₁)` is
    a `K(E₂)`-module via the pullback. This is computed, not stored. -/
noncomputable def degree (φ : Isogeny W₁ W₂) : ℕ :=
  @Module.finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule

/-- Composition of isogenies. -/
noncomputable def comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    Isogeny W₁ W₃ where
  pullback := φ.pullback.comp ψ.pullback
  toAddMonoidHom := ψ.toAddMonoidHom.comp φ.toAddMonoidHom

@[simp] theorem comp_toAddMonoidHom (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).toAddMonoidHom = ψ.toAddMonoidHom.comp φ.toAddMonoidHom := rfl

theorem comp_apply (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) (P : W₁.Point) :
    (ψ.comp φ).toAddMonoidHom P = ψ.toAddMonoidHom (φ.toAddMonoidHom P) := rfl

/-- The algebra map from (ψ∘φ)* factors through φ* and ψ*. -/
theorem comp_algebraMap_eq (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂)
    (x : W₃.FunctionField) :
    (ψ.comp φ).pullback x = φ.pullback (ψ.pullback x) := rfl

/-- **Degree multiplicativity**: `deg(ψ ∘ φ) = deg(φ) · deg(ψ)`.
    Follows from the tower law for field extensions. -/
theorem comp_degree (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).degree = φ.degree * ψ.degree := by
  unfold degree
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.toAlgebra
  letI : Algebra W₃.FunctionField W₂.FunctionField := ψ.toAlgebra
  letI : Algebra W₃.FunctionField W₁.FunctionField := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower W₃.FunctionField W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Free W₂.FunctionField W₁.FunctionField :=
    Module.Free.of_divisionRing _ _
  rw [mul_comm]
  exact (Module.finrank_mul_finrank
    W₃.FunctionField W₂.FunctionField W₁.FunctionField).symm

/-- **No zero divisors in End E (degree form)**: the composition of two isogenies of positive
    degree has positive degree. The degree restatement of "End E is an integral domain", since
    `Isogeny` carries no `Zero`/`Mul` for the `NoZeroDivisors (Isogeny E E)` formulation.
    Reference: Silverman III.4.2(c). -/
theorem comp_degree_pos (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂)
    (hψ : 0 < ψ.degree) (hφ : 0 < φ.degree) :
    0 < (ψ.comp φ).degree := by
  rw [comp_degree]
  exact Nat.mul_pos hφ hψ

/-- The identity isogeny. -/
noncomputable def id (W : Affine F) [W.IsElliptic] : Isogeny W W where
  pullback := AlgHom.id F W.FunctionField
  toAddMonoidHom := AddMonoidHom.id _

@[simp] theorem id_toAddMonoidHom (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).toAddMonoidHom = AddMonoidHom.id _ := rfl

@[simp] theorem id_pullback (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).pullback = AlgHom.id F W.FunctionField := rfl

/-- The identity isogeny has degree 1.
    Reference: Silverman III.4 (basic property of degree). -/
@[simp] theorem id_degree (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).degree = 1 := by
  change @Module.finrank W.FunctionField W.FunctionField _ _
    (Isogeny.id W).toAlgebra.toModule = 1
  exact Module.finrank_self W.FunctionField

/-- Apply an isogeny to a point. -/
def apply (α : Isogeny W₁ W₂) (P : W₁.Point) : W₂.Point :=
  α.toAddMonoidHom P

@[simp] theorem apply_def (α : Isogeny W₁ W₂) (P : W₁.Point) :
    α.apply P = α.toAddMonoidHom P := rfl

-- Every isogeny is a group homomorphism (T-III-4-010 / Silverman III.4.8). Here this
-- is a structural consequence of `Isogeny` carrying `toAddMonoidHom` as a field; the
-- content of Silverman III.4.8 (which uses Pic⁰ in the book) is axiomatized.
/-- **Silverman III.4.8 / T-III-4-010**: every isogeny respects addition. -/
@[simp] theorem apply_add (α : Isogeny W₁ W₂) (P Q : W₁.Point) :
    α.apply (P + Q) = α.apply P + α.apply Q :=
  α.toAddMonoidHom.map_add P Q

/-- **Silverman III.4.8 / T-III-4-010**: every isogeny maps zero to zero. -/
@[simp] theorem apply_zero (α : Isogeny W₁ W₂) :
    α.apply (0 : W₁.Point) = 0 :=
  α.toAddMonoidHom.map_zero

/-- **Silverman III.4.8 / T-III-4-010**: every isogeny respects negation. -/
@[simp] theorem apply_neg (α : Isogeny W₁ W₂) (P : W₁.Point) :
    α.apply (-P) = -α.apply P :=
  α.toAddMonoidHom.map_neg P

/-- **Silverman III.4.8 / T-III-4-010**: every isogeny respects integer scalar mult. -/
theorem apply_zsmul (α : Isogeny W₁ W₂) (n : ℤ) (P : W₁.Point) :
    α.apply (n • P) = n • α.apply P :=
  α.toAddMonoidHom.map_zsmul n P

/-- **T-III-4-010 / Silverman III.4.8** (bundled form): the underlying
    `AddMonoidHom` of an isogeny. (Trivial wrapper; provides a stable name.) -/
def asAddMonoidHom (α : Isogeny W₁ W₂) : W₁.Point →+ W₂.Point :=
  α.toAddMonoidHom

@[simp] theorem asAddMonoidHom_apply (α : Isogeny W₁ W₂) (P : W₁.Point) :
    α.asAddMonoidHom P = α.apply P := rfl

end Isogeny

variable {F : Type*} [Field F] [DecidableEq F]

/-- The multiplication-by-n endomorphism `[n]` viewed as an isogeny.

    The group homomorphism is `zsmulAddGroupHom n` (scalar multiplication on `E.Point`).

    The pullback `[n]* : K(E) →ₐ[F] K(E)` is defined via division polynomials:
    for `f ∈ K(E)`, `[n]*(f) = f ∘ [n]`, which can be expressed using the
    division polynomial `ψ_n` and the multiplication formulas. The degree of this
    pullback is `n²` (Silverman III.4.2, Sutherland Theorem 6.9).

    **The `n = 0` branch is an unavoidable junk default, not a placeholder.**
    The zero map `[0] : E → E` is the constant map to `O`; it is *not* an
    isogeny (an isogeny is a nonconstant — hence finite, surjective —
    morphism), so it has no finite function-field comorphism. Consequently
    `Isogeny W W` *cannot* faithfully represent `[0]`: the struct demands a
    pullback `K(E) →ₐ[F] K(E)`, but the honest comorphism of `[0]` lands in
    the constant subfield `F`, giving an infinite-index image (degree `0`/`∞`)
    that no single `AlgHom` of the required type encodes. Since `mulByInt` is a
    total function, the `n = 0` branch returns the arbitrary total-function
    default `AlgHom.id F K(E)` for the pullback (its `toAddMonoidHom` IS the
    genuine zero map, kernel `⊤`). This is the standard Lean "junk value for an
    out-of-domain input" idiom (cf. `x / 0 = 0`), NOT a rotten placeholder: no
    theorem relies on it, because every degree theorem (`mulByInt_degree`,
    `mulByInt_pullbackAlgHom`-driven equalities, `mulByInt_q_pullback_*`
    consumers) carries an explicit `n ≠ 0` / `0 < n` guard, and the two `n = 0`
    call sites use only the genuine point map (`IsogenyKernel`: kernel `= ⊤`).
    Callers needing the zero map at the point level should use
    `zsmulAddGroupHom 0` directly rather than `(mulByInt W 0).toAddMonoidHom`.
    See `.mathlib-quality/isogeny-compatibility-audit.md` (recommendation 4). -/
noncomputable def mulByInt (W : Affine F) [W.IsElliptic] (n : ℤ) : Isogeny W W where
  pullback :=
    if hn : n = 0 then AlgHom.id F W.FunctionField
    else mulByInt_pullbackAlgHom W n hn
  toAddMonoidHom := zsmulAddGroupHom n

@[simp] theorem mulByInt_apply (W : Affine F) [W.IsElliptic] (n : ℤ) (P : W.Point) :
    (mulByInt W n).toAddMonoidHom P = n • P := rfl

section DegreeInfra

variable (F : Type*) [Field F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

private noncomputable instance mulByInt_coordinateRing_module :
    Module F[X] W.toAffine.CoordinateRing :=
  @Algebra.toModule F[X] W.toAffine.CoordinateRing _ _ (inferInstance)

private instance mulByInt_coordinateRing_finite :
    Module.Finite F[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (Affine.CoordinateRing.basis W.toAffine)

omit [W.toAffine.IsElliptic] in
private theorem mulByInt_finrank_coordinateRing_eq_two :
    Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (Affine.CoordinateRing.basis W.toAffine)).trans
    (Fintype.card_fin 2)

private noncomputable instance mulByInt_faithfulSMul_poly_ff :
    FaithfulSMul F[X] W.toAffine.FunctionField where
  eq_of_smul_eq_smul h := by
    have hinj : Function.Injective (algebraMap F[X] W.toAffine.FunctionField) :=
      (IsFractionRing.injective
        W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
        Affine.CoordinateRing.algebraMap_poly_injective
    exact hinj (by simpa only [Algebra.smul_def, mul_one] using h 1)

private noncomputable instance mulByInt_algebra_fracRing_ff :
    Algebra (FractionRing F[X]) W.toAffine.FunctionField :=
  FractionRing.liftAlgebra F[X] W.toAffine.FunctionField

private noncomputable instance mulByInt_scalarTower_fracRing :
    IsScalarTower F[X] (FractionRing F[X]) W.toAffine.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra F[X] W.toAffine.FunctionField

private noncomputable instance mulByInt_isIntegral_poly_coord :
    Algebra.IsIntegral F[X] W.toAffine.CoordinateRing :=
  Algebra.IsIntegral.of_finite F[X] W.toAffine.CoordinateRing

private noncomputable instance mulByInt_faithfulSMul_poly_coord :
    FaithfulSMul F[X] W.toAffine.CoordinateRing where
  eq_of_smul_eq_smul h :=
    Affine.CoordinateRing.algebraMap_poly_injective
      (by simpa only [Algebra.smul_def, mul_one] using h 1)

private noncomputable instance mulByInt_isLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid W.toAffine.CoordinateRing (nonZeroDivisors F[X]))
      W.toAffine.FunctionField := by
  have : Algebra.IsAlgebraic F[X] W.toAffine.CoordinateRing :=
    Algebra.IsIntegral.isAlgebraic
  have := (FaithfulSMul.algebraMap_injective
    F[X] W.toAffine.CoordinateRing).noZeroDivisors _
    (map_zero _) (map_mul _)
  exact (IsLocalization.iff_of_le_of_exists_dvd _
    (nonZeroDivisors W.toAffine.CoordinateRing)
    (map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective F[X] W.toAffine.CoordinateRing) le_rfl)
    fun s hs ↦
      have ⟨r, ne, eq⟩ :=
        (Algebra.IsAlgebraic.isAlgebraic (R := F[X]) s).exists_nonzero_dvd hs
      ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

private noncomputable instance mulByInt_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors F[X])
      (IsScalarTower.toAlgHom F[X]
        W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

omit [W.toAffine.IsElliptic] in
private theorem mulByInt_isBaseChange_coordToFunc :
    IsBaseChange (FractionRing F[X])
      (IsScalarTower.toAlgHom F[X]
        W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors F[X]) ..).mp inferInstance

omit [W.toAffine.IsElliptic] in
private theorem mulByInt_finrank_functionField_eq_two :
    Module.finrank (FractionRing F[X]) W.toAffine.FunctionField = 2 := by
  rw [(mulByInt_isBaseChange_coordToFunc F W).finrank_eq,
    mulByInt_finrank_coordinateRing_eq_two]

omit [W.toAffine.IsElliptic] in
/-- **Silverman III.3.1.1**: The function field `K(E)` of an elliptic curve is a
    degree-2 extension of the rational function field `K(x)`, with basis `{1, Y}`.
    Reference: Silverman III.3.1.1. -/
theorem WeierstrassCurve.degree_functionField_over_kx :
    Module.finrank (FractionRing F[X]) W.toAffine.FunctionField = 2 :=
  mulByInt_finrank_functionField_eq_two F W

omit [W.toAffine.IsElliptic] in
/-- The coordinate ring side of `degree_functionField_over_kx`: the Weierstrass
    coordinate ring is a free `F[X]`-module of rank 2, with basis `{1, Y}`.
    Reference: Silverman III.3.1.1. -/
theorem WeierstrassCurve.degree_coordinateRing_over_polyX :
    Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  mulByInt_finrank_coordinateRing_eq_two F W

end DegreeInfra

section MulByIntFinrank

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

private noncomputable def mulByIntCompAlgHom {n : ℤ} (hn : n ≠ 0) :
    FractionRing F[X] →ₐ[F] W.toAffine.FunctionField :=
  (mulByInt_pullbackAlgHom W n hn).comp
    (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField)

private noncomputable def mulByIntFracRange {n : ℤ} (hn : n ≠ 0) :
    IntermediateField F W.toAffine.FunctionField :=
  (mulByIntCompAlgHom W hn).fieldRange

private theorem mulByIntFracRange_le_fieldRange {n : ℤ} (hn : n ≠ 0) :
    mulByIntFracRange W hn ≤ (mulByInt_pullbackAlgHom W n hn).fieldRange := by
  intro z hz
  rw [mulByIntFracRange, mulByIntCompAlgHom, AlgHom.mem_fieldRange] at hz
  rw [AlgHom.mem_fieldRange]
  obtain ⟨a, ha⟩ := hz
  exact ⟨IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField a, ha⟩

private noncomputable def mulByIntRangeEquiv {n : ℤ} (hn : n ≠ 0) :
    W.toAffine.FunctionField ≃+*
      (mulByInt_pullbackAlgHom W n hn).fieldRange :=
  (AlgEquiv.ofInjective (mulByInt_pullbackAlgHom W n hn)
    (mulByInt_pullbackAlgHom W n hn).toRingHom.injective).toRingEquiv

private theorem mulByIntCompAlgHom_algebraMap_X {n : ℤ} (hn : n ≠ 0) :
    mulByIntCompAlgHom W hn
      (algebraMap F[X] (FractionRing F[X]) Polynomial.X) = mulByInt_x W n := by
  change mulByInt_pullbackAlgHom W n hn
    (algebraMap (FractionRing F[X]) W.toAffine.FunctionField
      (algebraMap F[X] (FractionRing F[X]) Polynomial.X)) = _
  rw [show algebraMap (FractionRing F[X]) W.toAffine.FunctionField
      (algebraMap F[X] (FractionRing F[X]) Polynomial.X) =
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap F[X] W.toAffine.CoordinateRing Polynomial.X) by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]]
  change mulByInt_pullbackRingHom W n hn
    (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap F[X] W.toAffine.CoordinateRing Polynomial.X)) = _
  rw [mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  change mulByInt_coordHom W n hn (algebraMap F[X] W.toAffine.CoordinateRing Polynomial.X) = _
  rw [show algebraMap F[X] W.toAffine.CoordinateRing Polynomial.X =
    Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) from rfl]
  rw [mulByInt_coordHom, AdjoinRoot.lift_mk]
  simp [Polynomial.eval₂_C, mulByInt_xHom, mulByInt_x]

private theorem mulByInt_x_mem_mulByIntFracRange {n : ℤ} (hn : n ≠ 0) :
    mulByInt_x W n ∈ mulByIntFracRange W hn := by
  rw [mulByIntFracRange, AlgHom.mem_fieldRange]
  exact ⟨algebraMap F[X] (FractionRing F[X]) Polynomial.X,
    mulByIntCompAlgHom_algebraMap_X W hn⟩

omit [W.toAffine.IsElliptic] [DecidableEq F] in
private theorem adjoin_algebraMap_X_eq_top :
    IntermediateField.adjoin F
      ({algebraMap F[X] (FractionRing F[X]) Polynomial.X} : Set (FractionRing F[X])) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨p, q, _, hpq⟩ := IsFractionRing.div_surjective (A := F[X]) z
  rw [← hpq]
  set S := IntermediateField.adjoin F
    ({algebraMap F[X] (FractionRing F[X]) Polynomial.X} : Set (FractionRing F[X]))
  have hmem : ∀ f : F[X], algebraMap F[X] (FractionRing F[X]) f ∈ S := by
    intro f
    have : algebraMap F[X] (FractionRing F[X]) f =
        Polynomial.aeval (algebraMap F[X] (FractionRing F[X]) Polynomial.X) f := by
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq]
      | monomial n a =>
        simp only [Polynomial.aeval_monomial]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        congr 1
    rw [this]
    exact IntermediateField.algebra_adjoin_le_adjoin F _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  exact S.div_mem (hmem p) (hmem q)

private theorem mulByIntFracRange_eq_adjoin {n : ℤ} (hn : n ≠ 0) :
    mulByIntFracRange W hn =
      IntermediateField.adjoin F ({mulByInt_x W n} : Set W.toAffine.FunctionField) := by
  rw [mulByIntFracRange, AlgHom.fieldRange_eq_map,
    show (⊤ : IntermediateField F (FractionRing F[X])) =
      IntermediateField.adjoin F
        ({algebraMap F[X] (FractionRing F[X]) Polynomial.X} :
          Set (FractionRing F[X])) from
      adjoin_algebraMap_X_eq_top.symm,
    IntermediateField.adjoin_map, Set.image_singleton,
    mulByIntCompAlgHom_algebraMap_X W hn]

omit [DecidableEq F] in
private theorem max_natDegree_num_denom_mulByInt {n : ℤ} (hn : n ≠ 0) :
    max (RatFunc.num (algebraMap F[X] (RatFunc F) (W.Φ n) /
            algebraMap F[X] (RatFunc F) (W.ΨSq n))).natDegree
        (RatFunc.denom (algebraMap F[X] (RatFunc F) (W.Φ n) /
            algebraMap F[X] (RatFunc F) (W.ΨSq n))).natDegree =
      n.natAbs ^ 2 := by
  classical
  have hΨSq_ne : W.ΨSq n ≠ 0 := ΨSq_poly_ne_zero W hn
  have hΔ : W.Δ ≠ 0 := W.coe_Δ' ▸ W.Δ'.ne_zero
  have hcop : IsCoprime (W.Φ n) (W.ΨSq n) := isCoprime_Φ_ΨSq W hΔ hn
  have hgu : IsUnit (GCDMonoid.gcd (W.Φ n) (W.ΨSq n)) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  obtain ⟨c, hc_unit, hgcd_eq⟩ := Polynomial.isUnit_iff.mp hgu
  have hcinv_ne : c⁻¹ ≠ 0 := inv_ne_zero hc_unit.ne_zero
  rw [RatFunc.num_div, RatFunc.denom_div _ hΨSq_ne]
  have hΨSq_div_ne : W.ΨSq n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n) ≠ 0 := by
    rw [← hgcd_eq, Polynomial.div_C]
    exact mul_ne_zero hΨSq_ne (Polynomial.C_ne_zero.mpr hcinv_ne)
  have hlc_ne : (W.ΨSq n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n)).leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hΨSq_div_ne)
  have hΦ_nd : (Polynomial.C
      (W.ΨSq n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n)).leadingCoeff⁻¹ *
      (W.Φ n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n))).natDegree = (W.Φ n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc_ne, ← hgcd_eq, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv_ne]
  have hΨSq_nd : (Polynomial.C
      (W.ΨSq n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n)).leadingCoeff⁻¹ *
      (W.ΨSq n / GCDMonoid.gcd (W.Φ n) (W.ΨSq n))).natDegree = (W.ΨSq n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc_ne, ← hgcd_eq, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv_ne]
  rw [show max _ _ = max (W.Φ n).natDegree (W.ΨSq n).natDegree from
    congr_arg₂ max hΦ_nd hΨSq_nd]
  exact degree_mulByN_eq_sq W

omit [DecidableEq F] in
private theorem finrank_ratFunc_mulByInt {n : ℤ} (hn : n ≠ 0) :
    Module.finrank
      (IntermediateField.adjoin F
        ({algebraMap F[X] (RatFunc F) (W.Φ n) /
          algebraMap F[X] (RatFunc F) (W.ΨSq n)} : Set (RatFunc F)))
      (RatFunc F) = n.natAbs ^ 2 := by
  rw [RatFunc.finrank_eq_max_natDegree]
  exact max_natDegree_num_denom_mulByInt W hn

-- `backward.isDefEq.respectTransparency false` lets the `ext`/`change … rfl` compatibility
-- goals for `Algebra.finrank_eq_of_equiv_equiv` close by reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false in
private theorem mulByInt_finrank_aux_fracRange_le {n : ℤ} (hn : n ≠ 0) :
    mulByIntFracRange W hn ≤
      (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField).fieldRange := by
  set aR := (IsScalarTower.toAlgHom F (FractionRing F[X])
    W.toAffine.FunctionField).fieldRange with haR_def
  have h_poly_mem_aR : ∀ p : F[X],
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap F[X] W.toAffine.CoordinateRing p) ∈ aR := by
    intro p
    refine ⟨algebraMap F[X] (FractionRing F[X]) p, ?_⟩
    change algebraMap (FractionRing F[X]) W.toAffine.FunctionField
      (algebraMap F[X] (FractionRing F[X]) p) = _
    rw [← IsScalarTower.algebraMap_apply F[X] (FractionRing F[X]) W.toAffine.FunctionField,
      ← IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField]
  have h_mulByInt_x_mem_aR : mulByInt_x W n ∈ aR := by
    rw [mulByInt_x, Φ_ff, ΨSq_ff]
    exact aR.div_mem (h_poly_mem_aR _) (h_poly_mem_aR _)
  rw [mulByIntFracRange_eq_adjoin]
  exact IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr h_mulByInt_x_mem_aR)

omit [W.toAffine.IsElliptic] [DecidableEq F] in
set_option backward.isDefEq.respectTransparency false in
private theorem mulByInt_finrank_aux_top :
    Module.finrank
      (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField).fieldRange
      W.toAffine.FunctionField = 2 := by
  have := @Algebra.finrank_eq_of_equiv_equiv
    (FractionRing F[X]) W.toAffine.FunctionField _ _ _
    (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField).fieldRange
    W.toAffine.FunctionField _ _ _
    (AlgEquiv.ofInjective
      (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField)
      (IsScalarTower.toAlgHom F (FractionRing F[X])
        W.toAffine.FunctionField).toRingHom.injective
      ).toRingEquiv
    (RingEquiv.refl _) ?_
  · rw [mulByInt_finrank_functionField_eq_two] at this
    exact this.symm
  · ext x; rfl

-- The `FractionRing F[X]` analogue of `finrank_ratFunc_mulByInt`: transferring the latter along
-- the canonical `FractionRing F[X] ≃+* RatFunc F` field isomorphism `e`, which carries `gen_frac`
-- to the generator over `RatFunc F` and hence the adjunction `fracR` isomorphically onto `adjR`.
-- This is the `[K(x) : K([n]*x)] = n²` content that lives entirely over canonical
-- `IntermediateField` instances (unlike the outer `h_mid` step in `aux_total`).
omit [DecidableEq F] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 250000 in
private theorem finrank_fractionRing_mulByInt {n : ℤ} (hn : n ≠ 0) :
    Module.finrank
      (IntermediateField.adjoin F
        ({algebraMap F[X] (FractionRing F[X]) (W.Φ n) /
          algebraMap F[X] (FractionRing F[X]) (W.ΨSq n)} : Set (FractionRing F[X])))
      (FractionRing F[X]) = n.natAbs ^ 2 := by
  set gen_frac := algebraMap F[X] (FractionRing F[X]) (W.Φ n) /
    algebraMap F[X] (FractionRing F[X]) (W.ΨSq n) with hgen_frac_def
  set fracR := IntermediateField.adjoin F ({gen_frac} : Set (FractionRing F[X]))
  let e : FractionRing F[X] ≃+* RatFunc F :=
    (FractionRing.algEquiv F[X] (RatFunc F)).toRingEquiv
  set adjR := IntermediateField.adjoin F
    ({algebraMap F[X] (RatFunc F) (W.Φ n) /
      algebraMap F[X] (RatFunc F) (W.ΨSq n)} : Set (RatFunc F))
  have he_gen : e gen_frac = algebraMap F[X] (RatFunc F) (W.Φ n) /
      algebraMap F[X] (RatFunc F) (W.ΨSq n) := by
    simp only [e, gen_frac, map_div₀]
    congr 1 <;> exact (FractionRing.algEquiv F[X] (RatFunc F)).commutes _
  have he_algebraMap_comm : ∀ c : F,
      e (algebraMap F (FractionRing F[X]) c) = algebraMap F (RatFunc F) c := by
    intro c
    change (FractionRing.algEquiv F[X] (RatFunc F))
      (algebraMap F (FractionRing F[X]) c) = algebraMap F (RatFunc F) c
    rw [show algebraMap F (FractionRing F[X]) c =
      algebraMap F[X] (FractionRing F[X]) (algebraMap F F[X] c) from
      (IsScalarTower.algebraMap_apply F F[X] (FractionRing F[X]) c).symm,
      (FractionRing.algEquiv F[X] (RatFunc F)).commutes,
      IsScalarTower.algebraMap_apply F F[X] (RatFunc F)]
  have he_mem : ∀ x : fracR, e (x : FractionRing F[X]) ∈ adjR := by
    intro ⟨y, hy⟩
    suffices h : ∀ z ∈ IntermediateField.adjoin F
        ({gen_frac} : Set (FractionRing F[X])),
        e z ∈ adjR from h y hy
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx, he_gen]
      exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
    | algebraMap c => rw [he_algebraMap_comm]; exact adjR.algebraMap_mem c
    | add _ _ _ _ ha hb => rw [map_add]; exact adjR.add_mem ha hb
    | inv _ _ ha => rw [map_inv₀]; exact adjR.inv_mem ha
    | mul _ _ _ _ ha hb => rw [map_mul]; exact adjR.mul_mem ha hb
  have he_mem' : ∀ x : adjR, e.symm (x : RatFunc F) ∈ fracR := by
    intro ⟨y, hy⟩
    suffices h : ∀ z ∈ IntermediateField.adjoin F
        ({algebraMap F[X] (RatFunc F) (W.Φ n) /
          algebraMap F[X] (RatFunc F) (W.ΨSq n)} : Set (RatFunc F)),
        e.symm z ∈ fracR from h y hy
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx, ← he_gen, RingEquiv.symm_apply_apply]
      exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
    | algebraMap c =>
      rw [show e.symm (algebraMap F (RatFunc F) c) =
        algebraMap F (FractionRing F[X]) c by
        apply e.injective
        rw [RingEquiv.apply_symm_apply, he_algebraMap_comm]]
      exact fracR.algebraMap_mem c
    | add _ _ _ _ ha hb => rw [map_add]; exact fracR.add_mem ha hb
    | inv _ _ ha => rw [map_inv₀]; exact fracR.inv_mem ha
    | mul _ _ _ _ ha hb => rw [map_mul]; exact fracR.mul_mem ha hb
  let i' : fracR ≃+* adjR := {
    toFun := fun x ↦ ⟨e x, he_mem x⟩
    invFun := fun x ↦ ⟨e.symm x, he_mem' x⟩
    left_inv := fun ⟨y, _⟩ ↦ Subtype.ext (e.symm_apply_apply y)
    right_inv := fun ⟨y, _⟩ ↦ Subtype.ext (e.apply_symm_apply y)
    map_mul' := fun ⟨a, _⟩ ⟨b, _⟩ ↦ Subtype.ext (map_mul e a b)
    map_add' := fun ⟨a, _⟩ ⟨b, _⟩ ↦ Subtype.ext (map_add e a b) }
  rw [show Module.finrank fracR (FractionRing F[X]) =
    Module.finrank adjR (RatFunc F) from
    @Algebra.finrank_eq_of_equiv_equiv fracR (FractionRing F[X]) _ _ _
      adjR (RatFunc F) _ _ _ i' e (by ext ⟨x, hx⟩; rfl)]
  exact finrank_ratFunc_mulByInt W hn

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 250000 in
-- The inner `[K(x) : K([n]*x)] = n²` step (`h_mid`) is stated over the non-canonical
-- `mulByIntFracRange → aR` algebra (the inclusion from `mulByInt_finrank_aux_fracRange_le`), an
-- instance that cannot live in a helper's signature, so it stays inline. After splitting off
-- `aux_fracRange_le`/`aux_top`, the one irreducible step over the default budget is the
-- `Algebra.finrank_eq_of_equiv_equiv` defeq compatibility check for the `fracR ≃+* adjR` equiv
-- (an `ext ⟨x, hx⟩; rfl` through `IntermediateField` subtype coercions). 250000 is the minimal
-- budget that compiles (default 200000 times out at the `isDefEq` for that equiv).
private theorem mulByInt_finrank_aux_total {n : ℤ} (hn : n ≠ 0) :
    Module.finrank (mulByIntFracRange W hn) W.toAffine.FunctionField = 2 * n.natAbs ^ 2 := by
  set aR := (IsScalarTower.toAlgHom F (FractionRing F[X])
    W.toAffine.FunctionField).fieldRange with haR_def
  letI := (IntermediateField.inclusion (mulByInt_finrank_aux_fracRange_le W hn)).toRingHom.toAlgebra
  haveI : IsScalarTower (mulByIntFracRange W hn) aR W.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h2 := Module.finrank_mul_finrank (mulByIntFracRange W hn) aR W.toAffine.FunctionField
  have h_mid : Module.finrank (mulByIntFracRange W hn) aR = n.natAbs ^ 2 := by
    set gen_frac := algebraMap F[X] (FractionRing F[X]) (W.Φ n) /
      algebraMap F[X] (FractionRing F[X]) (W.ΨSq n) with hgen_frac_def
    set fracR := IntermediateField.adjoin F ({gen_frac} : Set (FractionRing F[X]))
    have hgen_image : (IsScalarTower.toAlgHom F (FractionRing F[X])
        W.toAffine.FunctionField) gen_frac = mulByInt_x W n := by
      simp only [gen_frac, map_div₀]
      rw [mulByInt_x, Φ_ff, ΨSq_ff]
      congr 1 <;> exact (IsScalarTower.algebraMap_apply F[X] (FractionRing F[X])
        W.toAffine.FunctionField _).symm
    have hfracR_map : fracR.map (IsScalarTower.toAlgHom F (FractionRing F[X])
        W.toAffine.FunctionField) = mulByIntFracRange W hn := by
      rw [show fracR = IntermediateField.adjoin F ({gen_frac} : Set (FractionRing F[X]))
        from rfl, IntermediateField.adjoin_map, Set.image_singleton, hgen_image,
        mulByIntFracRange_eq_adjoin]
    let i : fracR ≃+* (mulByIntFracRange W hn) :=
      ((IntermediateField.equivMap fracR
        (IsScalarTower.toAlgHom F (FractionRing F[X])
          W.toAffine.FunctionField)).trans
        (IntermediateField.equivOfEq hfracR_map)).toRingEquiv
    let j : (FractionRing F[X]) ≃+* aR :=
      (AlgEquiv.ofInjective
        (IsScalarTower.toAlgHom F (FractionRing F[X]) W.toAffine.FunctionField)
        (IsScalarTower.toAlgHom F (FractionRing F[X])
          W.toAffine.FunctionField).toRingHom.injective).toRingEquiv
    have h_transfer := @Algebra.finrank_eq_of_equiv_equiv
      fracR (FractionRing F[X]) _ _ _
      (mulByIntFracRange W hn) aR _ _ _ i j ?_
    · rw [← h_transfer]
      exact finrank_fractionRing_mulByInt W hn
    · ext ⟨x, hx⟩; rfl
  rw [h_mid, mulByInt_finrank_aux_top W] at h2
  linarith

-- `h_intermediate` (`[[n]*K(E) : K([n]*x)] = 2`) is stated over the non-canonical
-- `mulByIntFracRange → fieldRange` algebra from the inclusion of
-- `mulByIntFracRange_le_fieldRange`, so it cannot be a standalone helper's signature; it is
-- proved inline once that instance is in scope. `aux_total` is the canonical-codomain half
-- and is extracted above.
set_option backward.isDefEq.respectTransparency false in
private theorem mulByInt_finrank {n : ℤ} (hn : n ≠ 0) :
    Module.finrank (mulByInt_pullbackAlgHom W n hn).fieldRange
      W.toAffine.FunctionField = n.natAbs ^ 2 := by
  have hle := mulByIntFracRange_le_fieldRange W hn
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (mulByIntFracRange W hn)
      (mulByInt_pullbackAlgHom W n hn).fieldRange
      W.toAffine.FunctionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h_tower := Module.finrank_mul_finrank (mulByIntFracRange W hn)
    (mulByInt_pullbackAlgHom W n hn).fieldRange W.toAffine.FunctionField
  have h_intermediate : Module.finrank (mulByIntFracRange W hn)
      (mulByInt_pullbackAlgHom W n hn).fieldRange = 2 := by
    let i : (FractionRing F[X]) ≃+* (mulByIntFracRange W hn) :=
      (AlgEquiv.ofInjective (mulByIntCompAlgHom W hn)
        (mulByIntCompAlgHom W hn).toRingHom.injective).toRingEquiv
    let j := mulByIntRangeEquiv W hn
    have := @Algebra.finrank_eq_of_equiv_equiv
      (FractionRing F[X]) W.toAffine.FunctionField _ _ _
      (mulByIntFracRange W hn)
      (mulByInt_pullbackAlgHom W n hn).fieldRange _ _ _ i j ?_
    · rw [mulByInt_finrank_functionField_eq_two] at this
      exact this.symm
    · ext x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, i, j,
        mulByIntRangeEquiv]
      change (mulByIntCompAlgHom W hn x : W.toAffine.FunctionField) =
        ↑(AlgEquiv.ofInjective (mulByInt_pullbackAlgHom W n hn)
          (mulByInt_pullbackAlgHom W n hn).toRingHom.injective
          (algebraMap (FractionRing F[X]) W.toAffine.FunctionField x))
      simp [AlgEquiv.ofInjective_apply, mulByIntCompAlgHom]
  rw [h_intermediate, mulByInt_finrank_aux_total W hn] at h_tower
  linarith

end MulByIntFinrank

/-- The degree of `[n]` is `n²`. Reference: Silverman III.4.2. -/
theorem mulByInt_degree (W : Affine F) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W n).degree = (n ^ 2).toNat := by
  suffices h : (mulByInt W n).degree = n.natAbs ^ 2 by
    rw [h, show (n ^ 2).toNat = n.natAbs ^ 2 by
      have : n ^ 2 = (n.natAbs ^ 2 : ℕ) := by push_cast; simp
      rw [this, Int.toNat_natCast]]
  change @Module.finrank W.FunctionField W.FunctionField
    _ _ (mulByInt W n).toAlgebra.toModule = n.natAbs ^ 2
  have hpb : (mulByInt W n).pullback = mulByInt_pullbackAlgHom W n hn := dif_neg hn
  have hfr : (mulByInt W n).pullback.fieldRange =
      (mulByInt_pullbackAlgHom W n hn).fieldRange := by rw [hpb]
  have := @Algebra.finrank_eq_of_equiv_equiv
    W.FunctionField W.FunctionField _ _
    (mulByInt W n).toAlgebra
    (mulByInt_pullbackAlgHom W n hn).fieldRange W.FunctionField _ _ _
    ((AlgEquiv.ofInjective (mulByInt W n).pullback
      (mulByInt W n).pullback.toRingHom.injective).trans
      (IntermediateField.equivOfEq hfr)).toRingEquiv
    (RingEquiv.refl _) ?_
  · rw [this]; exact mulByInt_finrank W hn
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.coe_refl, id]
    rfl

/-- For nonzero `n`, the multiplication-by-`n` isogeny has positive degree.
    This is Silverman III.4.2(a)'s `[m] ≠ 0` for `m ≠ 0`, restated as a degree
    inequality (since `Isogeny` carries no `Zero` instance to compare against).
    Reference: Silverman III.4.2(a). -/
theorem mulByInt_degree_pos (W : Affine F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    0 < (mulByInt W n).degree := by
  rw [mulByInt_degree W n hn]
  have : (0 : ℤ) < n ^ 2 := by positivity
  omega

/-- For nonzero `n`, the multiplication-by-`n` isogeny has nonzero degree.
    Reference: Silverman III.4.2(a). -/
theorem mulByInt_degree_ne_zero (W : Affine F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (mulByInt W n).degree ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (mulByInt_degree_pos W hn)

section HomTorsionFree

variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The scalar action of `ℤ` on `Hom(E₁, E₂)`: `m • φ = [m]_{E₂} ∘ φ`.
    Reference: Silverman III.4.2(b). -/
noncomputable def Isogeny.zsmul (m : ℤ) (φ : Isogeny W₁ W₂) : Isogeny W₁ W₂ :=
  (mulByInt W₂ m).comp φ

/-- The point map of `m • φ` is `[m] ∘ φ` on rational points. -/
@[simp] theorem Isogeny.zsmul_toAddMonoidHom (m : ℤ) (φ : Isogeny W₁ W₂) :
    (φ.zsmul m).toAddMonoidHom =
      (mulByInt W₂ m).toAddMonoidHom.comp φ.toAddMonoidHom := rfl

/-- The point map of `m • φ` applied to a point `P` gives `m • (φ P)`. -/
theorem Isogeny.zsmul_apply (m : ℤ) (φ : Isogeny W₁ W₂) (P : W₁.Point) :
    (φ.zsmul m).toAddMonoidHom P = m • (φ.toAddMonoidHom P) := by
  simp [Isogeny.zsmul]

/-- The degree of `m • φ` is `φ.degree * (mulByInt m).degree`.
    Reference: Silverman III.4.2(b). -/
theorem Isogeny.zsmul_degree (m : ℤ) (φ : Isogeny W₁ W₂) :
    (φ.zsmul m).degree = φ.degree * (mulByInt W₂ m).degree :=
  Isogeny.comp_degree _ _

/-- **Hom(E₁, E₂) is torsion-free (degree form)**: for `m ≠ 0`, the scalar multiple
    `m • φ` has positive degree whenever `φ` does. This is the substance of
    Silverman III.4.2(b), restated in terms of degrees since `Isogeny` currently
    carries no `Zero`/`SMul ℤ` instances for the typeclass formulation.
    Reference: Silverman III.4.2(b). -/
theorem Isogeny.zsmul_degree_pos {φ : Isogeny W₁ W₂} (hφ : 0 < φ.degree)
    {m : ℤ} (hm : m ≠ 0) :
    0 < (φ.zsmul m).degree := by
  rw [Isogeny.zsmul_degree]
  exact Nat.mul_pos hφ (mulByInt_degree_pos W₂ hm)

end HomTorsionFree

/-- The **m-torsion subgroup** `E[m] = ker [m] = { P ∈ E : [m] P = O }`.
    Reference: Silverman III.4 (definition). -/
noncomputable def torsionSubgroup (W : Affine F) [W.IsElliptic] (m : ℤ) :
    AddSubgroup W.Point :=
  (mulByInt W m).toAddMonoidHom.ker

@[inherit_doc] scoped notation:max E"["m"]" => HasseWeil.torsionSubgroup E m

@[simp] theorem mem_torsionSubgroup (W : Affine F) [W.IsElliptic] (m : ℤ) (P : W.Point) :
    P ∈ W[m] ↔ m • P = 0 := by
  change P ∈ (mulByInt W m).toAddMonoidHom.ker ↔ m • P = 0
  rw [AddMonoidHom.mem_ker, mulByInt_apply]

/-- `E[1] = ⊥` (only zero has order 1). -/
@[simp] theorem torsionSubgroup_one (W : Affine F) [W.IsElliptic] :
    W[(1 : ℤ)] = ⊥ := by
  ext P
  simp [mem_torsionSubgroup]

/-- `E[0] = ⊤` (every point has "0-torsion"). -/
@[simp] theorem torsionSubgroup_zero (W : Affine F) [W.IsElliptic] :
    W[(0 : ℤ)] = ⊤ := by
  ext P
  simp [mem_torsionSubgroup]

/-- `E[-m] = E[m]`: m-torsion is symmetric under negation. -/
theorem torsionSubgroup_neg (W : Affine F) [W.IsElliptic] (m : ℤ) :
    W[(-m)] = W[m] := by
  ext P
  simp only [mem_torsionSubgroup, neg_zsmul, neg_eq_zero]

/-- `E[n] ≤ E[m·n]`: the n-torsion is contained in the m·n-torsion. -/
theorem torsionSubgroup_le_mul (W : Affine F) [W.IsElliptic] (m n : ℤ) :
    W[n] ≤ W[(m * n)] := by
  intro P hP
  simp only [mem_torsionSubgroup] at hP ⊢
  rw [mul_smul, hP, smul_zero]

/-- Over a field with finite point group (e.g., E/F_q), every torsion
    subgroup is automatically finite. -/
instance torsionSubgroup_finite (W : Affine F) [W.IsElliptic] [Finite W.Point] (m : ℤ) :
    Finite (W[m] : AddSubgroup W.Point) :=
  inferInstance

/-- `E[m] ⊓ E[n] = E[gcd(m, n)]`: the torsion subgroup at the gcd is the
    intersection of the individual torsion subgroups. -/
theorem torsionSubgroup_inf (W : Affine F) [W.IsElliptic] (m n : ℤ) :
    W[m] ⊓ W[n] = W[(m.gcd n : ℤ)] := by
  ext P
  simp only [AddSubgroup.mem_inf, mem_torsionSubgroup]
  refine ⟨?_, ?_⟩
  · rintro ⟨hm, hn⟩
    have h_eq : (m.gcd n : ℤ) = m * m.gcdA n + n * m.gcdB n := Int.gcd_eq_gcd_ab m n
    rw [h_eq, add_smul, mul_comm m _, mul_comm n _, mul_smul, mul_smul,
      hm, hn, smul_zero, smul_zero, add_zero]
  · intro hgcd
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ : (m.gcd n : ℤ) ∣ m := Int.gcd_dvd_left ..
      rw [hk, mul_comm, mul_smul, hgcd, smul_zero]
    · obtain ⟨k, hk⟩ : (m.gcd n : ℤ) ∣ n := Int.gcd_dvd_right ..
      rw [hk, mul_comm, mul_smul, hgcd, smul_zero]

/-- Coercion from an endoisogeny to the endomorphism ring `AddMonoid.End W.Point`.
    This forgets the pullback and degree information, retaining only the group hom. -/
def Isogeny.toEnd {W : Affine F} [W.IsElliptic] (α : Isogeny W W) :
    AddMonoid.End W.Point :=
  α.toAddMonoidHom

@[simp] theorem Isogeny.toEnd_apply {W : Affine F} [W.IsElliptic]
    (α : Isogeny W W) (P : W.Point) :
    α.toEnd P = α.toAddMonoidHom P := rfl

end HasseWeil
