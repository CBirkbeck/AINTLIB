/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IsTensorProduct

import HasseWeil.Auxiliary.Universal
import HasseWeil.Isogeny

/-!
# The Frobenius Isogeny via Function Fields

We construct the q-th power Frobenius as a concrete isogeny `π : E → E` using the
function field pullback `π* : K(E) →ₐ[K] K(E)` given by `x ↦ x^q`.

## Main Definitions

* `HasseWeil.frobeniusIsogeny`: The Frobenius as a `PullbackIsogeny K W W`, with pullback
  given by `frobeniusAlgHom K K(E)`.

## Main Results

* `HasseWeil.frobeniusIsogeny_degree`: The Frobenius isogeny has degree `q = #K`.
* `HasseWeil.frobeniusIsogeny_pow_mem_fieldRange`: pure inseparability of `K(E) / K(E)^q`
  (Silverman II.2.11(b)), stated as a power-membership fact.
* `HasseWeil.frobeniusIsogeny_pullback_range`: the pullback image is exactly the `q`-th
  powers in `K(E)` (Silverman II.2.11(a)).

## Implementation notes

The degree `[K(E) : K(E)^q] = q` is obtained from the tower law. Writing `x` for the image
of `X` in the coordinate ring, so `K(E) = K(x, y)`:

* `[K(E) : K(x)] = 2` and `[K(E)^q : K(x^q)] = 2` (the Weierstrass equation is the minimal
  polynomial of `y` over `K(x)`, and of `y^q` over `K(x^q)`);
* `[K(x) : K(x^q)] = q` (computed via `RatFunc.finrank_eq_max_natDegree`, after identifying
  the Frobenius range in `RatFunc K` with `K⟮X^q⟯`);
* the tower law gives `[K(E) : K(E)^q] · 2 = 2 · q`, hence `[K(E) : K(E)^q] = q`.

The Frobenius-twisted `Module.finrank` is reduced to the plain field extension `[K(E) : K(E)^q]`
via `Algebra.finrank_eq_of_equiv_equiv`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.6, II.2.11
-/

open WeierstrassCurve FiniteField
open scoped Polynomial

namespace HasseWeil

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- The `q`-th power Frobenius isogeny `π : E → E`, with function-field pullback the algebra
endomorphism `x ↦ x ^ q` of `K(E)`, where `q = #K`. -/
noncomputable def frobeniusIsogeny : PullbackIsogeny K W.toAffine W.toAffine where
  pullback := frobeniusAlgHom K W.toAffine.FunctionField

omit [DecidableEq K] in
/-- The Frobenius pullback sends `f ↦ f^q`. -/
theorem frobeniusIsogeny_pullback_apply (f : W.toAffine.FunctionField) :
    (frobeniusIsogeny K W).pullback f = f ^ Fintype.card K := by
  change frobeniusAlgHom K W.toAffine.FunctionField f = f ^ Fintype.card K
  rw [coe_frobeniusAlgHom]

private noncomputable def frobeniusRangeEquiv :
    W.toAffine.FunctionField ≃+*
      (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange :=
  (AlgEquiv.ofInjective (frobeniusAlgHom K W.toAffine.FunctionField)
    (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.injective).toRingEquiv

omit [DecidableEq K] [W.toAffine.IsElliptic] in
private theorem frobenius_finrank_eq_fieldRange_finrank :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
      (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.toAlgebra.toModule =
    Module.finrank (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange
      W.toAffine.FunctionField := by
  have := @Algebra.finrank_eq_of_equiv_equiv
    W.toAffine.FunctionField W.toAffine.FunctionField _ _
    (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.toAlgebra
    (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange W.toAffine.FunctionField _ _ _
    (frobeniusRangeEquiv K W) (RingEquiv.refl _) ?_
  · exact this
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.coe_refl, id]
    change ↑(AlgEquiv.ofInjective (frobeniusAlgHom K W.toAffine.FunctionField)
      (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.injective x) =
      (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom x
    simp [AlgEquiv.ofInjective_apply]

/-- Explicit module instance: `K[X]` acts on `CoordinateRing` via the algebra structure. -/
noncomputable instance coordinateRing_module :
    Module K[X] W.toAffine.CoordinateRing :=
  @Algebra.toModule K[X] W.toAffine.CoordinateRing _ _ inferInstance

instance coordinateRing_finite : Module.Finite K[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (Affine.CoordinateRing.basis W.toAffine)

omit [DecidableEq K] [Fintype K] [W.toAffine.IsElliptic] in
/-- The coordinate ring `K[x, y]/(W)` is a free `K[X]`-module of rank `2` (Silverman II.2). -/
theorem finrank_coordinateRing_eq_two :
    Module.finrank K[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (Affine.CoordinateRing.basis W.toAffine)).trans
    (Fintype.card_fin 2)

/-- FaithfulSMul: K[X] acts faithfully on FunctionField (algebraMap is injective). -/
noncomputable instance : FaithfulSMul K[X] W.toAffine.FunctionField :=
  (faithfulSMul_iff_algebraMap_injective K[X] W.toAffine.FunctionField).mpr <|
    (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
      Affine.CoordinateRing.algebraMap_poly_injective

/-- Algebra instance: FractionRing(K[X]) acts on FunctionField. -/
noncomputable instance : Algebra (FractionRing K[X]) W.toAffine.FunctionField :=
  FractionRing.liftAlgebra K[X] W.toAffine.FunctionField

noncomputable instance : IsScalarTower K[X] (FractionRing K[X]) W.toAffine.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra K[X] W.toAffine.FunctionField

/-- FunctionField is a localization of CoordinateRing at the image of K[X]⁰.
    Replicated from mathlib's Algebra.IsAlgebraic.IsFractionRing section
    (RingTheory/Algebraic/Integral.lean:493) which isn't exported. -/
noncomputable instance : Algebra.IsIntegral K[X] W.toAffine.CoordinateRing :=
  Algebra.IsIntegral.of_finite K[X] W.toAffine.CoordinateRing

noncomputable instance : FaithfulSMul K[X] W.toAffine.CoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective K[X] W.toAffine.CoordinateRing).mpr
    Affine.CoordinateRing.algebraMap_poly_injective

private noncomputable instance : IsLocalization
    (Algebra.algebraMapSubmonoid W.toAffine.CoordinateRing (nonZeroDivisors K[X]))
    W.toAffine.FunctionField := by
  have : Algebra.IsAlgebraic K[X] W.toAffine.CoordinateRing := Algebra.IsIntegral.isAlgebraic
  have := (FaithfulSMul.algebraMap_injective K[X] W.toAffine.CoordinateRing).noZeroDivisors _
    (map_zero _) (map_mul _)
  exact (IsLocalization.iff_of_le_of_exists_dvd _ (nonZeroDivisors W.toAffine.CoordinateRing)
    (map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective K[X] W.toAffine.CoordinateRing) le_rfl)
    fun s hs ↦
      have ⟨r, ne, eq⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K[X]) s).exists_nonzero_dvd hs
      ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

/-- IsLocalizedModule for the algebra map CoordinateRing → FunctionField at K[X]⁰. -/
private noncomputable instance : IsLocalizedModule (nonZeroDivisors K[X])
    (IsScalarTower.toAlgHom K[X] W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

omit [DecidableEq K] [Fintype K] [W.toAffine.IsElliptic] in
private theorem isBaseChange_coordToFunc :
    IsBaseChange (FractionRing K[X]) (IsScalarTower.toAlgHom K[X]
      W.toAffine.CoordinateRing W.toAffine.FunctionField).toLinearMap :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors K[X]) ..).mp inferInstance

omit [DecidableEq K] [Fintype K] [W.toAffine.IsElliptic] in
/-- The function field `K(E)` is a `2`-dimensional extension of `K(x) = FractionRing K[X]`. -/
theorem finrank_functionField_eq_two :
    Module.finrank (FractionRing K[X]) W.toAffine.FunctionField = 2 := by
  rw [(isBaseChange_coordToFunc K W).finrank_eq, finrank_coordinateRing_eq_two]

private noncomputable def frobFracRange : IntermediateField K W.toAffine.FunctionField :=
  (frobeniusAlgHom K (FractionRing K[X])).fieldRange.map
    (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField)

omit [DecidableEq K] [W.toAffine.IsElliptic] in
private theorem frobeniusAlgHom_comp_comm :
    (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField).comp
      (frobeniusAlgHom K (FractionRing K[X])) =
    (frobeniusAlgHom K W.toAffine.FunctionField).comp
      (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField) := by
  refine AlgHom.ext fun a => ?_
  change algebraMap (FractionRing K[X]) W.toAffine.FunctionField (a ^ Fintype.card K) =
    (algebraMap (FractionRing K[X]) W.toAffine.FunctionField a) ^ Fintype.card K
  exact map_pow _ a _

omit [DecidableEq K] [W.toAffine.IsElliptic] in
private theorem frobFracRange_le_frobRange :
    frobFracRange K W ≤ (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange := by
  rw [frobFracRange, AlgHom.map_fieldRange, frobeniusAlgHom_comp_comm K W]
  intro z hz
  rw [AlgHom.mem_fieldRange] at hz ⊢
  obtain ⟨a, ha⟩ := hz
  exact ⟨_, ha⟩

omit [DecidableEq K] in
private theorem frobenius_fieldRange_ratFunc :
    (frobeniusAlgHom K (RatFunc K)).fieldRange =
      IntermediateField.adjoin K
        ({(RatFunc.X (K := K)) ^ Fintype.card K} : Set (RatFunc K)) := by
  set q := Fintype.card K
  set Xq : RatFunc K := RatFunc.X ^ q
  set A := IntermediateField.adjoin K ({Xq} : Set (RatFunc K))
  apply le_antisymm
  · rw [AlgHom.fieldRange_eq_map, IntermediateField.map_le_iff_le_comap]
    intro g _
    change frobeniusAlgHom K (RatFunc K) g ∈ A
    simp only [coe_frobeniusAlgHom]
    obtain ⟨p, r, hr, rfl⟩ : ∃ p r : K[X], algebraMap K[X] (RatFunc K) r ≠ 0 ∧
      g = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) r :=
      ⟨g.num, g.denom, RatFunc.algebraMap_ne_zero g.denom_ne_zero, g.num_div_denom.symm⟩
    simp only [div_pow, ← map_pow, ← FiniteField.expand_card (K := K)]
    have hmem : ∀ f : K[X], algebraMap K[X] (RatFunc K) (Polynomial.expand K q f) ∈ A := by
      intro f
      have h_amap : ∀ g : K[X],
          algebraMap K[X] (RatFunc K) g = Polynomial.aeval (RatFunc.X (K := K)) g := by
        intro g
        induction g using Polynomial.induction_on' with
        | add p q hp hq => rw [map_add, map_add, hp, hq]
        | monomial n a =>
          simp only [Polynomial.aeval_monomial, RatFunc.algebraMap_monomial]; rfl
      rw [h_amap, Polynomial.expand_aeval]
      exact IntermediateField.algebra_adjoin_le_adjoin K ({Xq} : Set (RatFunc K))
        (Polynomial.aeval_mem_adjoin_singleton K Xq)
    exact A.div_mem (hmem p) (hmem r)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨RatFunc.X, rfl⟩

omit [DecidableEq K] in
private theorem finrank_ratFunc_frobenius :
    Module.finrank (frobeniusAlgHom K (RatFunc K)).fieldRange (RatFunc K) =
      Fintype.card K := by
  rw [show (frobeniusAlgHom K (RatFunc K)).fieldRange =
    IntermediateField.adjoin K
      ({(RatFunc.X (K := K)) ^ Fintype.card K} : Set (RatFunc K)) from
    frobenius_fieldRange_ratFunc K]
  rw [show (RatFunc.X (K := K)) ^ Fintype.card K =
    algebraMap K[X] (RatFunc K) (Polynomial.X ^ Fintype.card K) from
    (map_pow (algebraMap K[X] (RatFunc K)) Polynomial.X (Fintype.card K)).symm]
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    Polynomial.natDegree_X_pow, Polynomial.natDegree_one, Nat.max_zero]

omit [DecidableEq K] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
private theorem finrank_frobFracRange_functionField :
    Module.finrank (frobFracRange K W) W.toAffine.FunctionField = 2 * Fintype.card K := by
  set aR := (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField).fieldRange
  have hfr_le_aR : frobFracRange K W ≤ aR := by
    intro z hz
    rw [frobFracRange, AlgHom.map_fieldRange] at hz
    rw [AlgHom.mem_fieldRange] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    exact ⟨frobeniusAlgHom K (FractionRing K[X]) a, ha⟩
  let _ := (IntermediateField.inclusion hfr_le_aR).toRingHom.toAlgebra
  have : IsScalarTower (frobFracRange K W) aR W.toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h2 := Module.finrank_mul_finrank (frobFracRange K W) aR W.toAffine.FunctionField
  have h_top : Module.finrank aR W.toAffine.FunctionField = 2 := by
    have := @Algebra.finrank_eq_of_equiv_equiv
      (FractionRing K[X]) W.toAffine.FunctionField _ _ _ aR W.toAffine.FunctionField _ _ _
      (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField)
        (IsScalarTower.toAlgHom K (FractionRing K[X])
          W.toAffine.FunctionField).toRingHom.injective).toRingEquiv (RingEquiv.refl _) ?_
    · rw [finrank_functionField_eq_two] at this; exact this.symm
    · ext x; rfl
  have h_mid : Module.finrank (frobFracRange K W) aR = Fintype.card K := by
    set fR := (frobeniusAlgHom K (FractionRing K[X])).fieldRange
    let i : fR ≃+* (frobFracRange K W) :=
      (IntermediateField.equivMap fR
        (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField)).toRingEquiv
    let j : (FractionRing K[X]) ≃+* aR :=
      (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K (FractionRing K[X]) W.toAffine.FunctionField)
        (IsScalarTower.toAlgHom K (FractionRing K[X])
          W.toAffine.FunctionField).toRingHom.injective).toRingEquiv
    have h_transfer := @Algebra.finrank_eq_of_equiv_equiv
      fR (FractionRing K[X]) _ _ _ (frobFracRange K W) aR _ _ _ i j ?_
    · rw [← h_transfer]
      let e : FractionRing K[X] ≃+* RatFunc K :=
        (FractionRing.algEquiv K[X] (RatFunc K)).toRingEquiv
      set fRR := (frobeniusAlgHom K (RatFunc K)).fieldRange
      have he_mem : ∀ x : fR, e (x : FractionRing K[X]) ∈ fRR := by
        rintro ⟨y, a, ha⟩
        refine ⟨e a, ?_⟩
        change (e a) ^ Fintype.card K = e y
        rw [← map_pow]; exact congrArg e ha
      have he_mem' : ∀ x : fRR, e.symm (x : RatFunc K) ∈ fR := by
        rintro ⟨y, a, ha⟩
        refine ⟨e.symm a, ?_⟩
        change (e.symm a) ^ Fintype.card K = e.symm y
        rw [← map_pow]; exact congrArg e.symm ha
      let i' : fR ≃+* fRR :=
        { toFun := fun x ↦ ⟨e x, he_mem x⟩
          invFun := fun x ↦ ⟨e.symm x, he_mem' x⟩
          left_inv := fun ⟨y, _⟩ ↦ Subtype.ext (e.symm_apply_apply y)
          right_inv := fun ⟨y, _⟩ ↦ Subtype.ext (e.apply_symm_apply y)
          map_mul' := fun ⟨a, _⟩ ⟨b, _⟩ ↦ Subtype.ext (map_mul e a b)
          map_add' := fun ⟨a, _⟩ ⟨b, _⟩ ↦ Subtype.ext (map_add e a b) }
      rw [show Module.finrank fR (FractionRing K[X]) = Module.finrank fRR (RatFunc K) from
        @Algebra.finrank_eq_of_equiv_equiv fR (FractionRing K[X]) _ _ _
          fRR (RatFunc K) _ _ _ i' e (by ext ⟨x, hx⟩; rfl)]
      exact finrank_ratFunc_frobenius K
    · ext ⟨x, hx⟩; rfl
  rw [h_mid, h_top] at h2
  lia

omit [DecidableEq K] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
private theorem finrank_over_frobenius_image :
    Module.finrank (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange
      W.toAffine.FunctionField = Fintype.card K := by
  let _ := (IntermediateField.inclusion (frobFracRange_le_frobRange K W)).toRingHom.toAlgebra
  have : IsScalarTower (frobFracRange K W)
      (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange
      W.toAffine.FunctionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h_tower := Module.finrank_mul_finrank (frobFracRange K W)
    (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange W.toAffine.FunctionField
  have h_intermediate : Module.finrank (frobFracRange K W)
      (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange = 2 := by
    set φ := (IsScalarTower.toAlgHom K (FractionRing K[X])
      W.toAffine.FunctionField).comp (frobeniusAlgHom K (FractionRing K[X]))
    have hφ_range : φ.fieldRange = frobFracRange K W := by
      simp only [φ, frobFracRange, AlgHom.map_fieldRange]
    let i : (FractionRing K[X]) ≃+* (frobFracRange K W) :=
      ((AlgEquiv.ofInjective φ φ.toRingHom.injective).trans
        (IntermediateField.equivOfEq hφ_range)).toRingEquiv
    let j := frobeniusRangeEquiv K W
    have := @Algebra.finrank_eq_of_equiv_equiv
      (FractionRing K[X]) W.toAffine.FunctionField _ _ _
      (frobFracRange K W) (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange _ _ _ i j ?_
    · rw [finrank_functionField_eq_two] at this; exact this.symm
    · ext x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, i, j,
        frobeniusRangeEquiv]
      change (φ x : W.toAffine.FunctionField) = ↑(AlgEquiv.ofInjective
        (frobeniusAlgHom K W.toAffine.FunctionField)
        (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.injective
        (algebraMap (FractionRing K[X]) W.toAffine.FunctionField x))
      simp [AlgEquiv.ofInjective_apply, φ]
  rw [h_intermediate, finrank_frobFracRange_functionField K W] at h_tower
  lia

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **Core algebraic fact**: `[K(E) : K(E)^q] = q`, where the module structure on `K(E)` over
itself is via the `q`-th power Frobenius (Silverman II.2.11(a)). -/
theorem frobenius_finrank_functionField :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
      (frobeniusAlgHom K W.toAffine.FunctionField).toRingHom.toAlgebra.toModule =
    Fintype.card K := by
  rw [frobenius_finrank_eq_fieldRange_finrank]
  exact finrank_over_frobenius_image K W

omit [DecidableEq K] in
/-- The Frobenius isogeny has degree `q = #K` (Silverman III.4.6, II.2.11(a)). -/
theorem frobeniusIsogeny_degree :
    (frobeniusIsogeny K W).degree = Fintype.card K := by
  change @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
    (frobeniusIsogeny K W).toAlgebra.toModule = Fintype.card K
  exact frobenius_finrank_functionField K W

omit [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **Silverman II.2.11(b) (EC case, power-membership form)**: every element `x ∈ K(E)` has
    `x ^ p ^ r ∈ K(E)^q` where `q = #K = p ^ r`; equivalently `x ^ q` lies in the image of the
    Frobenius algebra map. This is the substance of pure inseparability of `K(E) / K(E)^q`. -/
theorem frobeniusIsogeny_pow_mem_fieldRange (x : W.toAffine.FunctionField) :
    ∃ n : ℕ, x ^ (Nat.minFac (Fintype.card K)) ^ n ∈
      (frobeniusAlgHom K W.toAffine.FunctionField).fieldRange := by
  obtain ⟨p, _hCharP, m, _hp, hcard⟩ := FiniteField.card' K
  have hmin : Nat.minFac (Fintype.card K) = p := by
    rw [hcard]; exact Nat.Prime.pow_minFac _hp m.ne_zero
  rw [hmin]
  refine ⟨m, x, ?_⟩
  change (frobeniusAlgHom K W.toAffine.FunctionField) x = x ^ p ^ (m : ℕ)
  rw [coe_frobeniusAlgHom, hcard]

omit [DecidableEq K] in
/-- **Silverman II.2.11(a) (EC case)**: the image of the Frobenius isogeny's pullback is
    exactly the set of `q`-th powers in `K(E)`, where `q = #K`. -/
theorem frobeniusIsogeny_pullback_range :
    Set.range (frobeniusIsogeny K W).pullback =
      Set.range ((· ^ Fintype.card K) :
        W.toAffine.FunctionField → W.toAffine.FunctionField) := by
  ext f
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg, frobeniusIsogeny_pullback_apply]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rwa [frobeniusIsogeny_pullback_apply]⟩

end HasseWeil
