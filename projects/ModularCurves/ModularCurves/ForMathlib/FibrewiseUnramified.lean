import ModularCurves.ForMathlib.FiniteFibrewiseFlat
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Support

/-!
# The fibrewise criterion for formal unramifiedness

**The BB-DIFF engine.** Let `A → R → T` with `T` an essentially-finite-type
`R`-algebra. If for every prime `q ⊆ A` the residue fibre map
`κ(q) ⊗[A] R → κ(q) ⊗[A] T` is formally unramified, then `T` is formally unramified
over `R`.

Proof: `Ω[T⁄R]` is a finite `T`-module (`KaehlerDifferential.finite`); by
`Module.support_eq_empty_iff` + local Nakayama (`IsLocalRing.subsingleton_tensorProduct`)
it suffices to kill `κ(Q) ⊗[T] Ω[T⁄R]` at every prime `Q ⊆ T`. Writing `q := Q ∩ A` and
`S' := κ(q) ⊗[A] R`, the base-changed Kähler module `S' ⊗[R] Ω[T⁄R] ≃ Ω[(S'⊗[R]T)⁄S']`
(`tensorKaehlerEquivBase`) is subsingleton by the fibre hypothesis (transported through
the pushout cancellation `κ(q) ⊗[A] T ≃ S' ⊗[R] T`), and every generator `1 ⊗ ω` of
`κ(Q) ⊗[T] Ω` factors through it along `κ(q) → κ(Q)` (`Ideal.ResidueField.map`), so it
vanishes.

This mirrors `flat_of_fibre_flat_of_finitePresentation` (the BB-FLAT engine) with the
same `fiberInclusion` interface, so the scheme-level chart assembly transports verbatim.
-/

open TensorProduct

universe u

namespace ModularCurves

section UnramifiedEngine

variable {A R T : Type u} [CommRing A] [CommRing R] [CommRing T]
  [Algebra A R] [Algebra A T] [Algebra R T] [IsScalarTower A R T]

/-- The residue-fibre transfer for an abstract module `M` (kept opaque so that no
instance search unfolds it): if `S' ⊗[R] M` is subsingleton (`S'` any `R`-algebra
mapping to a `T`-algebra field `L`), then so is `L ⊗[T] M`. -/
private lemma subsingleton_tensor_transfer
    {L : Type u} [CommRing L] [Algebra T L] [Algebra R L] [IsScalarTower R T L]
    (M : Type u) [AddCommGroup M] [Module T M] [Module R M] [IsScalarTower R T M]
    (S' : Type u) [CommRing S'] [Algebra R S']
    (χ₀ : S' →+* L)
    (hχ₀R : ∀ r : R, χ₀ (algebraMap R S' r) = algebraMap R L r)
    (hsub : Subsingleton (S' ⊗[R] M)) :
    Subsingleton (L ⊗[T] M) := by
  -- the transfer map `S' ⊗[R] M → L ⊗[T] M`, `x ⊗ m ↦ χ₀(x) ⊗ m`
  set χ : (S' ⊗[R] M) →ₗ[R] (L ⊗[T] M) :=
    TensorProduct.lift
      { toFun := fun x => ((TensorProduct.mk T L M) (χ₀ x)).restrictScalars R
        map_add' := fun x₁ x₂ => by
          ext m
          simp only [LinearMap.coe_restrictScalars, TensorProduct.mk_apply,
            LinearMap.add_apply, map_add]
        map_smul' := fun r x => by
          ext m
          simp only [LinearMap.coe_restrictScalars, RingHom.id_apply,
            LinearMap.smul_apply, TensorProduct.mk_apply]
          rw [show χ₀ (r • x) = r • χ₀ x from by
            rw [Algebra.smul_def, map_mul, hχ₀R, ← Algebra.smul_def]]
          rw [show (r • χ₀ x) ⊗ₜ[T] m
              = r • ((χ₀ x) ⊗ₜ[T] m) from TensorProduct.smul_tmul' r _ m |>.symm] }
    with hχdef
  have hgen : ∀ m : M, (1 : L) ⊗ₜ[T] m = 0 := by
    intro m
    have h1 : (1 : L) ⊗ₜ[T] m = χ ((1 : S') ⊗ₜ[R] m) := by
      simp only [hχdef, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_restrictScalars, TensorProduct.mk_apply, map_one]
    rw [h1, Subsingleton.elim ((1 : S') ⊗ₜ[R] m) 0, map_zero]
  constructor
  intro z₁ z₂
  have hz : ∀ z : L ⊗[T] M, z = 0 := by
    intro z
    induction z with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul x m =>
      rw [show x ⊗ₜ[T] m = x • ((1 : L) ⊗ₜ[T] m) from by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hgen, smul_zero]
  rw [hz z₁, hz z₂]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The fibrewise criterion for formal unramifiedness**: if all residue fibres of
`R → T` over `A` are formally unramified and `T` is essentially of finite type over
`R`, then `T` is formally unramified over `R`. -/
theorem formallyUnramified_of_fibre_formallyUnramified
    [Algebra.EssFiniteType R T]
    (hfib : ∀ (q : Ideal A) [q.IsPrime],
      RingHom.FormallyUnramified (fiberInclusion (R := R) (T := T) q).toRingHom) :
    Algebra.FormallyUnramified R T := by
  refine ⟨?_⟩
  rw [← Module.support_eq_empty_iff (R := T)]
  by_contra hne
  obtain ⟨Q, hQ⟩ := Set.nonempty_iff_ne_empty.mpr hne
  haveI : Q.asIdeal.IsPrime := Q.2
  -- the residue fibre of `Ω[T⁄R]` at `Q` vanishes
  have hvanish : Subsingleton (Q.asIdeal.ResidueField ⊗[T] Ω[T⁄R]) := by
    set q : Ideal A := Q.asIdeal.comap (algebraMap A T) with hqdef
    haveI hqprime : q.IsPrime := Ideal.IsPrime.comap _
    -- (i) the fibre hypothesis, transported to the base-change presentation
    haveI hbc : Algebra.FormallyUnramified (q.ResidueField ⊗[A] R) ((q.ResidueField ⊗[A] R) ⊗[R] T) := by
      letI : Algebra (q.ResidueField ⊗[A] R) (q.ResidueField ⊗[A] T) :=
        (fiberInclusion (R := R) (T := T) q).toRingHom.toAlgebra
      haveI h1 : Algebra.FormallyUnramified (q.ResidueField ⊗[A] R) (q.ResidueField ⊗[A] T) := hfib q
      let e : (q.ResidueField ⊗[A] T) ≃ₐ[q.ResidueField ⊗[A] R] ((q.ResidueField ⊗[A] R) ⊗[R] T) :=
        { __ := (Algebra.IsPushout.cancelBaseChangeAlg A q.ResidueField R (q.ResidueField ⊗[A] R) T).symm
          commutes' := fun x =>
            congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor A R T q.ResidueField) x) }
      exact Algebra.FormallyUnramified.of_surjective e.toAlgHom e.surjective
    -- (ii) hence the base-changed Kähler module is subsingleton
    haveI hΩbc : Subsingleton ((q.ResidueField ⊗[A] R) ⊗[R] Ω[T⁄R]) := by
      haveI := hbc.subsingleton_kaehlerDifferential
      exact (KaehlerDifferential.tensorKaehlerEquivBase R (q.ResidueField ⊗[A] R) T
        ((q.ResidueField ⊗[A] R) ⊗[R] T)).toEquiv.subsingleton
    -- (iii) the residue comparison `χ₀ : q.ResidueField ⊗[A] R → κ(Q)`
    set ρ : q.ResidueField →+* Q.asIdeal.ResidueField :=
      Ideal.ResidueField.map q Q.asIdeal (algebraMap A T) hqdef with hρdef
    have hρA : ∀ a : A, ρ (algebraMap A q.ResidueField a)
        = algebraMap A Q.asIdeal.ResidueField a := by
      intro a
      rw [hρdef, Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]
    set χ₀ : (q.ResidueField ⊗[A] R) →+* Q.asIdeal.ResidueField :=
      (Algebra.TensorProduct.lift
        (⟨ρ, hρA⟩ : q.ResidueField →ₐ[A] Q.asIdeal.ResidueField)
        (IsScalarTower.toAlgHom A R Q.asIdeal.ResidueField)
        (fun _ _ => Commute.all _ _)).toRingHom with hχ₀def
    have hχ₀R : ∀ r : R, χ₀ (algebraMap R (q.ResidueField ⊗[A] R) r)
        = algebraMap R Q.asIdeal.ResidueField r := by
      intro r
      simp only [hχ₀def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show algebraMap R (q.ResidueField ⊗[A] R) r = (1 : q.ResidueField) ⊗ₜ[A] r from rfl]
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    -- (iv) transfer the vanishing to the `κ(Q)`-fibre
    exact subsingleton_tensor_transfer Ω[T⁄R] (q.ResidueField ⊗[A] R) χ₀ hχ₀R hΩbc
  -- Nakayama at `Q`: the support membership contradicts the vanishing fibre
  haveI : Module.Finite T Ω[T⁄R] := KaehlerDifferential.finite R T
  have hmem := hQ
  rw [Module.mem_support_iff] at hmem
  haveI : Module.Finite (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl Ω[T⁄R]) :=
    Module.Finite.of_isLocalizedModule Q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ _)
  have hsub : Subsingleton (LocalizedModule Q.asIdeal.primeCompl Ω[T⁄R]) := by
    rw [← IsLocalRing.subsingleton_tensorProduct
      (R := Localization.AtPrime Q.asIdeal)]
    -- identify the residue fibre of the localization with `κ(Q) ⊗[T] Ω`
    have e : (IsLocalRing.ResidueField (Localization.AtPrime Q.asIdeal))
          ⊗[Localization.AtPrime Q.asIdeal]
          (LocalizedModule Q.asIdeal.primeCompl Ω[T⁄R])
        ≃ₗ[IsLocalRing.ResidueField (Localization.AtPrime Q.asIdeal)]
        (IsLocalRing.ResidueField (Localization.AtPrime Q.asIdeal)) ⊗[T] Ω[T⁄R] :=
      (AlgebraTensorModule.congr
        (LinearEquiv.refl _ (IsLocalRing.ResidueField (Localization.AtPrime Q.asIdeal)))
        (LocalizedModule.equivTensorProduct Q.asIdeal.primeCompl Ω[T⁄R])).trans
      (AlgebraTensorModule.cancelBaseChange T (Localization.AtPrime Q.asIdeal) _ _ _)
    haveI := hvanish
    exact e.toEquiv.subsingleton
  exact (not_subsingleton _) hsub

end UnramifiedEngine

end ModularCurves
