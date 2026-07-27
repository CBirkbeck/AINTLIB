/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.Module

/-!
# A prescribed basis vector after localization

A nonzero vector in a rank-one residue fibre of a finitely presented flat module becomes
the unique vector of a basis after restricting to a principal neighbourhood.
-/

open TensorProduct

noncomputable section

universe u

private theorem cancelBaseChange_one_one_tmul
    {R A K V : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Algebra A K]
    [IsScalarTower R A K] [AddCommGroup V] [Module R V]
    (v : V) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K V
        ((1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v)) =
      (1 : K) ⊗ₜ[R] v := by
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- A prescribed singleton basis after localization remains a prescribed
singleton basis after any compatible scalar extension and linear
equivalence. -/
theorem Module.exists_basis_singleton_of_localized_baseChange
    {R K V W : Type*} [CommRing R] [CommRing K]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module K W]
    (a : R) [Algebra R K] [Algebra (Localization.Away a) K]
    [IsScalarTower R (Localization.Away a) K]
    (v : V)
    (bA : Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a V))
    (hbA : bA 0 = LocalizedModule.mkLinearMap (.powers a) V v)
    (eBC : K ⊗[R] V ≃ₗ[K] W) (w : W)
    (hw : eBC ((1 : K) ⊗ₜ[R] v) = w) :
    ∃ b : Module.Basis (Fin 1) K W, b 0 = w := by
  let A := Localization.Away a
  let eLoc : K ⊗[A] LocalizedModule.Away a V ≃ₗ[K]
      K ⊗[A] (A ⊗[R] V) :=
    (LocalizedModule.equivTensorProduct (.powers a) V).baseChange A K _ _
  let eCancel : K ⊗[A] (A ⊗[R] V) ≃ₗ[K] K ⊗[R] V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K V
  let b : Module.Basis (Fin 1) K W :=
    (((bA.baseChange K).map eLoc).map eCancel).map eBC
  refine ⟨b, ?_⟩
  have hequiv :
      LocalizedModule.equivTensorProduct (.powers a) V
          (LocalizedModule.mk v 1) =
        (1 : A) ⊗ₜ[R] v := by
    rw [LocalizedModule.equivTensorProduct_apply_mk,
      Localization.mk_one_eq_algebraMap]
    simp
  have hbK :
      (bA.baseChange K) 0 = (1 : K) ⊗ₜ[A] bA 0 :=
    Module.Basis.baseChange_apply K bA 0
  have hloc :
      eLoc ((bA.baseChange K) 0) =
        (1 : K) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v) := by
    rw [hbK, hbA]
    simp only [eLoc, LinearEquiv.baseChange_tmul,
      LocalizedModule.mkLinearMap_apply]
    rw [hequiv]
  have hsource :
      eCancel (eLoc ((bA.baseChange K) 0)) =
        (1 : K) ⊗ₜ[R] v := by
    rw [hloc]
    exact cancelBaseChange_one_one_tmul v
  have hb :
      b 0 = eBC (eCancel (eLoc ((bA.baseChange K) 0))) := by
    simp only [b, Module.Basis.map_apply]
  calc
    b 0 = eBC (eCancel (eLoc ((bA.baseChange K) 0))) := hb
    _ = eBC ((1 : K) ⊗ₜ[R] v) := congrArg eBC hsource
    _ = w := hw

private theorem localized_toSpanSingleton_bijective_of_fiber_ne_zero
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (x : M)
    (hrank : Module.rankAtStalk M ⟨p, inferInstance⟩ = 1)
    (hx : (1 : p.ResidueField) ⊗ₜ[R] x ≠ (0 : p.Fiber M)) :
    Function.Bijective
      (LocalizedModule.map p.primeCompl
        (LinearMap.toSpanSingleton R M x)) := by
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  let k := p.ResidueField
  let v : Mp := LocalizedModule.mkLinearMap p.primeCompl M x
  letI : Module.Finite Rp Mp := inferInstance
  letI : Module.Flat Rp Mp := inferInstance
  letI : Module.Free Rp Mp := Module.free_of_flat_of_isLocalRing
  have hrankp : Module.finrank Rp Mp = 1 := by
    change Module.rankAtStalk M ⟨p, inferInstance⟩ = 1
    exact hrank
  let e : k ⊗[Rp] Mp ≃ₗ[k] k ⊗[R] M :=
    ((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp k Mp _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp k k M)
  have hequiv :
      LocalizedModule.equivTensorProduct p.primeCompl M
          (LocalizedModule.mk x 1) =
        (1 : Rp) ⊗ₜ[R] x := by
    rw [LocalizedModule.equivTensorProduct_apply_mk,
      Localization.mk_one_eq_algebraMap]
    simp
  have hev : e ((1 : k) ⊗ₜ[Rp] v) = (1 : k) ⊗ₜ[R] x := by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, v,
      LocalizedModule.mkLinearMap_apply]
    rw [hequiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  have hv : (1 : k) ⊗ₜ[Rp] v ≠ (0 : k ⊗[Rp] Mp) := by
    intro hvzero
    apply hx
    rw [← hev, hvzero, map_zero]
  have hrankFiber : Module.finrank k (k ⊗[Rp] Mp) = 1 := by
    rw [Module.finrank_baseChange, hrankp]
  let bk : Module.Basis (Fin 1) k (k ⊗[Rp] Mp) :=
    FiniteDimensional.basisSingleton (Fin 1) hrankFiber
      ((1 : k) ⊗ₜ[Rp] v) hv
  have hspan : Submodule.span Rp (Set.range (fun _ : Fin 1 => v)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (R := Rp)
      (f := fun _ : Fin 1 => v) bk (fun i => by simp [bk])
  have hliK : LinearIndependent k
      (TensorProduct.mk Rp k Mp 1 ∘ fun _ : Fin 1 => v) := by
    have hbk :
        (TensorProduct.mk Rp k Mp 1 ∘ fun _ : Fin 1 => v) = bk := by
      funext i
      change (1 : k) ⊗ₜ[Rp] v = bk i
      simp [bk]
    rw [hbk]
    exact bk.linearIndependent
  have hliRp : LinearIndependent Rp (fun _ : Fin 1 => v) :=
    Module.IsLocalRing.linearIndependent_of_flat _ hliK
  let bp : Module.Basis (Fin 1) Rp Mp := Module.Basis.mk hliRp hspan.ge
  have hbp : bp 0 = v := by simp [bp]
  let ep : Rp ≃ₗ[Rp] Mp :=
    (Module.Basis.singleton (Fin 1) Rp).equiv bp (Equiv.refl (Fin 1))
  have hep_one : ep 1 = v := by
    rw [← Module.Basis.singleton_apply (Fin 1) Rp 0]
    exact (Module.Basis.equiv_apply
      (Module.Basis.singleton (Fin 1) Rp) 0 bp (Equiv.refl (Fin 1))).trans hbp
  have hep : ep.toLinearMap = LinearMap.toSpanSingleton Rp Mp v := by
    apply LinearMap.ext
    intro r
    change ep r = r • v
    rw [← hep_one]
    simpa using (map_smul ep r (1 : Rp))
  let l := LinearMap.toSpanSingleton R M x
  let fR := Algebra.linearMap R Rp
  let fM := LocalizedModule.mkLinearMap p.primeCompl M
  have hlocalMap :
      IsLocalizedModule.map p.primeCompl fR fM l =
        (LinearMap.toSpanSingleton Rp Mp v).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl fR fM
    ext
    simpa [l, fR, fM, v, LinearMap.toSpanSingleton_apply] using
      (IsLocalizedModule.map_apply p.primeCompl fR fM l (1 : R))
  have hlocalBijective : Function.Bijective
      (IsLocalizedModule.map p.primeCompl fR fM l) := by
    rw [hlocalMap, ← hep]
    exact ep.bijective
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    fR fM).mp hlocalBijective

/-- If an element of a finitely presented flat module is nonzero in a rank-one residue fibre,
then it is the unique vector of a basis after localizing away from an element outside the prime. -/
theorem Module.FinitePresentation.exists_notMem_basis_singleton_of_fiber_ne_zero
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (x : M)
    (hrank : Module.rankAtStalk M ⟨p, inferInstance⟩ = 1)
    (hx : (1 : p.ResidueField) ⊗ₜ[R] x ≠ (0 : p.Fiber M)) :
    ∃ g : R, g ∉ p ∧
      ∃ b : Module.Basis (Fin 1) (Localization.Away g)
          (LocalizedModule.Away g M),
        b 0 = LocalizedModule.mkLinearMap (.powers g) M x := by
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  let l := LinearMap.toSpanSingleton R M x
  let fR := Algebra.linearMap R Rp
  let fM := LocalizedModule.mkLinearMap p.primeCompl M
  have hlocalBijective : Function.Bijective
      (IsLocalizedModule.map p.primeCompl fR fM l) := by
    apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
      fR fM).mpr
    exact localized_toSpanSingleton_bijective_of_fiber_ne_zero
      p x hrank hx
  obtain ⟨g, hg, hgmap⟩ :=
    Module.FinitePresentation.exists_notMem_bijective
      l p fR fM hlocalBijective
  let A := Localization.Away g
  let MR := LocalizedModule.Away g R
  let MM := LocalizedModule.Away g M
  let eR : MR ≃ₗ[A] A :=
    (LocalizedModule.equivTensorProduct (.powers g) R).trans
      (TensorProduct.AlgebraTensorModule.rid R A A)
  let eM : MR ≃ₗ[A] MM :=
    LinearEquiv.ofBijective (LocalizedModule.map (.powers g) l) hgmap
  let eAway : A ≃ₗ[A] MM := eR.symm.trans eM
  let b : Module.Basis (Fin 1) A MM :=
    (Module.Basis.singleton (Fin 1) A).map eAway
  refine ⟨g, hg, b, ?_⟩
  have heR_one : eR.symm (1 : A) = LocalizedModule.mk 1 1 := by
    change (LocalizedModule.equivTensorProduct (.powers g) R).symm
      ((TensorProduct.AlgebraTensorModule.rid R A A).symm 1) =
        LocalizedModule.mk 1 1
    rw [TensorProduct.AlgebraTensorModule.rid_symm_apply,
      LocalizedModule.equivTensorProduct_symm_apply_tmul_one]
  have heM_apply (m : MR) :
      eM m = LocalizedModule.map (.powers g) l m := rfl
  simp only [b, Module.Basis.map_apply, Module.Basis.singleton_apply]
  change eAway 1 = LocalizedModule.mk x 1
  change eM (eR.symm 1) = LocalizedModule.mk x 1
  rw [heR_one, heM_apply, LocalizedModule.map_mk]
  simp [l, LinearMap.toSpanSingleton_apply]

/-- A prescribed element of a finite flat rank-one module that is nonzero in
every maximal residue fibre is the unique vector of a global singleton basis. -/
theorem Module.exists_basis_singleton_of_forall_maximal_fiber_ne_zero
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M]
    (x : M)
    (hrank : ∀ (p : Ideal R) [p.IsMaximal],
      Module.rankAtStalk M ⟨p, inferInstance⟩ = 1)
    (hx : ∀ (p : Ideal R) [p.IsMaximal],
      (1 : p.ResidueField) ⊗ₜ[R] x ≠ (0 : p.Fiber M)) :
    ∃ b : Module.Basis (Fin 1) R M, b 0 = x := by
  let l := LinearMap.toSpanSingleton R M x
  have hl : Function.Bijective l :=
    bijective_of_localized_maximal l fun p _ =>
      localized_toSpanSingleton_bijective_of_fiber_ne_zero
        p x (hrank p) (hx p)
  let e : R ≃ₗ[R] M := LinearEquiv.ofBijective l hl
  let b : Module.Basis (Fin 1) R M :=
    (Module.Basis.singleton (Fin 1) R).map e
  refine ⟨b, ?_⟩
  simp only [b, Module.Basis.map_apply, Module.Basis.singleton_apply]
  change l 1 = x
  simp [l, LinearMap.toSpanSingleton_apply]

/-- Nonvanishing after scalar extension to a field implies nonvanishing in the
residue fibre determined by the kernel of the field structure map. -/
theorem Module.one_tmul_fiber_ne_zero_of_field_ne_zero
    {R M K : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Field K] [Algebra R K]
    (p : Ideal R) [p.IsPrime] (x : M)
    (hker : RingHom.ker (algebraMap R K) = p)
    (hx : (1 : K) ⊗ₜ[R] x ≠ (0 : K ⊗[R] M)) :
    (1 : p.ResidueField) ⊗ₜ[R] x ≠ (0 : p.Fiber M) := by
  have hp_le : p ≤ RingHom.ker (algebraMap R K) := hker.symm.le
  have hp_unit : p.primeCompl ≤
      (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hr_zero
    apply hr
    rw [← hker]
    exact hr_zero
  let φ : p.ResidueField →+* K :=
    Ideal.ResidueField.lift p (algebraMap R K) hp_le hp_unit
  letI : Algebra p.ResidueField K := φ.toAlgebra
  letI : IsScalarTower R p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (Ideal.ResidueField.lift_algebraMap
        p (algebraMap R K) hp_le hp_unit r).symm
  intro hzero
  apply hx
  calc
    (1 : K) ⊗ₜ[R] x =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R p.ResidueField K K M)
          ((1 : K) ⊗ₜ[p.ResidueField]
            ((1 : p.ResidueField) ⊗ₜ[R] x)) := by simp
    _ = (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R p.ResidueField K K M)
          ((1 : K) ⊗ₜ[p.ResidueField] (0 : p.Fiber M)) := by
            rw [hzero]
    _ = 0 := by simp

/-- If an element of a finitely presented flat module is nonzero after base change to a field
whose structure-map kernel is `p`, then it is the unique vector of a basis on a principal
neighbourhood of `p`. -/
theorem Module.FinitePresentation.exists_notMem_basis_singleton_of_field_ne_zero
    {R M K : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    [Field K] [Algebra R K]
    (p : Ideal R) [p.IsPrime] (x : M)
    (hrank : Module.rankAtStalk M ⟨p, inferInstance⟩ = 1)
    (hker : RingHom.ker (algebraMap R K) = p)
    (hx : (1 : K) ⊗ₜ[R] x ≠ (0 : K ⊗[R] M)) :
    ∃ g : R, g ∉ p ∧
      ∃ b : Module.Basis (Fin 1) (Localization.Away g)
          (LocalizedModule.Away g M),
        b 0 = LocalizedModule.mkLinearMap (.powers g) M x := by
  exact exists_notMem_basis_singleton_of_fiber_ne_zero
    p x hrank (Module.one_tmul_fiber_ne_zero_of_field_ne_zero
      p x hker hx)
