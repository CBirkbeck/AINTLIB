/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
    IsLocalRing.linearIndependent_of_flat _ hliK
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
