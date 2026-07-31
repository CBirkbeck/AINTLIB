/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The quotient by a product of two evaluation ideals is free of rank two

The uniform degree-two structure behind `[GAP-A-4]`'s divisor restriction: for
nonzerodivisors `rP, rQ` of an `R`-algebra `A` whose quotients are identified with `R`
by two "evaluations", the quotient `A ⧸ (rP·rQ)` is free of rank two — via the exact
sequence `0 → A/(rQ) → A/(rP·rQ) → A/(rP) → 0` (multiplication by `rP`, then the
projection), which is valid uniformly in `rP = rQ` (the tangent case).
-/

namespace ModularCurves

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

open Ideal

/-- Multiplication by `rP` descends to a well-defined `R`-linear map
`A ⧸ (rQ) → A ⧸ (rP·rQ)`. -/
noncomputable def mulQuotHom (rP rQ : A) :
    (A ⧸ Ideal.span {rQ}) →ₗ[R] (A ⧸ Ideal.span {rP * rQ}) := by
  refine Submodule.mapQ
    ((Ideal.span {rQ}).restrictScalars R)
    ((Ideal.span {rP * rQ}).restrictScalars R)
    ((Algebra.lmul R A) rP) ?_
  intro a ha
  simp only [Submodule.restrictScalars_mem] at ha ⊢
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  refine Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩
  subst hc
  show c * (rP * rQ) = rP * (c * rQ)
  ring

@[simp]
theorem mulQuotHom_mk (rP rQ : A) (a : A) :
    mulQuotHom (R := R) rP rQ (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (rP * a) := by
  show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk a) = _
  rw [Submodule.mapQ_apply]
  rfl

/-- The projection `A ⧸ (rP·rQ) → A ⧸ (rP)`. -/
noncomputable def quotProjHom (rP rQ : A) :
    (A ⧸ Ideal.span {rP * rQ}) →ₗ[R] (A ⧸ Ideal.span {rP}) := by
  refine Submodule.mapQ
    ((Ideal.span {rP * rQ}).restrictScalars R)
    ((Ideal.span {rP}).restrictScalars R)
    (LinearMap.id) ?_
  intro a ha
  simp only [Submodule.restrictScalars_mem] at ha ⊢
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  refine Ideal.mem_span_singleton'.mpr ⟨c * rQ, ?_⟩
  subst hc
  show c * rQ * rP = c * (rP * rQ)
  ring

@[simp]
theorem quotProjHom_mk (rP rQ : A) (a : A) :
    quotProjHom (R := R) rP rQ (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := by
  show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk a) = _
  rw [Submodule.mapQ_apply]
  rfl

theorem quotProjHom_surjective (rP rQ : A) :
    Function.Surjective (quotProjHom (R := R) rP rQ) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem mulQuotHom_injective (rP rQ : A)
    (hP : rP ∈ nonZeroDivisors A) :
    Function.Injective (mulQuotHom (R := R) rP rQ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mulQuotHom_mk] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  refine Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩
  have hmul : (c * rQ) * rP = a * rP := by
    calc (c * rQ) * rP = c * (rP * rQ) := by ring
      _ = rP * a := hc
      _ = a * rP := by ring
  exact (mul_cancel_right_mem_nonZeroDivisors hP).mp hmul

theorem exact_mulQuotHom_quotProjHom (rP rQ : A) :
    LinearMap.ker (quotProjHom (R := R) rP rQ) =
      LinearMap.range (mulQuotHom (R := R) rP rQ) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    have hx' : Ideal.Quotient.mk (Ideal.span {rP}) a = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx'
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [mulQuotHom_mk]
    subst hc
    congr 1
    ring
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mulQuotHom_mk] at hy
    have : Ideal.Quotient.mk (Ideal.span {rP * rQ}) a =
        Ideal.Quotient.mk _ (rP * c) := hy.symm
    show quotProjHom (R := R) rP rQ (Ideal.Quotient.mk _ a) = 0
    rw [this, quotProjHom_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩

/-- **The rank-two equivalence.** Given `R`-module identifications of the two
evaluation quotients with `R`, the quotient by the product ideal is free of rank two:
the projection is split by `a ↦ (eP a) • u` for a lift `u` of `eP⁻¹ 1`, and the split
short exact sequence gives the product decomposition. -/
noncomputable def quotientSpanMulEquivProd (rP rQ : A)
    (hP : rP ∈ nonZeroDivisors A)
    (eP : (A ⧸ Ideal.span {rP}) ≃ₗ[R] R)
    (eQ : (A ⧸ Ideal.span {rQ}) ≃ₗ[R] R) :
    (A ⧸ Ideal.span {rP * rQ}) ≃ₗ[R] (Fin 2 → R) := by
  classical
  let u : A := (Ideal.Quotient.mk_surjective (eP.symm 1)).choose
  have hu : Ideal.Quotient.mk (Ideal.span {rP}) u = eP.symm 1 :=
    (Ideal.Quotient.mk_surjective (eP.symm 1)).choose_spec
  let π := quotProjHom (R := R) rP rQ
  let ι := mulQuotHom (R := R) rP rQ
  have hexact := exact_mulQuotHom_quotProjHom (R := R) rP rQ
  have hinj := mulQuotHom_injective (R := R) rP rQ hP
  -- the splitting of the projection
  let σ : (A ⧸ Ideal.span {rP}) →ₗ[R] (A ⧸ Ideal.span {rP * rQ}) :=
    { toFun := fun a => (eP a) • (Ideal.Quotient.mk _ u)
      map_add' := fun a b => by rw [map_add, add_smul]
      map_smul' := fun r a => by
        rw [map_smul, smul_eq_mul, mul_smul]
        rfl }
  have hπu : π (Ideal.Quotient.mk _ u) = eP.symm 1 := by
    show quotProjHom (R := R) rP rQ (Ideal.Quotient.mk _ u) = eP.symm 1
    rw [quotProjHom_mk, hu]
  have hπσ : ∀ a, π (σ a) = a := by
    intro a
    show π ((eP a) • (Ideal.Quotient.mk _ u)) = a
    rw [LinearMap.map_smul, hπu, show (eP a) • eP.symm 1 =
      eP.symm ((eP a) • 1) from (eP.symm.map_smul _ _).symm,
      smul_eq_mul, mul_one, eP.symm_apply_apply]
  have hπι : ∀ b, π (ι b) = 0 := by
    intro b
    have : ι b ∈ LinearMap.ker π := by
      rw [hexact]
      exact ⟨b, rfl⟩
    exact this
  -- residual corestriction and the inverse of ι on the kernel
  let ρmem : ∀ x : A ⧸ Ideal.span {rP * rQ},
      x - σ (π x) ∈ LinearMap.range ι := by
    intro x
    rw [← hexact]
    show π (x - σ (π x)) = 0
    rw [map_sub, hπσ, sub_self]
  let ιr := LinearEquiv.ofInjective ι hinj
  let ρ : (A ⧸ Ideal.span {rP * rQ}) →ₗ[R] LinearMap.range ι :=
    (LinearMap.id - σ ∘ₗ π).codRestrict (LinearMap.range ι) ρmem
  let φ : (A ⧸ Ideal.span {rP * rQ}) →ₗ[R] (A ⧸ Ideal.span {rQ}) :=
    (ιr.symm : LinearMap.range ι →ₗ[R] (A ⧸ Ideal.span {rQ})) ∘ₗ ρ
  have hιφ : ∀ x, ι (φ x) = x - σ (π x) := by
    intro x
    show ι (ιr.symm (ρ x)) = _
    have : ∀ y : LinearMap.range ι, ι (ιr.symm y) = y := by
      intro y
      have h1 := ιr.apply_symm_apply y
      have h2 : (ιr (ιr.symm y) : A ⧸ Ideal.span {rP * rQ}) = y := by
        rw [h1]
      rw [← h2]
      rfl
    rw [this (ρ x)]
    rfl
  have hφι : ∀ b, φ (ι b) = b := by
    intro b
    apply hinj
    rw [hιφ (ι b), hπι b, map_zero, sub_zero]
  -- assemble
  have hfb : (LinearMap.prod π φ) ∘ₗ
      (σ ∘ₗ LinearMap.fst R _ _ + ι ∘ₗ LinearMap.snd R _ _) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have h1 : π (σ a + ι b) = a := by
      rw [map_add, hπσ, hπι, add_zero]
    have h2 : φ (σ a + ι b) = b := by
      apply hinj
      rw [hιφ (σ a + ι b), h1]
      rw [show σ a + ι b - σ a = ι b from by abel]
    show (π (σ a + ι b), φ (σ a + ι b)) = (a, b)
    rw [h1, h2]
  have hbf : (σ ∘ₗ LinearMap.fst R _ _ + ι ∘ₗ LinearMap.snd R _ _) ∘ₗ
      (LinearMap.prod π φ) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show σ (π x) + ι (φ x) = x
    rw [hιφ]
    abel
  exact ((LinearEquiv.ofLinear (LinearMap.prod π φ)
    (σ ∘ₗ LinearMap.fst R _ _ + ι ∘ₗ LinearMap.snd R _ _) hfb hbf :
      (A ⧸ Ideal.span {rP * rQ}) ≃ₗ[R]
        ((A ⧸ Ideal.span {rP}) × (A ⧸ Ideal.span {rQ})))).trans
    ((eP.prodCongr eQ).trans (LinearEquiv.finTwoArrow R R).symm)

end ModularCurves