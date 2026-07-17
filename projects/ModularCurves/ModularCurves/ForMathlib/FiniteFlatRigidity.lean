/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.Projective

/-!
# Rank rigidity for surjections of finite projective modules

**[KM-W0 / T-D8 ⟸ / RANK-RIGIDITY] ForMathlib brick (candidate mathlib PR).**
A surjective linear map between finite projective modules with equal rank at every
prime is bijective: the kernel is a finite projective direct summand of rank zero
everywhere, hence subsingleton. This is the module engine behind KM 1.10.2 ("a closed
subscheme of a finite flat scheme of the same constant rank is the whole scheme") —
the scheme-level statement reduces to this over affines.
-/

universe u

namespace ModularCurves

open Module

/-- A surjective linear map between finite projective modules of equal rank at every
prime is bijective. -/
theorem bijective_of_surjective_of_rankAtStalk_eq {R A B : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    (φ : A →ₗ[R] B) (hsurj : Function.Surjective φ)
    (hrank : Module.rankAtStalk (R := R) A = Module.rankAtStalk (R := R) B) :
    Function.Bijective φ := by
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  have hσa : ∀ b, φ (σ b) = b := fun b => DFunLike.congr_fun hσ b
  -- the splitting equivalence `A ≃ ker φ × B`
  let e : A ≃ₗ[R] (LinearMap.ker φ) × B :=
    { toFun := fun a => (⟨a - σ (φ a), by
        rw [LinearMap.mem_ker, map_sub, hσa, sub_self]⟩, φ a)
      invFun := fun kb => kb.1.1 + σ kb.2
      left_inv := fun a => by simp
      right_inv := fun kb => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · have hk : φ kb.1.1 = 0 := kb.1.2
          simp [hk, hσa]
        · have hk : φ kb.1.1 = 0 := kb.1.2
          simp [hk, hσa]
      map_add' := fun a₁ a₂ => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, Prod.fst_add, Submodule.coe_add]
          abel
        · simp
      map_smul' := fun r a => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_smul, RingHom.id_apply, Prod.smul_fst, SetLike.val_smul]
          rw [smul_sub]
        · simp }
  -- the kernel is a finite projective direct summand
  haveI hkerProj : Module.Projective R (LinearMap.ker φ) :=
    Module.Projective.of_split ((LinearMap.ker φ).subtype)
      ((LinearMap.fst R (LinearMap.ker φ) B).comp e.toLinearMap)
      (by
        ext k
        have hk : φ k.1 = 0 := k.2
        simp [e, hk])
  haveI hkerFin : Module.Finite R (LinearMap.ker φ) :=
    Module.Finite.of_surjective ((LinearMap.fst R (LinearMap.ker φ) B).comp e.toLinearMap)
      (fun k => ⟨k.1, by
        refine Subtype.ext ?_
        have hk : φ k.1 = 0 := k.2
        simp [e, hk]⟩)
  -- rank bookkeeping: `rank A = rank ker + rank B` and `rank A = rank B`
  have hprod : Module.rankAtStalk (R := R) A
      = Module.rankAtStalk (R := R) (LinearMap.ker φ) + Module.rankAtStalk (R := R) B := by
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  have hzero : Module.rankAtStalk (R := R) (LinearMap.ker φ) = 0 := by
    funext p
    have h1 := congrFun hprod p
    have h2 := congrFun hrank p
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
    omega
  haveI hsub : Subsingleton (LinearMap.ker φ) :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp hzero
  refine ⟨LinearMap.ker_eq_bot.mp ?_, hsurj⟩
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker φ) ⟨0, (LinearMap.ker φ).zero_mem⟩
  exact congrArg Subtype.val this

end ModularCurves
