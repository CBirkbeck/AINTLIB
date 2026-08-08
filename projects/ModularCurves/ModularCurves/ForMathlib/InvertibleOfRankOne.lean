/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The line-bundle criterion: finite projective of rank one is invertible

`Module.Invertible.of_finite_of_projective_of_rankAtStalk_eq_one`: a finitely generated
projective module whose rank at every prime is `1` is an invertible module. This is the open
item in mathlib's `PicardGroup` TODO list ([Stacks 00NX]); it packages `AP2-A2`'s kernel data
(finite ∧ projective ∧ rank-one) into the `Module.Invertible` form the Picard-side consumers
use.

The two supporting lemmas are of independent interest:
* `Module.rankAtStalk_dual`: for finite projective `M`, the dual has the same rank at every
  prime (the dual localizes by `Module.FinitePresentation.isLocalizedModule_mapExtendScalars`,
  and the dual of a finite free module has the same rank).
* `Module.contractLeft_surjective_of_rankAtStalk_pos`: if the rank at every prime is positive,
  the evaluation map `Mᵛ ⊗ M → R` is surjective (its range — the trace ideal — is contained in
  no maximal ideal, because a local basis coordinate lifts to a functional of unit value).
-/

universe u v

open TensorProduct

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- For a finite projective module, the dual has the same rank at every prime: localization
commutes with duals of finitely presented modules, and duals of finite free modules preserve
the rank. -/
theorem rankAtStalk_dual (p : PrimeSpectrum R) :
    rankAtStalk (R := R) (Dual R M) p = rankAtStalk (R := R) M p := by
  haveI := Module.finitePresentation_of_projective R M
  set S : Submonoid R := p.asIdeal.primeCompl with hS
  let Rₚ := Localization.AtPrime p.asIdeal
  letI : Module.Free Rₚ (LocalizedModule S M) := Module.free_of_flat_of_isLocalRing
  let F : Dual R M →ₗ[R] (LocalizedModule S M →ₗ[Rₚ] Rₚ) :=
    IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
      (Algebra.linearMap R Rₚ) Rₚ
  let e : LocalizedModule S (Dual R M) ≃ₗ[R] (LocalizedModule S M →ₗ[Rₚ] Rₚ) :=
    IsLocalizedModule.iso S F
  let e' : LocalizedModule S (Dual R M) ≃ₗ[Rₚ] (LocalizedModule S M →ₗ[Rₚ] Rₚ) :=
    e.extendScalarsOfIsLocalization S Rₚ
  show Module.finrank Rₚ (LocalizedModule S (Dual R M)) =
    Module.finrank Rₚ (LocalizedModule S M)
  rw [e'.finrank_eq, Module.finrank_linearMap_self]

/-- If a finite projective module has positive rank at every prime, the contraction
`Mᵛ ⊗ M → R` is surjective: were its range contained in a maximal ideal `m`, a basis
coordinate of the free localization `Mₘ` would lift to a functional whose value at a lift of
the basis vector is a unit times an element of `m`. -/
theorem contractLeft_surjective_of_rankAtStalk_pos
    (h : ∀ p, 0 < rankAtStalk (R := R) M p) :
    Function.Surjective (contractLeft R M) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := Module.finitePresentation_of_projective R M
  set S : Submonoid R := m.primeCompl with hS
  let Rₚ := Localization.AtPrime m
  let Mₚ := LocalizedModule S M
  letI : Module.Free Rₚ Mₚ := Module.free_of_flat_of_isLocalRing
  have hpos : 0 < Module.finrank Rₚ Mₚ := h ⟨m, hmax.isPrime⟩
  let b := Module.finBasis Rₚ Mₚ
  let i₀ : Fin (Module.finrank Rₚ Mₚ) := ⟨0, hpos⟩
  let δ : Mₚ →ₗ[Rₚ] Rₚ := b.coord i₀
  let F : Dual R M →ₗ[R] (Mₚ →ₗ[Rₚ] Rₚ) :=
    IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
      (Algebra.linearMap R Rₚ) Rₚ
  obtain ⟨⟨φ, s⟩, hφs⟩ := IsLocalizedModule.surj S F δ
  obtain ⟨⟨x, u⟩, hxu⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S M) (b i₀)
  have h1 : (F φ) ((LocalizedModule.mkLinearMap S M) x) = algebraMap R Rₚ (φ x) := by
    simp only [F, IsLocalizedModule.mapExtendScalars_apply_apply,
      IsLocalizedModule.map_apply, Algebra.linearMap_apply]
  have h2 : (F φ) ((LocalizedModule.mkLinearMap S M) x) = algebraMap R Rₚ ((s : R) * u) := by
    rw [← hxu, ← hφs]
    have hδ : δ (b i₀) = 1 := by
      simp [δ, Basis.coord_apply]
    rw [LinearMap.smul_apply, Submonoid.smul_def u, Submonoid.smul_def s,
      ← algebraMap_smul Rₚ (u : R) (b i₀), map_smul, hδ, smul_eq_mul, mul_one,
      Algebra.smul_def, ← map_mul]
  have hunit : IsUnit (algebraMap R Rₚ (φ x)) := by
    rw [h1.symm.trans h2]
    exact IsLocalization.map_units Rₚ ⟨(s : R) * u, mul_mem s.2 u.2⟩
  have hmem : φ x ∈ m.primeCompl :=
    (IsLocalization.AtPrime.isUnit_to_map_iff Rₚ m (φ x)).mp hunit
  exact hmem (hle ⟨φ ⊗ₜ x, contractLeft_apply φ x⟩)

/-- **Line-bundle criterion.** A finitely generated projective module of constant rank one is
invertible: the contraction `Mᵛ ⊗ M → R` is bijective. This is the module form of
[Stacks 00NX] and discharges the corresponding TODO in `Mathlib.RingTheory.PicardGroup`. -/
theorem Invertible.of_finite_of_projective_of_rankAtStalk_eq_one
    (h : Module.rankAtStalk (R := R) M = fun _ ↦ 1) : Module.Invertible R M := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := Module.subsingleton R (Dual R M ⊗[R] M)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · refine ⟨Module.bijective_of_surjective_of_rankAtStalk_eq
      (contractLeft_surjective_of_rankAtStalk_pos fun p => by simp [h]) fun m _ => ?_⟩
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, rankAtStalk_dual, rankAtStalk_self]
    simp [h]

end Module
