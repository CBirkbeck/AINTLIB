/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# A surjection of free modules of equal rank is injective (YFULL route γ)

Over a commutative ring `R`, a surjective linear map `f : M →ₗ[R] Q` between two finite
free `R`-modules of the same rank is injective (hence bijective). This is the module core
of the "same-degree effective Cartier divisor containment ⟹ equality" step in the `Y(N)`
clopen full-level argument.

The proof combines two mathlib facts: two finite free modules of equal rank are linearly
isomorphic (`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`), and every commutative
ring has the Orzech property (`instOrzechPropertyOfCommRing`), i.e. a surjection onto a
finite module that also *embeds* into it is injective
(`OrzechProperty.injective_of_surjective_of_injective`).
-/

open Module

universe u v

namespace ModularCurves

/-- **A surjection of finite free modules of equal rank is injective.** -/
theorem injective_of_surjective_of_free_finrank_eq {R : Type u} [CommRing R] [Nontrivial R]
    {M Q : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (h : Module.finrank R M = Module.finrank R Q)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨i⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := R) (M := M) (M' := Q) h
  exact OrzechProperty.injective_of_surjective_of_injective i.toLinearMap f i.injective hf

/-- A surjection of finite free modules of equal rank is bijective. -/
theorem bijective_of_surjective_of_free_finrank_eq {R : Type u} [CommRing R] [Nontrivial R]
    {M Q : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (h : Module.finrank R M = Module.finrank R Q)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨injective_of_surjective_of_free_finrank_eq h f hf, hf⟩

attribute [local instance] Module.free_of_flat_of_isLocalRing

/-- **A surjection of finite flat modules of equal stalkwise rank is injective.** Over a
commutative ring `R`, a surjective `R`-linear map between two finite flat `R`-modules with
the same rank at every prime is injective (hence bijective). Localizing at each maximal
ideal reduces to the finite-free case (`injective_of_surjective_of_free_finrank_eq`). -/
theorem injective_of_surjective_of_flat_rankAtStalk_eq {R : Type u} [CommRing R]
    {M Q : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p = Module.rankAtStalk (R := R) Q p)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  apply Module.subsingleton_of_localization_maximal (R := R)
    (fun P _ => LocalizedModule P.primeCompl (LinearMap.ker f))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (LinearMap.ker f))
  intro P hP
  haveI := hP.isPrime
  haveI : Nontrivial (Localization.AtPrime P) := inferInstance
  -- the localized map is surjective, and free of equal rank at `P`, hence injective
  have hfP : Function.Injective
      (LocalizedModule.map P.primeCompl f) := by
    refine injective_of_surjective_of_free_finrank_eq (R := Localization.AtPrime P) ?_
      (LocalizedModule.map P.primeCompl f) (LocalizedModule.map_surjective P.primeCompl f hf)
    exact h ⟨P, hP.isPrime⟩
  -- the localized inclusion of `ker f` is injective with image `= ker (map f) = ⊥`
  have hsub : Function.Injective
      (LocalizedModule.map P.primeCompl (LinearMap.ker f).subtype) :=
    LocalizedModule.map_injective P.primeCompl _ (Submodule.subtype_injective _)
  have hex : Function.Exact (LocalizedModule.map P.primeCompl (LinearMap.ker f).subtype)
      (LocalizedModule.map P.primeCompl f) :=
    LocalizedModule.map_exact P.primeCompl (LinearMap.ker f).subtype f
      (LinearMap.exact_subtype_ker_map f)
  refine ⟨fun x y => ?_⟩
  apply hsub
  apply hfP
  have hfx := (hex (LocalizedModule.map P.primeCompl (LinearMap.ker f).subtype x)).mpr ⟨x, rfl⟩
  have hfy := (hex (LocalizedModule.map P.primeCompl (LinearMap.ker f).subtype y)).mpr ⟨y, rfl⟩
  rw [hfx, hfy]

/-- A surjection of finite flat modules of equal stalkwise rank is bijective. -/
theorem bijective_of_surjective_of_flat_rankAtStalk_eq {R : Type u} [CommRing R]
    {M Q : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p = Module.rankAtStalk (R := R) Q p)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨injective_of_surjective_of_flat_rankAtStalk_eq h f hf, hf⟩

/-- **A surjective ring homomorphism of finite flat algebras of equal stalkwise rank over a
base is an isomorphism.** For `φ : A →+* B` surjective with `A`, `B` finite flat over `R₀`
of the same rank at every prime of `R₀`, `φ` is bijective. This is the affine/ring form of
"a closed immersion of finite locally free schemes of equal rank over the base is an
isomorphism" — the same-degree-divisor-equality step of the `Y(N)` clopen argument. -/
theorem bijective_of_surjective_ringHom_of_flat_rankAtStalk_eq {R₀ : Type u} [CommRing R₀]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]
    [Module.Finite R₀ A] [Module.Flat R₀ A] [Module.Finite R₀ B] [Module.Flat R₀ B]
    (h : ∀ p : PrimeSpectrum R₀,
      Module.rankAtStalk (R := R₀) A p = Module.rankAtStalk (R := R₀) B p)
    (φ : A →+* B) (hφR₀ : ∀ r : R₀, φ (algebraMap R₀ A r) = algebraMap R₀ B r)
    (hφ : Function.Surjective φ) : Function.Bijective φ := by
  let φₗ : A →ₗ[R₀] B :=
    { toFun := φ, map_add' := map_add φ,
      map_smul' := fun r a => by
        simp only [Algebra.smul_def, map_mul, hφR₀, RingHom.id_apply, Algebra.smul_def] }
  exact bijective_of_surjective_of_flat_rankAtStalk_eq h φₗ hφ

end ModularCurves
