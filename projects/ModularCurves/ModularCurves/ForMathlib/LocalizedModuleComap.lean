/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Localisation of a module under a surjective algebra map

Let `P ↠ S` be a surjective `R`-algebra map, `M` an `S`-module (hence a `P`-module through the
surjection), and `q` a prime of `S` with contraction `𝔮ᴾ = q.comap (algebraMap P S)`.  Because the
`P`-action on `M` factors through `S`, localising `M` at the `P`-multiplicative set `(𝔮ᴾ)ᶜ` gives the
same module as localising at `qᶜ`:

* `algebraMapSubmonoid_primeCompl_comap` : the image of `(𝔮ᴾ).primeCompl` in `S` is `q.primeCompl`
  (this is where surjectivity is used).
* `localizedModuleComapEquiv` : `M_{𝔮ᴾ} ≃ₗ[R] M_𝔮` as `R`-modules.

This is the `M_𝔮 ≅ M_{𝔮ᴾ}` step of the polynomial-ring reduction (`[T-REDUCEP]`) in the flat-locus
spreading argument, isolated so it does not depend on the Buchsbaum–Eisenbud machinery.
-/
import Mathlib
import ModularCurves.ForMathlib.FlatLocus

open scoped TensorProduct

variable {R P S M : Type*} [CommRing R] [CommRing P] [CommRing S]
  [Algebra R P] [Algebra P S] [Algebra R S] [IsScalarTower R P S]
  [AddCommGroup M] [Module S M] [Module P M] [Module R M]
  [IsScalarTower P S M] [IsScalarTower R P M] [IsScalarTower R S M]

/-- The image in `S` of the prime-complement of the contraction `q.comap (P → S)` is exactly
`q.primeCompl`, provided `P → S` is surjective. -/
theorem algebraMapSubmonoid_primeCompl_comap (hf : Function.Surjective (algebraMap P S))
    (q : Ideal S) [q.IsPrime] :
    Algebra.algebraMapSubmonoid S (q.comap (algebraMap P S)).primeCompl = q.primeCompl := by
  ext s
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.primeCompl,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, Ideal.mem_comap]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hs
    obtain ⟨p, rfl⟩ := hf s
    exact ⟨p, hs, rfl⟩

/-- **Localisation commutes with the surjection `P ↠ S`.** For `M` an `S`-module and `q` a prime of
`S`, the localisation of `M` at the contracted prime `q.comap (P → S)` (as a `P`-module) is
`R`-linearly isomorphic to the localisation of `M` at `q` (as an `S`-module). -/
noncomputable def localizedModuleComapEquiv (hf : Function.Surjective (algebraMap P S))
    (q : Ideal S) [q.IsPrime] :
    LocalizedModule (q.comap (algebraMap P S)).primeCompl M ≃ₗ[R]
      LocalizedModule q.primeCompl M := by
  -- View the canonical localisation `M → M_𝔮` (an `S`-linear map, restricted to `P`) as a
  -- localisation of `M` at `(𝔮ᴾ).primeCompl` via `IsLocalizedModule.restrictScalars`.
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid S (q.comap (algebraMap P S)).primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl M) := by
    rw [algebraMapSubmonoid_primeCompl_comap hf q]
    infer_instance
  haveI hloc : IsLocalizedModule (q.comap (algebraMap P S)).primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars P) :=
    IsLocalizedModule.restrictScalars (A := S) _ (LocalizedModule.mkLinearMap q.primeCompl M)
  -- The canonical localisation `M → M_{𝔮ᴾ}` and this one agree up to a unique `P`-linear iso;
  -- restrict scalars to `R`.
  exact ((IsLocalizedModule.iso (q.comap (algebraMap P S)).primeCompl
    ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars P)).restrictScalars R)

/-- **Flat locus transports across the surjection `P ↠ S`.** `M_𝔮` is `R`-flat iff `M_{𝔮ᴾ}` is
`R`-flat, where `𝔮ᴾ = q.comap (P → S)`.  This is the module-level half of the `[T-REDUCEP]`
reduction (`flatLocus R S M` pulls back to `flatLocus R P M` along `Spec S ↪ Spec P`); combine with
`mem_flatLocus` and `PrimeSpectrum.comap_asIdeal` at the call site to phrase it on `flatLocus`. -/
theorem flat_localizedModule_comap_iff (hf : Function.Surjective (algebraMap P S))
    (q : Ideal S) [q.IsPrime] :
    Module.Flat R (LocalizedModule q.primeCompl M) ↔
      Module.Flat R (LocalizedModule (q.comap (algebraMap P S)).primeCompl M) := by
  constructor
  · intro h
    haveI := h
    exact Module.Flat.of_linearEquiv (localizedModuleComapEquiv hf q)
  · intro h
    haveI := h
    exact Module.Flat.of_linearEquiv (localizedModuleComapEquiv hf q).symm
