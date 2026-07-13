/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Free

/-!
# A finite flat algebra of finite presentation is free on a basic-open neighbourhood

The pure-algebra heart of the `[HG-C3d]` freeness leaf: for a module-finite, flat,
finitely-presented algebra `A / R` and a prime `p`, there is `r ∉ p` with `A[1/r]` free
over `R[1/r]`. Chain: module-finite + algebra-finitely-presented ⟹ module-finitely-presented
(stacks 0564); finite flat over the local ring `R_p` ⟹ `A_p` free; spread the basis to a
basic open (`Module.FinitePresentation.exists_free_localizedModule_powers`).
-/

namespace ModularCurves

/-- **Finite flat f.p. algebras are free near every prime.** For `A / R` module-finite, flat,
and finitely presented as an algebra, and `p` a prime of `R`, there is `r ∉ p` with
`A[1/r]` free over `R[1/r]`. -/
theorem exists_away_free_of_finite_of_flat (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Module.Free (Localization (Submonoid.powers r)) (LocalizedModule.Away r A) := by
  haveI : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  haveI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl A) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A) (Localization.AtPrime p.asIdeal)
  exact ⟨r, hr, hfree⟩

/-- **Freeness transport to a concrete localization pair.** If the model localization
`M[1/r] / R[1/r]` (spelled `LocalizedModule` / `Localization`) is free, then so is any
concrete realization: a ring `R'` with `IsLocalization.Away r R'` and a module `M'` with
`IsLocalizedModule (powers r) (g : M →ₗ[R] M')` compatible via a scalar tower. The linear
equivalence of the two localized modules is semilinear over the canonical ring equivalence
(`IsLocalization.algEquiv`), and freeness transports along semilinear equivalences. -/
theorem Module.Free.of_isLocalizedModule_away {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (R' M' : Type*) [CommRing R'] [Algebra R R']
    [IsLocalization.Away r R'] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (g : M →ₗ[R] M') [IsLocalizedModule (Submonoid.powers r) g]
    [Module.Free (Localization (Submonoid.powers r)) (LocalizedModule.Away r M)] :
    Module.Free R' M' := by
  -- the `R`-linear comparison of the two localizations
  let φ : LocalizedModule (Submonoid.powers r) M ≃ₗ[R] M' :=
    IsLocalizedModule.iso (Submonoid.powers r) g
  -- the canonical ring equivalence between the two localizations of `R`
  let σ : Localization (Submonoid.powers r) ≃ₐ[R] R' :=
    IsLocalization.algEquiv (Submonoid.powers r) _ _
  -- `φ` is semilinear over `σ`
  have hsl : ∀ (t : Localization (Submonoid.powers r))
      (y : LocalizedModule (Submonoid.powers r) M), φ (t • y) = σ t • φ y := by
    intro t y
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (Submonoid.powers r) t
    simp only at has
    have eL : (s : R) • φ (t • y) = a • φ y := by
      rw [← map_smul φ, ← algebraMap_smul (Localization (Submonoid.powers r)) (s : R) (t • y),
        smul_smul, mul_comm (algebraMap R (Localization (Submonoid.powers r)) (s : R)) t, has,
        algebraMap_smul, map_smul φ]
    have hsc : (s : R) • σ t = algebraMap R R' a := by
      rw [← algebraMap_smul (A := R') (s : R) (σ t), smul_eq_mul, ← σ.commutes (s : R),
        ← map_mul, mul_comm (algebraMap R (Localization (Submonoid.powers r)) (s : R)) t, has,
        σ.commutes a]
    have eR : (s : R) • (σ t • φ y) = a • φ y := by
      rw [← smul_assoc, hsc, algebraMap_smul]
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).injective
    simp only [Module.algebraMap_end_apply]
    rw [eL, eR]
  haveI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv σ.toRingEquiv.symm
  let e₂ : LocalizedModule (Submonoid.powers r) M
      ≃ₛₗ[(σ.toRingEquiv : Localization (Submonoid.powers r) →+* R')] M' :=
    { toFun := φ
      map_add' := fun x y => φ.map_add x y
      map_smul' := fun t y => hsl t y
      invFun := φ.symm
      left_inv := φ.left_inv
      right_inv := φ.right_inv }
  exact Module.Free.of_equiv e₂

end ModularCurves
