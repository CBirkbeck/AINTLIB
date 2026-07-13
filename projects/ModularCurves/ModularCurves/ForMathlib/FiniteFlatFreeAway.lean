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

end ModularCurves
