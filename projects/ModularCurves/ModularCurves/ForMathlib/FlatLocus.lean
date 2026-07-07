/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-FL* (openness of the flat locus).
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Algebra.Module.LocalizedModule.Exact
import ModularCurves.ForMathlib.GenericFlatness

/-!
# Openness of the flat locus (Stacks Tag 00RC / Theorem 10.129.4)

Let `R` be a Noetherian ring, `R → S` of finite presentation, and `M` a finitely-presented
`S`-module.  The **flat locus**
`{q ∈ Spec S : M_q is flat over R}` is open in `Spec S`.

The route is the classical one via **generic flatness** (Stacks 051R), consumed here as the black
box `exists_generically_free` from `ModularCurves.ForMathlib.GenericFlatness`, together with
Noetherian induction on `Spec R`.

## Main results

* `flat_localizedModule_of_flat`: localising an `R`-flat `S`-module at any submonoid of `S` keeps
  it `R`-flat (localisation is an exact `R`-linear functor).  This is the engine behind both
  generisation-stability and the neighbourhood lemma.
* `isOpen_flatLocus`: the flat locus is open.
-/

open scoped TensorProduct

namespace Module.Flat

/-- **Localisation preserves flatness over a base** (the exactness of the localisation functor).

If `N` is a flat `R`-module carrying a compatible `S`-action (`R → S` an algebra, `R → S → N` a
scalar tower), then for any submonoid `T ≤ S` the localised module `T⁻¹N = LocalizedModule T N` is
again flat over `R`.  Indeed for a submodule inclusion `N' ↪ P` of `R`-modules, tensoring with
`T⁻¹N` is the `T`-localisation of tensoring with `N` (`IsLocalizedModule.map_lTensor`), and the
localisation of an injective map is injective (`IsLocalizedModule.map_injective`). -/
theorem _root_.flat_localizedModule_of_flat {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (T : Submonoid S)
    [Module.Flat R N] : Module.Flat R (LocalizedModule T N) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N'
  rw [← AlgebraTensorModule.coe_lTensor (A := S),
    ← IsLocalizedModule.map_lTensor T (LocalizedModule.mkLinearMap T N) N'.subtype]
  apply IsLocalizedModule.map_injective
  rw [AlgebraTensorModule.coe_lTensor (A := S)]
  exact (Module.Flat.iff_lTensor_injectiveₛ.mp ‹Module.Flat R N›) N'

end Module.Flat

/-!
## The flat locus and its neighbourhood structure
-/

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The **flat locus** of `M` over `R`: the primes `q` of `S` at which the localisation `M_q` is
flat over `R`. -/
def flatLocus (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S | Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)}

theorem mem_flatLocus {q : PrimeSpectrum S} :
    q ∈ flatLocus R S M ↔ Module.Flat R (LocalizedModule q.asIdeal.primeCompl M) := Iff.rfl

/-- **Generisation-stability of the flat locus.** If `M_q` is flat over `R` and `q'` generises `q`
(`q' ⊆ q`), then `M_{q'}` is flat over `R`, because `M_{q'}` is a further localisation of `M_q`. -/
theorem flatLocus_stableUnderGeneralization :
    StableUnderGeneralization (flatLocus R S M) := by
  sorry

/-- **The neighbourhood lemma from generic flatness.** If, after inverting a single `f : R`, the
localised module `M_f` is *free* over `R_f` (the conclusion of generic flatness), then `M` is flat
over `R` at every prime `q` of `S` not containing the image `algebraMap R S f`.  Consequently the
basic open `D(algebraMap R S f)` is contained in the flat locus. -/
theorem basicOpen_subset_flatLocus_of_free (f : R)
    (hfree : Module.Free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    ↑(PrimeSpectrum.basicOpen (algebraMap R S f)) ⊆ flatLocus R S M := by
  sorry

theorem isOpen_flatLocus {R S M : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.FinitePresentation S M] :
    IsOpen (flatLocus R S M) := by
  sorry
