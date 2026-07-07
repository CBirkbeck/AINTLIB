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
`S`-module.  The **flat locus** `{q ∈ Spec S : M_q is flat over R}` is open in `Spec S`.

The route is the classical one via **generic flatness** (Stacks 051R), consumed here as the black
box `exists_generically_free` from `ModularCurves.ForMathlib.GenericFlatness`, together with
Noetherian induction on `Spec R`.

## Main results

* `flat_localizedModule_of_flat` / `flat_of_isLocalizedModule_flat`: localising an `R`-flat
  `S`-module at any submonoid of `S` keeps it `R`-flat (localisation is an exact `R`-linear
  functor).  This is the engine behind both generisation-stability and the neighbourhood lemma.
* `basicOpen_subset_flatLocus_of_free`: the neighbourhood lemma — generic flatness data
  (`M_f` free over `R_f`) puts the basic open `D(algebraMap R S f)` inside the flat locus.
* `isOpen_flatLocus`: the flat locus is open.
-/

open scoped TensorProduct
open TensorProduct

/-!
## Localisation preserves flatness over the base

The exactness of the localisation functor: an `R`-flat `S`-module stays `R`-flat after localising
at any submonoid of `S`.  This is the workhorse.
-/

/-- **Localisation preserves flatness over a base.** If `N` is a flat `R`-module carrying a
compatible `S`-action, then for any submonoid `T ≤ S` the localised module `T⁻¹N` is again flat
over `R`.  For a submodule inclusion `N' ↪ P` of `R`-modules, tensoring with `T⁻¹N` is the
`T`-localisation of tensoring with `N` (`IsLocalizedModule.map_lTensor`), and the localisation of
an injective map is injective (`IsLocalizedModule.map_injective`). -/
theorem flat_localizedModule_of_flat {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (T : Submonoid S)
    [Module.Flat R N] : Module.Flat R (LocalizedModule T N) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N'
  simp only [← AlgebraTensorModule.coe_lTensor (A := S),
    ← IsLocalizedModule.map_lTensor (A := S) (S := T) (f := N'.subtype)
      (g := LocalizedModule.mkLinearMap T N)]
  apply IsLocalizedModule.map_injective
  simpa only [AlgebraTensorModule.coe_lTensor (A := S)] using
    (Module.Flat.iff_lTensor_injectiveₛ.mp ‹Module.Flat R N›) N'

/-- **Localisation preserves flatness over a base, `IsLocalizedModule` form.** Any localisation
`N'` of an `R`-flat `S`-module `N` (at a submonoid `T ≤ S`) is again flat over `R`. -/
theorem flat_of_isLocalizedModule_flat {R S N N' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
    (T : Submonoid S) (φ : N →ₗ[S] N') [IsLocalizedModule T φ] [Module.Flat R N] :
    Module.Flat R N' := by
  haveI : Module.Flat R (LocalizedModule T N) := flat_localizedModule_of_flat T
  let e : LocalizedModule T N ≃ₗ[S] N' :=
    IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T N) φ
  exact Module.Flat.of_linearEquiv (e.restrictScalars R).symm

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

/-- **Generisation-stability of the flat locus.** If `M_q` is flat over `R` and `x` generises `q`
(`x ⤳ q`, i.e. `x ≤ q`), then `M_x` is flat over `R`, because `M_x` is a further localisation of
`M_q` (`IsLocalizedModule.liftOfLE`). -/
theorem flatLocus_stableUnderGeneralization :
    StableUnderGeneralization (flatLocus R S M) := by
  intro x y hyx hx
  rw [mem_flatLocus] at hx ⊢
  -- `y ⤳ x` gives `y ≤ x`, hence `y.asIdeal ≤ x.asIdeal` and `x.primeCompl ≤ y.primeCompl`.
  have hle_ideal : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).mpr hyx
  have hle : x.asIdeal.primeCompl ≤ y.asIdeal.primeCompl := by
    intro a ha
    exact fun hay => ha (hle_ideal hay)
  -- `M_y` is a further localisation of `M_x`.
  exact flat_of_isLocalizedModule_flat y.asIdeal.primeCompl
    (IsLocalizedModule.liftOfLE x.asIdeal.primeCompl y.asIdeal.primeCompl hle
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl M))

/-- **The neighbourhood lemma from generic flatness.** If, after inverting a single `f : R`, the
localised module `M_f` is *free* over `R_f` (the conclusion of generic flatness), then `M` is flat
over `R` at every prime `q` of `S` not containing the image `algebraMap R S f`.  Consequently the
basic open `D(algebraMap R S f)` is contained in the flat locus. -/
theorem basicOpen_subset_flatLocus_of_free (f : R)
    (hfree : Module.Free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    ↑(PrimeSpectrum.basicOpen (algebraMap R S f)) ⊆ flatLocus R S M := by
  -- Step 1: `M_f` is flat over `R` (free over `R_f`, and `R_f` is flat over `R`).
  haveI : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := hfree
  haveI : Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
    Module.Flat.of_free
  haveI : Module.Flat R (Localization.Away f) := IsLocalization.flat _ (Submonoid.powers f)
  haveI hMf : Module.Flat R (LocalizedModule (Submonoid.powers f) M) :=
    Module.Flat.trans R (Localization.Away f) _
  -- Step 2: transport freeness to the `S`-side localisation `M_g`, `g = algebraMap R S f`.
  haveI hbridge : IsLocalizedModule (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M).restrictScalars R) :=
    IsLocalizedModule.restrictScalars_powers f
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M)
  have e : LocalizedModule (Submonoid.powers f) M ≃ₗ[R]
      LocalizedModule (Submonoid.powers (algebraMap R S f)) M :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M).restrictScalars R)
  haveI hMg : Module.Flat R (LocalizedModule (Submonoid.powers (algebraMap R S f)) M) :=
    Module.Flat.of_linearEquiv e.symm
  -- Step 3: every `q ∈ D(g)` lies in the flat locus (`M_q` is a further localisation of `M_g`).
  intro q hq
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq
  rw [mem_flatLocus]
  have hle : Submonoid.powers (algebraMap R S f) ≤ q.asIdeal.primeCompl := by
    rw [Submonoid.powers_le]
    exact hq
  exact flat_of_isLocalizedModule_flat q.asIdeal.primeCompl
    (IsLocalizedModule.liftOfLE (Submonoid.powers (algebraMap R S f)) q.asIdeal.primeCompl hle
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) M)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))

/-- **Generic flatness, geometric form.** Over a Noetherian *domain* `R`, the flat locus of a
finite `S`-module `M` contains a nonempty basic open of the base: there is a nonzero `f : R` with
`D(algebraMap R S f) ⊆ flatLocus`.  This is the direct geometric consumption of
`exists_generically_free` through the neighbourhood lemma, and shows the flat locus is dense
(indeed contains a dense open) when `R` is a domain. -/
theorem exists_basicOpen_subset_flatLocus_of_isDomain [IsDomain R] [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ ↑(PrimeSpectrum.basicOpen (algebraMap R S f)) ⊆ flatLocus R S M := by
  obtain ⟨f, hf, hfree⟩ := exists_generically_free (R := R) (S := S) (M := M)
  exact ⟨f, hf, basicOpen_subset_flatLocus_of_free f hfree⟩

/-- **Openness of the flat locus** (Stacks Tag 00RC / Theorem 10.129.4).  Let `R` be Noetherian,
`R → S` of finite presentation and `M` a finitely-presented `S`-module.  Then the locus of primes
`q` of `S` at which `M_q` is flat over `R` is open.

*Route and current status.*  The generisation-stability of the flat locus
(`flatLocus_stableUnderGeneralization`) and the neighbourhood/density input from generic flatness
(`basicOpen_subset_flatLocus_of_free`, `exists_basicOpen_subset_flatLocus_of_isDomain`) are proved
above and are the two structural halves of the classical argument.  Assembling them into full
openness proceeds by **Noetherian induction on `Spec R`**: one shows the non-flat locus
`(flatLocus)ᶜ` is closed by inducting on closed subsets `Z ⊆ Spec R`, at each stage peeling off an
irreducible component `V(𝔭)` on whose generic point generic flatness (over the domain `R ⧸ 𝔭`)
provides a flat basic open, so that the non-flat part sinks into a strictly smaller closed
`Z ∩ V(f)`.

*The one boxed step.*  This reduction requires the **local criterion of flatness** / *critère de
platitude par fibres* (Stacks Tags 00MK, 039A): passing from flatness of the base-changed module
`M ⧸ 𝔭·M` over the domain `R ⧸ 𝔭` back to flatness of `M` over `R` in a neighbourhood.  That
criterion is `Tor`-theoretic and is **not yet available in mathlib** (there is no
`Tor₁`/local-flatness-criterion API), so the assembly is left as a single `sorry` here.  Everything
that does *not* depend on it — the localisation-preserves-flatness engine, generisation-stability,
and the generic-flatness neighbourhood lemma — is proved unconditionally above. -/
theorem isOpen_flatLocus {R S M : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.FinitePresentation S M] :
    IsOpen (flatLocus R S M) := by
  sorry
