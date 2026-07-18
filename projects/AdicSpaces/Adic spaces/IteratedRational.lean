/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison
import «Adic spaces».CompletionLocalization

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13): helpers

Helper lemmas about `canonicalMap` and `restrictionMapHom` that feed into the
iterated rational identification and the Laurent bridges. The Wedhorn
Example 6.38 machinery used to live here under the name `Example638`; that
block now lives in `«Adic spaces».Example638` (extracted to break the cycle
with `LaurentRefinement`).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Helpers

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- `D₀.canonicalMap D₀.s` is a unit in `presheafValue D₀`, because `D₀.s`
becomes a unit under `algebraMap A (Localization.Away D₀.s)` (definition of
localization) and `D₀.coeRingHom` preserves units. -/
theorem canonicalMap_s_isUnit (D₀ : RationalLocData A) :
    IsUnit (D₀.canonicalMap D₀.s) := by
  simp only [RationalLocData.canonicalMap, RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map D₀.coeRingHom
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

/-- Compatibility: `restrictionMapHom D₀ D' hsub ∘ D₀.canonicalMap = D'.canonicalMap`.
Follows directly from `UniformSpace.Completion.extensionHom_coe` + the
`IsLocalization.Away.lift_eq` identity for the underlying alg map. -/
theorem restrictionMapHom_canonicalMap (D₀ D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D₀.T D₀.s) (a : A) :
    restrictionMapHom D₀ D' h (D₀.canonicalMap a) = D'.canonicalMap a := by
  letI := D₀.uniformSpace
  letI := D₀.isTopologicalRing
  letI := D₀.isUniformAddGroup
  letI := D'.uniformSpace
  letI := D'.isTopologicalRing
  letI := D'.isUniformAddGroup
  change restrictionMapHom D₀ D' h
      (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
      D'.coeRingHom (algebraMap A (Localization.Away D'.s) a)
  have h_ext :
      restrictionMapHom D₀ D' h
        (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a)) =
      restrictionMapAlg D₀ D' h (algebraMap A (Localization.Away D₀.s) a) :=
    UniformSpace.Completion.extensionHom_coe (restrictionMapAlg D₀ D' h)
      (restrictionMapAlg_continuous D₀ D' h)
      (algebraMap A (Localization.Away D₀.s) a)
  rw [h_ext, restrictionMapAlg, IsLocalization.Away.lift_eq]
  rfl

end Helpers

-- DELETED 2026-06-11 (false orphan): the audit-pass-3 section held only
-- `presheafValue_eq_quotient_AlangleX_iterated`, a `sorry` whose own docstring
-- flagged it FALSE (b2_log #6: `MvPolynomial D.T A ⧸ (s·Xₜ − t)` = the *algebraic*
-- `A[1/s]`, but `presheafValue D` is its *completion* in the localization topology —
-- counterexample `A = ℤ` p-adic, `s = p`: RHS ≅ ℤ, LHS ≅ ℚ_p). It was referenced
-- nowhere, and the FAITHFUL Wedhorn-7.55/Example-6.38 comparison iso `presheafValue D
-- ≃+* C⧸ker` (Tate algebra `restrictedMvPowerSeriesSubring`, NOT `MvPolynomial`) has
-- since landed in `Example638.lean`/`MvTateAlgebraTopology.lean` (axiom-clean). Per the
-- quote-or-delete discipline (false + orphan + superseded), the dead stub is removed.

end ValuationSpectrum
