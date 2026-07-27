/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».SpaRationalOpenComparison
import «Adic spaces».PresheafFunctoriality

/-!
# Stalk theory of the structure presheaf, I: point valuations (Wedhorn §8.3)

The valuation-theoretic substrate of the stalk package for `Spa (A, A⁺)`:

* `ValuationSpectrum.pointValue` : the unique Spa-point of `presheafValue D`
  over a Spa-point of `A` inside `R(D.T/D.s)` — Wedhorn Proposition 8.2 read
  backwards through `spaPresheafValueEquivRationalOpen`;
* `ValuationSpectrum.comap_pointValue` / `eq_pointValue_of_comap_eq` : the
  defining property and its uniqueness;
* `ValuationSpectrum.comap_restrictionMapHom_pointValue` : **germ coherence**
  — point valuations are intertwined by the restriction maps, the input for
  the valuation on the stalk (Wedhorn 8.14).
-/

noncomputable section

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **The point valuation on a rational value** (Wedhorn 8.2 read backwards): a
Spa-point of `A` inside the rational subset `R(D.T/D.s)` induces a Spa-point of
the completed rational localization `presheafValue D`, its unique extension. -/
def pointValue (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    Spv (presheafValue D) :=
  ((spaPresheafValueEquivRationalOpen D).symm ⟨v, hv⟩).val

theorem pointValue_mem_spa (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    pointValue D hv ∈ Spa (presheafValue D) (presheafValue D)⁺ :=
  ((spaPresheafValueEquivRationalOpen D).symm ⟨v, hv⟩).property

theorem pointValue_isContinuous (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    (pointValue D hv).IsContinuous :=
  ((mem_spa_iff _).mp (pointValue_mem_spa D hv)).1

/-- The defining property: the point valuation pulls back to the point. -/
theorem comap_pointValue (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap D.canonicalMap (pointValue D hv) = v :=
  congrArg Subtype.val
    ((spaPresheafValueEquivRationalOpen D).apply_symm_apply ⟨v, hv⟩)

/-- Uniqueness: any continuous valuation on the value pulling back to the point
is the point valuation. -/
theorem eq_pointValue_of_comap_eq (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
    {w : Spv (presheafValue D)} (hw : w.IsContinuous)
    (h : comap D.canonicalMap w = v) :
    w = pointValue D hv :=
  comap_canonicalMap_inj_of_isContinuous D hw
    (pointValue_isContinuous D hv) (h.trans (comap_pointValue D hv).symm)

/-- **Restriction compatibility of point valuations** (the germ coherence, S2):
pulling the point valuation of the smaller rational back along the restriction
map gives the point valuation of the larger rational. -/
theorem comap_restrictionMapHom_pointValue [HasLocLiftPowerBounded A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) {v : Spv A}
    (hv' : v ∈ (rationalOpen D'.T D'.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap (restrictionMapHom D D' h) (pointValue D' hv')
      = pointValue D ⟨h hv'.1, hv'.2⟩ := by
  refine eq_pointValue_of_comap_eq D ⟨h hv'.1, hv'.2⟩
    (comap_isContinuous (restrictionMapHom_continuous D D' h)
      (pointValue_isContinuous D' hv')) ?_
  have hcomp : (restrictionMapHom D D' h).comp D.canonicalMap
      = D'.canonicalMap :=
    RingHom.ext (restrictionMapHom_canonicalMap_generic D D' h)
  calc comap D.canonicalMap
        (comap (restrictionMapHom D D' h) (pointValue D' hv'))
      = comap ((restrictionMapHom D D' h).comp D.canonicalMap)
          (pointValue D' hv') := by
        rw [comap_comp]
        rfl
    _ = comap D'.canonicalMap (pointValue D' hv') := by rw [hcomp]
    _ = v := comap_pointValue D' hv'

end ValuationSpectrum

end
