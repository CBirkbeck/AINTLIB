/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».SpaRationalOpenComparison
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».RationalBasis
import «Adic spaces».StructurePresheafLimit

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


/-! ### The point valuation on the sections over an arbitrary open (S3a)

Over a Tate pair with integrally-closed plus-ring, the rational opens form a
basis (`exists_isRational_spaOpen_subset`), and the point valuation extends to
the projective-limit sections `limitSections V` over any open neighbourhood,
coherently with all restrictions. -/

section OpenValue

open TopologicalSpace

variable [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [HasLocLiftPowerBounded A]

noncomputable local instance : DecidableEq A := Classical.decEq _

/-- Every open neighbourhood admits a valid rational index containing the
point (the rational basis, in `RationalIndex` form). -/
theorem exists_rationalIndex_mem {V : Opens ↥(Spa A A⁺)} {v : ↥(Spa A A⁺)}
    (hv : v ∈ V) : ∃ i : RationalIndex V,
      (v : Spv A) ∈ (rationalOpen i.D.T i.D.s ∩ Spa A A⁺ : Set (Spv A)) := by
  obtain ⟨D, hDrat, hvD, hDV⟩ := exists_isRational_spaOpen_subset V.2 hv
  exact ⟨⟨D, hDrat, hDV⟩, hvD, v.2⟩

/-- **The valuation of a point on the sections over any open neighbourhood**:
pull the point valuation of a rational neighbourhood back along the rational
evaluation. Independence of the choice is `comap_limitEvalHom_pointValue`. -/
noncomputable def openValue (V : Opens ↥(Spa A A⁺)) {v : ↥(Spa A A⁺)}
    (hv : v ∈ V) : Spv ↥(limitSections V) :=
  comap (limitEvalHom (exists_rationalIndex_mem hv).choose)
    (pointValue _ (exists_rationalIndex_mem hv).choose_spec)

/-- Evaluation-restriction compatibility: restricting a compatible family and
evaluating is evaluating (the defining property of the limit). -/
theorem restrictionMapHom_comp_limitEvalHom {V : Opens ↥(Spa A A⁺)}
    (i k : RationalIndex V)
    (h : rationalOpen k.D.T k.D.s ⊆ rationalOpen i.D.T i.D.s) :
    (restrictionMapHom i.D k.D h).comp (limitEvalHom i) = limitEvalHom k :=
  RingHom.ext fun x => x.2 i k h

/-- **Choice independence**: any rational index containing the point computes
`openValue`. -/
theorem comap_limitEvalHom_pointValue {V : Opens ↥(Spa A A⁺)}
    {v : ↥(Spa A A⁺)} (hv : v ∈ V) (i : RationalIndex V)
    (hvi : (v : Spv A) ∈ (rationalOpen i.D.T i.D.s ∩ Spa A A⁺ : Set (Spv A))) :
    comap (limitEvalHom i) (pointValue i.D hvi) = openValue V hv := by
  set j := (exists_rationalIndex_mem hv).choose with hjdef
  have hj := (exists_rationalIndex_mem hv).choose_spec
  -- refine at `v` inside the open intersection of the two rational opens
  obtain ⟨E, hErat, hvE, hEsub⟩ := exists_isRational_spaOpen_subset
    (IsOpen.inter (isOpen_spaOpen i.D) (isOpen_spaOpen j.D))
    (Set.mem_inter (mem_spaOpen.mpr hvi.1) (mem_spaOpen.mpr hj.1))
  have hEi : rationalOpen E.T E.s ⊆ rationalOpen i.D.T i.D.s :=
    spaOpen_subset_iff.mp (hEsub.trans Set.inter_subset_left)
  have hEj : rationalOpen E.T E.s ⊆ rationalOpen j.D.T j.D.s :=
    spaOpen_subset_iff.mp (hEsub.trans Set.inter_subset_right)
  have hvE' : (v : Spv A) ∈ (rationalOpen E.T E.s ∩ Spa A A⁺ : Set (Spv A)) :=
    ⟨mem_spaOpen.mp hvE, v.2⟩
  have key : ∀ (l : RationalIndex V)
      (hvl : (v : Spv A) ∈ (rationalOpen l.D.T l.D.s ∩ Spa A A⁺ : Set (Spv A)))
      (hEl : rationalOpen E.T E.s ⊆ rationalOpen l.D.T l.D.s),
      comap (limitEvalHom l) (pointValue l.D hvl)
        = comap (limitEvalHom
            (⟨E, hErat, (hEsub.trans Set.inter_subset_left).trans i.subset⟩
              : RationalIndex V))
          (pointValue E hvE') := by
    intro l hvl hEl
    have hS2 := comap_restrictionMapHom_pointValue l.D E hEl hvE'
    have hpv : pointValue l.D hvl
        = comap (restrictionMapHom l.D E hEl) (pointValue E hvE') := by
      rw [hS2]
    rw [hpv]
    rw [show comap (limitEvalHom l)
        (comap (restrictionMapHom l.D E hEl) (pointValue E hvE'))
      = comap ((restrictionMapHom l.D E hEl).comp (limitEvalHom l))
          (pointValue E hvE') from by rw [comap_comp]; rfl]
    rw [restrictionMapHom_comp_limitEvalHom l
      ⟨E, hErat, (hEsub.trans Set.inter_subset_left).trans i.subset⟩ hEl]
  rw [key i hvi hEi, ← key j hj hEj]
  rfl

/-- **Restriction coherence**: the point's valuation is intertwined by the
presheaf restrictions. -/
theorem comap_limitRestrict_openValue {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) :
    comap (limitRestrict h) (openValue W hvW) = openValue V (h hvW) := by
  set k := (exists_rationalIndex_mem hvW).choose with hkdef
  have hk := (exists_rationalIndex_mem hvW).choose_spec
  have h1 : openValue W hvW = comap (limitEvalHom k) (pointValue k.D hk) := rfl
  rw [h1]
  rw [show comap (limitRestrict h) (comap (limitEvalHom k) (pointValue k.D hk))
      = comap ((limitEvalHom k).comp (limitRestrict h)) (pointValue k.D hk)
    from by rw [comap_comp]; rfl]
  rw [show (limitEvalHom k).comp (limitRestrict h)
      = limitEvalHom (k.mono h) from RingHom.ext fun x => rfl]
  exact comap_limitEvalHom_pointValue (h hvW) (k.mono h) hk

/-- The `vle`-relation of the point is restriction-invariant. -/
theorem openValue_vle_restrict {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) (f g : ↥(limitSections V)) :
    (openValue V (h hvW)).vle f g
      ↔ (openValue W hvW).vle (limitRestrict h f) (limitRestrict h g) := by
  rw [← comap_limitRestrict_openValue h hvW, comap_vle]

end OpenValue

end ValuationSpectrum

end
