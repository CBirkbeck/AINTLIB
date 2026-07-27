/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».SpaRationalOpenComparison
import «Adic spaces».PresheafFunctoriality
import «Adic spaces».RationalBasis
import «Adic spaces».StructurePresheafLimit
import «Adic spaces».StructurePresheafBundled
import «Adic spaces».StructureSheaf
import Mathlib.Algebra.Category.Ring.FilteredColimits

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


/-! ### The stalk valuation (S3b, Wedhorn 8.14 substrate)

The germ relation on the ring stalk of the structure presheaf is a valuative
relation; the resulting point `stalkValue v` of `Spv` pulls back to
`openValue` along every germ map. -/

section StalkValue

open TopologicalSpace CategoryTheory TopCat

variable [IsTateRing A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [HasLocLiftPowerBounded A]

noncomputable local instance : DecidableEq A := Classical.decEq _

variable (A) in
/-- The underlying `CommRingCat`-presheaf of the structure presheaf. -/
abbrev spaRingPresheaf : TopCat.Presheaf CommRingCat.{u} (SpaTop A) :=
  structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToCommRingCat

/-- Germs commute with restriction (the `limitRestrict` form). -/
theorem germ_limitRestrict {V W : Opens ↥(Spa A A⁺)} (h : W ≤ V)
    {v : ↥(Spa A A⁺)} (hvW : v ∈ W) (f : ↥(limitSections V)) :
    (spaRingPresheaf A).germ W v hvW (limitRestrict h f)
      = (spaRingPresheaf A).germ V v (h hvW) f := by
  have hres := TopCat.Presheaf.germ_res_apply (spaRingPresheaf A)
    (homOfLE h) v hvW f
  rw [← hres]
  rfl

/-- **The stalk relation**: two stalk elements compare if some common
representatives over a neighbourhood compare under the point's valuation. -/
def stalkVle (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) : Prop :=
  ∃ (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) (f g : ↥(limitSections U)),
    (spaRingPresheaf A).germ U v hvU f = a
    ∧ (spaRingPresheaf A).germ U v hvU g = b
    ∧ (openValue U hvU).vle f g

/-- Any two stalk elements admit common representatives. -/
theorem exists_common_rep (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) :
    ∃ (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) (f g : ↥(limitSections U)),
      (spaRingPresheaf A).germ U v hvU f = a
      ∧ (spaRingPresheaf A).germ U v hvU g = b := by
  obtain ⟨U₁, h₁, f, rfl⟩ := (spaRingPresheaf A).exists_germ_eq a
  obtain ⟨U₂, h₂, g, rfl⟩ := (spaRingPresheaf A).exists_germ_eq b
  refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, limitRestrict inf_le_left f,
    limitRestrict inf_le_right g, ?_, ?_⟩
  · exact germ_limitRestrict inf_le_left ⟨h₁, h₂⟩ f
  · exact germ_limitRestrict inf_le_right ⟨h₁, h₂⟩ g

/-- **Witness transport**: a `stalkVle`-witness descends to any pair of
representatives after shrinking the neighbourhood. -/
theorem stalkVle_elim {v : ↥(Spa A A⁺)}
    {a b : ToType ((spaRingPresheaf A).stalk v)}
    (hab : stalkVle v a b) {U : Opens ↥(Spa A A⁺)} (hvU : v ∈ U)
    {f g : ↥(limitSections U)}
    (hf : (spaRingPresheaf A).germ U v hvU f = a)
    (hg : (spaRingPresheaf A).germ U v hvU g = b) :
    ∃ (W : Opens ↥(Spa A A⁺)) (hvW : v ∈ W) (hWU : W ≤ U),
      (openValue W hvW).vle (limitRestrict hWU f) (limitRestrict hWU g) := by
  obtain ⟨U', hvU', f', g', hf', hg', hvle⟩ := hab
  obtain ⟨W₁, hvW₁, i₁, i₁', he₁⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU hvU' f f' (hf.trans hf'.symm)
  obtain ⟨W₂, hvW₂, i₂, i₂', he₂⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU hvU' g g' (hg.trans hg'.symm)
  have hWU : W₁ ⊓ W₂ ≤ U := inf_le_left.trans (leOfHom i₁)
  have hWU' : W₁ ⊓ W₂ ≤ U' := inf_le_left.trans (leOfHom i₁')
  refine ⟨W₁ ⊓ W₂, ⟨hvW₁, hvW₂⟩, hWU, ?_⟩
  have hres₁ : limitRestrict hWU f = limitRestrict hWU' f' := by
    have h1 := congrArg
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) he₁
    exact h1
  have hres₂ : limitRestrict hWU g = limitRestrict hWU' g' := by
    have h2 := congrArg
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) he₂
    exact h2
  have hfinal := (openValue_vle_restrict hWU' ⟨hvW₁, hvW₂⟩ f' g').mp hvle
  rw [← hres₁, ← hres₂] at hfinal
  exact hfinal

theorem stalkVle_intro {v : ↥(Spa A A⁺)} {U : Opens ↥(Spa A A⁺)}
    {hvU : v ∈ U} {f g : ↥(limitSections U)}
    (h : (openValue U hvU).vle f g) :
    stalkVle v ((spaRingPresheaf A).germ U v hvU f)
      ((spaRingPresheaf A).germ U v hvU g) :=
  ⟨U, hvU, f, g, rfl, rfl, h⟩

theorem germ_add {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U)
    (f g : ↥(limitSections U)) :
    (spaRingPresheaf A).germ U v hvU (f + g)
      = (spaRingPresheaf A).germ U v hvU f
        + (spaRingPresheaf A).germ U v hvU g :=
  map_add ((spaRingPresheaf A).germ U v hvU).hom f g

theorem germ_mul {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U)
    (f g : ↥(limitSections U)) :
    (spaRingPresheaf A).germ U v hvU (f * g)
      = (spaRingPresheaf A).germ U v hvU f
        * (spaRingPresheaf A).germ U v hvU g :=
  map_mul ((spaRingPresheaf A).germ U v hvU).hom f g

theorem germ_one {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) :
    (spaRingPresheaf A).germ U v hvU 1 = 1 :=
  map_one ((spaRingPresheaf A).germ U v hvU).hom

theorem germ_zero {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺)) (hvU : v ∈ U) :
    (spaRingPresheaf A).germ U v hvU 0 = 0 :=
  map_zero ((spaRingPresheaf A).germ U v hvU).hom

theorem stalkVle_total (v : ↥(Spa A A⁺))
    (a b : ToType ((spaRingPresheaf A).stalk v)) :
    stalkVle v a b ∨ stalkVle v b a := by
  obtain ⟨U, hvU, f, g, hf, hg⟩ := exists_common_rep v a b
  rcases (openValue U hvU).vle_total f g with h | h
  · exact Or.inl (hf ▸ hg ▸ stalkVle_intro h)
  · exact Or.inr (hg ▸ hf ▸ stalkVle_intro h)

theorem stalkVle_add {v : ↥(Spa A A⁺)}
    {x y z : ToType ((spaRingPresheaf A).stalk v)}
    (hxz : stalkVle v x z) (hyz : stalkVle v y z) :
    stalkVle v (x + y) z := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict inf_le_left hvU fx).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict inf_le_left hvU fy).trans hfy
  have hfz' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_right fz)
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    germ_limitRestrict inf_le_right hvU fz
  obtain ⟨W₁, hvW₁, hW₁, hv1⟩ := stalkVle_elim hxz hvU hfx' hfz'
  obtain ⟨W₂, hvW₂, hW₂, hv2⟩ := stalkVle_elim hyz hvU hfy' hfz'
  have hvW : v ∈ W₁ ⊓ W₂ := ⟨hvW₁, hvW₂⟩
  have hd1 := (openValue_vle_restrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁) hvW _ _).mp hv1
  have hd2 := (openValue_vle_restrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂) hvW _ _).mp hv2
  -- the two z-restrictions agree (proof-irrelevant restriction paths)
  have hzz : limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
      (limitRestrict hW₂ (limitRestrict inf_le_right fz))
      = limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_right fz)) := rfl
  rw [hzz] at hd2
  have hadd := (openValue (W₁ ⊓ W₂) hvW).vle_add hd1 hd2
  have hfin := stalkVle_intro (v := v) hadd
  have hgx : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_left fx))) = x :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans hfx')
  have hgy : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_left fy))) = y :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₂ _).trans hfy')
  have hgz : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_right fz)))
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans hfz')
  have hsum : (spaRingPresheaf A).germ (W₁ ⊓ W₂) v hvW
      (limitRestrict (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
          (limitRestrict hW₁ (limitRestrict inf_le_left fx))
        + limitRestrict (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
          (limitRestrict hW₂ (limitRestrict inf_le_left fy))) = x + y :=
    (germ_add _ hvW _ _).trans (congrArg₂ (· + ·) hgx hgy)
  exact hsum ▸ hgz ▸ hfin

theorem stalkVle_mul_left {v : ↥(Spa A A⁺)}
    {x y : ToType ((spaRingPresheaf A).stalk v)}
    (h : stalkVle v x y) (z : ToType ((spaRingPresheaf A).stalk v)) :
    stalkVle v (x * z) (y * z) := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict inf_le_left hvU fx).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict inf_le_left hvU fy).trans hfy
  obtain ⟨W, hvW, hW, hv1⟩ := stalkVle_elim h hvU hfx' hfy'
  have hmul := (openValue W hvW).mul_vle_mul_left hv1
    (limitRestrict hW (limitRestrict inf_le_right fz))
  have hfin := stalkVle_intro (v := v) hmul
  have hgz : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_right fz))
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_limitRestrict _ hvW _).trans (germ_limitRestrict _ hvU _)
  have hprodx : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fx)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      = x * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvW _ _).trans (congrArg₂ (· * ·)
      ((germ_limitRestrict _ hvW _).trans hfx') hgz)
  have hprody : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fy)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      = y * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvW _ _).trans (congrArg₂ (· * ·)
      ((germ_limitRestrict _ hvW _).trans hfy') hgz)
  exact hprodx ▸ hprody ▸ hfin

theorem stalkVle_mul_comm {v : ↥(Spa A A⁺)}
    {x y : ToType ((spaRingPresheaf A).stalk v)} :
    stalkVle v (x * y) (y * x) := by
  obtain ⟨U, hvU, f, g, hf, hg⟩ := exists_common_rep v x y
  have h := (openValue U hvU).vle_mul_comm (x := f) (y := g)
  have hfin := stalkVle_intro (v := v) h
  have h1 : (spaRingPresheaf A).germ U v hvU (f * g) = x * y :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hf hg)
  have h2 : (spaRingPresheaf A).germ U v hvU (g * f) = y * x :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hg hf)
  exact h1 ▸ h2 ▸ hfin

theorem not_stalkVle_one_zero (v : ↥(Spa A A⁺)) :
    ¬ stalkVle v (1 : ToType ((spaRingPresheaf A).stalk v)) 0 := by
  intro hcon
  have h1 : (spaRingPresheaf A).germ ⊤ v (TopologicalSpace.Opens.mem_top v)
      (1 : ↥(limitSections ⊤)) = 1 := germ_one ⊤ (TopologicalSpace.Opens.mem_top v)
  have h0 : (spaRingPresheaf A).germ ⊤ v (TopologicalSpace.Opens.mem_top v)
      (0 : ↥(limitSections ⊤)) = 0 := germ_zero ⊤ (TopologicalSpace.Opens.mem_top v)
  obtain ⟨W, hvW, hWU, hres⟩ := stalkVle_elim hcon (TopologicalSpace.Opens.mem_top v) h1 h0
  have hone : limitRestrict hWU (1 : ↥(limitSections ⊤)) = 1 := map_one _
  have hzero : limitRestrict hWU (0 : ↥(limitSections ⊤)) = 0 := map_zero _
  rw [hone, hzero] at hres
  exact (openValue W hvW).not_vle_one_zero hres

theorem stalkVle_trans {v : ↥(Spa A A⁺)}
    {c b a : ToType ((spaRingPresheaf A).stalk v)}
    (hab : stalkVle v a b) (hbc : stalkVle v b c) : stalkVle v a c := by
  obtain ⟨U, hvU, f, g, hfa, hgb⟩ := exists_common_rep v a b
  obtain ⟨U', hvU', g', h', hgb', hhc⟩ := exists_common_rep v b c
  have hvU0 : v ∈ U ⊓ U' := ⟨hvU, hvU'⟩
  have ha0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_left f) = a :=
    (germ_limitRestrict _ hvU0 _).trans hfa
  have hb0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_left g) = b :=
    (germ_limitRestrict _ hvU0 _).trans hgb
  have hb0' : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_right g') = b :=
    (germ_limitRestrict _ hvU0 _).trans hgb'
  have hc0 : (spaRingPresheaf A).germ (U ⊓ U') v hvU0
      (limitRestrict inf_le_right h') = c :=
    (germ_limitRestrict _ hvU0 _).trans hhc
  obtain ⟨W₁, hvW₁, hW₁, hv1⟩ := stalkVle_elim hab hvU0 ha0 hb0
  obtain ⟨W₂, hvW₂, hW₂, hv2⟩ := stalkVle_elim hbc hvU0 hb0' hc0
  obtain ⟨W₃, hvW₃, i₃, i₃', he₃⟩ := TopCat.Presheaf.germ_eq
    (spaRingPresheaf A) v hvU0 hvU0 (limitRestrict inf_le_left g)
    (limitRestrict inf_le_right g') (hb0.trans hb0'.symm)
  have hvW : v ∈ W₁ ⊓ W₂ ⊓ W₃ := ⟨⟨hvW₁, hvW₂⟩, hvW₃⟩
  have hda := (openValue_vle_restrict
    ((inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)) hvW _ _).mp hv1
  have hdc := (openValue_vle_restrict
    ((inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)) hvW _ _).mp hv2
  have hbb : limitRestrict (inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)
      (limitRestrict hW₁ (limitRestrict inf_le_left g))
      = limitRestrict (inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_right g')) := by
    have h3 := congrArg
      (limitRestrict (inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₃)) he₃
    exact h3
  rw [hbb] at hda
  have htr := (openValue (W₁ ⊓ W₂ ⊓ W₃) hvW).vle_trans hda hdc
  have hfin := stalkVle_intro (v := v) htr
  have hga : (spaRingPresheaf A).germ (W₁ ⊓ W₂ ⊓ W₃) v hvW
      (limitRestrict (inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁)
        (limitRestrict hW₁ (limitRestrict inf_le_left f))) = a :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₁ _).trans ha0)
  have hgc : (spaRingPresheaf A).germ (W₁ ⊓ W₂ ⊓ W₃) v hvW
      (limitRestrict (inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂)
        (limitRestrict hW₂ (limitRestrict inf_le_right h'))) = c :=
    (germ_limitRestrict _ hvW _).trans
      ((germ_limitRestrict _ hvW₂ _).trans hc0)
  exact hga ▸ hgc ▸ hfin

theorem stalkVle_mul_cancel {v : ↥(Spa A A⁺)}
    {x y z : ToType ((spaRingPresheaf A).stalk v)}
    (hz : ¬ stalkVle v z 0) (hmul : stalkVle v (x * z) (y * z)) :
    stalkVle v x y := by
  obtain ⟨U₁, h₁, fx, fy, hfx, hfy⟩ := exists_common_rep v x y
  obtain ⟨U₂, h₂, fz, rfl⟩ := (spaRingPresheaf A).exists_germ_eq z
  have hvU : v ∈ U₁ ⊓ U₂ := ⟨h₁, h₂⟩
  have hfx' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx) = x :=
    (germ_limitRestrict _ hvU _).trans hfx
  have hfy' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy) = y :=
    (germ_limitRestrict _ hvU _).trans hfy
  have hfz' : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_right fz)
      = (spaRingPresheaf A).germ U₂ v h₂ fz :=
    germ_limitRestrict _ hvU _
  have hxz : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fx * limitRestrict inf_le_right fz)
      = x * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hfx' hfz')
  have hyz : (spaRingPresheaf A).germ (U₁ ⊓ U₂) v hvU
      (limitRestrict inf_le_left fy * limitRestrict inf_le_right fz)
      = y * (spaRingPresheaf A).germ U₂ v h₂ fz :=
    (germ_mul _ hvU _ _).trans (congrArg₂ (· * ·) hfy' hfz')
  obtain ⟨W, hvW, hW, hres⟩ := stalkVle_elim hmul hvU hxz hyz
  have hznz : ¬ (openValue W hvW).vle
      (limitRestrict hW (limitRestrict inf_le_right fz)) 0 := by
    intro hcon
    refine hz ⟨W, hvW, limitRestrict hW (limitRestrict inf_le_right fz), 0,
      ?_, germ_zero W hvW, hcon⟩
    exact (germ_limitRestrict _ hvW _).trans hfz'
  have hres' : (openValue W hvW).vle
      (limitRestrict hW (limitRestrict inf_le_left fx)
        * limitRestrict hW (limitRestrict inf_le_right fz))
      (limitRestrict hW (limitRestrict inf_le_left fy)
        * limitRestrict hW (limitRestrict inf_le_right fz)) := hres
  have hcanc := (openValue W hvW).vle_mul_cancel hznz hres'
  have hfin := stalkVle_intro (v := v) hcanc
  have hgx : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fx)) = x :=
    (germ_limitRestrict _ hvW _).trans hfx'
  have hgy : (spaRingPresheaf A).germ W v hvW
      (limitRestrict hW (limitRestrict inf_le_left fy)) = y :=
    (germ_limitRestrict _ hvW _).trans hfy'
  exact hgx ▸ hgy ▸ hfin

/-- **The stalk `ValuativeRel`** (Wedhorn 8.14 substrate): the germ relation
is a valuative relation on the ring stalk. -/
noncomputable def stalkValuativeRel (v : ↥(Spa A A⁺)) :
    ValuativeRel (ToType ((spaRingPresheaf A).stalk v)) where
  vle := stalkVle v
  vle_total := stalkVle_total v
  vle_trans := stalkVle_trans
  vle_add := stalkVle_add
  mul_vle_mul_left := stalkVle_mul_left
  vle_mul_cancel := stalkVle_mul_cancel
  not_vle_one_zero := not_stalkVle_one_zero v
  vle_mul_comm := fun {x y} => stalkVle_mul_comm

/-- **The valuation of the point on the stalk** of the structure presheaf. -/
noncomputable def stalkValue (v : ↥(Spa A A⁺)) :
    Spv (ToType ((spaRingPresheaf A).stalk v)) :=
  ⟨stalkValuativeRel v⟩

/-- The stalk valuation pulls back to the point's valuation on the sections
over any open neighbourhood. -/
theorem comap_germ_stalkValue {v : ↥(Spa A A⁺)} (U : Opens ↥(Spa A A⁺))
    (hvU : v ∈ U) :
    comap ((spaRingPresheaf A).germ U v hvU).hom (stalkValue v)
      = openValue U hvU := by
  refine ValuationSpectrum.ext (funext₂ fun f g => propext ?_)
  constructor
  · intro h
    obtain ⟨W, hvW, hWU, hres⟩ := stalkVle_elim h hvU rfl rfl
    exact (openValue_vle_restrict hWU hvW f g).mpr hres
  · intro h
    exact stalkVle_intro h

/-! ### Locality of the stalk (S4: Wedhorn 8.14, reduced to the shrink claim) -/

/-- A stalk unit has nonzero stalk value. -/
theorem not_stalkValue_vle_zero_of_isUnit {v : ↥(Spa A A⁺)}
    {x : ToType ((spaRingPresheaf A).stalk v)} (hx : IsUnit x) :
    ¬ (stalkValue v).vle x 0 := by
  intro h
  obtain ⟨u, rfl⟩ := hx
  have h1 := (stalkValue v).mul_vle_mul_left h ((u⁻¹ : _ˣ) : _)
  rw [Units.mul_inv, zero_mul] at h1
  exact (stalkValue v).not_vle_one_zero h1

/-- The germ of a section that is a unit is a stalk unit. -/
theorem isUnit_germ_of_isUnit {v : ↥(Spa A A⁺)} {U : Opens ↥(Spa A A⁺)}
    (hvU : v ∈ U) {f : ↥(limitSections U)} (hf : IsUnit f) :
    IsUnit ((spaRingPresheaf A).germ U v hvU f) :=
  hf.map ((spaRingPresheaf A).germ U v hvU).hom

/-- The stalk is nontrivial. -/
theorem stalk_nontrivial (v : ↥(Spa A A⁺)) :
    Nontrivial (ToType ((spaRingPresheaf A).stalk v)) := by
  refine ⟨1, 0, fun h => ?_⟩
  refine (stalkValue v).not_vle_one_zero ?_
  rw [h]
  rcases (stalkValue v).vle_total 0 0 with h0 | h0 <;> exact h0

/-- **The shrink claim** (the hard half of Wedhorn 8.14, discharged in the
S4-core step): every stalk element of nonzero value is a unit. -/
def StalkShrink (v : ↥(Spa A A⁺)) : Prop :=
  ∀ x : ToType ((spaRingPresheaf A).stalk v),
    ¬ (stalkValue v).vle x 0 → IsUnit x

/-- Under the shrink claim, units are exactly the elements of nonzero value. -/
theorem isUnit_iff_not_vle_zero {v : ↥(Spa A A⁺)} (hs : StalkShrink v)
    (x : ToType ((spaRingPresheaf A).stalk v)) :
    IsUnit x ↔ ¬ (stalkValue v).vle x 0 :=
  ⟨not_stalkValue_vle_zero_of_isUnit, hs x⟩

/-- Under the shrink claim, the nonunits are the support of the stalk
valuation. -/
theorem mem_nonunits_iff_vle_zero {v : ↥(Spa A A⁺)} (hs : StalkShrink v)
    (x : ToType ((spaRingPresheaf A).stalk v)) :
    x ∈ nonunits (ToType ((spaRingPresheaf A).stalk v))
      ↔ x ∈ (stalkValue v).supp := by
  rw [mem_supp_iff, mem_nonunits_iff, isUnit_iff_not_vle_zero hs x, not_not]

/-- **Wedhorn 8.14, packaged**: under the shrink claim the stalk is a local
ring. -/
theorem isLocalRing_stalk_of_shrink {v : ↥(Spa A A⁺)} (hs : StalkShrink v) :
    IsLocalRing (ToType ((spaRingPresheaf A).stalk v)) := by
  haveI := stalk_nontrivial v
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff_vle_zero hs] at ha hb ⊢
  rw [mem_supp_iff] at ha hb ⊢
  exact (stalkValue v).vle_add ha hb

/-- Under the shrink claim, the maximal ideal is the support of the stalk
valuation (the `val_supp` field of the `VPreObj` packaging). -/
theorem maximalIdeal_stalk_eq_supp {v : ↥(Spa A A⁺)} (hs : StalkShrink v) :
    @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk_of_shrink hs)
      = (stalkValue v).supp := by
  refine Ideal.ext fun x => ?_
  rw [@IsLocalRing.mem_maximalIdeal _ _ (isLocalRing_stalk_of_shrink hs)]
  exact mem_nonunits_iff_vle_zero hs x

/-! ### Reduction of the shrink claim to the rational level -/

variable (A) in
/-- **The rational shrink claim** (the rational-level core of Wedhorn 8.14):
an element of a completed rational localization with nonzero point value
becomes a unit on a smaller valid rational neighbourhood of the point. -/
def RationalShrink : Prop :=
  ∀ (D : RationalLocData A) (_hD : D.IsRational) (v' : Spv A)
    (hv : v' ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
    (b : presheafValue D), ¬ (pointValue D hv).vle b 0 →
    ∃ (D' : RationalLocData A) (_hD' : D'.IsRational)
      (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s),
      v' ∈ rationalOpen D'.T D'.s ∧ IsUnit (restrictionMapHom D D' h b)

/-- **Reduction of the stalk shrink claim to the rational one**: representing
a nonzero-value germ over a rational neighbourhood, shrinking by
`RationalShrink`, and transporting the unit through the rational-open
comparison `limitEval`. -/
theorem stalkShrink_of_rationalShrink (hRS : RationalShrink A)
    (v : ↥(Spa A A⁺)) : StalkShrink v := by
  intro x hx
  obtain ⟨U, hvU, f, rfl⟩ := (spaRingPresheaf A).exists_germ_eq x
  -- the section has nonzero value
  have hnz : ¬ (openValue U hvU).vle f 0 := by
    intro hcon
    refine hx ⟨U, hvU, f, 0, rfl, germ_zero U hvU, hcon⟩
  -- compute at the defining rational index
  set i := (exists_rationalIndex_mem hvU).choose with hidef
  have hi := (exists_rationalIndex_mem hvU).choose_spec
  have hnzD : ¬ (pointValue i.D hi).vle (limitEvalHom i f) 0 :=
    fun hcon => hnz hcon
  -- rational shrink
  obtain ⟨D', hD', hsub, hvD', hunit⟩ := hRS i.D i.isRational
    (v : Spv A) hi (limitEvalHom i f) hnzD
  -- the smaller rational open, as an open of the subtype
  have hW'U : spaOpens D' ≤ U :=
    (spaOpen_subset_of_rationalOpen_subset hsub).trans i.subset
  have hvW' : v ∈ spaOpens D' := mem_spaOpen.mpr hvD'
  -- the restricted section is a unit via the rational-open comparison
  have hcomp : limitEval hD' (limitRestrict hW'U f)
      = restrictionMapHom i.D D' hsub (limitEvalHom i f) :=
    (f.2 i ((RationalIndex.self D' hD').mono hW'U) hsub).symm
  have hfunit : IsUnit (limitRestrict hW'U f) := by
    have h1 : IsUnit (limitEval hD' (limitRestrict hW'U f)) := by
      rw [hcomp]
      exact hunit
    have h2 := h1.map (limitEval hD').symm.toRingHom
    rwa [show (limitEval hD').symm.toRingHom (limitEval hD'
        (limitRestrict hW'U f)) = limitRestrict hW'U f from
      (limitEval hD').symm_apply_apply _] at h2
  have hgerm : (spaRingPresheaf A).germ (spaOpens D') v hvW'
      (limitRestrict hW'U f) = (spaRingPresheaf A).germ U v hvU f :=
    germ_limitRestrict hW'U hvW' f
  rw [← hgerm]
  exact isUnit_germ_of_isUnit hvW' hfunit

end StalkValue

end ValuationSpectrum

end
