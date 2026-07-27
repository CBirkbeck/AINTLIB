/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.FrobeniusLimit

/-!
# Equivariance of the point and open valuations under the Frobenius (D-iii-4a)

The valuation-level heart of `val_compat`: the point-valuation equivariance
of the Huber value equivalence (both directions), and the open-valuation
equivariance of the Frobenius transport of limit sections
(`comap_limitFrobHom_openValue`).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter CategoryTheory Opposite

set_option linter.overlappingInstances false

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} {B : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DecidableEq B] [PlusSubring A] [PlusSubring B]
  [IsHuberRing A] [IsHuberRing B]

/-- **Equivariance of the point valuation under the Huber value
equivalence**: the pull-back of the transported rational's point valuation
along the forward equivalence is the original rational's point valuation at
the pulled-back point. -/
theorem comap_presheafValueRingEquivHuber_pointValue
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom)
    (D : RationalLocData A) {v' : Spv B}
    (hv' : v' ∈ (rationalOpen (D.mapHuber e he he').T
      (D.mapHuber e he he').s ∩ Spa B B⁺ : Set (Spv B))) :
    comap (presheafValueRingEquivHuber e he he' D).toRingHom
        (pointValue (D.mapHuber e he he') hv')
      = pointValue D ⟨(mem_rationalOpen_mapHuber_iff e he he' hplus D).mp hv'.1,
          comap_mem_spa_map e (A⁺ : Subring A) he (hplus ▸ hv'.2)⟩ := by
  refine eq_pointValue_of_comap_eq D _
    (comap_isContinuous (presheafValueRingEquivHuber_continuous e he he' D)
      (pointValue_isContinuous (D.mapHuber e he he') hv')) ?_
  have hcomp : ((presheafValueRingEquivHuber e he he' D).toRingHom.comp
      D.canonicalMap) = ((D.mapHuber e he he').canonicalMap).comp e.toRingHom :=
    RingHom.ext fun a => presheafValueRingEquivHuber_canonicalMap e he he' D a
  calc comap D.canonicalMap
        (comap (presheafValueRingEquivHuber e he he' D).toRingHom
          (pointValue (RationalLocData.mapHuber e he he' D) hv'))
      = comap ((presheafValueRingEquivHuber e he he' D).toRingHom.comp
          D.canonicalMap)
          (pointValue (RationalLocData.mapHuber e he he' D) hv') := by
        rw [ValuationSpectrum.comap_comp]
        rfl
    _ = comap (((D.mapHuber e he he').canonicalMap).comp e.toRingHom)
          (pointValue (RationalLocData.mapHuber e he he' D) hv') := by
        rw [hcomp]
    _ = comap e.toRingHom (comap ((D.mapHuber e he he').canonicalMap)
          (pointValue (RationalLocData.mapHuber e he he' D) hv')) := by
        rw [ValuationSpectrum.comap_comp]
        rfl
    _ = comap e.toRingHom v' := by
        rw [comap_pointValue (D.mapHuber e he he') hv']

/-- The symm-direction canonical-map naturality of the Huber value
equivalence. -/
theorem presheafValueRingEquivHuber_symm_canonicalMap
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) (b : B) :
    (presheafValueRingEquivHuber e he he' D).symm
        ((D.mapHuber e he he').canonicalMap b)
      = D.canonicalMap (e.symm b) := by
  refine (presheafValueRingEquivHuber e he he' D).symm_apply_eq.mpr ?_
  rw [presheafValueRingEquivHuber_canonicalMap e he he' D (e.symm b),
    e.apply_symm_apply]

/-- **Equivariance of the point valuation, symm direction**: pulling the
original rational's point valuation back along the inverse equivalence gives
the transported rational's point valuation at the pushed point. -/
theorem comap_presheafValueRingEquivHuber_symm_pointValue
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (D : RationalLocData A) {v : Spv A}
    (hv : v ∈ (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
    {v' : Spv B}
    (hv' : v' ∈ (rationalOpen (D.mapHuber e he he').T
      (D.mapHuber e he he').s ∩ Spa B B⁺ : Set (Spv B)))
    (hcom : comap e.toRingHom v' = v) :
    comap (presheafValueRingEquivHuber e he he' D).symm.toRingHom
        (pointValue D hv)
      = pointValue (D.mapHuber e he he') hv' := by
  refine eq_pointValue_of_comap_eq (D.mapHuber e he he') hv'
    (comap_isContinuous
      (presheafValueRingEquivHuber_symm_continuous e he he' D)
      (pointValue_isContinuous D hv)) ?_
  have hcomp : ((presheafValueRingEquivHuber e he he' D).symm.toRingHom.comp
      (D.mapHuber e he he').canonicalMap)
      = (D.canonicalMap).comp e.symm.toRingHom :=
    RingHom.ext fun b =>
      presheafValueRingEquivHuber_symm_canonicalMap e he he' D b
  calc comap (D.mapHuber e he he').canonicalMap
        (comap (presheafValueRingEquivHuber e he he' D).symm.toRingHom
          (pointValue D hv))
      = comap ((presheafValueRingEquivHuber e he he' D).symm.toRingHom.comp
          (D.mapHuber e he he').canonicalMap) (pointValue D hv) := by
        rw [ValuationSpectrum.comap_comp]
        rfl
    _ = comap ((D.canonicalMap).comp e.symm.toRingHom) (pointValue D hv) := by
        rw [hcomp]
    _ = comap e.symm.toRingHom (comap D.canonicalMap (pointValue D hv)) := by
        rw [ValuationSpectrum.comap_comp]
        rfl
    _ = comap e.symm.toRingHom v := by rw [comap_pointValue D hv]
    _ = v' := by
        rw [← hcom]
        exact comap_comap_of_ringEquiv e v'

end ValuationSpectrum

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- The transported-side membership of the Frobenius image point (inlined
backward direction of the transport iff, split for kernel budget). -/
theorem spaFrob_mem_frobIndex_datum (k : ℤ)
    {W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (E : RationalIndex (frobOpens p F k W))
    {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hvE : (v : Spv (Ainf p F)) ∈ (rationalOpen E.D.T E.D.s
      ∩ Spa (Ainf p F) ((Ainf p F)⁺) : Set (Spv (Ainf p F)))) :
    (spaFrob p F k v).1
      ∈ (rationalOpen (frobIndex p F k E).D.T (frobIndex p F k E).D.s
        ∩ Spa (Ainf p F) ((Ainf p F)⁺) : Set (Spv (Ainf p F))) := by
  have hround : comap (frobPow p F (-k)).toRingHom (spaFrob p F k v).1
      = (v : Spv (Ainf p F)) :=
    congrArg Subtype.val (spaFrob_spaFrob p F k v)
  obtain ⟨hspa, hvle, hs0⟩ := hvE.1
  refine ⟨⟨(spaFrob p F k v).2, fun t' ht' => ?_, fun h0 => ?_⟩,
    (spaFrob p F k v).2⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp
      (show t' ∈ E.D.T.image (frobPow p F (-k)) from ht')
    have := hvle t ht
    rw [← hround] at this
    rw [comap_vle] at this
    exact this
  · refine hs0 ?_
    rw [← hround, comap_vle, map_zero]
    exact h0

private theorem limitEvalHom_limitFrobHom (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (E : RationalIndex (frobOpens p F k W)) :
    (limitEvalHom E).comp (limitFrobHom p F k W)
      = ((presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm.toRingHom).comp (limitEvalHom (frobIndex p F k E)) := by
  refine RingHom.ext fun x => ?_
  show limitEvalHom E (limitFrobHom p F k W x)
    = (presheafValueRingEquivHuber (frobPow p F (-k))
        (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
        E.D).symm.toRingHom (limitEvalHom (frobIndex p F k E) x)
  exact (limitEvalHom_apply E (limitFrobHom p F k W x)).trans
    ((limitFrobHom_component p F k W x E).trans
      (congrArg (⇑(presheafValueRingEquivHuber (frobPow p F (-k))
        (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
        E.D).symm)
        (limitEvalHom_apply (frobIndex p F k E) x).symm))

private theorem comap_comp_apply {R S T' : Type*} [CommRing R] [CommRing S]
    [CommRing T'] (f : R →+* S) (g : S →+* T') (w : Spv T') :
    comap (g.comp f) w = comap f (comap g w) := rfl

private theorem stepMid (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (E : RationalIndex (frobOpens p F k W))
    (hvE : (v : Spv (Ainf p F)) ∈ (rationalOpen E.D.T E.D.s
      ∩ Spa (Ainf p F) ((Ainf p F)⁺) : Set (Spv (Ainf p F)))) :
    comap (limitFrobHom p F k W)
        (comap (limitEvalHom E) (pointValue E.D hvE))
      = comap (limitEvalHom (frobIndex p F k E))
          (pointValue (frobIndex p F k E).D
            (spaFrob_mem_frobIndex_datum p F k E hvE)) := by
  have hround : comap (frobPow p F (-k)).toRingHom (spaFrob p F k v).1
      = (v : Spv (Ainf p F)) :=
    congrArg Subtype.val (spaFrob_spaFrob p F k v)
  have hpoint := ValuationSpectrum.comap_presheafValueRingEquivHuber_symm_pointValue
    (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k)) E.D hvE
    (spaFrob_mem_frobIndex_datum p F k E hvE) hround
  have h1 : comap (limitFrobHom p F k W)
      (comap (limitEvalHom E) (pointValue E.D hvE))
      = comap ((limitEvalHom E).comp (limitFrobHom p F k W))
          (pointValue E.D hvE) :=
    (comap_comp_apply (limitFrobHom p F k W) (limitEvalHom E)
      (pointValue E.D hvE)).symm
  have h2 : comap ((limitEvalHom E).comp (limitFrobHom p F k W))
      (pointValue E.D hvE)
      = comap (((presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm.toRingHom).comp (limitEvalHom (frobIndex p F k E)))
          (pointValue E.D hvE) :=
    congrArg (fun h => ValuationSpectrum.comap h (pointValue E.D hvE))
      (limitEvalHom_limitFrobHom p F k W E)
  have h3 : comap (((presheafValueRingEquivHuber (frobPow p F (-k))
      (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
      E.D).symm.toRingHom).comp (limitEvalHom (frobIndex p F k E)))
      (pointValue E.D hvE)
      = comap (limitEvalHom (frobIndex p F k E))
          (comap (presheafValueRingEquivHuber (frobPow p F (-k))
            (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
            E.D).symm.toRingHom (pointValue E.D hvE)) :=
    comap_comp_apply (limitEvalHom (frobIndex p F k E)) _
      (pointValue E.D hvE)
  have h4 : comap (limitEvalHom (frobIndex p F k E))
      (comap (presheafValueRingEquivHuber (frobPow p F (-k))
        (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
        E.D).symm.toRingHom (pointValue E.D hvE))
      = comap (limitEvalHom (frobIndex p F k E))
          (pointValue (frobIndex p F k E).D
            (spaFrob_mem_frobIndex_datum p F k E hvE)) :=
    congrArg (ValuationSpectrum.comap
      (limitEvalHom (frobIndex p F k E))) hpoint
  exact ((h1.trans h2).trans h3).trans h4

/-- **Equivariance of the open valuation under the Frobenius transport**
(the section-level heart of `val_compat`). -/
theorem comap_limitFrobHom_openValue (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hv : v ∈ frobOpens p F k W) :
    comap (limitFrobHom p F k W) (openValue (frobOpens p F k W) hv)
      = openValue W (show spaFrob p F k v ∈ W from hv) := by
  obtain ⟨E, hvE⟩ := exists_rationalIndex_mem hv
  rw [← comap_limitEvalHom_pointValue hv E hvE]
  rw [stepMid p F k W E hvE]
  exact comap_limitEvalHom_pointValue _ (frobIndex p F k E)
    (spaFrob_mem_frobIndex_datum p F k E hvE)

/-- The Frobenius preimages of opens roundtrip. -/
theorem frobOpens_frobOpens (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    frobOpens p F k (frobOpens p F (-k) W) = W := by
  refine Opens.ext ?_
  ext v
  show spaFrob p F (-k) (spaFrob p F k v) ∈ W ↔ v ∈ W
  rw [spaFrob_spaFrob p F k v]

/-- **Germ naturality of the ambient Frobenius stalk transport.** -/
theorem ringStalkMap_ambientFrob_germ (k : ℤ)
    (x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hx : spaFrob p F k x ∈ U) (f : ↥(limitSections U)) :
    (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom
        ((yAmbientPresheafedSpace p F).ringPresheaf.germ U
          (spaFrob p F k x) hx f)
      = (yAmbientPresheafedSpace p F).ringPresheaf.germ
          (frobOpens p F k U) x hx (limitFrobHom p F k U f) := by
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := CommRingCat) U (ConcreteCategory.hom (ambientFrobHom p F k).base x)
    hx (Functor.whiskerRight (ambientFrobHom p F k).c
      CompleteTopCommRingCat.forgetToCommRingCat) f
  have h2 := TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat
    (ambientFrobHom p F k).base
    ((yAmbientPresheafedSpace p F).presheaf
      ⋙ CompleteTopCommRingCat.forgetToCommRingCat) U x hx
    ((Functor.whiskerRight (ambientFrobHom p F k).c
      CompleteTopCommRingCat.forgetToCommRingCat).app (op U) f)
  show (ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward CommRingCat
      (ambientFrobHom p F k).base
      ((yAmbientPresheafedSpace p F).presheaf
        ⋙ CompleteTopCommRingCat.forgetToCommRingCat) x))
      ((ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat
          (ConcreteCategory.hom (ambientFrobHom p F k).base x)).map
        (Functor.whiskerRight (ambientFrobHom p F k).c
          CompleteTopCommRingCat.forgetToCommRingCat)))
        ((ConcreteCategory.hom
          (TopCat.Presheaf.germ
            ((yAmbientPresheafedSpace p F).presheaf
              ⋙ CompleteTopCommRingCat.forgetToCommRingCat) U
            (ConcreteCategory.hom (ambientFrobHom p F k).base x) hx)) f))
      = _
  rw [h1]
  exact h2

/-- The other-order roundtrip. -/
theorem frobOpens_frobOpens' (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    frobOpens p F (-k) (frobOpens p F k W) = W := by
  have h := frobOpens_frobOpens p F (-k) W
  rwa [neg_neg] at h

/-- The open-valuation `vle` transports along the Frobenius (both sides as a
propositional equality). -/
theorem openValue_vle_frobTransport (k : ℤ)
    (U' : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (hx : x ∈ frobOpens p F k U') (s t : ↥(limitSections U')) :
    ((openValue (frobOpens p F k U') hx).vle
        (limitFrobHom p F k U' s) (limitFrobHom p F k U' t))
      = ((openValue U' (show spaFrob p F k x ∈ U' from hx)).vle s t) := by
  rw [← comap_limitFrobHom_openValue p F k U' hx]
  exact (comap_vle (limitFrobHom p F k U') _ s t).symm

/-- Transport of `stalkVle` along equalities of the arguments. -/
theorem stalkVle_congr {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    {a a' b b' : ToType ((spaRingPresheaf (Ainf p F)).stalk v)}
    (ha : a = a') (hb : b = b') (h : stalkVle v a b) : stalkVle v a' b' := by
  subst ha
  subst hb
  exact h

/-- **The ambient stalk-value equivariance** (D-iii-4b, the ambient core of
`val_compat`): pulling the stalk valuation back along the Frobenius stalk
transport gives the stalk valuation at the image point. -/
theorem comap_ringStalkMap_ambientFrob_stalkValue (k : ℤ)
    (x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    comap (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom
        (stalkValue x)
      = stalkValue (spaFrob p F k x) := by
  refine ValuationSpectrum.ext (funext₂ fun a b => propext ⟨?_, ?_⟩)
  · -- forward: comap-vle ⇒ stalkVle at the image point
    intro hab
    obtain ⟨U, hxU, f, g, hf, hg⟩ := exists_common_rep (spaFrob p F k x) a b
    have hMa : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom a
        = (yAmbientPresheafedSpace p F).ringPresheaf.germ
            (frobOpens p F k U) x hxU (limitFrobHom p F k U f) := by
      rw [← hf]
      exact ringStalkMap_ambientFrob_germ p F k x U hxU f
    have hMb : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom b
        = (yAmbientPresheafedSpace p F).ringPresheaf.germ
            (frobOpens p F k U) x hxU (limitFrobHom p F k U g) := by
      rw [← hg]
      exact ringStalkMap_ambientFrob_germ p F k x U hxU g
    have hab' := stalkVle_congr p F hMa hMb hab
    obtain ⟨W, hxW, hWU, hvle⟩ := stalkVle_elim hab' hxU rfl rfl
    have hEq : frobOpens p F k (frobOpens p F (-k) W) = W :=
      frobOpens_frobOpens p F k W
    have hle1 : frobOpens p F k (frobOpens p F (-k) W) ≤ W := hEq.le
    have hxW' : x ∈ frobOpens p F k (frobOpens p F (-k) W) := hEq.symm ▸ hxW
    have hU'U : frobOpens p F (-k) W ≤ U := by
      have h := frobOpens_mono p F (-k) hWU
      rwa [frobOpens_frobOpens' p F k U] at h
    have hvle2 := (openValue_vle_restrict hle1 hxW'
      (limitRestrict hWU (limitFrobHom p F k U f))
      (limitRestrict hWU (limitFrobHom p F k U g))).mp hvle
    have hcolf : limitRestrict hle1
        (limitRestrict hWU (limitFrobHom p F k U f))
        = limitFrobHom p F k (frobOpens p F (-k) W)
            (limitRestrict hU'U f) := by
      have hcomp := congr_fun (congrArg DFunLike.coe
        (limitRestrict_comp hle1 hWU)) (limitFrobHom p F k U f)
      refine (hcomp.trans ?_)
      exact (limitFrobHom_limitRestrict p F k hU'U f).symm
    have hcolg : limitRestrict hle1
        (limitRestrict hWU (limitFrobHom p F k U g))
        = limitFrobHom p F k (frobOpens p F (-k) W)
            (limitRestrict hU'U g) := by
      have hcomp := congr_fun (congrArg DFunLike.coe
        (limitRestrict_comp hle1 hWU)) (limitFrobHom p F k U g)
      refine (hcomp.trans ?_)
      exact (limitFrobHom_limitRestrict p F k hU'U g).symm
    have hvle3 : (openValue (frobOpens p F k (frobOpens p F (-k) W))
        hxW').vle
        (limitFrobHom p F k (frobOpens p F (-k) W) (limitRestrict hU'U f))
        (limitFrobHom p F k (frobOpens p F (-k) W)
          (limitRestrict hU'U g)) := hcolf ▸ hcolg ▸ hvle2
    have hcv := Eq.mp (openValue_vle_frobTransport p F k
      (frobOpens p F (-k) W) hxW'
      (limitRestrict hU'U f) (limitRestrict hU'U g)) hvle3
    have hst := stalkVle_intro (v := spaFrob p F k x) hcv
    exact stalkVle_congr p F
      ((germ_limitRestrict hU'U _ f).trans hf)
      ((germ_limitRestrict hU'U _ g).trans hg) hst
  · -- backward
    intro hab
    obtain ⟨U, hxU, f, g, hf, hg⟩ := exists_common_rep (spaFrob p F k x) a b
    obtain ⟨W', hxW', hW'U, hvle⟩ := stalkVle_elim hab hxU hf hg
    have hxF : x ∈ frobOpens p F k W' := hxW'
    have hcv := Eq.mpr (openValue_vle_frobTransport p F k W' hxF
      (limitRestrict hW'U f) (limitRestrict hW'U g)) hvle
    have hst := stalkVle_intro (v := x) hcv
    have hMa : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom a
        = (yAmbientPresheafedSpace p F).ringPresheaf.germ
            (frobOpens p F k U) x hxU (limitFrobHom p F k U f) := by
      rw [← hf]
      exact ringStalkMap_ambientFrob_germ p F k x U hxU f
    have hMb : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom b
        = (yAmbientPresheafedSpace p F).ringPresheaf.germ
            (frobOpens p F k U) x hxU (limitFrobHom p F k U g) := by
      rw [← hg]
      exact ringStalkMap_ambientFrob_germ p F k x U hxU g
    have hgf : (spaRingPresheaf (Ainf p F)).germ (frobOpens p F k W') x hxF
        (limitFrobHom p F k W' (limitRestrict hW'U f))
        = (spaRingPresheaf (Ainf p F)).germ (frobOpens p F k U) x hxU
            (limitFrobHom p F k U f) := by
      rw [limitFrobHom_limitRestrict p F k hW'U f]
      exact germ_limitRestrict (frobOpens_mono p F k hW'U) hxF
        (limitFrobHom p F k U f)
    have hgg : (spaRingPresheaf (Ainf p F)).germ (frobOpens p F k W') x hxF
        (limitFrobHom p F k W' (limitRestrict hW'U g))
        = (spaRingPresheaf (Ainf p F)).germ (frobOpens p F k U) x hxU
            (limitFrobHom p F k U g) := by
      rw [limitFrobHom_limitRestrict p F k hW'U g]
      exact germ_limitRestrict (frobOpens_mono p F k hW'U) hxF
        (limitFrobHom p F k U g)
    exact stalkVle_congr p F (hgf.trans hMa.symm) (hgg.trans hMb.symm) hst

end FarguesFontaine


end
