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

end FarguesFontaine


end
