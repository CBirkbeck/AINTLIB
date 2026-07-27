/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.FrobeniusSpa

/-!
# The Frobenius transport of limit sections (D-iii-2b)

Sections of the ambient structure presheaf over `W` pull back to sections
over the Frobenius preimage `frobOpens k W`, componentwise through the Huber
value equivalences at the transported rational indices (`frobIndex`). The
transport is a continuous ring homomorphism (`limitFrobHom`, built at the
`Pi`-level so the ring laws are free) and commutes with restriction
definitionally. Substrate for the φ-morphism of presheafed spaces (D-iii-3).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter CategoryTheory Opposite

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- The preimage of an open under the `k`-th Frobenius, as an open. -/
def frobOpens (k : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  ⟨spaFrob p F k ⁻¹' (W : Set _), W.2.preimage (continuous_spaFrob p F k)⟩

/-- The subset witness of the transported rational index, extracted so the
`frobIndex` literal stays small (kernel projection-reduction budget). -/
theorem frobIndex_subset (k : ℤ)
    {W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (E : RationalIndex (frobOpens p F k W)) :
    spaOpen (E.D.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
        (continuous_frobPow_symm p F (-k)))
      ⊆ (W : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
    have h1 : spaFrob p F (-k) ⁻¹' spaOpen E.D
        = spaOpen (E.D.mapHuber (frobPow p F (-k))
            (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))) :=
      spaFrob_preimage_spaOpen p F (-k) E.D
    rw [← h1]
    intro v hv
    have hsub := E.subset hv
    show v ∈ (W : Set _)
    have hroundtrip : spaFrob p F k (spaFrob p F (-k) v) = v := by
      have h := spaFrob_spaFrob p F (-k) v
      rwa [neg_neg] at h
    rw [← hroundtrip]
    exact hsub

/-- The transported rational index: a rational index of the Frobenius
preimage pulls back to a rational index of the original open. -/
def frobIndex (k : ℤ) {W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (E : RationalIndex (frobOpens p F k W)) : RationalIndex W where
  D := E.D.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k))
  isRational := RationalLocData.mapHuber_isRational _ _ _ E.D E.isRational
  subset := frobIndex_subset p F k E

/-- The Pi-level Frobenius transport (all ring-hom laws free). -/
def limitFrobPiHom (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    (∀ j : RationalIndex W, presheafValue j.D)
      →+* (∀ E : RationalIndex (frobOpens p F k W), presheafValue E.D) :=
  Pi.ringHom fun E =>
    ((presheafValueRingEquivHuber (frobPow p F (-k))
        (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
        E.D).symm.toRingHom).comp
      (Pi.evalRingHom _ (frobIndex p F k E))

theorem limitFrobPiHom_apply (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (x : ∀ j : RationalIndex W, presheafValue j.D)
    (E : RationalIndex (frobOpens p F k W)) :
    limitFrobPiHom p F k W x E
      = (presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm (x (frobIndex p F k E)) := rfl

/-- The Pi-level transport of a compatible family is compatible. -/
theorem limitFrobPiHom_mem (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (x : ↥(limitSections W)) :
    limitFrobPiHom p F k W
        ((x : ∀ j : RationalIndex W, presheafValue j.D))
      ∈ limitSections (frobOpens p F k W) := by
  rw [mem_limitSections]
  intro E E' hE'E
  rw [limitFrobPiHom_apply, limitFrobPiHom_apply]
  have hsub' := rationalOpen_mapHuber_subset_of_subset
    (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k))
    (ringPlus_map_frobPow p F (-k)) E'.D E.D hE'E
  have hx := x.2 (frobIndex p F k E) (frobIndex p F k E') hsub'
  exact (presheafValueRingEquivHuber_symm_restriction
    (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k)) E.D E'.D hE'E hsub'
    ((x : ∀ j : RationalIndex W, presheafValue j.D)
      (frobIndex p F k E))).symm.trans
    (congrArg (⇑(presheafValueRingEquivHuber (frobPow p F (-k))
      (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
      E'.D).symm) hx)

/-- **The Frobenius transport of limit sections** (D-iii-2b): sections over
`W` pull back to sections over the Frobenius preimage, componentwise through
the Huber value equivalences. -/
def limitFrobHom (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    ↥(limitSections W) →+* ↥(limitSections (frobOpens p F k W)) :=
  RingHom.codRestrict
    ((limitFrobPiHom p F k W).comp (limitSections W).subtype)
    (limitSections (frobOpens p F k W))
    (fun x => limitFrobPiHom_mem p F k W x)

theorem limitFrobHom_component (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (x : ↥(limitSections W)) (E : RationalIndex (frobOpens p F k W)) :
    ((limitFrobHom p F k W x : ↥(limitSections (frobOpens p F k W)))
        : ∀ j : RationalIndex (frobOpens p F k W), presheafValue j.D) E
      = (presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm
        ((x : ∀ j : RationalIndex W, presheafValue j.D)
          (frobIndex p F k E)) := rfl

theorem limitFrobHom_continuous (k : ℤ)
    (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    Continuous (limitFrobHom p F k W) := by
  refine continuous_induced_rng.mpr ?_
  have hfun : (Subtype.val ∘ ⇑(limitFrobHom p F k W))
      = fun (x : ↥(limitSections W))
          (E : RationalIndex (frobOpens p F k W)) =>
        (presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm
        ((x : ∀ j : RationalIndex W, presheafValue j.D)
          (frobIndex p F k E)) := rfl
  rw [hfun]
  exact continuous_pi fun E =>
    (presheafValueRingEquivHuber_symm_continuous (frobPow p F (-k))
      (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
      E.D).comp
    ((continuous_apply (frobIndex p F k E)).comp continuous_subtype_val)

/-- The Frobenius preimage of opens is monotone. -/
theorem frobOpens_mono (k : ℤ)
    {V W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (h : V ≤ W) :
    frobOpens p F k V ≤ frobOpens p F k W :=
  fun _ hv => h hv

/-- **Naturality of the Frobenius transport in the open** (definitional
componentwise). -/
theorem limitFrobHom_limitRestrict (k : ℤ)
    {V W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (h : V ≤ W)
    (x : ↥(limitSections W)) :
    limitFrobHom p F k V (limitRestrict h x)
      = limitRestrict (frobOpens_mono p F k h) (limitFrobHom p F k W x) :=
  Subtype.ext (funext fun _ => rfl)

/-- The Frobenius on the ambient adic spectrum, as a `TopCat`-morphism. -/
def spaFrobTop (k : ℤ) : SpaTop (Ainf p F) ⟶ SpaTop (Ainf p F) :=
  TopCat.ofHom ⟨spaFrob p F k, continuous_spaFrob p F k⟩

/-- **The Frobenius comparison of the ambient structure presheaf**: the
natural transformation into the pushforward, with components the limit
transports. -/
def ambientFrobNat (k : ℤ) :
    structurePresheaf (Ainf p F)
      ⟶ (Opens.map (spaFrobTop p F k)).op ⋙ structurePresheaf (Ainf p F) where
  app V := ⟨limitFrobHom p F k V.unop, limitFrobHom_continuous p F k V.unop⟩
  naturality V V' i := by
    refine Subtype.ext (RingHom.ext fun x => ?_)
    show limitFrobHom p F k V'.unop
        (((structurePresheaf (Ainf p F)).map i).1 x)
      = (((Opens.map (spaFrobTop p F k)).op ⋙ structurePresheaf (Ainf p F)).map
            i).1 (limitFrobHom p F k V.unop x)
    exact (congrArg (limitFrobHom p F k V'.unop)
        (structurePresheaf_map i x)).trans
      ((limitFrobHom_limitRestrict p F k (leOfHom i.unop) x).trans
        (structurePresheaf_map ((Opens.map (spaFrobTop p F k)).op.map i)
          (limitFrobHom p F k V.unop x)).symm)

/-- **The Frobenius endomorphism of the ambient presheafed space.** -/
def ambientFrobHom (k : ℤ) :
    yAmbientPresheafedSpace p F ⟶ yAmbientPresheafedSpace p F where
  base := spaFrobTop p F k
  c := ambientFrobNat p F k

/-- Two-sided `𝒴`-stability of the Frobenius. -/
theorem spaFrob_mem_ySpaSet_iff (k : ℤ)
    {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} :
    spaFrob p F k v ∈ ySpaSet p F ϖ ↔ v ∈ ySpaSet p F ϖ := by
  constructor
  · intro h
    have h2 := spaFrob_mem_ySpaSet p F ϖ (-k) h
    rwa [spaFrob_spaFrob p F k v] at h2
  · exact spaFrob_mem_ySpaSet p F ϖ k

/-- The Frobenius on the `𝒴`-carrier. -/
def yFrobTop (k : ℤ) : yTop p F ϖ ⟶ yTop p F ϖ :=
  TopCat.ofHom ⟨fun y => ⟨spaFrob p F k y.1, spaFrob_mem_ySpaSet p F ϖ k y.2⟩,
    Continuous.subtype_mk ((continuous_spaFrob p F k).comp
      continuous_subtype_val) _⟩

/-- **The Frobenius preimage commutes with the `𝒴`-image functor.** -/
theorem yFunctor_frobOpens (k : ℤ) (V : Opens ↥(yTop p F ϖ)) :
    frobOpens p F k ((yFunctor p F ϖ).obj V)
      = (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ k)).obj V) := by
  refine Opens.ext ?_
  ext v
  constructor
  · rintro hv
    obtain ⟨y, hyV, hyeq⟩ := hv
    have hvY : v ∈ ySpaSet p F ϖ := by
      rw [← spaFrob_mem_ySpaSet_iff p F ϖ k]
      rw [← hyeq]
      exact y.2
    refine ⟨⟨v, hvY⟩, ?_, rfl⟩
    show yFrobTop p F ϖ k ⟨v, hvY⟩ ∈ V
    have heq : yFrobTop p F ϖ k ⟨v, hvY⟩ = y :=
      Subtype.ext (show spaFrob p F k v = _ from hyeq.symm)
    rwa [heq]
  · rintro ⟨y, hyV, rfl⟩
    exact ⟨yFrobTop p F ϖ k y, hyV, rfl⟩

/-- Indices of the `𝒴`-image of a Frobenius preimage are indices of the
Frobenius preimage of the `𝒴`-image (the opens are equal). -/
def yFrobIndexBridge (k : ℤ) (V : Opens ↥(yTop p F ϖ))
    (E : RationalIndex ((yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ k)).obj V))) :
    RationalIndex (frobOpens p F k ((yFunctor p F ϖ).obj V)) :=
  ⟨E.D, E.isRational, by
    rw [yFunctor_frobOpens p F ϖ k V]
    exact E.subset⟩

/-- The `𝒴`-level Pi transport. -/
def yLimitFrobPiHom (k : ℤ) (V : Opens ↥(yTop p F ϖ)) :
    (∀ j : RationalIndex ((yFunctor p F ϖ).obj V), presheafValue j.D)
      →+* (∀ E : RationalIndex ((yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ k)).obj V)), presheafValue E.D) :=
  Pi.ringHom fun E =>
    ((presheafValueRingEquivHuber (frobPow p F (-k))
        (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
        E.D).symm.toRingHom).comp
      (Pi.evalRingHom _ (frobIndex p F k (yFrobIndexBridge p F ϖ k V E)))

theorem yLimitFrobPiHom_apply (k : ℤ) (V : Opens ↥(yTop p F ϖ))
    (x : ∀ j : RationalIndex ((yFunctor p F ϖ).obj V), presheafValue j.D)
    (E : RationalIndex ((yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ k)).obj V))) :
    yLimitFrobPiHom p F ϖ k V x E
      = (presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm
        (x (frobIndex p F k (yFrobIndexBridge p F ϖ k V E))) := rfl

/-- The `𝒴`-level transport of a compatible family is compatible. -/
theorem yLimitFrobPiHom_mem (k : ℤ) (V : Opens ↥(yTop p F ϖ))
    (x : ↥(limitSections ((yFunctor p F ϖ).obj V))) :
    yLimitFrobPiHom p F ϖ k V
        ((x : ∀ j : RationalIndex ((yFunctor p F ϖ).obj V),
          presheafValue j.D))
      ∈ limitSections ((yFunctor p F ϖ).obj
          ((Opens.map (yFrobTop p F ϖ k)).obj V)) := by
  intro E E' hE'E
  rw [yLimitFrobPiHom_apply, yLimitFrobPiHom_apply]
  have hsub' := rationalOpen_mapHuber_subset_of_subset
    (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k))
    (ringPlus_map_frobPow p F (-k)) E'.D E.D hE'E
  have hx := x.2 (frobIndex p F k (yFrobIndexBridge p F ϖ k V E))
    (frobIndex p F k (yFrobIndexBridge p F ϖ k V E')) hsub'
  exact (presheafValueRingEquivHuber_symm_restriction
    (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k)) E.D E'.D hE'E hsub'
    ((x : ∀ j : RationalIndex ((yFunctor p F ϖ).obj V), presheafValue j.D)
      (frobIndex p F k (yFrobIndexBridge p F ϖ k V E)))).symm.trans
    (congrArg (⇑(presheafValueRingEquivHuber (frobPow p F (-k))
      (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
      E'.D).symm) hx)

/-- **The `𝒴`-level Frobenius transport of limit sections.** -/
def yLimitFrobHom (k : ℤ) (V : Opens ↥(yTop p F ϖ)) :
    ↥(limitSections ((yFunctor p F ϖ).obj V))
      →+* ↥(limitSections ((yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ k)).obj V))) :=
  RingHom.codRestrict
    ((yLimitFrobPiHom p F ϖ k V).comp
      (limitSections ((yFunctor p F ϖ).obj V)).subtype)
    (limitSections ((yFunctor p F ϖ).obj
      ((Opens.map (yFrobTop p F ϖ k)).obj V)))
    (fun x => yLimitFrobPiHom_mem p F ϖ k V x)

theorem yLimitFrobHom_continuous (k : ℤ) (V : Opens ↥(yTop p F ϖ)) :
    Continuous (yLimitFrobHom p F ϖ k V) := by
  refine continuous_induced_rng.mpr ?_
  have hfun : (Subtype.val ∘ ⇑(yLimitFrobHom p F ϖ k V))
      = fun (x : ↥(limitSections ((yFunctor p F ϖ).obj V)))
          (E : RationalIndex ((yFunctor p F ϖ).obj
            ((Opens.map (yFrobTop p F ϖ k)).obj V))) =>
        (presheafValueRingEquivHuber (frobPow p F (-k))
          (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
          E.D).symm
        ((x : ∀ j : RationalIndex ((yFunctor p F ϖ).obj V),
          presheafValue j.D)
          (frobIndex p F k (yFrobIndexBridge p F ϖ k V E))) := rfl
  rw [hfun]
  exact continuous_pi fun E =>
    (presheafValueRingEquivHuber_symm_continuous (frobPow p F (-k))
      (continuous_frobPow p F (-k)) (continuous_frobPow_symm p F (-k))
      E.D).comp
    ((continuous_apply _).comp continuous_subtype_val)

/-- **The `𝒴`-Frobenius comparison**: the natural transformation of the
restricted presheaf into its pushforward (naturality definitional). -/
def yFrobNat (k : ℤ) :
    (yPresheafedSpace p F ϖ).presheaf
      ⟶ (Opens.map (yFrobTop p F ϖ k)).op ⋙ (yPresheafedSpace p F ϖ).presheaf where
  app V := ⟨yLimitFrobHom p F ϖ k V.unop, yLimitFrobHom_continuous p F ϖ k V.unop⟩
  naturality V V' i := Subtype.ext (RingHom.ext fun x => Subtype.ext
    (funext fun E => rfl))

/-- **The Frobenius endomorphism of the `𝒴`-presheafed space** (D-iii-3b). -/
def yFrobHom (k : ℤ) :
    yPresheafedSpace p F ϖ ⟶ yPresheafedSpace p F ϖ where
  base := yFrobTop p F ϖ k
  c := yFrobNat p F ϖ k

end FarguesFontaine

end
