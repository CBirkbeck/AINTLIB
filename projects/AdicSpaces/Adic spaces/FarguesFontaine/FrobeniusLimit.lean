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

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter

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

/-- The transported rational index: a rational index of the Frobenius
preimage pulls back to a rational index of the original open. -/
def frobIndex (k : ℤ) {W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))}
    (E : RationalIndex (frobOpens p F k W)) : RationalIndex W where
  D := E.D.mapHuber (frobPow p F (-k)) (continuous_frobPow p F (-k))
    (continuous_frobPow_symm p F (-k))
  isRational := RationalLocData.mapHuber_isRational _ _ _ E.D E.isRational
  subset := by
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

end FarguesFontaine

end
