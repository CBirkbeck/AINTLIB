/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RingEquivPresheafTransportHuber
import «Adic spaces».FarguesFontaine.YSheaf

/-!
# The Frobenius action on `Spa(A_inf)` (D-iii-2a)

The `k`-th Frobenius power as a bicontinuous ring equivalence (`frobPow`), its
alignment with the `φ^ℤ`-action (`comap_frobPow_eq_smul`), the induced
homeomorphism of the adic spectrum (`spaFrobHomeo`), the Huber-transported
preimage description of rational traces (`spaFrob_preimage_spaOpen`), and
stability of the `𝒴`-trace. Substrate for the φ-action on the `𝒴`-object
(D-iii).
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

/-- The `k`-th Frobenius power as a ring equivalence. -/
def frobPow (k : ℤ) : Ainf p F ≃+* Ainf p F :=
  ((frob p F ^ k : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F)

theorem frobPow_apply (k : ℤ) (x : Ainf p F) :
    frobPow p F k x = (Multiplicative.ofAdd k) • x :=
  (ofAdd_zsmul_def p F k x).symm

theorem continuous_frobPow (k : ℤ) : Continuous (frobPow p F k) := by
  have h := (instContinuousConstSMulAinf p F).1 (Multiplicative.ofAdd k)
  refine h.congr fun x => ?_
  exact (frobPow_apply p F k x).symm

theorem frobPow_symm (k : ℤ) : (frobPow p F k).symm = frobPow p F (-k) := by
  show ((frob p F ^ k : RingAut (Ainf p F)) : Ainf p F ≃+* Ainf p F).symm = _
  rw [show (frobPow p F (-k)) = ((frob p F ^ k)⁻¹ : RingAut (Ainf p F)) from by
    rw [← zpow_neg]
    rfl]
  rfl

theorem continuous_frobPow_symm (k : ℤ) :
    Continuous (frobPow p F k).symm := by
  rw [frobPow_symm]
  exact continuous_frobPow p F (-k)

/-- The plus subring `⊤` corresponds to itself under any Frobenius power. -/
theorem ringPlus_map_frobPow (k : ℤ) :
    (ringPlus (Ainf p F) : Subring (Ainf p F))
      = (ringPlus (Ainf p F) : Subring (Ainf p F)).map
          (frobPow p F k).toRingHom := by
  show (⊤ : Subring (Ainf p F))
    = Subring.map (frobPow p F k).toRingHom (⊤ : Subring (Ainf p F))
  refine ((Subring.eq_top_iff'
    (Subring.map (frobPow p F k).toRingHom (⊤ : Subring (Ainf p F)))).mpr
    fun x => ?_).symm
  exact ⟨(frobPow p F k).symm x, trivial, (frobPow p F k).apply_symm_apply x⟩

/-- The Frobenius-power ring hom agrees with the action's ring hom. -/
theorem frobPow_toRingHom_eq (k : ℤ) :
    (frobPow p F k).toRingHom
      = MulSemiringAction.toRingHom (Multiplicative ℤ) (Ainf p F)
          (Multiplicative.ofAdd k) :=
  RingHom.ext fun x => frobPow_apply p F k x

/-- `comap` of the `k`-th Frobenius power is the `(-k)`-action on `Spv`. -/
theorem comap_frobPow_eq_smul (k : ℤ) (v : Spv (Ainf p F)) :
    comap (frobPow p F k).toRingHom v = (Multiplicative.ofAdd (-k)) • v := by
  show _ = comap (MulSemiringAction.toRingHom (Multiplicative ℤ) (Ainf p F)
    ((Multiplicative.ofAdd (-k))⁻¹)) v
  rw [frobPow_toRingHom_eq]
  congr 1
  rw [show ((Multiplicative.ofAdd (-k))⁻¹ : Multiplicative ℤ)
    = Multiplicative.ofAdd k from by
      rw [← ofAdd_neg, neg_neg]]

/-- The comap of a Frobenius power preserves `Spa` (extracted so the
`spaFrob` literal stays small). -/
theorem spaFrob_mem_spa (k : ℤ)
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    comap (frobPow p F k).toRingHom v.1
      ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) := by
  refine comap_mem_spa_map (frobPow p F k) (ringPlus (Ainf p F))
    (continuous_frobPow p F k) ?_
  rw [← ringPlus_map_frobPow p F k]
  exact v.2

/-- **The Frobenius action on the adic spectrum** (the `k`-th power), via
`comap`; lands in `Spa` since `⊤` is stable. -/
def spaFrob (k : ℤ) (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  ⟨comap (frobPow p F k).toRingHom v.1, spaFrob_mem_spa p F k v⟩

theorem spaFrob_coe (k : ℤ) (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    (spaFrob p F k v : Spv (Ainf p F))
      = (Multiplicative.ofAdd (-k)) • (v : Spv (Ainf p F)) :=
  comap_frobPow_eq_smul p F k v.1

theorem continuous_spaFrob (k : ℤ) : Continuous (spaFrob p F k) :=
  Continuous.subtype_mk ((comap_continuous _).comp continuous_subtype_val) _

theorem spaFrob_spaFrob (k : ℤ) (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) :
    spaFrob p F (-k) (spaFrob p F k v) = v := by
  refine Subtype.ext ?_
  show comap (frobPow p F (-k)).toRingHom
    (comap (frobPow p F k).toRingHom v.1) = v.1
  rw [← frobPow_symm p F k]
  exact comap_comap_of_ringEquiv (frobPow p F k) v.1

/-- The Frobenius action on `Spa` as a homeomorphism. -/
def spaFrobHomeo (k : ℤ) :
    ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))
      ≃ₜ ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) where
  toFun := spaFrob p F k
  invFun := spaFrob p F (-k)
  left_inv := spaFrob_spaFrob p F k
  right_inv v := by
    have h := spaFrob_spaFrob p F (-k) v
    rwa [neg_neg] at h
  continuous_toFun := continuous_spaFrob p F k
  continuous_invFun := continuous_spaFrob p F (-k)

/-- The `spaFrob`-preimage of a rational trace is the trace of the
Huber-transported datum. -/
theorem spaFrob_preimage_spaOpen (k : ℤ) (D : RationalLocData (Ainf p F)) :
    spaFrob p F k ⁻¹' spaOpen D
      = spaOpen (D.mapHuber (frobPow p F k) (continuous_frobPow p F k)
          (continuous_frobPow_symm p F k)) := by
  ext v
  show comap (frobPow p F k).toRingHom v.1 ∈ rationalOpen D.T D.s ↔ _
  exact (mem_rationalOpen_mapHuber_iff (frobPow p F k)
    (continuous_frobPow p F k) (continuous_frobPow_symm p F k)
    (ringPlus_map_frobPow p F k) D).symm

/-- The Frobenius action preserves the `𝒴`-trace. -/
theorem spaFrob_mem_ySpaSet (k : ℤ)
    {v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (hv : v ∈ ySpaSet p F ϖ) :
    spaFrob p F k v ∈ ySpaSet p F ϖ := by
  show (spaFrob p F k v : Spv (Ainf p F)) ∈ Y p F ϖ
  rw [spaFrob_coe]
  exact smul_mem_Y p F ϖ _ hv

end FarguesFontaine

end
