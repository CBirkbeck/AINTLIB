/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.MapTranslateGenericAdditive
import HasseWeil.WeilPairing.FrobeniusGenericCovariance
import HasseWeil.WeilPairing.SeparableWitnesses
import HasseWeil.WeilPairing.PencilSeparable
import HasseWeil.WeilPairing.WallAGeometricRealization

/-!
# Generic-point covariance for `(rπ − s)_{K̄}`

This file discharges the translation covariance `hcomm'` for the base-changed separable pencil
`(rπ − s)_{K̄}` over `AlgebraicClosure K`, without carrying an extra `hgcomm` hypothesis.  The
argument decomposes the pencil into the `r·π` and `−s·id` covariance leaves, proves Wall A
genuineness, and then converts it to the canonical action used by `SeparableWitnesses`.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section General

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- Translating `[ℓ](P_gen)` by `S` gives `[ℓ]P_gen + lift(ℓ • S)`. -/
private theorem map_translate_smul_genericPoint (ℓ : ℤ) (S : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom
        (ℓ • HasseWeil.genericPoint W) =
      ℓ • HasseWeil.genericPoint W + HasseWeil.liftPointToKE W (ℓ • S) := by
  set m : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom
      with hm
  have hmaster : m (HasseWeil.genericPoint W) =
      HasseWeil.genericPoint W + HasseWeil.liftPointToKE W S := by
    rw [hm]; exact HasseWeil.translateAlgEquivOfPoint_map_genericPoint W S
  calc m (ℓ • HasseWeil.genericPoint W)
      = ℓ • m (HasseWeil.genericPoint W) := map_zsmul m ℓ _
    _ = ℓ • (HasseWeil.genericPoint W + HasseWeil.liftPointToKE W S) := by rw [hmaster]
    _ = ℓ • HasseWeil.genericPoint W + ℓ • HasseWeil.liftPointToKE W S := zsmul_add _ _ _
    _ = ℓ • HasseWeil.genericPoint W + HasseWeil.liftPointToKE W (ℓ • S) := by
      rw [map_zsmul]

/-- The generic-point covariance leaf is preserved by `zsmul` of the isogeny. -/
theorem mapTranslateGenericPoint_zsmul (φ : Isogeny W.toAffine W.toAffine)
    (g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point) (m : ℤ)
    (h : MapTranslateGenericPoint W φ g) :
    MapTranslateGenericPoint W (φ.zsmul m) (m • g) := by
  intro S
  set τ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (translateAlgEquivOfPoint W S).toAlgHom with hτ
  have e1 : (m • g) (genericPoint W) = m • g (genericPoint W) := rfl
  have e2 : (φ.zsmul m).toAddMonoidHom S = m • φ.toAddMonoidHom S := Isogeny.zsmul_apply m φ S
  have hS : τ (g (genericPoint W)) =
      g (genericPoint W) + liftPointToKE W (φ.toAddMonoidHom S) := h S
  have hlift : liftPointToKE W (m • φ.toAddMonoidHom S) =
      m • liftPointToKE W (φ.toAddMonoidHom S) :=
    (liftPointToKE W).map_zsmul m (φ.toAddMonoidHom S)
  calc τ ((m • g) (genericPoint W))
      = τ (m • g (genericPoint W)) := by rw [e1]
    _ = m • τ (g (genericPoint W)) := map_zsmul τ m (g (genericPoint W))
    _ = m • (g (genericPoint W) + liftPointToKE W (φ.toAddMonoidHom S)) := by rw [hS]
    _ = m • g (genericPoint W) + m • liftPointToKE W (φ.toAddMonoidHom S) := by module
    _ = (m • g) (genericPoint W) + liftPointToKE W ((φ.zsmul m).toAddMonoidHom S) := by
          rw [e1, e2, hlift]

/-- The `[m]` generic-point covariance leaf for the geometric action `zsmulPointHom m`. -/
theorem mapTranslateGenericPoint_mulByInt (m : ℤ) :
    MapTranslateGenericPoint W (mulByInt W.toAffine m) (zsmulPointHom W m) := by
  intro S
  show WeierstrassCurve.Affine.Point.map (W' := W) (translateAlgEquivOfPoint W S).toAlgHom
      (m • genericPoint W) =
      m • genericPoint W + liftPointToKE W ((mulByInt W.toAffine m).toAddMonoidHom S)
  rw [map_translate_smul_genericPoint W m S, mulByInt_apply]

end General

section Pencil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- The geometric `K̄`-action `r·frobₗ + [−s]` for `(rπ − s)_{K̄}`. -/
noncomputable def gKbarPencil (r' s' : ℤ) :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  r' • frobFunctionFieldPointKbar W + zsmulPointHom (W.baseChange (AlgebraicClosure K)) (-s')

/-- The point-map sum decomposition of `pencilIsogBaseChange` as `(r·π̄) + [−s]`. -/
theorem pencilIsogBaseChange_toAddMonoidHom_decomp (r' s' : ℤ)
    (pullback_L :
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom =
      ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W
          (AlgebraicClosure K)).zsmul r').toAddMonoidHom +
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).toAddMonoidHom := by
  rw [pencilIsogBaseChange_toAddMonoidHom]
  ext P
  rw [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Isogeny.zsmul_apply,
    mulByInt_apply, AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
  show r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) P - s' • P =
      r' • (Isogeny.frobeniusIsog_baseChange_charP_pow p r W
        (AlgebraicClosure K)).toAddMonoidHom P + (-s') • P
  rw [show (Isogeny.frobeniusIsog_baseChange_charP_pow p r W
      (AlgebraicClosure K)).toAddMonoidHom P =
      frobeniusHomBaseChange W p r (AlgebraicClosure K) P from rfl, neg_smul]
  abel

/-- `gKbarPencil` satisfies the generic-point covariance leaf. -/
theorem mapTranslateGenericPoint_gKbarPencil (r' s' : ℤ)
    (pullback_L :
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
      (gKbarPencil W r' s') :=
  mapTranslateGenericPoint_add (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
    ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K)).zsmul r')
    (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
    (r' • frobFunctionFieldPointKbar W)
    (zsmulPointHom (W.baseChange (AlgebraicClosure K)) (-s'))
    (pencilIsogBaseChange_toAddMonoidHom_decomp W p r r' s' pullback_L)
    (mapTranslateGenericPoint_zsmul (W.baseChange (AlgebraicClosure K))
      (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K))
      (frobFunctionFieldPointKbar W) r'
      (mapTranslateGenericPoint_frobenius_Kbar W p r))
    (mapTranslateGenericPoint_mulByInt (W.baseChange (AlgebraicClosure K)) (-s'))

/-- At the generic point, `gKbarPencil` is the base change of the `K`-level action. -/
theorem gKbarPencil_genericPoint (r' s' : ℤ) :
    gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      ffBaseChangePoint W (AlgebraicClosure K)
        ((((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
          (HasseWeil.genericPoint W)) := by
  have hrhs : ((((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
        (HasseWeil.genericPoint W)) =
      r' • frobeniusW_KE W (genericPoint W) + (-s') • genericPoint W := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, zsmulPointHom_apply]
  have hadd : ffBaseChangePoint W (AlgebraicClosure K)
        (r' • frobeniusW_KE W (genericPoint W) + (-s') • genericPoint W) =
      ffBaseChangePoint W (AlgebraicClosure K) (r' • frobeniusW_KE W (genericPoint W)) +
        ffBaseChangePoint W (AlgebraicClosure K) ((-s') • genericPoint W) :=
    map_add _ _ _
  have hz1 : ffBaseChangePoint W (AlgebraicClosure K) (r' • frobeniusW_KE W (genericPoint W)) =
      r' • ffBaseChangePoint W (AlgebraicClosure K) (frobeniusW_KE W (genericPoint W)) :=
    map_zsmul _ r' _
  have hz2 : ffBaseChangePoint W (AlgebraicClosure K) ((-s') • genericPoint W) =
      (-s') • ffBaseChangePoint W (AlgebraicClosure K) (genericPoint W) := map_zsmul _ (-s') _
  have hlhs : gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      r' • frobFunctionFieldPointKbar W (genericPoint (W.baseChange (AlgebraicClosure K))) +
        (-s') • genericPoint (W.baseChange (AlgebraicClosure K)) := rfl
  rw [hlhs, hrhs, hadd, hz1, hz2, ffbc_frob_comm, ffBaseChangePoint_genericPoint]
  rfl

/-- Wall A pencil genuineness over `K̄` for the geometric action `gKbarPencil`. -/
theorem pencil_isGenuineWith_Kbar (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    HasseWeil.IsGenuineWith (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (gKbarPencil W r' s') := by
  obtain ⟨X, Y, hns, hgK, hXeq, hYeq⟩ :=
    HasseWeil.genuineIsogSmulSub_isGenuineWith W r' s' hr hs hrK hsK
  have hgen : gKbarPencil W r' s' (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      Affine.Point.some
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) X)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) Y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange
            (AlgebraicClosure K)).injective X Y).mpr hns) := by
    rw [gKbarPencil_genericPoint W r' s']
    rw [show (((zsmulPointHom W r').comp (frobeniusW_KE W)) + zsmulPointHom W (-s'))
        (HasseWeil.genericPoint W) = Affine.Point.some X Y hns from hgK]
    exact ffBaseChangePoint_some W (AlgebraicClosure K) X Y hns
  have hpbx : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) X := by
    simp only [pencilIsogBaseChange_pullback]
    rw [hXeq, ← functionFieldMap_x_gen W (AlgebraicClosure K)]
    unfold pencilBaseChangePullback
    exact baseChangePullback_functionFieldMap _ _ _ _
  have hpby : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) Y := by
    simp only [pencilIsogBaseChange_pullback]
    rw [hYeq, ← functionFieldMap_y_gen W (AlgebraicClosure K)]
    unfold pencilBaseChangePullback
    exact baseChangePullback_functionFieldMap _ _ _ _
  exact ⟨_, _, _, hgen, hpbx.symm, hpby.symm⟩

/-- The canonical-action generic-point covariance for `(rπ − s)_{K̄}`. -/
theorem mapTranslateGenericPoint_pencil_canonical (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback) :=
  mapTranslateGenericPoint_canonical_of_genuine (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (pencil_isGenuineWith_Kbar W p r r' s' hr hs hrK hsK)
    (mapTranslateGenericPoint_gKbarPencil W p r r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))

/-- The fully discharged translation covariance `hcomm'` for `(rπ − s)_{K̄}`. -/
theorem pencil_hcommPrime_discharged (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
      (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
          T = 0),
      translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ)
              (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
                (pencilBaseChangePullback W
                  (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
                  T)
              hφT)) =
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
          (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
              (pencilBaseChangePullback W
                (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
                S)
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ)
              (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
                (pencilBaseChangePullback W
                  (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
                  T)
              hφT)) :=
  pencil_hcommPrime_of_hgcomm W p r r' s'
    (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)
    (mapTranslateGenericPoint_pencil_canonical W p r r' s' hr hs hrK hsK)

end Pencil

end HasseWeil.WeilPairing
