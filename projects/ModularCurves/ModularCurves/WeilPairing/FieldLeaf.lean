/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear
import ModularCurves.WeilPairing.FieldComparisonBridge

/-!
# The field leaf: comparing the KM pairing with the Silverman pairing (U5)

Per the validated sub-decomposition (`.mathlib-quality/decomposition-e4a-self.md`, U5
section): over a field the Katz–Mazur pairing value `torsionSplittingEval` and HasseWeil's
Silverman pairing `weilPairing` satisfy the *same* translation characterisation
(`τ_{P}^# g = e · g`) against divisor-matched function objects, so they agree; alternation
then imports from `HasseWeil.weilPairing_self`.

This file builds the comparison bottom-up:
* **L2a (this commit)** — the τ-relation for a *held* normalised splitting, extracted from
  the proof of `torsionSplittingEval_add` (`KMBilinear.lean`) as a standalone lemma:
  `τ_{P'}^# h_i = h_i · π^# h(P')`, over any base.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)
variable (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
variable (M : (pullback E.π t).Modules)
variable (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  (kappa E hsm t Q).val = toSkeleton M)
variable {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
variable (e : ∀ i, M.over (W i) ≅
  _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
variable (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
  sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))

/-- **(U5-L2a — the τ-relation for a held splitting, KM p. 89)** For any normalised splitting
`h` of the `[N]`-pulled transition cocycle and any `N`-torsion section `P'`,

  `τ_{P'}^# h_i = h_i · π^# h(P')`,

where `h(P') = torsionSplittingEval … P'`. Extracted verbatim from the proof of
`torsionSplittingEval_add` (`KMBilinear.lean`) so the field-level comparison can consume the
relation on a single chart. -/
theorem unitPullback_translateByPoint_eq_of_splitting
    (h : ∀ i, Γ(pullback E.π t, mulByN E t N ⁻¹ᵁ W i)ˣ)
    (hn : ∀ i, h i ∈ sectionUnits (baseChangeZero E.π E.zero E.zero_π t)
      (mulByN E t N ⁻¹ᵁ W i))
    (hsplit : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      Scheme.resUnit (inf_le_left : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W i) (h i) *
        (Scheme.resUnit (inf_le_right : mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
          mulByN E t N ⁻¹ᵁ W j) (h j))⁻¹)
    (P' : (E.baseChange t).Point (𝟙 T)) (hP' : P' ∈ torsionPoints E t N) (i : ι) :
    unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i) (mulByN E t N ⁻¹ᵁ W i)
        (le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i)).symm) (h i) =
      h i * globalTwist (pullback.snd E.π t) (mulByN E t N ⁻¹ᵁ W i)
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP') := by
  have hτle : ∀ i, mulByN E t N ⁻¹ᵁ W i ≤
      translateByPoint E t P' ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := fun i =>
    le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i)).symm
  have hτinf : ∀ i j, mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j ≤
      translateByPoint E t P' ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) := fun i j =>
    le_of_eq (preimage_translateByPoint_mulByN E t P' N hP' (W i ⊓ W j)).symm
  have hFeq : ∀ i j, Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) =
      unitPullback (mulByN E t N) (W i ⊓ W j)
        (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j)
        (Scheme.Hom.preimage_inf (mulByN E t N)).ge (transitionUnitOfCover M W e i j) :=
    fun i j => map_app_eq_unitPullback _ _ _
  have hτF : ∀ i j, unitPullback (translateByPoint E t P')
      (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j)
      (mulByN E t N ⁻¹ᵁ W i ⊓ mulByN E t N ⁻¹ᵁ W j) (hτinf i j)
      (Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j)) =
      Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j) := by
    intro i j
    rw [hFeq i j, unitPullback_unitPullback]
    exact unitPullback_congr (translateByPoint_comp_mulByN E t P' N hP') _ _ _ _ _
  have hzval : ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) =
      baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  have hzτ : baseChangeZero E.π E.zero E.zero_π t ≫ translateByPoint E t P' =
      (P'.1 : T ⟶ pullback E.π t) := by
    rw [← hzval]
    exact (comp_translateByPoint E t P' 0).trans (congrArg Subtype.val (zero_add P'))
  have hC : ∀ i, sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i)
        (unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i)
          (mulByN E t N ⁻¹ᵁ W i) (hτle i) (h i)) =
      Scheme.resUnit (le_top : baseChangeZero E.π E.zero E.zero_π t ⁻¹ᵁ
          (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤)
        (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP') := by
    intro i
    have hP'le : baseChangeZero E.π E.zero E.zero_π t ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤
        (P'.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) := by
      rw [← hzτ]
      exact Scheme.Hom.preimage_mono _ (hτle i)
    calc sectionEval (baseChangeZero E.π E.zero E.zero_π t) (mulByN E t N ⁻¹ᵁ W i)
          (unitPullback (translateByPoint E t P') (mulByN E t N ⁻¹ᵁ W i)
            (mulByN E t N ⁻¹ᵁ W i) (hτle i) (h i))
        = Scheme.resUnit
            (Scheme.Hom.preimage_mono (baseChangeZero E.π E.zero E.zero_π t) (hτle i))
            (sectionEval (baseChangeZero E.π E.zero E.zero_π t ≫ translateByPoint E t P')
              (mulByN E t N ⁻¹ᵁ W i) (h i)) := sectionEval_unitPullback _ _ _ _
      _ = Scheme.resUnit hP'le
            (sectionEval (P'.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i) (h i)) :=
          resUnit_sectionEval_congr hzτ (mulByN E t N ⁻¹ᵁ W i) (h i)
            (Scheme.Hom.preimage_mono (baseChangeZero E.π E.zero E.zero_π t) (hτle i)) hP'le
      _ = Scheme.resUnit hP'le (Scheme.resUnit
            (le_top : (P'.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i) ≤ ⊤)
            (torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP')) := by
          rw [resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP' h hn hsplit i]
      _ = _ := Scheme.resUnit_resUnit _ _ _
  have hkey := eq_mul_globalTwist_of_translate t
    E.toEllipticCurveGeom.universallyOConnected
    (baseChangeZero_snd E.π E.zero E.zero_π t)
    (fun i => mulByN E t N ⁻¹ᵁ W i)
    ((mulByN E t N).iSup_preimage_eq_top hW)
    (F := fun i j => Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
      (transitionUnitOfCover M W e i j))
    hn hsplit hτle hτinf hτF hC
  exact hkey i

end ModularCurves
