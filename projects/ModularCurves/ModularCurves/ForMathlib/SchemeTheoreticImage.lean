/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Scheme-theoretic images and separated-target extensionality

The map to the scheme-theoretic image of a quasi-compact morphism is scheme-theoretically
dominant. Consequently, precomposition by a scheme-theoretically dominant morphism detects
equality between morphisms over a separated target, without a reducedness assumption.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}}

/-- The canonical map from the source of a quasi-compact morphism to its scheme-theoretic image
is scheme-theoretically dominant. -/
lemma Scheme.Hom.toImage_isSchemeTheoreticallyDominant (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦
      ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩)
    (f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)) ?_
  intro U
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

/-- Morphisms over a separated target are equal if they agree after precomposition by a
scheme-theoretically dominant morphism. -/
lemma ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hEq : ι' ≫ f' = ι' ≫ g' := by
    ext1
    exact hU
  let l : U' ⟶ equalizer f' g' := equalizer.lift ι' hEq
  have hlift : l.left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hkerLe : (equalizer.ι f' g').left.ker ≤ ι.ker := by
    rw [← hlift]
    exact Scheme.Hom.le_ker_comp l.left (equalizer.ι f' g').left
  have hker : (equalizer.ι f' g').left.ker = ⊥ :=
    le_antisymm (hkerLe.trans_eq ι.ker_eq_bot) bot_le
  haveI : IsClosedImmersion (equalizer.ι f' g').left :=
    isClosedImmersion_equalizer_ι_left f' g'
  haveI : IsIso (equalizer.ι f' g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

end AlgebraicGeometry
