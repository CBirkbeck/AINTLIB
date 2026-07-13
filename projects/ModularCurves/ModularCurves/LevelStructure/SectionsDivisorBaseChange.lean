/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.CartierDivisor

/-!
# Base change of the sections divisor (T-D8-⟹ plumbing, KM 1.1)

The section divisor `Σᵢ [Pᵢ]` commutes with base change: pulling `(sectionsDivisor π P).ideal`
back along `t : T ⟶ S` yields the section divisor of the base-changed sections of
`pullback.snd π t`. This is the fibre-reduction step of the `[YF-⊆]` / `fullLevel_divisor_iff_
naive_gen` ⟹ argument — assembled from the ideal-level base change `baseChange_ideal`, the
per-section `ker_sectionBaseChange`, and `comap_prod`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace RelEffCartierDiv

variable {C S : Scheme.{u}} {π : C ⟶ S}

/-- The base change of a section `z : S ⟶ C` (over `𝟙 S`) to a section of `pullback.snd π t`
over `𝟙 T`. -/
noncomputable def sectionBaseChange (z : { z : S ⟶ C // z ≫ π = 𝟙 S }) {T : Scheme.{u}}
    (t : T ⟶ S) : { w : T ⟶ pullback π t // w ≫ pullback.snd π t = 𝟙 T } :=
  ⟨pullback.lift (t ≫ z.1) (𝟙 T)
      (by rw [Category.assoc, z.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

/-- **(KM 1.1)** The section divisor commutes with base change: pulling
`(sectionsDivisor π P).ideal` back along `t` gives the section divisor of the base-changed
sections of `pullback.snd π t`. -/
theorem sectionsDivisor_baseChange [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    {n : ℕ} (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) {T : Scheme.{u}} (t : T ⟶ S) :
    (sectionsDivisor π P).ideal.comap (pullback.fst π t) =
      (sectionsDivisor (pullback.snd π t) (fun i => sectionBaseChange (P i) t)).ideal := by
  haveI : IsSeparated (pullback.snd π t) := MorphismProperty.pullback_snd _ _ ‹_›
  haveI hsm' : SmoothOfRelativeDimension 1 (pullback.snd π t) := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd π t hsm
  rw [show (sectionsDivisor π P).ideal = ∏ i, Scheme.Hom.ker (P i).1 from by
      rw [sectionsDivisor, dif_pos ⟨‹_›, hsm⟩],
    show (sectionsDivisor (pullback.snd π t) (fun i => sectionBaseChange (P i) t)).ideal
        = ∏ i, Scheme.Hom.ker (sectionBaseChange (P i) t).1 from by
      rw [sectionsDivisor, dif_pos ⟨‹_›, hsm'⟩],
    Scheme.IdealSheafData.comap_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (ker_sectionBaseChange (P i).1 (P i).2 t).symm

end RelEffCartierDiv

end ModularCurves
