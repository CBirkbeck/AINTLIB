/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ModularCurves.ForMathlib.SchemeTheoreticImage

/-!
# Proper morphisms extending dense open immersions

A proper morphism which extends an open immersion from a quasi-compact
scheme-theoretically dense open is an isomorphism over the range of that open.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {U X Y : Scheme.{u}}

/-- A proper morphism extending a quasi-compact scheme-theoretically dense open immersion
is an isomorphism over the corresponding target open. -/
lemma Scheme.Hom.isIso_morphismRestrict_opensRange_of_isProper
    (f : X ⟶ Y) (i : U ⟶ X) (j : U ⟶ Y)
    [IsProper f] [IsOpenImmersion i] [IsSchemeTheoreticallyDominant i]
    [QuasiCompact i] [IsOpenImmersion j] (h : i ≫ f = j) :
    IsIso (f ∣_ j.opensRange) := by
  have hi : Set.range i ⊆ Set.range (f ⁻¹ᵁ j.opensRange).ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨i x, ?_⟩, rfl⟩
    change f (i x) ∈ j.opensRange
    apply Scheme.Hom.mem_opensRange.mpr
    refine ⟨x, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : U ⟶ Y ↦ k x) h.symm
  let s : U ⟶ (f ⁻¹ᵁ j.opensRange).toScheme :=
    IsOpenImmersion.lift (f ⁻¹ᵁ j.opensRange).ι i hi
  have hs_fac : s ≫ (f ⁻¹ᵁ j.opensRange).ι = i :=
    IsOpenImmersion.lift_fac (f ⁻¹ᵁ j.opensRange).ι i hi
  letI : IsOpenImmersion s := by infer_instance
  letI : IsSchemeTheoreticallyDominant s := by
    dsimp only [s]
    exact IsSchemeTheoreticallyDominant.lift_of_isOpenImmersion i
      (f ⁻¹ᵁ j.opensRange).ι hi
  have hsg : s ≫ (f ∣_ j.opensRange) = j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι]
    calc
      (s ≫ (f ∣_ j.opensRange)) ≫ j.opensRange.ι =
          s ≫ ((f ∣_ j.opensRange) ≫ j.opensRange.ι) :=
        Category.assoc _ _ _
      _ = s ≫ ((f ⁻¹ᵁ j.opensRange).ι ≫ f) := by
        rw [morphismRestrict_ι]
      _ = (s ≫ (f ⁻¹ᵁ j.opensRange).ι) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = i ≫ f := by rw [hs_fac]
      _ = j := h
      _ = j.isoOpensRange.hom ≫ j.opensRange.ι :=
        (Scheme.Hom.isoOpensRange_hom_ι j).symm
  letI : IsProper (f ∣_ j.opensRange) := by infer_instance
  haveI : IsProper (s ≫ (f ∣_ j.opensRange)) := by
    rw [hsg]
    infer_instance
  letI : IsProper s := IsProper.of_comp s (f ∣_ j.opensRange)
  letI : QuasiCompact s := inferInstance
  letI : IsDominant s := inferInstance
  letI : Surjective s := surjective_of_isDominant_of_isClosed_range s
    s.isClosedMap.isClosed_range
  letI : IsIso s :=
    (isIso_iff_isOpenImmersion_and_surjective s).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso (s ≫ (f ∣_ j.opensRange)) := by
    rw [hsg]
    infer_instance
  exact (isIso_comp_left_iff s (f ∣_ j.opensRange)).mp inferInstance

end

end AlgebraicGeometry
