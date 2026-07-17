import Mathlib.CategoryTheory.Abelian.Injective.Ext
import ModularCurves.ForMathlib.SheafCechInjectiveAugmentation
import ModularCurves.ForMathlib.SheafCohomologyTerminal

/-!
# Sheaf cohomology over open subsets

This file compares mathlib's cohomology-presheaf values with ordinary cohomology
after restriction to an open subset. The degree-one comparison is obtained by
evaluating an injective resolution on the open and using the represented-free-sheaf
description of sections.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}

/-- Degree-one vanishing for the restriction to an open implies degree-one
vanishing for the corresponding value of the cohomology presheaf. -/
theorem subsingleton_HPrime_one_of_subsingleton_restrict_H
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat U.isOpenEmbedding).obj F) 1)] :
    Subsingleton ((toSiteSheaf F).H' 1 U) := by
  let I := injectiveResolution (toSiteSheaf F)
  change Subsingleton (CategoryTheory.Abelian.Ext
    (HPrimeRepresentingSheaf U) (toSiteSheaf F) 1)
  refine ⟨fun a b ↦ ?_⟩
  have eq_zero (x : CategoryTheory.Abelian.Ext
      (HPrimeRepresentingSheaf U) (toSiteSheaf F) 1) : x = 0 := by
    obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x 2 rfl
    rw [I.extMk_eq_zero_iff f 2 rfl hf 0 rfl]
    have hExact := injectiveResolution_app_exactAt_one_of_subsingleton_H F U
    rw [ShortComplex.ab_exact_iff] at hExact
    let y := HPrimeRepresentingSheafHomAddEquiv U (I.cocomplex.X 1) f
    have hy : ((I.cocomplex.d 1 2).hom.app (op U)) y = 0 := by
      rw [← HPrimeRepresentingSheafHomAddEquiv_naturality_right U f
        (I.cocomplex.d 1 2)]
      rw [hf, map_zero]
    obtain ⟨z, hz⟩ := hExact y hy
    let g := (HPrimeRepresentingSheafHomAddEquiv U (I.cocomplex.X 0)).symm z
    refine ⟨g, ?_⟩
    apply (HPrimeRepresentingSheafHomAddEquiv U (I.cocomplex.X 1)).injective
    rw [HPrimeRepresentingSheafHomAddEquiv_naturality_right,
      AddEquiv.apply_symm_apply]
    exact hz
  exact (eq_zero a).trans (eq_zero b).symm

end


end TopCat.Sheaf
