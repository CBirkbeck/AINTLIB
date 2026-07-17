import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
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

private def siteSheafEquivTop (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≌
      Sheaf AddCommGrpCat.{u} X where
  functor :=
    { obj := fun F ↦ F
      map := fun f ↦ f }
  inverse :=
    { obj := fun F ↦ F
      map := fun f ↦ f }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

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

/-- Positive-degree vanishing after restriction to an open implies the corresponding
positive-degree vanishing for the cohomology presheaf. -/
theorem subsingleton_HPrime_succ_of_subsingleton_restrict_H
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat U.isOpenEmbedding).obj F) (n + 1))] :
    Subsingleton ((toSiteSheaf F).H' (n + 1) U) := by
  induction n generalizing F with
  | zero =>
      exact subsingleton_HPrime_one_of_subsingleton_restrict_H F U
  | succ n ih =>
      let pres := (EnoughInjectives.presentation (toSiteSheaf F)).some
      let S := pres.shortComplex
      have hS : S.ShortExact := pres.shortExact_shortComplex
      let R := restrict AddCommGrpCat.{u} U.isOpenEmbedding
      haveI : R.Additive := restrict_additive U.isOpenEmbedding
      have hR : R.PreservesZeroMorphisms :=
        { map_zero := fun _ _ ↦ R.mapAddHom.map_zero }
      have hRlim : PreservesFiniteLimits R := by
        dsimp [R]
        exact restrict_preservesFiniteLimits U.isOpenEmbedding
      have hRcolim : PreservesFiniteColimits R := by
        dsimp [R]
        infer_instance
      let SU := @ShortComplex.map _ _ _ _ _ _ S R hR
      have hSU : SU.ShortExact := by
        exact @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS R hR
          hRlim hRcolim
      letI : Injective S.X₂ := by
        dsimp [S]
        exact pres.injective
      let E := siteSheafEquivTop X
      letI : E.functor.IsEquivalence := E.isEquivalence_functor
      let ITop : Sheaf AddCommGrpCat.{u} X := E.functor.obj S.X₂
      letI : Injective ITop := by
        dsimp [ITop]
        exact E.functor.injective_obj_of_injective (inferInstance : Injective S.X₂)
      letI : IsFlasque ITop := IsFlasque.of_injective ITop
      letI : IsFlasque SU.X₂ := by
        change IsFlasque (R.obj ITop)
        exact IsFlasque.of_restrict AddCommGrpCat ITop U.isOpenEmbedding
      have hF : Subsingleton (TopCat.Sheaf.H SU.X₁ (n + 2)) := by
        change Subsingleton (TopCat.Sheaf.H (R.obj F) (n + 2))
        simpa [Nat.add_assoc] using
          (inferInstance : Subsingleton (TopCat.Sheaf.H (R.obj F) (n + 1 + 1)))
      letI : Subsingleton (TopCat.Sheaf.H SU.X₁ (n + 2)) := hF
      have hI : Subsingleton (TopCat.Sheaf.H SU.X₂ (n + 1)) :=
        IsFlasque.subsingleton_H n
      letI : Subsingleton (TopCat.Sheaf.H SU.X₂ (n + 1)) := hI
      have hQ : Subsingleton (TopCat.Sheaf.H SU.X₃ (n + 1)) := by
        refine subsingleton_of_forall_eq 0 fun x ↦ ?_
        have hxδ : CategoryTheory.Sheaf.H.δ hSU (n + 1) (n + 2) rfl x = 0 :=
          Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
          hSU (n + 1) (n + 2) rfl x hxδ
        rw [← hy, Subsingleton.elim y 0, map_zero]
      letI : Subsingleton (TopCat.Sheaf.H (R.obj S.X₃) (n + 1)) := by
        change Subsingleton (TopCat.Sheaf.H SU.X₃ (n + 1))
        exact hQ
      have hQ' : Subsingleton (S.X₃.H' (n + 1) U) := ih S.X₃
      change Subsingleton (CategoryTheory.Abelian.Ext
        (HPrimeRepresentingSheaf U) (toSiteSheaf F) (n + 2))
      refine ⟨fun a b ↦ ?_⟩
      have eq_zero (x : CategoryTheory.Abelian.Ext
          (HPrimeRepresentingSheaf U) (toSiteSheaf F) (n + 2)) : x = 0 := by
        have hx : x.comp (CategoryTheory.Abelian.Ext.mk₀ S.f)
            (add_zero (n + 2)) = 0 :=
          CategoryTheory.Abelian.Ext.eq_zero_of_injective _
        obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
          (HPrimeRepresentingSheaf U) hS x hx rfl
        rw [← hy]
        haveI : Subsingleton (CategoryTheory.Abelian.Ext
            (HPrimeRepresentingSheaf U) S.X₃ (n + 1)) := by
          change Subsingleton (S.X₃.H' (n + 1) U)
          exact hQ'
        rw [Subsingleton.elim y 0, CategoryTheory.Abelian.Ext.zero_comp]
      exact (eq_zero a).trans (eq_zero b).symm

end


end TopCat.Sheaf
