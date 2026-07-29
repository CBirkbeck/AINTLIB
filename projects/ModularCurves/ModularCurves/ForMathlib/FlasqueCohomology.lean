import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Sheaves.Flasque
import ModularCurves.ForMathlib.SheafCohomologyExact

/-!
# Cohomology of flasque sheaves

This file contains an option-free version of the flasque-acyclicity core of mathlib
PR #35790. It constructs the free abelian sheaves which detect restriction maps,
proves that injective additive sheaves are flasque, and deduces vanishing of their
positive-degree sheaf cohomology.
-/

open CategoryTheory TopologicalSpace Opposite Limits

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the `show`/`rfl`/`rw` steps below at `implicit` transparency.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}

/-- Regard a topological sheaf as a sheaf on the site of open subsets. -/
abbrev toSiteSheaf (F : Sheaf AddCommGrpCat.{u} X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  F

instance : HasExt.{u} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

/-- Cohomology of an additive sheaf on a topological space. -/
abbrev H (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H (toSiteSheaf F) n

/-- The map on cohomology induced by a morphism of additive sheaves. -/
abbrev H.map {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (n : ℕ) :
    H F n →+ H G n :=
  CategoryTheory.Sheaf.H.map f n

/-- Degree-zero cohomology is equivalent to global sections. -/
abbrev H.equiv₀ (F : Sheaf AddCommGrpCat X) :
    H F 0 ≃+ ↑((toSiteSheaf F).obj.obj (op ⊤)) :=
  CategoryTheory.Sheaf.H.equiv₀ (toSiteSheaf F) isTerminalTop

namespace IsFlasque

/-- The sheafification of the free abelian presheaf represented by an open set. -/
abbrev freeAbSheaf (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- An inclusion of opens induces a morphism between their free abelian sheaves. -/
abbrev freeAbSheafMap {U V : Opens X} (i : U ⟶ V) : freeAbSheaf U ⟶ freeAbSheaf V :=
  (presheafToSheaf _ _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

private def freeAbHomToSiteEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ I) ≃
      ((presheafToSheaf _ _).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ toSiteSheaf I) where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev underlyingSections (I : Sheaf AddCommGrpCat.{u} X) :=
  ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat)).obj
    (toSiteSheaf I).obj

/-- Morphisms from the free abelian sheaf on `U` correspond to sections over `U`. -/
def freeAbSheafHomEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ I) ≃ (underlyingSections I).obj (op U) :=
  (freeAbHomToSiteEquiv U I).trans <|
    ((sheafificationAdjunction _ _).homEquiv (yoneda.obj U ⋙ AddCommGrpCat.free)
      (toSiteSheaf I)).trans <|
      ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U)
        (toSiteSheaf I).obj).trans yonedaEquiv

private abbrev sheafificationHomEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :=
  (sheafificationAdjunction _ _).homEquiv (yoneda.obj U ⋙ AddCommGrpCat.free)
    (toSiteSheaf I)

private abbrev freeHomEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :=
  (AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U)
    (toSiteSheaf I).obj

private def sectionEquiv (I : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    ↑(I.obj.obj (op U)) ≃ (underlyingSections I).obj (op U) where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

private lemma sectionEquiv_map {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X) (s : ↑(I.obj.obj (op V))) :
    sectionEquiv I U (I.obj.map i.op s) =
      (underlyingSections I).map i.op (sectionEquiv I V s) :=
  rfl

private def sheafificationToFreeHomEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶
        (sheafToPresheaf _ _).obj (toSiteSheaf I)) ≃
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj (yoneda.obj U) ⟶
        (toSiteSheaf I).obj) where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev sheafificationToFreeHom (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X)
    (f : yoneda.obj U ⋙ AddCommGrpCat.free ⟶
      (sheafToPresheaf _ _).obj (toSiteSheaf I)) :=
  sheafificationToFreeHomEquiv U I f

private lemma freeAbSheafHomEquiv_apply (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X)
    (f : freeAbSheaf U ⟶ I) :
    freeAbSheafHomEquiv U I f =
      yonedaEquiv (freeHomEquiv U I (sheafificationToFreeHom U I
        (sheafificationHomEquiv U I (freeAbHomToSiteEquiv U I f)))) :=
  rfl

private lemma sheafificationHom_naturality {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    sheafificationHomEquiv U I (freeAbHomToSiteEquiv U I (freeAbSheafMap i ≫ f)) =
      Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫
        sheafificationHomEquiv V I (freeAbHomToSiteEquiv V I f) := by
  change sheafificationHomEquiv U I
      ((presheafToSheaf _ _).map
        (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫
          freeAbHomToSiteEquiv V I f) = _
  exact (sheafificationAdjunction _ _).homEquiv_naturality_left _ _

private lemma freeHom_naturality {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X)
    (f : yoneda.obj V ⋙ AddCommGrpCat.free ⟶
      (sheafToPresheaf _ _).obj (toSiteSheaf I)) :
    freeHomEquiv U I (sheafificationToFreeHom U I
        (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫ f)) =
      yoneda.map i ≫ freeHomEquiv V I (sheafificationToFreeHom V I f) := by
  change freeHomEquiv U I
      (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫
        sheafificationToFreeHom V I f) = _
  exact (AddCommGrpCat.adj.whiskerRight _).homEquiv_naturality_left _ _

private lemma freeAbSheafHomEquiv_underlying_naturality {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    freeAbSheafHomEquiv U I (freeAbSheafMap i ≫ f) =
      (underlyingSections I).map i.op (freeAbSheafHomEquiv V I f) := by
  rw [freeAbSheafHomEquiv_apply, freeAbSheafHomEquiv_apply,
    yonedaEquiv_naturality]
  apply congrArg yonedaEquiv
  exact (congrArg (fun g ↦ freeHomEquiv U I (sheafificationToFreeHom U I g))
      (sheafificationHom_naturality i I f)).trans
    (freeHom_naturality i I
      (sheafificationHomEquiv V I (freeAbHomToSiteEquiv V I f)))

lemma freeAbSheafHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    freeAbSheafHomEquiv U I (freeAbSheafMap i ≫ f) =
      (underlyingSections I).map i.op (freeAbSheafHomEquiv V I f) :=
  freeAbSheafHomEquiv_underlying_naturality i I f

instance freeAbSheafMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbSheafMap i) := by
  letI : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasSheafify.isLeftExact
  exact preserves_mono_of_preservesLimit (presheafToSheaf _ _) _

/-- Injective additive sheaves are flasque. -/
instance of_injective (I : Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasque I where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr fun s ↦ by
    obtain ⟨h, hh⟩ := Injective.factors
      ((freeAbSheafHomEquiv _ I).symm (sectionEquiv I _ s))
      (freeAbSheafMap i.unop)
    refine ⟨(sectionEquiv I _).symm (freeAbSheafHomEquiv _ I h), ?_⟩
    apply (sectionEquiv I _).injective
    calc
      _ = (underlyingSections I).map i
          (sectionEquiv I _ ((sectionEquiv I _).symm (freeAbSheafHomEquiv _ I h))) :=
        sectionEquiv_map i.unop I _
      _ = (underlyingSections I).map i (freeAbSheafHomEquiv _ I h) := by
        rw [Equiv.apply_symm_apply]
      _ = freeAbSheafHomEquiv _ I (freeAbSheafMap i.unop ≫ h) := by
        simpa only [Quiver.Hom.op_unop] using
          (freeAbSheafHomEquiv_naturality i.unop I h).symm
      _ = freeAbSheafHomEquiv _ I
          ((freeAbSheafHomEquiv _ I).symm (sectionEquiv I _ s)) :=
        congrArg (freeAbSheafHomEquiv _ I) hh
      _ = sectionEquiv I _ s := Equiv.apply_symm_apply _ _

private theorem H_one_isZero (F : Sheaf AddCommGrpCat X) [IsFlasque F] :
    IsZero (AddCommGrpCat.of (H F 1)) := by
  let pres := (EnoughInjectives.presentation F).some
  let S := pres.shortComplex
  have hS : S.ShortExact := pres.shortExact_shortComplex
  letI : Subsingleton (H F 1) := subsingleton_of_forall_eq 0 fun c ↦ by
    obtain ⟨x₃, hx₃⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁ hS 0 1 rfl c
      (Subsingleton.elim _ _)
    have hg : Function.Surjective (S.g.hom.app (op ⊤)) :=
      AddCommGrpCat.epi_iff_surjective _ |>.mp (epi_of_shortExact hS)
    obtain ⟨s₂, hs₂⟩ := hg (H.equiv₀ S.X₃ x₃)
    let x₂ := (H.equiv₀ S.X₂).symm s₂
    have hx₂ : H.map S.g 0 x₂ = x₃ := by
      apply (H.equiv₀ S.X₃).injective
      rw [← CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop]
      simpa [x₂] using hs₂
    rw [← hx₃, ← hx₂]
    exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃ hS 0 1 rfl x₂
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem H_succ_isZero (n : ℕ)
    (ih : ∀ (F : Sheaf AddCommGrpCat X), IsFlasque F →
      IsZero (AddCommGrpCat.of (H F (n + 1))))
    (F : Sheaf AddCommGrpCat X) [IsFlasque F] :
    IsZero (AddCommGrpCat.of (H F (n + 2))) := by
  let pres := (EnoughInjectives.presentation F).some
  let S := pres.shortComplex
  have hS : S.ShortExact := pres.shortExact_shortComplex
  letI : IsFlasque S.X₃ := of_shortExact_of_isFlasque₁₂ hS
  letI : Subsingleton (H S.X₃ (n + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero (ih S.X₃ inferInstance)
  letI : Subsingleton (H F (n + 2)) := subsingleton_of_forall_eq 0 fun c ↦ by
    obtain ⟨x₃, hx₃⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁ hS
      (n + 1) (n + 2) rfl c (Subsingleton.elim _ _)
    rw [← hx₃, Subsingleton.elim x₃ 0, map_zero]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Flasque additive sheaves have zero positive-degree sheaf cohomology. -/
theorem H_isZero (F : Sheaf AddCommGrpCat X) [IsFlasque F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (H F (n + 1))) := by
  induction n generalizing F with
  | zero => exact H_one_isZero F
  | succ n ih => exact H_succ_isZero n (fun G hG ↦ @ih G hG) F

instance subsingleton_H {F : Sheaf AddCommGrpCat X} [IsFlasque F] (n : ℕ) :
    Subsingleton (H F (n + 1)) :=
  AddCommGrpCat.subsingleton_of_isZero (H_isZero F n)

end IsFlasque

end

end TopCat.Sheaf
