import ModularCurves.ForMathlib.FlasqueCohomology

/-!
# Cohomology over a terminal object

This file identifies degree-zero values of mathlib's cohomology presheaf with sections,
and its value at a terminal object with ordinary sheaf cohomology. The latter fills the
terminal-object comparison TODO recorded in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}

private abbrev siteSheaf (X : TopCat.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

private abbrev freeAbSheaf (T : Opens X) : siteSheaf X :=
  (presheafToSheaf _ _).obj (yoneda.obj T ⋙ AddCommGrpCat.free)

private abbrev underlyingSections (F : siteSheaf X) :=
  ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat)).obj F.obj

private def freeAbSheafHomEquiv (T : Opens X) (F : siteSheaf X) :
    (freeAbSheaf T ⟶ F) ≃ (underlyingSections F).obj (op T) :=
  ((sheafificationAdjunction _ _).homEquiv (yoneda.obj T ⋙ AddCommGrpCat.free) F).trans <|
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj T) F.obj).trans yonedaEquiv

private def sectionEquiv (F : siteSheaf X) (T : Opens X) :
    ↑(F.obj.obj (op T)) ≃ (underlyingSections F).obj (op T) where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

private lemma sectionEquiv_map {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X) (s : ↑(F.obj.obj (op V))) :
    sectionEquiv F U (F.obj.map i.op s) =
      (underlyingSections F).map i.op (sectionEquiv F V s) :=
  rfl

private abbrev freeAbSheafMap {U V : Opens X} (i : U ⟶ V) :
    freeAbSheaf U ⟶ freeAbSheaf V :=
  (presheafToSheaf _ _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

private abbrev sheafificationHomEquiv (T : Opens X) (F : siteSheaf X) :=
  (sheafificationAdjunction _ _).homEquiv (yoneda.obj T ⋙ AddCommGrpCat.free) F

private abbrev freeHomEquiv (T : Opens X) (F : siteSheaf X) :=
  (AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj T) F.obj

private def sheafificationToFreeHomEquiv (T : Opens X) (F : siteSheaf X) :
    (yoneda.obj T ⋙ AddCommGrpCat.free ⟶
        (sheafToPresheaf _ _).obj F) ≃
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj (yoneda.obj T) ⟶
        F.obj) where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev sheafificationToFreeHom (T : Opens X) (F : siteSheaf X)
    (f : yoneda.obj T ⋙ AddCommGrpCat.free ⟶
      (sheafToPresheaf _ _).obj F) :=
  sheafificationToFreeHomEquiv T F f

private lemma freeAbSheafHomEquiv_apply (T : Opens X) (F : siteSheaf X)
    (f : freeAbSheaf T ⟶ F) :
    freeAbSheafHomEquiv T F f =
      yonedaEquiv (freeHomEquiv T F
        (sheafificationToFreeHom T F (sheafificationHomEquiv T F f))) :=
  rfl

private lemma sheafificationHomEquiv_naturality_left {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X) (f : freeAbSheaf V ⟶ F) :
    sheafificationHomEquiv U F (freeAbSheafMap i ≫ f) =
      Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫
        sheafificationHomEquiv V F f := by
  exact (sheafificationAdjunction _ _).homEquiv_naturality_left _ _

private lemma freeHomEquiv_naturality_left {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X)
    (f : yoneda.obj V ⋙ AddCommGrpCat.free ⟶
      (sheafToPresheaf _ _).obj F) :
    freeHomEquiv U F
        (sheafificationToFreeHom U F
          (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫ f)) =
      yoneda.map i ≫ freeHomEquiv V F (sheafificationToFreeHom V F f) := by
  change freeHomEquiv U F
      (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free ≫
        sheafificationToFreeHom V F f) = _
  exact (AddCommGrpCat.adj.whiskerRight _).homEquiv_naturality_left _ _

private lemma freeAbSheafHomEquiv_naturality_left {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X) (f : freeAbSheaf V ⟶ F) :
    freeAbSheafHomEquiv U F (freeAbSheafMap i ≫ f) =
      (underlyingSections F).map i.op (freeAbSheafHomEquiv V F f) := by
  rw [freeAbSheafHomEquiv_apply, freeAbSheafHomEquiv_apply,
    yonedaEquiv_naturality]
  apply congrArg yonedaEquiv
  exact (congrArg (freeHomEquiv U F)
      (congrArg (sheafificationToFreeHomEquiv U F)
        (sheafificationHomEquiv_naturality_left i F f))).trans
    (freeHomEquiv_naturality_left i F (sheafificationHomEquiv V F f))

private def freeAbSheafHomSectionEquiv (T : Opens X) (F : siteSheaf X) :
    (freeAbSheaf T ⟶ F) ≃ ↑(F.obj.obj (op T)) :=
  (freeAbSheafHomEquiv T F).trans (sectionEquiv F T).symm

private lemma freeAbSheafHomSectionEquiv_naturality_left {U V : Opens X}
    (i : U ⟶ V) (F : siteSheaf X) (f : freeAbSheaf V ⟶ F) :
    freeAbSheafHomSectionEquiv U F (freeAbSheafMap i ≫ f) =
      F.obj.map i.op (freeAbSheafHomSectionEquiv V F f) := by
  change (sectionEquiv F U).symm
      (freeAbSheafHomEquiv U F (freeAbSheafMap i ≫ f)) =
    F.obj.map i.op ((sectionEquiv F V).symm (freeAbSheafHomEquiv V F f))
  apply (sectionEquiv F U).injective
  rw [Equiv.apply_symm_apply, sectionEquiv_map, Equiv.apply_symm_apply]
  exact freeAbSheafHomEquiv_naturality_left i F f

private lemma freeAbSheafHomSectionEquiv_add (T : Opens X) (F : siteSheaf X)
    (f g : freeAbSheaf T ⟶ F) :
    freeAbSheafHomSectionEquiv T F (f + g) =
      freeAbSheafHomSectionEquiv T F f + freeAbSheafHomSectionEquiv T F g := by
  change (sectionEquiv F T).symm (freeAbSheafHomEquiv T F (f + g)) =
    (sectionEquiv F T).symm (freeAbSheafHomEquiv T F f) +
      (sectionEquiv F T).symm (freeAbSheafHomEquiv T F g)
  apply (sectionEquiv F T).injective
  change freeAbSheafHomEquiv T F (f + g) = _
  rw [freeAbSheafHomEquiv_apply]
  simp only [(sheafificationAdjunction _ _).homAddEquiv_add]
  rfl

private def freeAbSheafHomAddEquiv (T : Opens X) (F : siteSheaf X) :
    (freeAbSheaf T ⟶ F) ≃+ ↑(F.obj.obj (op T)) where
  toEquiv := freeAbSheafHomSectionEquiv T F
  map_add' := freeAbSheafHomSectionEquiv_add T F

private lemma freeAbSheafHomAddEquiv_naturality_left {U V : Opens X}
    (i : U ⟶ V) (F : siteSheaf X) (f : freeAbSheaf V ⟶ F) :
    freeAbSheafHomAddEquiv U F (freeAbSheafMap i ≫ f) =
      F.obj.map i.op (freeAbSheafHomAddEquiv V F f) :=
  freeAbSheafHomSectionEquiv_naturality_left i F f

private def hPrimeZeroExtAddEquiv (F : siteSheaf X) (T : Opens X) :
    ↑(F.H' 0 T) ≃+
      CategoryTheory.Abelian.Ext (freeAbSheaf T) F 0 where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private lemma hPrimeZeroExtAddEquiv_map {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X) (x : F.H' 0 V) :
    hPrimeZeroExtAddEquiv F U ((F.cohomologyPresheaf 0).map i.op x) =
      (CategoryTheory.Abelian.Ext.mk₀ (freeAbSheafMap i)).comp
        (hPrimeZeroExtAddEquiv F V x) (zero_add 0) :=
  rfl

private lemma extAddEquivZero_precomp {U V : Opens X} (i : U ⟶ V)
    (F : siteSheaf X)
    (x : CategoryTheory.Abelian.Ext (freeAbSheaf V) F 0) :
    CategoryTheory.Abelian.Ext.addEquiv₀
        ((CategoryTheory.Abelian.Ext.mk₀ (freeAbSheafMap i)).comp x (zero_add 0)) =
      freeAbSheafMap i ≫ CategoryTheory.Abelian.Ext.addEquiv₀ x := by
  apply (CategoryTheory.Abelian.Ext.mk₀_bijective _ _).injective
  rw [CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply]
  rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
    CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply]

/-- Degree-zero cohomology over an open set is naturally equivalent to its sections. -/
def HPrimeZeroAddEquivSections (F : siteSheaf X) (T : Opens X) :
    ↑(F.H' 0 T) ≃+ ↑(F.obj.obj (op T)) :=
  (hPrimeZeroExtAddEquiv F T).trans <|
    CategoryTheory.Abelian.Ext.addEquiv₀.trans (freeAbSheafHomAddEquiv T F)

@[simp]
lemma HPrimeZeroAddEquivSections_apply (F : siteSheaf X)
    (T : Opens X) (x : F.H' 0 T) :
    HPrimeZeroAddEquivSections F T x =
      freeAbSheafHomAddEquiv T F
        (CategoryTheory.Abelian.Ext.addEquiv₀ (hPrimeZeroExtAddEquiv F T x)) :=
  rfl

/-- The degree-zero comparison commutes with restriction to a smaller open set. -/
lemma HPrimeZeroAddEquivSections_naturality (F : siteSheaf X)
    {U V : Opens X} (i : U ⟶ V) (x : F.H' 0 V) :
    HPrimeZeroAddEquivSections F U (F.cohomologyPresheaf 0 |>.map i.op x) =
      F.obj.map i.op (HPrimeZeroAddEquivSections F V x) := by
  rw [HPrimeZeroAddEquivSections_apply, HPrimeZeroAddEquivSections_apply]
  rw [hPrimeZeroExtAddEquiv_map, extAddEquivZero_precomp,
    freeAbSheafHomAddEquiv_naturality_left]

private abbrev constantZSheaf (X : TopCat.{u}) : siteSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

private def constantSheafHomEquiv (T : Opens X) (hT : IsTerminal T)
    (F : siteSheaf X) :
    (constantZSheaf X ⟶ F) ≃
      ↑(F.obj.obj (op T)) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} hT).homEquiv
    (AddCommGrpCat.of (ULift ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv

private lemma constantSheafHomEquiv_naturality (T : Opens X) (hT : IsTerminal T)
    {F G : siteSheaf X}
    (f : constantZSheaf X ⟶ F) (g : F ⟶ G) :
    constantSheafHomEquiv T hT G (f ≫ g) =
      g.hom.app (op T) (constantSheafHomEquiv T hT F f) := by
  change (AddCommGrpCat.coyonedaObjIsoForget.hom.app _)
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} hT).homEquiv _ _
        (f ≫ g)) = _
  rw [(constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    hT).homEquiv_naturality_right]
  rfl

private lemma freeAbSheafHomEquiv_naturality_right (T : Opens X)
    {F G : siteSheaf X} (f : freeAbSheaf T ⟶ F) (g : F ⟶ G) :
    freeAbSheafHomEquiv T G (f ≫ g) =
      g.hom.app (op T) (freeAbSheafHomEquiv T F f) := by
  rfl

/-- The free abelian sheaf represented by a terminal open is the constant sheaf `ℤ`. -/
def freeAbSheafIsoConstantOfIsTerminal (T : Opens X) (hT : IsTerminal T) :
    freeAbSheaf T ≅ constantZSheaf X :=
  Coyoneda.ext (C := siteSheaf X) _ _
    (fun {Z : siteSheaf X} f ↦
      (constantSheafHomEquiv T hT Z).symm
        (freeAbSheafHomEquiv T Z f))
    (fun {Z : siteSheaf X} f ↦
      (freeAbSheafHomEquiv T Z).symm
        (constantSheafHomEquiv T hT Z f))
    (fun f ↦ by simp)
    (fun f ↦ by simp)
    (fun f g ↦ by
      apply (freeAbSheafHomEquiv T _).injective
      rw [Equiv.apply_symm_apply, freeAbSheafHomEquiv_naturality_right,
        Equiv.apply_symm_apply]
      exact constantSheafHomEquiv_naturality T hT f g)

/-- At a terminal open, the cohomology presheaf value is ordinary sheaf cohomology. -/
def HPrimeAddEquivHOfIsTerminal (F : Sheaf AddCommGrpCat.{u} X)
    (T : Opens X) (hT : IsTerminal T) (n : ℕ) :
    ↑((toSiteSheaf F).H' n T) ≃+ H F n :=
  (((CategoryTheory.Abelian.extFunctor
    (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) n).mapIso
    (freeAbSheafIsoConstantOfIsTerminal T hT).symm.op).app
      (toSiteSheaf F)).addCommGroupIsoToAddEquiv

end

end TopCat.Sheaf
