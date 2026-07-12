import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections
import ModularCurves.ForMathlib.FlasqueCohomology

/-!
# Sheaf cohomology as derived global sections

This file identifies `Ext` from a representing object with the right-derived functors of
the represented additive functor. It then specializes this comparison to identify genuine
sheaf cohomology with right-derived global sections.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Abelian.Ext

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

private def cochainToSectionsEquiv
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor C 0).obj Z) K n ≃+
      ↑(G.obj (K.X n)) :=
  (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans (e (K.X n))

private def cochainToSectionsIso
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    (((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).X n ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj K).X n :=
  (cochainToSectionsEquiv e K n).toAddCommGrpIso

omit [G.Additive] in
private lemma cochainToSectionsEquiv_fromSingleMk
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) (f : Z ⟶ K.X n) :
    cochainToSectionsEquiv e K n
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n)) = e (K.X n) f := by
  exact congrArg (e (K.X n))
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk f (zero_add n))

private lemma cochainToSectionsIso_hom_apply
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    (cochainToSectionsIso e K n).hom.hom α = cochainToSectionsEquiv e K n α :=
  rfl

private lemma homComplex_d_apply
    (K : CochainComplex C ℤ) (i j : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K i) :
    ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).d i j).hom α =
      CochainComplex.HomComplex.δ i j α :=
  rfl

private def homComplexIsoSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (K : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj Z).HomComplex K ≅
      (G.mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (cochainToSectionsIso e K) fun i j hij ↦ by
    ext α
    obtain ⟨f, rfl⟩ :=
      CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α i (zero_add i)
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
      cochainToSectionsIso_hom_apply, Functor.mapHomologicalComplex_obj_d,
      homComplex_d_apply, cochainToSectionsIso_hom_apply]
    rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j
      (zero_add j), cochainToSectionsEquiv_fromSingleMk,
      cochainToSectionsEquiv_fromSingleMk]
    exact (he f (K.d i j)).symm

private def mapXIso (K : CochainComplex C ℕ) (n : ℕ) :
    G.obj (K.X n) ≅ ((G.mapHomologicalComplex (.up ℕ)).obj K).X n :=
  Iso.refl _

private lemma mapXIso_naturality (K : CochainComplex C ℕ) (i j : ℕ) :
    (mapXIso K i).hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d i j =
      G.map (K.d i j) ≫ (mapXIso K j).hom :=
  rfl

private def mapExtendXIso
    (K : CochainComplex C ℕ) (n : ℤ) :
    G.obj ((K.extend ComplexShape.embeddingUpNat).X n) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X n := by
  classical
  exact if h : ∃ k, ComplexShape.embeddingUpNat.f k = n then
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat h.choose_spec) ≪≫
        mapXIso K h.choose ≪≫
        (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat h.choose_spec).symm
    else
      IsZero.iso
        (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat n
          (fun k hk ↦ h ⟨k, hk⟩)))
        (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat n (fun k hk ↦ h ⟨k, hk⟩))

private def mapExtendIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso K) fun i j hij ↦ by
    by_cases hi : ∃ k, ComplexShape.embeddingUpNat.f k = i
    · by_cases hj : ∃ k, ComplexShape.embeddingUpNat.f k = j
      · simp only [mapExtendXIso, dif_pos hi, dif_pos hj]
        rw [Functor.mapHomologicalComplex_obj_d,
          HomologicalComplex.extend_d_eq ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat hi.choose_spec hj.choose_spec,
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
            hi.choose_spec hj.choose_spec]
        let eᵢ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          hi.choose_spec
        let eⱼ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          hj.choose_spec
        let fᵢ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat hi.choose_spec
        let fⱼ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat hj.choose_spec
        let mᵢ := mapXIso (G := G) K hi.choose
        let mⱼ := mapXIso (G := G) K hj.choose
        change (G.map eᵢ.hom ≫ mᵢ.hom ≫ fᵢ.inv) ≫
            (fᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
              hi.choose hj.choose ≫ fⱼ.inv) =
          G.map (eᵢ.hom ≫ K.d hi.choose hj.choose ≫ eⱼ.inv) ≫
            (G.map eⱼ.hom ≫ mⱼ.hom ≫ fⱼ.inv)
        calc
          _ = G.map eᵢ.hom ≫
              (mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                hi.choose hj.choose) ≫ fⱼ.inv := by
            simp [Category.assoc]
          _ = G.map eᵢ.hom ≫
              (G.map (K.d hi.choose hj.choose) ≫ mⱼ.hom) ≫ fⱼ.inv := by
            rw [show mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                hi.choose hj.choose = G.map (K.d hi.choose hj.choose) ≫ mⱼ.hom by
              exact mapXIso_naturality K hi.choose hj.choose]
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      · exact (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat j (fun k hk ↦ hj ⟨k, hk⟩) |>.eq_of_tgt _ _)
    · exact (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun k hk ↦ hi ⟨k, hk⟩)) |>.eq_of_src _ _)

private def extAddEquivHomComplexHomology
    [HasExt.{v} C] (R : InjectiveResolution F) (n : ℕ) :
    Ext.{v} Z F n ≃+
      ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) :=
  (R.extAddEquivCohomologyClass (X := Z)).trans
    (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj Z) R.cochainComplex n).symm

private def homComplexHomologyAddEquivSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (R : InjectiveResolution F) (n : ℕ) :
    ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
    (homComplexIsoSections e he R.cochainComplex)).addCommGroupIsoToAddEquiv

private def sectionsCochainHomologyAddEquivCocomplex
    (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
      (mapExtendIso R.cocomplex)).addCommGroupIsoToAddEquiv.trans
    (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).addCommGroupIsoToAddEquiv

private def sectionsCocomplexHomologyAddEquivRightDerived
    [HasInjectiveResolutions C] (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) ≃+
      ↑((G.rightDerived n).obj F) :=
  (R.isoRightDerivedObj G n).symm.addCommGroupIsoToAddEquiv

/-- If an additive functor is represented by `Z`, then `Extⁿ(Z, -)` agrees with its
right-derived functor in degree `n`. -/
noncomputable def addEquivRightDerived
    [HasExt.{v} C] [HasInjectiveResolutions C]
    (G : C ⥤ AddCommGrpCat.{v}) [G.Additive] (Z F : C)
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f)) (n : ℕ) :
    Ext.{v} Z F n ≃+ ↑((G.rightDerived n).obj F) :=
  let R := injectiveResolution F
  (extAddEquivHomComplexHomology R n).trans
    ((homComplexHomologyAddEquivSections e he R n).trans
      ((sectionsCochainHomologyAddEquivCocomplex R n).trans
        (sectionsCocomplexHomologyAddEquivRightDerived R n)))

end

end CategoryTheory.Abelian.Ext

open TopologicalSpace

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}

private abbrev J (X : TopCat.{u}) := Opens.grothendieckTopology X

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (J X) AddCommGrpCat.{u}

private abbrev constantZ (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (J X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

noncomputable local instance : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).right_adjoint_additive

private def homToGlobalSectionsEquiv
    (F : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}) :
    (constantZ X ⟶ F) ≃+ ↑((globalSections X).obj F) :=
  ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homAddEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj F))

private lemma homToGlobalSectionsEquiv_naturality
    {F G : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}}
    (f : constantZ X ⟶ F) (g : F ⟶ G) :
    homToGlobalSectionsEquiv G (f ≫ g) =
      (globalSections X).map g (homToGlobalSectionsEquiv F f) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homEquiv _ _ (f ≫ g)) = _
  rw [(CategoryTheory.constantSheafΓAdj
    (J X) AddCommGrpCat.{u}).homEquiv_naturality_right]
  rfl

/-- Sheaf cohomology agrees with the right-derived functors of global sections. -/
noncomputable def H.addEquivRightDerivedGlobalSections
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H F n ≃+ ↑(((globalSections X).rightDerived n).obj (toSiteSheaf F)) := by
  exact CategoryTheory.Abelian.Ext.addEquivRightDerived
    (globalSections X) (constantZ X) (toSiteSheaf F)
    homToGlobalSectionsEquiv
    (fun f g ↦ homToGlobalSectionsEquiv_naturality f g) n

end

end TopCat.Sheaf
