import ModularCurves.ForMathlib.CochainComplexKernel
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Global sections and the ordered base-linear Cech complex

Identify global sections with the kernel of the first differential in the bounded ordered
base-linear Cech complex. In degree zero, every one-tuple is strictly increasing, so the
projection from the native Cech complex to the ordered complex is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- In degree zero, the ordered-to-native alternating extension is also a retraction of the
native-to-ordered projection. -/
theorem baseCechToOrderedF_comp_orderedToBaseCechAlternatingF_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechToOrderedF π M U 0 ≫
        orderedToBaseCechAlternatingF π M U 0 = 𝟙 _ := by
  apply (cancel_mono (baseCechXIsoPi π M U 0).hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi : StrictMono i := by
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    exact Fin.elim0 j
  let p : ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ j : Fin 1 → ι, baseCechFactor π M U 0 j) ⟶
      ModuleCat.of Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U 0 i) :=
    ModuleCat.ofHom (LinearMap.proj i)
  have hcomp :
      ((baseCechToOrderedF π M U 0 ≫
          orderedToBaseCechAlternatingF π M U 0) ≫
            (baseCechXIsoPi π M U 0).hom) ≫ p =
        ((𝟙 (baseCechComplex π M U).X 0) ≫
          (baseCechXIsoPi π M U 0).hom) ≫ p := by
    dsimp only [p]
    simp only [Category.assoc]
    rw [baseCechXIsoPi_hom_comp_proj π M U 0 i]
    rw [orderedToBaseCechAlternatingF_comp_π_of_strictMono π M U 0 i hi]
    exact baseCechToOrderedF_comp_π π M U 0 ⟨i, hi⟩
  exact ConcreteCategory.congr_hom hcomp x

private noncomputable def baseCechKernelToOrderedLinearMap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    LinearMap.ker ((baseCechComplex π M U).d 0 1).hom →ₗ[
        Γ(S, (⊤ : S.Opens))]
      LinearMap.ker ((orderedBaseCechComplex π M U).d 0 1).hom where
  toFun x := ⟨(baseCechToOrderedF π M U 0).hom x.1, by
    rw [orderedBaseCechComplex_d]
    change ((baseCechToOrderedF π M U 0 ≫
      orderedBaseCechDifferential π M U 0).hom) x.1 = 0
    rw [← baseCechComplex_d_comp_baseCechToOrderedF π M U 0]
    change (baseCechToOrderedF π M U 1).hom
      (((baseCechComplex π M U).d 0 1).hom x.1) = 0
    rw [x.2, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change (baseCechToOrderedF π M U 0).hom (r • x.1) =
      r • (baseCechToOrderedF π M U 0).hom x.1
    exact (baseCechToOrderedF π M U 0).hom.map_smul r x.1

private noncomputable def orderedBaseCechKernelToBaseLinearMap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    LinearMap.ker ((orderedBaseCechComplex π M U).d 0 1).hom →ₗ[
        Γ(S, (⊤ : S.Opens))]
      LinearMap.ker ((baseCechComplex π M U).d 0 1).hom where
  toFun x := ⟨(orderedToBaseCechAlternatingF π M U 0).hom x.1, by
    change ((orderedToBaseCechAlternatingF π M U 0 ≫
      (baseCechComplex π M U).d 0 1).hom) x.1 = 0
    rw [orderedToBaseCechAlternatingF_comp_d π M U 0]
    change (orderedToBaseCechAlternatingF π M U 1).hom
      (((orderedBaseCechComplex π M U).d 0 1).hom x.1) = 0
    rw [x.2]
    change (orderedToBaseCechAlternatingF π M U 1).hom
      (0 : orderedBaseCechObject π M U 1) = 0
    exact (orderedToBaseCechAlternatingF π M U 1).hom.map_zero⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change (orderedToBaseCechAlternatingF π M U 0).hom (r • x.1) =
      r • (orderedToBaseCechAlternatingF π M U 0).hom x.1
    exact (orderedToBaseCechAlternatingF π M U 0).hom.map_smul r x.1

private theorem baseCechKernelToOrdered_comp_orderedBaseCechKernelToBase
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (baseCechKernelToOrderedLinearMap π M U).comp
      (orderedBaseCechKernelToBaseLinearMap π M U) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (orderedToBaseCechAlternatingF_comp_baseCechToOrderedF π M U 0) x.1

private theorem orderedBaseCechKernelToBase_comp_baseCechKernelToOrdered
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (orderedBaseCechKernelToBaseLinearMap π M U).comp
      (baseCechKernelToOrderedLinearMap π M U) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (baseCechToOrderedF_comp_orderedToBaseCechAlternatingF_zero π M U) x.1

/-- The degree-zero kernels of the native and ordered base-linear Cech complexes are linearly
equivalent. -/
noncomputable def baseCechKernelOrderedLinearEquiv
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    LinearMap.ker ((baseCechComplex π M U).d 0 1).hom ≃ₗ[
        Γ(S, (⊤ : S.Opens))]
      LinearMap.ker ((orderedBaseCechComplex π M U).d 0 1).hom :=
  LinearEquiv.ofLinear (baseCechKernelToOrderedLinearMap π M U)
    (orderedBaseCechKernelToBaseLinearMap π M U)
    (baseCechKernelToOrdered_comp_orderedBaseCechKernelToBase π M U)
    (orderedBaseCechKernelToBase_comp_baseCechKernelToOrdered π M U)

/-- The native-to-ordered kernel equivalence is induced by the degree-zero
projection to the ordered Cech complex. -/
theorem baseCechKernelOrderedLinearEquiv_coe
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : LinearMap.ker ((baseCechComplex π M U).d 0 1).hom) :
    (baseCechKernelOrderedLinearEquiv π M U x).1 =
      (baseCechToOrderedF π M U 0).hom x.1 := by
  rfl

/-- The ordered-to-native kernel equivalence is induced by the degree-zero
alternating extension to the native Cech complex. -/
theorem baseCechKernelOrderedLinearEquiv_symm_coe
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (x : LinearMap.ker ((orderedBaseCechComplex π M U).d 0 1).hom) :
    ((baseCechKernelOrderedLinearEquiv π M U).symm x).1 =
      (orderedToBaseCechAlternatingF π M U 0).hom x.1 := by
  rfl

/-- Algebraic base change preserves the degree-zero kernel equivalence between the native
and ordered base-linear Cech complexes. -/
noncomputable def baseCechKernelOrderedBaseChangeLinearEquiv
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (A : Type u) [CommRing A] [Algebra Γ(S, (⊤ : S.Opens)) A] :
    LinearMap.ker
        (((baseCechComplex π M U).d 0 1).hom.baseChange A) ≃ₗ[A]
      LinearMap.ker
        (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange A) := by
  let F := ModuleCat.extendScalars (algebraMap Γ(S, (⊤ : S.Opens)) A)
  let C := baseCechComplex π M U
  let D := orderedBaseCechComplex π M U
  let p := (F.mapHomologicalComplex (.up ℕ)).map
    (baseCechToOrdered π M U)
  let i := (F.mapHomologicalComplex (.up ℕ)).map
    (orderedToBaseCechAlternating π M U)
  have hpi : p.f 0 ≫ i.f 0 = 𝟙 _ := by
    change F.map (baseCechToOrderedF π M U 0) ≫
      F.map (orderedToBaseCechAlternatingF π M U 0) =
        𝟙 (F.obj ((baseCechComplex π M U).X 0))
    rw [← F.map_comp,
      baseCechToOrderedF_comp_orderedToBaseCechAlternatingF_zero,
      F.map_id]
  have hip : i.f 0 ≫ p.f 0 = 𝟙 _ := by
    change F.map (orderedToBaseCechAlternatingF π M U 0) ≫
      F.map (baseCechToOrderedF π M U 0) =
        𝟙 (F.obj ((orderedBaseCechComplex π M U).X 0))
    rw [← F.map_comp,
      orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
      F.map_id]
    rfl
  exact (ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv C A).trans
    ((HomologicalComplex.kernelZeroLinearEquivOfHom p i hpi hip).trans
      (ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv D A).symm)

/-- The inverse ordered/native base-changed Cech-kernel equivalence is induced by
the algebraic base change of the degree-zero alternating extension. -/
theorem baseCechKernelOrderedBaseChangeLinearEquiv_symm_coe
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (A : Type u) [CommRing A] [Algebra Γ(S, (⊤ : S.Opens)) A]
    (x : LinearMap.ker
      (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange A)) :
    ((baseCechKernelOrderedBaseChangeLinearEquiv π M U A).symm x).1 =
      ((orderedToBaseCechAlternatingF π M U 0).hom.baseChange A) x.1 := by
  let F := ModuleCat.extendScalars (algebraMap Γ(S, (⊤ : S.Opens)) A)
  let C := baseCechComplex π M U
  let D := orderedBaseCechComplex π M U
  let p := (F.mapHomologicalComplex (.up ℕ)).map
    (baseCechToOrdered π M U)
  let i := (F.mapHomologicalComplex (.up ℕ)).map
    (orderedToBaseCechAlternating π M U)
  have hpi : p.f 0 ≫ i.f 0 = 𝟙 _ := by
    change F.map (baseCechToOrderedF π M U 0) ≫
      F.map (orderedToBaseCechAlternatingF π M U 0) =
        𝟙 (F.obj ((baseCechComplex π M U).X 0))
    rw [← F.map_comp,
      baseCechToOrderedF_comp_orderedToBaseCechAlternatingF_zero,
      F.map_id]
  have hip : i.f 0 ≫ p.f 0 = 𝟙 _ := by
    change F.map (orderedToBaseCechAlternatingF π M U 0) ≫
      F.map (baseCechToOrderedF π M U 0) =
        𝟙 (F.obj ((orderedBaseCechComplex π M U).X 0))
    rw [← F.map_comp,
      orderedToBaseCechAlternatingF_comp_baseCechToOrderedF,
      F.map_id]
    rfl
  change ((ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv
      C A).symm
    ((HomologicalComplex.kernelZeroLinearEquivOfHom p i hpi hip).symm
      (ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv
        D A x))).1 = _
  rw [ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv_symm_coe]
  rw [HomologicalComplex.kernelZeroLinearEquivOfHom_symm_coe]
  rw [ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv_coe]
  apply (ModularCurves.moduleCatExtendScalarsObjLinearEquiv A (C.X 0)).injective
  calc
    _ = (i.f 0).hom
        (ModularCurves.moduleCatExtendScalarsObjLinearEquiv A (D.X 0) x.1) :=
      (ModularCurves.moduleCatExtendScalarsObjLinearEquiv A
        (C.X 0)).apply_symm_apply _
    _ = _ := by
      change
        ((ModuleCat.extendScalars
          (algebraMap Γ(S, (⊤ : S.Opens)) A)).map
            (orderedToBaseCechAlternatingF π M U 0)).hom
              (ModularCurves.moduleCatExtendScalarsObjLinearEquiv A
                ((orderedBaseCechComplex π M U).X 0) x.1) =
          ModularCurves.moduleCatExtendScalarsObjLinearEquiv A
            ((baseCechComplex π M U).X 0)
              (((orderedToBaseCechAlternatingF π M U 0).hom.baseChange A) x.1)
      exact (ModularCurves.moduleCatExtendScalarsObjLinearEquiv_baseChange A
        (orderedToBaseCechAlternatingF π M U 0) x.1).symm

/-- For an ordered open cover, global sections are the kernel of the first differential in the
ordered base-linear Cech complex. -/
noncomputable def baseSectionsIsoKernelOrderedBaseCechDifferential
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U) :
    baseSections π M ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (LinearMap.ker ((orderedBaseCechComplex π M U).d 0 1).hom) :=
  baseSectionsIsoKernelBaseCechDifferential π M U hU ≪≫
    (baseCechKernelOrderedLinearEquiv π M U).toModuleIso

private theorem compEqHom_apply {R : Type u} [CommRing R]
    {A B C : ModuleCat.{u} R} {p : A ⟶ B} {q : B ⟶ C} {r : A ⟶ C}
    (h : p ≫ q = r) (y : A) : q (p y) = r y := by
  have hy := ConcreteCategory.congr_hom h y
  rwa [ConcreteCategory.comp_apply] at hy

/-- **Componentwise extensionality for ordered Cech cochains.** Two cochains agree as soon as all
their components at strictly increasing indices agree. -/
theorem orderedBaseCechObject_ext
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {u v : (orderedBaseCechObject π M U n : Type u)}
    (h : ∀ i : OrderedCechIndex ι n,
      (Pi.π (fun j : OrderedCechIndex ι n => baseCechFactor π M U n j.1) i) u =
        (Pi.π (fun j : OrderedCechIndex ι n => baseCechFactor π M U n j.1) i) v) :
    u = v := by
  refine (ConcreteCategory.bijective_of_isIso
    (orderedBaseCechObjectIsoPi π M U n).hom).injective ?_
  funext i
  have hu := compEqHom_apply (orderedBaseCechObjectIsoPi_hom_comp_proj π M U n i) u
  have hv := compEqHom_apply (orderedBaseCechObjectIsoPi_hom_comp_proj π M U n i) v
  exact hu.trans ((h i).trans hv.symm)

/-- **Element description of the global-sections/ordered-kernel identification.** A global
section is sent to the ordered projection of its Cech augmentation, i.e. to the family of its
restrictions to the members of the cover. -/
theorem baseSectionsIsoKernelOrderedBaseCechDifferential_hom_coe
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (x : baseSections π M) :
    ((baseSectionsIsoKernelOrderedBaseCechDifferential π M U hU).hom x).1 =
      (baseCechToOrderedF π M U 0).hom
        ((baseCechAugmentation π M U) x) := by
  have hchain : (baseSectionsIsoKernelOrderedBaseCechDifferential π M U hU).hom x =
      baseCechKernelOrderedLinearEquiv π M U
        ((baseSectionsIsoKernelBaseCechDifferential π M U hU).hom x) := rfl
  rw [hchain, baseCechKernelOrderedLinearEquiv_coe]
  refine ConcreteCategory.congr_arg (baseCechToOrderedF π M U 0) ?_
  exact ConcreteCategory.congr_hom
    (baseSectionsIsoKernelBaseCechDifferential_hom_subtype π M U hU) x

/-- **Componentwise form of the previous lemma.** The component of the ordered degree-zero
cocycle attached to a global section at a strictly increasing index is the restriction of that
section to the corresponding Cech intersection. -/
theorem baseSectionsIsoKernelOrderedBaseCechDifferential_hom_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (x : baseSections π M) (i : OrderedCechIndex ι 0) :
    (Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1) i)
        ((baseSectionsIsoKernelOrderedBaseCechDifferential π M U hU).hom x).1 =
      (baseModulePresheaf π M).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i.1 k)) ≤
          (⊤ : X.Opens) from le_top)).op x := by
  refine (ConcreteCategory.congr_arg
    (Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor π M U 0 j.1) i)
    (baseSectionsIsoKernelOrderedBaseCechDifferential_hom_coe π M U hU x)).trans ?_
  refine (compEqHom_apply (baseCechToOrderedF_comp_π π M U 0 i)
    ((baseCechAugmentation π M U) x)).trans ?_
  exact compEqHom_apply (baseCechAugmentation_comp_π π M U i.1) x

end

end AlgebraicGeometry.Scheme.Modules
