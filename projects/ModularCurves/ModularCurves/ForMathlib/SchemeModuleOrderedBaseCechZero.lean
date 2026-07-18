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

end

end AlgebraicGeometry.Scheme.Modules
