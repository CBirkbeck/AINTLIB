import Mathlib.Algebra.Category.ModuleCat.Kernels
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SheafCechInjectiveComparison

/-!
# Global sections as the kernel of the base-linear Cech differential

For a scheme module over a base scheme, identify its module of global sections
with the kernel of the first differential in the base-linear Cech complex of an
open cover.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Global sections of a scheme module, retaining the action of global
functions on the base. -/
abbrev baseSections {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :=
  (baseModulePresheaf π M).obj (op (⊤ : X.Opens))

/-- An isomorphism of scheme modules induces an isomorphism on global sections,
retaining the action of global functions on the base. -/
noncomputable def baseSectionsMapIso
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (e : M ≅ N) :
    baseSections π M ≅ baseSections π N := by
  let eVal : M.1 ≅ N.1 :=
    { hom := e.hom.val
      inv := e.inv.val
      hom_inv_id := congrArg (fun q : M ⟶ M ↦ q.val) e.hom_inv_id
      inv_hom_id := congrArg (fun q : N ⟶ N ↦ q.val) e.inv_hom_id }
  exact (ModuleCat.restrictScalars π.appTop.hom).mapIso
    (((PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).mapIso eVal).app
        (op (⊤ : X.Opens)))

/-- The base-ring action on global sections agrees with the total-space action
through the structure morphism. -/
theorem baseSections_smul
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    (a : Γ(S, (⊤ : S.Opens))) (x : Γ(M, (⊤ : X.Opens))) :
    (show Γ(M, (⊤ : X.Opens)) from
      a • (show baseSections π M from x)) = π.appTop.hom a • x := by
  let B :=
    (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).obj M.1
  letI : Module ↑Γ(X, (⊤ : X.Opens))
      (B.obj (op (⊤ : X.Opens))) :=
    ModuleCat.isModule (B.obj (op (⊤ : X.Opens)))
  have hinner :
      (show B.obj (op (⊤ : X.Opens)) from
          a • (show baseSections π M from x)) =
        (X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to
              (op (⊤ : X.Opens)))).hom (π.appTop.hom a) • x := by
    rfl
  have htop :
      (initialOpOfTerminal isTerminalTop).to
          (op (⊤ : X.Opens)) = 𝟙 (op (⊤ : X.Opens)) :=
    Subsingleton.elim _ _
  rw [hinner, htop]
  simp

/-- Restriction of global sections to the degree-zero term of the base-linear
Cech complex. -/
noncomputable def baseCechAugmentation
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    baseSections π M ⟶ (baseCechComplex π M U).X 0 := by
  change (baseModulePresheaf π M).obj (op (⊤ : X.Opens)) ⟶
    ∏ᶜ fun i : Fin 1 → ι =>
      (baseModulePresheaf π M).obj
        (op (∏ᶜ fun k : Fin 1 => U (i k)))
  exact Pi.lift fun i =>
    (baseModulePresheaf π M).map
      (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op

/-- Forgetting the base action on global sections agrees with the global
sections object of the underlying additive sheaf. -/
noncomputable def baseSectionsForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    (baseModuleForget S).obj (baseSections π M) ≅
      TopCat.Sheaf.globalSectionsFunctor X |>.obj M.sheaf :=
  (baseModulePresheafForgetIso π M).app (op (⊤ : X.Opens)) ≪≫
    ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).app M.sheaf).symm

/-- Forgetting the base action in one degree of the Cech complex recovers the
corresponding native additive Cech term. -/
noncomputable def baseCechXForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseModuleForget S).obj ((baseCechComplex π M U).X n) ≅
      ((cechComplexFunctor U).obj M.sheaf.obj).X n :=
  (HomologicalComplex.eval AddCommGrpCat.{u} (.up ℕ) n).mapIso
    (baseCechComplexForgetIso π M U)

@[simp]
theorem baseCechXForgetIso_hom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechXForgetIso π M U n).hom =
      (baseCechComplexForgetIso π M U).hom.f n :=
  rfl

/-- The degreewise comparison with the native Cech complex is componentwise
the identity on the underlying sections. -/
theorem baseCechXForgetIso_hom_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : (baseCechComplex π M U).X n)
    (i : Fin (n + 1) → ι) :
    cechCochainAddEquiv M.sheaf.obj U n
        ((baseCechXForgetIso π M U n).hom x) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
        (baseModulePresheaf π M).obj
          (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i x := by
  let V := (FormalCoproduct.mk _ U).cech.rightOp.obj
    (SimplexCategory.mk n)
  have h := ConcreteCategory.congr_hom
    (evalOpForgetIso_hom_π Γ(S, (⊤ : S.Opens))
      (baseModulePresheaf π M) V i) x
  simp [baseCechXForgetIso, baseCechComplexForgetIso,
    baseCechCosimplicialIso]
  let y := (evalOpForgetIso Γ(S, (⊤ : S.Opens))
    (baseModulePresheaf π M)).hom.app V x
  have hmap := Pi.map_π_apply
    (fun j => (baseModulePresheafForgetIso π M).hom.app
      (op (V.unop.obj j))) i y
  let yi := Pi.π (fun j => (baseModuleForget S).obj
    ((baseModulePresheaf π M).obj (op (V.unop.obj j)))) i y
  have hforget :
      (baseModulePresheafForgetIso π M).hom.app
          (op (V.unop.obj i)) yi = yi := rfl
  exact hmap.trans (hforget.trans h)

/-- The base-linear Cech augmentation becomes the native global-sections
augmentation after forgetting the base action. -/
theorem baseCechAugmentation_forget
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (baseModuleForget S).map (baseCechAugmentation π M U) ≫
        (baseCechXForgetIso π M U 0).hom =
      (baseSectionsForgetIso π M).hom ≫
        TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (cechCochainAddEquiv M.sheaf.obj U 0).injective
  funext i
  simp only [ConcreteCategory.comp_apply, baseCechXForgetIso_hom_apply]
  rw [TopCat.Sheaf.cechGlobalSectionsAugmentation_apply]
  let eΓ := (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).app M.sheaf
  let r := (homOfLE (show
    (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op
  have hleft := Pi.lift_π_apply
    (fun j : Fin 1 → ι =>
      (baseModulePresheaf π M).map
        (homOfLE (show
          (∏ᶜ fun k : Fin 1 => U (j k)) ≤ ⊤ from le_top)).op)
    i x
  let x₀ := (baseModulePresheafForgetIso π M).hom.app
    (op (⊤ : X.Opens)) x
  have hcancel := ConcreteCategory.congr_hom eΓ.inv_hom_id x₀
  have hx₀ : x₀ = x := rfl
  have hsource := hcancel.trans hx₀
  change _ = M.presheaf.map r (eΓ.hom (eΓ.inv x₀))
  calc
    _ = M.presheaf.map r x := by
      change (Pi.π (fun j : Fin 1 → ι =>
          (baseModulePresheaf π M).obj
            (op (∏ᶜ fun k : Fin 1 => U (j k)))) i).hom
          ((Pi.lift (fun j : Fin 1 → ι =>
            (baseModulePresheaf π M).map
              (homOfLE (show
                (∏ᶜ fun k : Fin 1 => U (j k)) ≤ ⊤ from le_top)).op)).hom x) =
        ((baseModulePresheaf π M).map r).hom x
      exact hleft
    _ = M.presheaf.map r (eΓ.hom (eΓ.inv x₀)) :=
      (congrArg (M.presheaf.map r) hsource).symm

/-- The base-linear Cech augmentation lands in the kernel of the first
differential. -/
theorem baseCechAugmentation_comp_d
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    baseCechAugmentation π M U ≫ (baseCechComplex π M U).d 0 1 = 0 := by
  apply (baseModuleForget S).map_injective
  apply (cancel_mono (baseCechXForgetIso π M U 1).hom).1
  rw [Functor.map_comp, Functor.map_zero, zero_comp]
  let hcomm := (baseCechComplexForgetIso π M U).hom.comm 0 1
  let haug := baseCechAugmentation_forget π M U
  calc
    _ = (baseModuleForget S).map (baseCechAugmentation π M U) ≫
        ((baseCechComplexForgetIso π M U).hom.f 0 ≫
          ((cechComplexFunctor U).obj M.sheaf.obj).d 0 1) := by
      exact congrArg (fun q =>
        (baseModuleForget S).map (baseCechAugmentation π M U) ≫ q)
        hcomm.symm
    _ = ((baseModuleForget S).map (baseCechAugmentation π M U) ≫
          (baseCechXForgetIso π M U 0).hom) ≫
        ((cechComplexFunctor U).obj M.sheaf.obj).d 0 1 := by
      rw [baseCechXForgetIso_hom]
      exact (Category.assoc
        ((baseModuleForget S).map (baseCechAugmentation π M U))
        ((baseCechComplexForgetIso π M U).hom.f 0)
        (((cechComplexFunctor U).obj M.sheaf.obj).d 0 1)).symm
    _ = ((baseSectionsForgetIso π M).hom ≫
          TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U) ≫
        ((cechComplexFunctor U).obj M.sheaf.obj).d 0 1 := by
      rw [haug]
    _ = (baseSectionsForgetIso π M).hom ≫
        (TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U ≫
          ((cechComplexFunctor U).obj M.sheaf.obj).d 0 1) := by
      rw [Category.assoc]
    _ = 0 := by
      rw [TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d, comp_zero]

/-- The first two terms of the base-linear Cech complex, augmented by global
sections. -/
noncomputable def baseCechAugmentedShortComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    ShortComplex (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) :=
  ShortComplex.mk (baseCechAugmentation π M U)
    ((baseCechComplex π M U).d 0 1)
    (baseCechAugmentation_comp_d π M U)

/-- After forgetting the base action, the augmented base-linear short complex
is the native Cech short complex augmented by global sections. -/
noncomputable def baseCechAugmentedShortComplexForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (baseCechAugmentedShortComplex π M U).map (baseModuleForget S) ≅
      TopCat.Sheaf.cechGlobalSectionsNativeShortComplex U M.sheaf :=
  ShortComplex.isoMk (baseSectionsForgetIso π M)
    (baseCechXForgetIso π M U 0) (baseCechXForgetIso π M U 1)
    (baseCechAugmentation_forget π M U).symm
    ((baseCechComplexForgetIso π M U).hom.comm 0 1)

/-- The base-linear Cech short complex augmented by global sections is exact
for a genuine open cover. -/
theorem baseCechAugmentedShortComplex_exact
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    (baseCechAugmentedShortComplex π M U).Exact := by
  apply (ShortComplex.exact_iff_exact_map_forget₂
    (S := baseCechAugmentedShortComplex π M U)).mpr
  exact ShortComplex.exact_of_iso
    (baseCechAugmentedShortComplexForgetIso π M U).symm
    (TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U M.sheaf hU)

/-- Restriction of global sections into Cech degree zero is monic for a
genuine open cover. -/
theorem baseCechAugmentation_mono
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    Mono (baseCechAugmentation π M U) := by
  letI : Mono (TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U) :=
    TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U M.sheaf hU
  letI : Mono ((baseSectionsForgetIso π M).hom ≫
      TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U) := inferInstance
  have hcomp : Mono ((baseModuleForget S).map
      (baseCechAugmentation π M U) ≫
        (baseCechXForgetIso π M U 0).hom) := by
    rw [baseCechAugmentation_forget]
    infer_instance
  letI : Mono ((baseModuleForget S).map
      (baseCechAugmentation π M U) ≫
        (baseCechXForgetIso π M U 0).hom) := hcomp
  have hmap : Mono ((baseModuleForget S).map
      (baseCechAugmentation π M U)) :=
    mono_of_mono_fac (show
      (baseModuleForget S).map (baseCechAugmentation π M U) ≫
          (baseCechXForgetIso π M U 0).hom =
        (baseModuleForget S).map (baseCechAugmentation π M U) ≫
          (baseCechXForgetIso π M U 0).hom from rfl)
  exact Functor.mono_of_mono_map (baseModuleForget S) hmap

private noncomputable def shortComplexLeftKernelIso
    {R : Type u} [CommRing R] (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.Exact) [Mono T.f] :
    T.X₁ ≅ ModuleCat.of R (LinearMap.ker T.g.hom) :=
  (limit.isoLimitCone ⟨_, hT.fIsKernel⟩).symm ≪≫
    ModuleCat.kernelIsoKer T.g

@[reassoc]
private theorem shortComplexLeftKernelIso_hom_subtype
    {R : Type u} [CommRing R] (T : ShortComplex (ModuleCat.{u} R))
    (hT : T.Exact) [Mono T.f] :
    (shortComplexLeftKernelIso T hT).hom ≫
        ModuleCat.ofHom (LinearMap.ker T.g.hom).subtype = T.f := by
  let t : LimitCone (parallelPair T.g 0) := ⟨_, hT.fIsKernel⟩
  change ((limit.isoLimitCone t).symm ≪≫
      ModuleCat.kernelIsoKer T.g).hom ≫
        ModuleCat.ofHom (LinearMap.ker T.g.hom).subtype = T.f
  rw [Iso.trans_hom, Category.assoc,
    ModuleCat.kernelIsoKer_hom_ker_subtype]
  exact limit.isoLimitCone_inv_π t WalkingParallelPair.zero

/-- For an open cover, the module of global sections is the linear kernel of
the first base-linear Cech differential. -/
noncomputable def baseSectionsIsoKernelBaseCechDifferential
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    baseSections π M ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (LinearMap.ker ((baseCechComplex π M U).d 0 1).hom) := by
  let T := baseCechAugmentedShortComplex π M U
  letI : Mono T.f := baseCechAugmentation_mono π M U hU
  let hT : T.Exact := baseCechAugmentedShortComplex_exact π M U hU
  exact shortComplexLeftKernelIso T hT

/-- The global-sections-to-kernel isomorphism followed by the kernel inclusion
is the Cech augmentation. -/
@[reassoc]
theorem baseSectionsIsoKernelBaseCechDifferential_hom_subtype
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    (baseSectionsIsoKernelBaseCechDifferential π M U hU).hom ≫
        ModuleCat.ofHom
          (LinearMap.ker ((baseCechComplex π M U).d 0 1).hom).subtype =
      baseCechAugmentation π M U := by
  let T := baseCechAugmentedShortComplex π M U
  letI : Mono T.f := baseCechAugmentation_mono π M U hU
  let hT : T.Exact := baseCechAugmentedShortComplex_exact π M U hU
  change (shortComplexLeftKernelIso T hT).hom ≫
      ModuleCat.ofHom (LinearMap.ker T.g.hom).subtype = T.f
  exact shortComplexLeftKernelIso_hom_subtype T hT

end

end AlgebraicGeometry.Scheme.Modules
