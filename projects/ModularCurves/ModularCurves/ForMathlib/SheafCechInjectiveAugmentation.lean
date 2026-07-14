import ModularCurves.ForMathlib.SheafCechInjectiveBicomplex
import ModularCurves.ForMathlib.SheafDerivedGlobalSections
import ModularCurves.ForMathlib.TotalComplexUpNatVerticalEdge

/-!
# The Cech augmentation into an injective resolution

Apply the native Cech functor to the augmentation of the chosen injective
resolution and record the low-column exactness used by the vertical total edge.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

private abbrev sectionsAt (V : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  (CategoryTheory.sheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (Opposite.op V)

private noncomputable instance sectionsAt_preservesFiniteLimits (V : Opens X) :
    PreservesFiniteLimits (sectionsAt V) := by
  letI : PreservesFiniteLimits
      (CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  change PreservesFiniteLimits
    (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V))
  exact comp_preservesFiniteLimits _ _

private theorem injectiveResolution_augmentation_app_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V) ≫
      ((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V) = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h : (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 :=
    congrArg (fun f ↦ f.hom) I.ι_f_zero_comp_complex_d
  change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
  exact (congr_app h _).trans rfl

private theorem injectiveResolution_augmentation_app_exact
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (ShortComplex.mk
      (((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V))
      (injectiveResolution_augmentation_app_comp_d F V)).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit
    (I.kernelFork.mapIsLimit I.isLimitKernelFork (sectionsAt V)) ?_
  apply Fork.ext (Iso.refl _)

/-- The native Cech map induced by the augmentation into the chosen injective
resolution. -/
noncomputable def cechInjectiveResolutionAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) :
    (cechComplexFunctor U).obj F.obj ⟶
      (cechInjectiveResolutionBicomplex U F).X 0 :=
  (cechComplexFunctor U).map
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom

@[simp]
theorem cechInjectiveResolutionAugmentation_f
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p =
      ((cechComplexFunctor U).map
        ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom).f p :=
  rfl

@[reassoc]
theorem cechInjectiveResolutionAugmentation_f_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p ≫
      ((cechInjectiveResolutionBicomplex U F).d 0 1).f p = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h :
      (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 := by
    exact congrArg (fun f ↦ f.hom)
      (InjectiveResolution.ι_f_zero_comp_complex_d I)
  change Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) ≫
    Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.cocomplex.d 0 1).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) = 0
  rw [Limits.Pi.map_comp_map]
  refine Limits.Pi.hom_ext _ _ fun i ↦ ?_
  rw [Limits.Pi.map_π]
  have hi := congr_app h
    (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
  have hi' :
      (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) ≫
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) = 0 := by
    change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
    exact hi.trans rfl
  rw [hi', comp_zero, zero_comp]

noncomputable instance cechInjectiveResolutionAugmentation_f_mono
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    Mono ((cechInjectiveResolutionAugmentation U F).f p) := by
  change Mono (Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app
      (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))))
  infer_instance

/-- The augmented resolution column in every Cech degree is exact at resolution
degree zero. -/
theorem cechInjectiveResolutionAugmentation_exact
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (ShortComplex.mk
      ((cechInjectiveResolutionAugmentation U F).f p)
      (((cechInjectiveResolutionBicomplex U F).d 0 1).f p)
      (cechInjectiveResolutionAugmentation_f_comp_d U F p)).Exact := by
  let I := injectiveResolution (toSiteSheaf F)
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hy' :
      Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) y = 0 :=
    hy
  have preimage (i : Fin (p + 1) → ι) :
      ∃ x : F.obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))),
        (I.ι.f 0).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) x =
          Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y := by
    let V := ∏ᶜ fun k : Fin (p + 1) ↦ U (i k)
    have hyi :
        (I.cocomplex.d 0 1).hom.app (Opposite.op V)
          (Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (I.cocomplex.X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i y) = 0 := by
      have hmap := ConcreteCategory.congr_hom
        (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
          (I.cocomplex.d 0 1).hom.app
            (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) y
      calc
        _ = Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
              (I.cocomplex.X 1).obj.obj
                (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i
              (Limits.Pi.map (fun j : Fin (p + 1) → ι ↦
                (I.cocomplex.d 0 1).hom.app
                  (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) y) :=
          hmap.symm
        _ = 0 := by rw [hy', map_zero]
    exact ((ShortComplex.mk
      (((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app (Opposite.op V))
      (((injectiveResolution (toSiteSheaf F)).cocomplex.d 0 1).hom.app
        (Opposite.op V))
      (injectiveResolution_augmentation_app_comp_d F V)).ab_exact_iff.mp
        (injectiveResolution_augmentation_app_exact F V)) _ hyi
  choose x hx using preimage
  let x' := (cechCochainAddEquiv F.obj U p).symm x
  refine ⟨x', ?_⟩
  change Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) x' = y
  apply (cechCochainAddEquiv (I.cocomplex.X 0).obj U p).injective
  funext i
  rw [cechCochainAddEquiv_apply, cechCochainAddEquiv_apply]
  have hmap := ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i) x'
  have hx'i :
      Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
        (((CochainComplex.single₀
          (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u})).obj (toSiteSheaf F)).X 0).obj.obj
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i x' = x i := by
    change cechCochainAddEquiv F.obj U p x' i = x i
    simp [x']
  calc
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
          (Limits.Pi.π (fun j : Fin (p + 1) → ι ↦
            (((CochainComplex.single₀
              (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
                AddCommGrpCat.{u})).obj (toSiteSheaf F)).X 0).obj.obj
              (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (j k)))) i x') := by
        simpa only [ConcreteCategory.comp_apply] using hmap
    _ = (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) (x i) := by
        rw [hx'i]
    _ = _ := hx i

end

end TopCat.Sheaf
