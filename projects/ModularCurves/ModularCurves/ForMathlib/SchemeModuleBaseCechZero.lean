import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SheafCechInjectiveComparison
import ModularCurves.ForMathlib.SheafCohomologyExact

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

/-- A morphism of scheme modules induces a morphism on global sections,
retaining the action of global functions on the base. -/
noncomputable def baseSectionsMap
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N) :
    baseSections π M ⟶ baseSections π N :=
  (ModuleCat.restrictScalars π.appTop.hom).map
    (((PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).map f.val).app
        (op (⊤ : X.Opens)))

/-- Global sections of a composite is the composite of global sections. -/
@[reassoc]
theorem baseSectionsMap_comp
    {X S : Scheme.{u}} (π : X ⟶ S) {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    baseSectionsMap π (f ≫ g) = baseSectionsMap π f ≫ baseSectionsMap π g := by
  show (ModuleCat.restrictScalars π.appTop.hom).map
      (((PresheafOfModules.forgetToPresheafModuleCat
        (op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).map (f ≫ g).val).app
          (op (⊤ : X.Opens))) = _
  rw [show (f ≫ g).val = f.val ≫ g.val from rfl, Functor.map_comp]
  rfl

/-- If the source of a monomorphism has vanishing first cohomology, then
global sections of its target surject onto global sections of its cokernel. -/
theorem baseSectionsMap_cokernel_surjective_of_subsingleton_H_one
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    [Mono f] [Subsingleton (CategoryTheory.Sheaf.H M.sheaf 1)] :
    Function.Surjective (baseSectionsMap π (cokernel.π f)) := by
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
  let Ts := T.map (toSheaf X)
  have hTs : Ts.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hT (toSheaf X)
  letI : Subsingleton (Ts.X₁.H 1) := by
    change Subsingleton (M.sheaf.H 1)
    infer_instance
  exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    hTs isTerminalTop

/-- Global sections are exact at the target of a monomorphism and the source
of its cokernel map. -/
theorem baseSectionsMap_exact_cokernel
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    [Mono f] :
    Function.Exact (baseSectionsMap π f).hom
      (baseSectionsMap π (cokernel.π f)).hom := by
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
  let Ts := T.map (toSheaf X)
  have hTs : Ts.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hT (toSheaf X)
  rw [LinearMap.exact_iff]
  ext y
  constructor
  · intro hy
    have hy' : Ts.g.hom.app (op (⊤ : X.Opens)) y = 0 := by
      change (baseSectionsMap π (cokernel.π f)).hom y = 0
      exact LinearMap.mem_ker.mp hy
    obtain ⟨x, hx⟩ := CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₂
      (hT := isTerminalTop) (hS := hTs) y hy'
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change ((cokernel.π f).app (⊤ : X.Opens)) (f.app (⊤ : X.Opens) x) = 0
    have hzero : f ≫ cokernel.π f = 0 := cokernel.condition f
    exact congrArg (fun q : M ⟶ cokernel f => q.app (⊤ : X.Opens) x) hzero

/-- A monomorphism of scheme modules induces a monomorphism on global
sections over the base ring. -/
theorem baseSectionsMap_mono
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    (hf : Mono f) : Mono (baseSectionsMap π f) := by
  letI := hf
  let F := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  letI : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits
      X.ringCatSheaf (op (⊤ : X.Opens))
  letI : PreservesLimitsOfShape WalkingCospan F :=
    PreservesFiniteLimits.preservesFiniteLimits WalkingCospan
  letI : F.PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape F
  haveI : Mono (F.map f) := @Functor.map_mono _ _ _ _ F
    inferInstance _ _ f hf
  apply (ModuleCat.mono_iff_injective (baseSectionsMap π f)).mpr
  exact (ModuleCat.mono_iff_injective (F.map f)).mp inferInstance

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

@[simp]
theorem baseSectionsMapIso_hom_apply
    {X S : Scheme.{u}} (f : X ⟶ S) {M N : X.Modules} (e : M ≅ N)
    (x : baseSections f M) :
    (baseSectionsMapIso f e).hom x = e.hom.val.app (.op ⊤) x := by
  rfl

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

/-- Restricting scalars on base-linear global sections agrees with composing
the structural morphism to the base. -/
noncomputable def baseSectionsCompIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules) :
    (ModuleCat.restrictScalars g.appTop.hom).obj (baseSections f M) ≅
      baseSections (f ≫ g) M := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext x
  let x' : Γ(M, (⊤ : X.Opens)) := x
  have hleft := baseSections_smul f M (g.appTop.hom r) x'
  have hright := baseSections_smul (f ≫ g) M r x'
  rw [Scheme.Hom.comp_appTop] at hright
  exact hleft.trans hright.symm

/-- The composite-base isomorphism is the identity on underlying sections. -/
@[simp]
theorem baseSectionsCompIso_hom_apply
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (M : X.Modules)
    (m : baseSections f M) :
    (baseSectionsCompIso f g M).hom m = m := by
  rfl

/-- Base-linear global sections agree with top sections equipped with the
directly restricted scalar action. -/
noncomputable def baseSectionsIsoRestrictScalarsTop
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) :
    baseSections π M ≅
      (ModuleCat.restrictScalars π.appTop.hom).obj
        (ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens))) := by
  let D := (ModuleCat.restrictScalars π.appTop.hom).obj
    (ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens)))
  let eAdd : (baseSections π M : Type u) ≃+ (D : Type u) := AddEquiv.refl _
  let eLin : (baseSections π M : Type u) ≃ₗ[Γ(S, (⊤ : S.Opens))]
      (D : Type u) :=
    { eAdd with
      map_smul' := by
        intro r x
        change (show Γ(M, (⊤ : X.Opens)) from r • x) =
          π.appTop.hom r • (show Γ(M, (⊤ : X.Opens)) from x)
        exact baseSections_smul π M r x }
  exact eLin.toModuleIso

/-- A bijective restriction map identifies base-linear global sections with
top sections of the module restricted to that open. -/
noncomputable def baseSectionsRestrictIsoOfBijective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (hbij : Function.Bijective fun s : Γ(M, (⊤ : X.Opens)) ↦
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op s) :
    baseSections π M ≅
      baseSections (U.ι ≫ π) (M.restrict U.ι) := by
  let res := (baseModulePresheaf π M).map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
  have hres : Function.Bijective res.hom := by
    change Function.Bijective fun s : Γ(M, (⊤ : X.Opens)) ↦
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op s
    exact hbij
  exact (LinearEquiv.ofBijective res.hom hres).toModuleIso ≪≫
    baseModulePresheafRestrictIso π M U ≪≫
      (baseSectionsIsoRestrictScalarsTop
        (U.ι ≫ π) (M.restrict U.ι)).symm

@[simp]
theorem baseSectionsRestrictIsoOfBijective_hom_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (hbij : Function.Bijective fun s : Γ(M, (⊤ : X.Opens)) ↦
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op s)
    (x : baseSections f M) :
    (baseSectionsRestrictIsoOfBijective f M U hbij).hom x =
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op
          (M.presheaf.map
            (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op x)) := by
  rfl

/-- The base-linear global sections of the pushed-forward structure module
along a section form the regular module of global functions on the base. -/
noncomputable def baseSectionsPushforwardUnitIsoOfSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) :
    baseSections g ((pushforward f).obj
      (_root_.SheafOfModules.unit X.ringCatSheaf)) ≅
      ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(X, (⊤ : X.Opens)) := by
  let eAdd :
      (baseSections g ((pushforward f).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)) : Type u) ≃+
        Γ(X, (⊤ : X.Opens)) := AddEquiv.refl _
  let eLin :
      (baseSections g ((pushforward f).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)) : Type u) ≃ₗ[
          Γ(X, (⊤ : X.Opens))] Γ(X, (⊤ : X.Opens)) :=
    { eAdd with
      map_smul' := by
        intro r x
        change (show Γ(X, (⊤ : X.Opens)) from r • x) =
          r * (show Γ(X, (⊤ : X.Opens)) from x)
        have hbase : (show Γ(X, (⊤ : X.Opens)) from r • x) =
            f.appTop.hom (g.appTop.hom r) *
              (show Γ(X, (⊤ : X.Opens)) from x) := by
          exact baseSections_smul g
            ((pushforward f).obj
              (_root_.SheafOfModules.unit X.ringCatSheaf)) r x
        have happ : (f ≫ g).appTop = Scheme.Hom.appTop (𝟙 X) :=
          congrArg Scheme.Hom.appTop h
        rw [Scheme.Hom.comp_appTop] at happ
        have hr : f.appTop.hom (g.appTop.hom r) = r := by
          have hx := ConcreteCategory.congr_hom happ r
          simpa using hx
        exact hbase.trans (by rw [hr]) }
  exact eLin.toModuleIso

private theorem restrictPushforwardUnit_baseScalar
    {C S : Scheme.{u}} (π : C ⟶ S) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤)
    (htop : (⊤ : S.Opens) =
      z ⁻¹ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    (r : Γ(S, (⊤ : S.Opens))) :
    S.presheaf.map (eqToHom htop).op
      (z.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
        ((U.ι.appIso (⊤ : U.toScheme.Opens)).inv
          ((U.ι ≫ π).appTop.hom r))) = r := by
  have hzrange : Set.range ⇑z ⊆ Set.range ⇑U.ι := by
    rintro _ ⟨s, rfl⟩
    have hs : s ∈ z ⁻¹ᵁ U := by
      rw [hU]
      trivial
    exact ⟨⟨z s, hs⟩, rfl⟩
  let zU : S ⟶ U.toScheme := IsOpenImmersion.lift U.ι z hzrange
  have hzU : zU ≫ (U.ι ≫ π) = 𝟙 S := by
    rw [← Category.assoc, show zU ≫ U.ι = z by
      exact IsOpenImmersion.lift_fac U.ι z hzrange, hz]
  have hlift : S.presheaf.map (eqToHom htop).op
      (z.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
        ((U.ι.appIso (⊤ : U.toScheme.Opens)).inv
          ((U.ι ≫ π).appTop.hom r))) =
        zU.appTop ((U.ι ≫ π).appTop.hom r) := by
    convert ConcreteCategory.congr_hom
      (IsOpenImmersion.lift_app U.ι z hzrange
        (⊤ : U.toScheme.Opens)).symm
      ((U.ι ≫ π).appTop.hom r) using 1
    · simp
    · rfl
    · rfl
  rw [hlift]
  have happ : (zU ≫ (U.ι ≫ π)).appTop =
      Scheme.Hom.appTop (𝟙 S) :=
    congrArg Scheme.Hom.appTop hzU
  rw [Scheme.Hom.comp_appTop] at happ
  have hr := ConcreteCategory.congr_hom happ r
  simpa using hr

/-- If a section lies in an open neighborhood, the base-linear top sections
of its restricted pushed-forward structure module form the regular base
module. -/
noncomputable def baseSectionsRestrictPushforwardUnitIsoOfSection
    {C S : Scheme.{u}} (π : C ⟶ S) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤) :
    baseSections (U.ι ≫ π)
        ((restrictFunctor U.ι).obj ((pushforward z).obj
          (_root_.SheafOfModules.unit S.ringCatSheaf))) ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens)) := by
  let OS : S.Modules := _root_.SheafOfModules.unit S.ringCatSheaf
  let N := (pushforward z).obj OS
  have htop : (⊤ : S.Opens) =
      z ⁻¹ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
    rw [U.ι_image_top, hU]
  let eAdd : Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens)) ≅
      Γ(OS, (⊤ : S.Opens)) :=
    N.restrictAppIso U.ι (⊤ : U.toScheme.Opens) ≪≫
      OS.presheaf.mapIso (eqToIso htop).op
  let eMap (q : Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens))) :
      Γ(OS, (⊤ : S.Opens)) :=
    OS.presheaf.map (eqToHom htop).op
      ((N.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).hom q)
  have heAdd (q : Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens))) :
      eAdd.hom q = eMap q := rfl
  let eLin :
      (baseSections (U.ι ≫ π)
        ((restrictFunctor U.ι).obj ((pushforward z).obj OS)) :
          Type u) ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens)) :=
    { AddEquiv.ofBijective eAdd.hom.hom
        (ConcreteCategory.bijective_of_isIso eAdd.hom) with
      map_smul' := by
        intro r x
        let x' : Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens)) := x
        have hbase := baseSections_smul (U.ι ≫ π) (N.restrict U.ι) r x'
        change (show Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens)) from r • x) =
          (U.ι ≫ π).appTop.hom r • x' at hbase
        change (show Γ(S, (⊤ : S.Opens)) from eAdd.hom (r • x)) =
          r * (show Γ(S, (⊤ : S.Opens)) from eAdd.hom x')
        calc
          (show Γ(S, (⊤ : S.Opens)) from eAdd.hom (r • x)) =
              (show Γ(S, (⊤ : S.Opens)) from
                eAdd.hom ((U.ι ≫ π).appTop.hom r • x')) := by
            exact congrArg
              (fun q : Γ(N.restrict U.ι, (⊤ : U.toScheme.Opens)) ↦
                (show Γ(S, (⊤ : S.Opens)) from eAdd.hom q)) hbase
          _ = r * (show Γ(S, (⊤ : S.Opens)) from eAdd.hom x') := by
            calc
              (show Γ(S, (⊤ : S.Opens)) from
                  eAdd.hom ((U.ι ≫ π).appTop.hom r • x')) =
                  (show Γ(S, (⊤ : S.Opens)) from
                    eMap ((U.ι ≫ π).appTop.hom r • x')) := by
                exact congrArg
                  (fun q : Γ(OS, (⊤ : S.Opens)) ↦
                    (show Γ(S, (⊤ : S.Opens)) from q))
                  (heAdd _)
              _ = r * (show Γ(S, (⊤ : S.Opens)) from eMap x') := by
                dsimp only [eMap]
                rw [smul_restrictAppIso_hom_apply]
                change S.presheaf.map (eqToHom htop).op
                    (z.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
                        ((U.ι.appIso (⊤ : U.toScheme.Opens)).inv
                          ((U.ι ≫ π).appTop.hom r)) *
                      (show Γ(S, z ⁻¹ᵁ
                        (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) from
                          (N.restrictAppIso U.ι
                            (⊤ : U.toScheme.Opens)).hom x')) =
                  r * S.presheaf.map (eqToHom htop).op
                    (show Γ(S, z ⁻¹ᵁ
                      (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) from
                        (N.restrictAppIso U.ι
                          (⊤ : U.toScheme.Opens)).hom x')
                rw [map_mul]
                rw [restrictPushforwardUnit_baseScalar π z hz U hU htop]
              _ = r * (show Γ(S, (⊤ : S.Opens)) from eAdd.hom x') := by
                exact congrArg
                  (fun q : Γ(OS, (⊤ : S.Opens)) ↦
                    r * (show Γ(S, (⊤ : S.Opens)) from q))
                  (heAdd x').symm }
  exact eLin.toModuleIso

@[simp]
theorem baseSectionsRestrictPushforwardUnitIsoOfSection_hom_apply
    {C S : Scheme.{u}} (π : C ⟶ S) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤)
    (x : baseSections (U.ι ≫ π)
      ((restrictFunctor U.ι).obj ((pushforward z).obj
        (_root_.SheafOfModules.unit S.ringCatSheaf)))) :
    let OS : S.Modules := _root_.SheafOfModules.unit S.ringCatSheaf
    let N := (pushforward z).obj OS
    let htop : (⊤ : S.Opens) =
        z ⁻¹ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
      rw [U.ι_image_top, hU]
    (baseSectionsRestrictPushforwardUnitIsoOfSection
      π z hz U hU).hom x =
      OS.presheaf.map (eqToHom htop).op
        ((N.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).hom x) := by
  rfl

/-- The restricted structure-sheaf map, evaluated through the canonical
section-pushforward isomorphism, is pullback of the corresponding local
function along the section. -/
theorem baseSectionsRestrictPushforwardUnitIsoOfSection_hom_unitToPushforwardObjUnit
    {C S : Scheme.{u}} (π : C ⟶ S) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤)
    (x : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) :
    let F := restrictFunctor U.ι
    let eUnit := restrictUnitIso U.ι
    let htop : (⊤ : S.Opens) =
        z ⁻¹ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
      rw [U.ι_image_top, hU]
    (baseSectionsRestrictPushforwardUnitIsoOfSection
      π z hz U hU).hom
        (baseSectionsMap (U.ι ≫ π)
          (F.map (_root_.SheafOfModules.unitToPushforwardObjUnit
            z.toRingCatSheafHom))
          (eUnit.inv.val.app (.op ⊤) x)) =
      S.presheaf.map (eqToHom htop).op
        (z.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
          ((U.ι.appIso (⊤ : U.toScheme.Opens)).inv x)) := by
  let F := restrictFunctor U.ι
  let eUnit := restrictUnitIso U.ι
  let OS : S.Modules := _root_.SheafOfModules.unit S.ringCatSheaf
  let N := (pushforward z).obj OS
  let htop : (⊤ : S.Opens) =
      z ⁻¹ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
    rw [U.ι_image_top, hU]
  dsimp only
  let y := baseSectionsMap (U.ι ≫ π)
    (F.map (_root_.SheafOfModules.unitToPushforwardObjUnit
      z.toRingCatSheafHom)) (eUnit.inv.val.app (.op ⊤) x)
  have hpush :
      (baseSectionsRestrictPushforwardUnitIsoOfSection
        π z hz U hU).hom y =
        S.presheaf.map (eqToHom htop).op
          ((N.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).hom y) := by
    exact baseSectionsRestrictPushforwardUnitIsoOfSection_hom_apply
      π z hz U hU y
  refine hpush.trans ?_
  rfl

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

/-- A component of the degree-zero Cech augmentation is restriction from the
top open to the corresponding one-fold intersection. -/
@[reassoc]
theorem baseCechAugmentation_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (i : Fin 1 → ι) :
    baseCechAugmentation π M U ≫
        Pi.π (fun j : Fin 1 → ι =>
          (baseModulePresheaf π M).obj
            (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      (baseModulePresheaf π M).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op := by
  exact Pi.lift_π _ i

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
