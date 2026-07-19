import ModularCurves.EllipticCurve.PoleSheafCechHOne
import ModularCurves.EllipticCurve.PoleSheafFibreHOne
import ModularCurves.EllipticCurve.PoleSheafFibreSections
import ModularCurves.ForMathlib.AffineModuleCechBaseChange
import ModularCurves.ForMathlib.CochainComplexKernel
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero

/-!
# Base-linear Cech comparison for pole sheaves

Retain the affine-base module structure on the Cech model computing degree-one
cohomology of the pole line bundles on a smooth proper pointed relative curve.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

private theorem isSeparated_fiberToSpecResidueField
    {E S : Scheme.{u}} (π : E ⟶ S) [IsSeparated π] (s : S) :
    IsSeparated (π.fiberToSpecResidueField s) := by
  change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
  exact AlgebraicGeometry.IsSeparated.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π (S.fromSpecResidueField s))
    (show IsSeparated π from inferInstance)

/-- On an affine open cover, forgetting the base-module structure on degree-one
Cech homology of `O(n[0])` recovers its genuine sheaf cohomology. -/
noncomputable def sectionPoleSheafPower_baseCechHomologyOneIso
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) {ι : Type u} (U : ι → E.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    (Scheme.Modules.baseModuleForget S).obj
        ((Scheme.Modules.baseCechComplex π
          (sectionPoleSheafPower π z hz n) U).homology 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology E) 1).obj
          (sectionPoleSheafPower π z hz n).sheaf := by
  letI : (sectionPoleSheafPower π z hz n).IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm z hz n
  exact Scheme.Modules.baseCechHomologyOneIso_of_affine_openCover
    π (sectionPoleSheafPower π z hz n) U hU hUaff

/-- A smooth proper pointed curve over an affine base admits a finite affine
cover whose base-linear Cech homology computes `H¹(O(n[0]))` after forgetting
the base-module structure. -/
theorem exists_sectionPoleSheafPower_finiteAffineBaseCechComparison
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Nonempty ((Scheme.Modules.baseModuleForget S).obj
            ((Scheme.Modules.baseCechComplex π
              (sectionPoleSheafPower π z hz n) U).homology 1) ≅
          (CategoryTheory.Sheaf.functorH
            (Opens.grothendieckTopology E) 1).obj
              (sectionPoleSheafPower π z hz n).sheaf) := by
  obtain ⟨ι, hι, U, hU, hUaff, _⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  exact ⟨ι, hι, U, hU, hUaff,
    ⟨sectionPoleSheafPower_baseCechHomologyOneIso
      hsm z hz n U hU hUaff⟩⟩

/-- The pole-filtration map on global sections, retaining the affine-base
module structure. -/
noncomputable def sectionPoleSheafPower_baseSectionsLEHom
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) {n m : ℕ} (h : n ≤ m) :
    Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n) ⟶
      Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m) :=
  Scheme.Modules.baseSectionsMap π (sectionPoleSheafLEHom π z hz h)

/-- Pole-filtration maps are injective on global sections over the affine
base ring. -/
theorem sectionPoleSheafPower_baseSectionsLEHom_mono
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) {n m : ℕ} (h : n ≤ m) :
    Mono (sectionPoleSheafPower_baseSectionsLEHom z hz h) :=
  Scheme.Modules.baseSectionsMap_mono π
    (sectionPoleSheafLEHom π z hz h)
    (sectionPoleSheafLEHom_mono hsm z hz h)

/-- Global sections of `O(n[0])` are the degree-zero kernel of its ordered base-linear Cech
complex. -/
noncomputable def sectionPoleSheafPower_baseSectionsIsoKernelOrderedBaseCechDifferential
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    {ι : Type u} [LinearOrder ι] (U : ι → E.Opens) (hU : IsOpenCover U) :
    Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n) ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (LinearMap.ker ((Scheme.Modules.orderedBaseCechComplex π
          (sectionPoleSheafPower π z hz n) U).d 0 1).hom) :=
  Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
    π (sectionPoleSheafPower π z hz n) U hU

/-- Global sections of a residue-fibre pole sheaf are linearly equivalent to
the degree-zero kernel of any base-linear Cech complex computing them. -/
noncomputable def FibrewiseElliptic.sectionPoleSheafPower_fiberSectionsEquivBaseCechKernel
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (s : S) {n : ℕ} {ι : Type u}
    (U : ι → (π.fiber s).Opens) (hU : IsOpenCover U) :
    letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
      isSeparated_fiberToSpecResidueField π s
    let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
    let C := Scheme.Modules.baseCechComplex
      (π.fiberToSpecResidueField s) M U
    letI : Module ↑(S.residueField s) Γ(M, (⊤ : (π.fiber s).Opens)) :=
      Module.compHom _
        (Scheme.Modules.baseScalarHom (π.fiberToSpecResidueField s))
    letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
      Module.compHom _
        (Scheme.ΓSpecIso (S.residueField s)).inv.hom
    Γ(M, (⊤ : (π.fiber s).Opens)) ≃ₗ[↑(S.residueField s)]
      LinearMap.ker (C.d 0 1).hom := by
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  let C := Scheme.Modules.baseCechComplex
    (π.fiberToSpecResidueField s) M U
  letI : Module ↑(S.residueField s) Γ(M, (⊤ : (π.fiber s).Opens)) :=
    Module.compHom _
      (Scheme.Modules.baseScalarHom (π.fiberToSpecResidueField s))
  letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
    Module.compHom _
      (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  let e := Scheme.Modules.baseSectionsIsoKernelBaseCechDifferential
    (π.fiberToSpecResidueField s) M U hU
  exact
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => by
        change e.inv.hom (e.hom.hom x) = x
        exact e.toLinearEquiv.left_inv x
      right_inv := fun x => by
        change e.hom.hom (e.inv.hom x) = x
        exact e.toLinearEquiv.right_inv x
      map_add' := fun x y => e.hom.hom.map_add x y
      map_smul' := fun r x => by
        have hx :
            (show Scheme.Modules.baseSections
                (π.fiberToSpecResidueField s) M from r • x) =
              (Scheme.ΓSpecIso (S.residueField s)).inv.hom r •
                (show Scheme.Modules.baseSections
                  (π.fiberToSpecResidueField s) M from x) := by
          let B :=
            (PresheafOfModules.forgetToPresheafModuleCat
              (Opposite.op (⊤ : (π.fiber s).Opens))
              (initialOpOfTerminal isTerminalTop)).obj M.1
          letI : Module ↑Γ(π.fiber s, (⊤ : (π.fiber s).Opens))
              (B.obj (Opposite.op (⊤ : (π.fiber s).Opens))) :=
            ModuleCat.isModule
              (B.obj (Opposite.op (⊤ : (π.fiber s).Opens)))
          let a := (π.fiberToSpecResidueField s).appTop.hom
            ((Scheme.ΓSpecIso (S.residueField s)).inv.hom r)
          have houter :
              (Scheme.ΓSpecIso (S.residueField s)).inv.hom r •
                  (show Scheme.Modules.baseSections
                    (π.fiberToSpecResidueField s) M from x) =
                a • (show B.obj
                  (Opposite.op (⊤ : (π.fiber s).Opens)) from x) := by
            rfl
          have hinner :
              a • (show B.obj
                  (Opposite.op (⊤ : (π.fiber s).Opens)) from x) =
                ((π.fiber s).presheaf.map
                    ((initialOpOfTerminal isTerminalTop).to
                      (Opposite.op (⊤ : (π.fiber s).Opens)))).hom a • x := by
            rfl
          have htop :
              (initialOpOfTerminal isTerminalTop).to
                  (Opposite.op (⊤ : (π.fiber s).Opens)) =
                𝟙 (Opposite.op (⊤ : (π.fiber s).Opens)) :=
            Subsingleton.elim _ _
          rw [houter, hinner, htop]
          simp [a]
          rfl
        have hinput := congrArg
          (fun y : Scheme.Modules.baseSections
            (π.fiberToSpecResidueField s) M => e.hom y) hx
        have hlinear := e.hom.hom.map_smul
          ((Scheme.ΓSpecIso (S.residueField s)).inv.hom r)
          (show Scheme.Modules.baseSections
            (π.fiberToSpecResidueField s) M from x)
        exact hinput.trans hlinear }

/-- The degree-zero kernel of a residue-fibre pole Cech complex has dimension
`n` for `n ≥ 1`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_fiber_baseCech_kernel_finrank
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (h : FibrewiseElliptic π z hz)
    (s : S) {n : ℕ} (hn : 1 ≤ n) {ι : Type u}
    (U : ι → (π.fiber s).Opens) (hU : IsOpenCover U) :
    letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
      isSeparated_fiberToSpecResidueField π s
    let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
    let C := Scheme.Modules.baseCechComplex
      (π.fiberToSpecResidueField s) M U
    letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
      Module.compHom _
        (Scheme.ΓSpecIso (S.residueField s)).inv.hom
    Module.finrank ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) = n := by
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  let C := Scheme.Modules.baseCechComplex
    (π.fiberToSpecResidueField s) M U
  letI : Module ↑(S.residueField s) Γ(M, (⊤ : (π.fiber s).Opens)) :=
    Module.compHom _
      (Scheme.Modules.baseScalarHom (π.fiberToSpecResidueField s))
  letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
    Module.compHom _
      (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  let e := FibrewiseElliptic.sectionPoleSheafPower_fiberSectionsEquivBaseCechKernel
    (π := π) z hz s (n := n) U hU
  exact e.finrank_eq.symm.trans
    (h.sectionPoleSheafPower_fiber_finrank z hz s hn)

/-- The degree-zero kernel of an ordered residue-fibre pole Cech complex has dimension `n` for
`n ≥ 1`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_fiber_orderedBaseCech_kernel_finrank
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (h : FibrewiseElliptic π z hz)
    (s : S) {n : ℕ} (hn : 1 ≤ n) {ι : Type u} [LinearOrder ι]
    (U : ι → (π.fiber s).Opens) (hU : IsOpenCover U) :
    letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
      isSeparated_fiberToSpecResidueField π s
    let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
    let C := Scheme.Modules.orderedBaseCechComplex
      (π.fiberToSpecResidueField s) M U
    letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
      Module.compHom _
        (Scheme.ΓSpecIso (S.residueField s)).inv.hom
    Module.finrank ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) = n := by
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  let M := @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  let C := Scheme.Modules.baseCechComplex
    (π.fiberToSpecResidueField s) M U
  let D := Scheme.Modules.orderedBaseCechComplex
    (π.fiberToSpecResidueField s) M U
  letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
    Module.compHom _
      (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  letI : Module ↑(S.residueField s) (LinearMap.ker (D.d 0 1).hom) :=
    Module.compHom _
      (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  let eA := Scheme.Modules.baseCechKernelOrderedLinearEquiv
    (π.fiberToSpecResidueField s) M U
  let e : LinearMap.ker (C.d 0 1).hom ≃ₗ[↑(S.residueField s)]
      LinearMap.ker (D.d 0 1).hom :=
    { toFun := eA
      invFun := eA.symm
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_add' := eA.map_add
      map_smul' := fun r x =>
        eA.map_smul ((Scheme.ΓSpecIso (S.residueField s)).inv.hom r) x }
  exact e.finrank_eq.symm.trans
    (h.sectionPoleSheafPower_fiber_baseCech_kernel_finrank
      z hz s hn U hU)

/-- The degree-zero Cech kernel of the pullback of `O(n[0])` to a residue fibre has
dimension `n` for `n ≥ 1`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_pullback_fiber_baseCech_kernel_finrank
    {E S : Scheme.{u}} {f : E ⟶ S} [IsSeparated f]
    (hsm : SmoothOfRelativeDimension 1 f)
    (z : S ⟶ E) (hz : z ≫ f = 𝟙 S) (h : FibrewiseElliptic f z hz)
    (s : S) {n : ℕ} (hn : 1 ≤ n) {ι : Type u}
    (U : ι → (f.fiber s).Opens) (hU : IsOpenCover U) :
    let M := sectionPoleSheafPower f z hz n
    let P := (Scheme.Modules.pullback (f.fiberι s)).obj M
    let C := Scheme.Modules.baseCechComplex
      (f.fiberToSpecResidueField s) P U
    letI : Module ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) :=
      Module.compHom _ (Scheme.ΓSpecIso (S.residueField s)).inv.hom
    Module.finrank ↑(S.residueField s) (LinearMap.ker (C.d 0 1).hom) = n := by
  letI hsepFiber : IsSeparated (f.fiberToSpecResidueField s) := by
    change IsSeparated (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  let M := sectionPoleSheafPower f z hz n
  let P := (Scheme.Modules.pullback (f.fiberι s)).obj M
  let MF := sectionPoleSheafPower (f.fiberToSpecResidueField s)
    (sectionFiberPoint f z hz s) (pullback.lift_snd _ _ _) n
  let C := Scheme.Modules.baseCechComplex
    (f.fiberToSpecResidueField s) P U
  let k := ↑(S.residueField s)
  let ρ := (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  letI : Module k (LinearMap.ker (C.d 0 1).hom) := Module.compHom _ ρ
  letI : Module k Γ(P, (⊤ : (f.fiber s).Opens)) :=
    Module.compHom _
      (Scheme.Modules.baseScalarHom (f.fiberToSpecResidueField s))
  letI : Module k Γ(MF, (⊤ : (f.fiber s).Opens)) :=
    Module.compHom _
      (Scheme.Modules.baseScalarHom (f.fiberToSpecResidueField s))
  let eCechA := Scheme.Modules.baseSectionsIsoKernelBaseCechDifferential
    (f.fiberToSpecResidueField s) P U hU
  let eCech : Γ(P, (⊤ : (f.fiber s).Opens)) ≃ₗ[k]
      LinearMap.ker (C.d 0 1).hom :=
    { toFun := eCechA.hom
      invFun := eCechA.inv
      left_inv := eCechA.toLinearEquiv.left_inv
      right_inv := eCechA.toLinearEquiv.right_inv
      map_add' := eCechA.hom.hom.map_add
      map_smul' := fun r x ↦ by
        change eCechA.hom.hom
          ((f.fiberToSpecResidueField s).appTop.hom (ρ r) • x) =
            ρ r • eCechA.hom.hom x
        rw [← Scheme.Modules.baseSections_smul
          (f.fiberToSpecResidueField s) P (ρ r) x]
        exact eCechA.hom.hom.map_smul (ρ r) x }
  let eM := sectionPoleSheafPowerFiberIso hsm z hz s n
  let eSectionsA := Scheme.Modules.baseSectionsMapIso
    (f.fiberToSpecResidueField s) eM
  let eSections : Γ(P, (⊤ : (f.fiber s).Opens)) ≃ₗ[k]
      Γ(MF, (⊤ : (f.fiber s).Opens)) :=
    { toFun := eSectionsA.hom
      invFun := eSectionsA.inv
      left_inv := eSectionsA.toLinearEquiv.left_inv
      right_inv := eSectionsA.toLinearEquiv.right_inv
      map_add' := eSectionsA.hom.hom.map_add
      map_smul' := fun r x ↦ by
        change eSectionsA.hom.hom
          ((f.fiberToSpecResidueField s).appTop.hom (ρ r) • x) =
            (f.fiberToSpecResidueField s).appTop.hom (ρ r) •
              (show Γ(MF, (⊤ : (f.fiber s).Opens)) from
                eSectionsA.hom.hom x)
        rw [← Scheme.Modules.baseSections_smul
          (f.fiberToSpecResidueField s) P (ρ r) x]
        rw [← Scheme.Modules.baseSections_smul
          (f.fiberToSpecResidueField s) MF (ρ r) (eSectionsA.hom.hom x)]
        exact eSectionsA.hom.hom.map_smul (ρ r) x }
  have hfin := h.sectionPoleSheafPower_fiber_finrank z hz s hn
  exact eCech.finrank_eq.symm.trans (eSections.finrank_eq.trans hfin)

/-- After categorical extension to a residue field, the degree-zero Cech kernel of
`O(n[0])` has dimension `n` for `n ≥ 1`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_kernel_finrank
    {E S : Scheme.{u}} {f : E ⟶ S} [IsProper f] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 f)
    (z : S ⟶ E) (hz : z ≫ f = 𝟙 S) (h : FibrewiseElliptic f z hz)
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    let t := S.fromSpecResidueField s
    let M := sectionPoleSheafPower f z hz n
    let C := Scheme.Modules.baseCechComplex f M U
    let K := ((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj C
    letI : Module ↑(S.residueField s) (LinearMap.ker (K.d 0 1).hom) :=
      Module.compHom _ (Scheme.ΓSpecIso (S.residueField s)).inv.hom
    Module.finrank ↑(S.residueField s) (LinearMap.ker (K.d 0 1).hom) = n := by
  let t := S.fromSpecResidueField s
  let M := sectionPoleSheafPower f z hz n
  let C := Scheme.Modules.baseCechComplex f M U
  let K := ((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
    (.up ℕ)).obj C
  let Uf : ι → (f.fiber s).Opens := fun i ↦ pullback.fst f t ⁻¹ᵁ U i
  let P := (Scheme.Modules.pullback (pullback.fst f t)).obj M
  let CF := Scheme.Modules.baseCechComplex (pullback.snd f t) P Uf
  let ρ := (Scheme.ΓSpecIso (S.residueField s)).inv.hom
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  letI hsepFiber : IsSeparated (f.fiberToSpecResidueField s) := by
    change IsSeparated (pullback.snd f t)
    infer_instance
  letI : Module ↑(S.residueField s) (LinearMap.ker (K.d 0 1).hom) :=
    Module.compHom _ ρ
  letI : Module ↑(S.residueField s) (LinearMap.ker (CF.d 0 1).hom) :=
    Module.compHom _ ρ
  have hUf : IsOpenCover Uf :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst f t) hU
  let eA := (HomologicalComplex.kernelZeroIsoOfIso
    (Scheme.Modules.baseCechComplexBaseChangeIso f t M U hUaff)).toLinearEquiv
  let e : LinearMap.ker (K.d 0 1).hom ≃ₗ[↑(S.residueField s)]
      LinearMap.ker (CF.d 0 1).hom :=
    { toFun := eA
      invFun := eA.symm
      left_inv := eA.left_inv
      right_inv := eA.right_inv
      map_add' := eA.map_add
      map_smul' := fun r x ↦ eA.map_smul (ρ r) x }
  exact e.finrank_eq.trans
    (h.sectionPoleSheafPower_pullback_fiber_baseCech_kernel_finrank
      hsm z hz s hn Uf hUf)

/-- The kernel of the algebraically residue-field-base-changed first Cech differential of
`O(n[0])` has dimension `n` for `n ≥ 1`. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_baseChange_kernel_finrank
    {E S : Scheme.{u}} {f : E ⟶ S} [IsProper f] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 f)
    (z : S ⟶ E) (hz : z ≫ f = 𝟙 S) (h : FibrewiseElliptic f z hz)
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    let k := ↑(S.residueField s)
    letI : Algebra Γ(S, (⊤ : S.Opens)) k :=
      ((S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    let C := Scheme.Modules.baseCechComplex f
      (sectionPoleSheafPower f z hz n) U
    Module.finrank k
      (LinearMap.ker ((C.d 0 1).hom.baseChange k)) = n := by
  dsimp only
  let k := ↑(S.residueField s)
  let t := S.fromSpecResidueField s
  let eΓ := Scheme.ΓSpecIso (S.residueField s)
  letI : Algebra Γ(S, (⊤ : S.Opens)) k :=
    (t.appTop ≫ eΓ.hom).hom.toAlgebra
  let C := Scheme.Modules.baseCechComplex f
    (sectionPoleSheafPower f z hz n) U
  let K := ((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
    (.up ℕ)).obj C
  let eFun : ModuleCat.extendScalars
      (algebraMap Γ(S, (⊤ : S.Opens)) k) ≅
        ModuleCat.extendScalars t.appTop.hom ⋙
          ModuleCat.restrictScalars eΓ.inv.hom :=
    ModuleCat.extendScalarsComp t.appTop.hom eΓ.hom.hom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars t.appTop.hom)
        (moduleCatExtendScalarsIsoRestrictScalarsOfRingEquiv
          eΓ.commRingCatIsoToRingEquiv)
  let eComplex := (NatIso.mapHomologicalComplex eFun (.up ℕ)).app C
  let eKernel := (HomologicalComplex.baseChangeKernelZeroLinearEquiv C k).trans
    (HomologicalComplex.kernelZeroIsoOfIso eComplex).toLinearEquiv
  letI : Module k (LinearMap.ker (K.d 0 1).hom) :=
    Module.compHom _ eΓ.inv.hom
  exact eKernel.finrank_eq.trans
    (h.sectionPoleSheafPower_residueField_baseCech_kernel_finrank
      hsm z hz U hU hUaff s hn)

/-- The algebraically residue-field-base-changed first differential of the ordered Cech
complex of `O(n[0])` has an `n`-dimensional kernel for `n ≥ 1`. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_baseChange_kernel_finrank
    {E S : Scheme.{u}} {f : E ⟶ S} [IsProper f] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 f)
    (z : S ⟶ E) (hz : z ≫ f = 𝟙 S) (h : FibrewiseElliptic f z hz)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    let k := ↑(S.residueField s)
    letI : Algebra Γ(S, (⊤ : S.Opens)) k :=
      ((S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    let C := Scheme.Modules.orderedBaseCechComplex f
      (sectionPoleSheafPower f z hz n) U
    Module.finrank k
      (LinearMap.ker ((C.d 0 1).hom.baseChange k)) = n := by
  dsimp only
  let k := ↑(S.residueField s)
  letI : Algebra Γ(S, (⊤ : S.Opens)) k :=
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
  let M := sectionPoleSheafPower f z hz n
  let e := Scheme.Modules.baseCechKernelOrderedBaseChangeLinearEquiv
    f M U k
  exact e.finrank_eq.symm.trans
    (h.sectionPoleSheafPower_residueField_baseCech_baseChange_kernel_finrank
      hsm z hz U hU hUaff s hn)

/-- After extension to a residue field, the base-linear Cech complex of
`O(n[0])` is exact in degree one for `n ≥ 1` on a fibrewise elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_exactAt_one
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.baseCechComplex π
        (sectionPoleSheafPower π z hz n) U)).ExactAt 1 := by
  let t := S.fromSpecResidueField s
  let M := sectionPoleSheafPower π z hz n
  let Uf : ι → (π.fiber s).Opens :=
    fun i ↦ pullback.fst π t ⁻¹ᵁ U i
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) := by
    change IsSeparated (pullback.snd π t)
    infer_instance
  let MF : (π.fiber s).Modules :=
    @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  have hUf : IsOpenCover Uf := by
    exact Scheme.Hom.iSup_preimage_eq_top (pullback.fst π t) hU
  have hUfaff : ∀ i, IsAffineOpen (Uf i) := by
    intro i
    exact IsAffineOpen.preimage_pullback_fst π t (hUaff i)
  have hsmFiber : SmoothOfRelativeDimension 1 (π.fiberToSpecResidueField s) := by
    change SmoothOfRelativeDimension 1 (pullback.snd π t)
    exact
      (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback π t) hsm
  letI : MF.IsQuasicoherent := by
    dsimp only [MF]
    exact sectionPoleSheafPower_isQuasicoherent hsmFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  let eM :
      (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
        MF := by
    dsimp only [t, M, MF]
    exact sectionPoleSheafPowerFiberIso hsm z hz s n
  letI : ((Scheme.Modules.pullback (pullback.fst π t)).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (π.fiber s).ringCatSheaf).prop_of_iso
      eM.symm inferInstance
  letI hFiberH : Subsingleton (CategoryTheory.Sheaf.H MF.sheaf 1) := by
    dsimp only [MF]
    exact h.sectionPoleSheafPower_fiber_subsingleton_H_one z hz s hn
  have hPullbackH : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf 1) := by
    let eH :=
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) 1).mapIso
          ((Scheme.Modules.toSheaf (π.fiber s)).mapIso eM)
    change Subsingleton ↑((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (π.fiber s)) 1).obj
        ((Scheme.Modules.toSheaf (π.fiber s)).obj
          ((Scheme.Modules.pullback (pullback.fst π t)).obj M)))
    letI : Subsingleton ↑((CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) 1).obj
      ((Scheme.Modules.toSheaf (π.fiber s)).obj MF)) := by
      change Subsingleton (CategoryTheory.Sheaf.H MF.sheaf 1)
      exact hFiberH
    exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  have hFiberExact :
      (Scheme.Modules.baseCechComplex (pullback.snd π t)
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M) Uf).ExactAt 1 := by
    exact (Scheme.Modules.baseCechComplex_exactAt_one_iff_subsingleton_H
      (pullback.snd π t)
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
      Uf hUf hUfaff).mpr hPullbackH
  exact hFiberExact.of_iso
    (Scheme.Modules.baseCechComplexBaseChangeIso
      π t M U hUaff).symm

end ModularCurves
