import ModularCurves.EllipticCurve.PoleSheafCechHOne
import ModularCurves.EllipticCurve.PoleSheafFibreHOne
import ModularCurves.ForMathlib.AffineModuleCechBaseChange
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology

/-!
# Base-linear Cech comparison for pole sheaves

Retain the affine-base module structure on the Cech model computing degree-one
cohomology of the pole line bundles on a smooth proper pointed relative curve.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

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
