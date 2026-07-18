import ModularCurves.EllipticCurve.PoleSheafBaseCechHOne
import ModularCurves.ForMathlib.AcyclicAffineCechComparison
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Higher base-linear Cech exactness for pole sheaves

Prove exactness in every positive degree after extending the base-linear Cech
complex of a pole sheaf to a residue field.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

/-- After extension to a residue field, the base-linear Cech complex of
`O(n[0])` is exact in every positive degree for `n ≥ 1` on a fibrewise
elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_exactAt_succ
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.baseCechComplex π
        (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) := by
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
  letI : (π.fiber s).IsSeparated := ⟨by
    rw [← terminal.comp_from (π.fiberToSpecResidueField s)]
    infer_instance⟩
  letI : (pullback π t).IsSeparated := ⟨by
    rw [← terminal.comp_from (pullback.snd π t)]
    infer_instance⟩
  let MF : (π.fiber s).Modules :=
    @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  have hUf : IsOpenCover Uf :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst π t) hU
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
      (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅ MF := by
    dsimp only [t, M, MF]
    exact sectionPoleSheafPowerFiberIso hsm z hz s n
  letI : ((Scheme.Modules.pullback (pullback.fst π t)).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (π.fiber s).ringCatSheaf).prop_of_iso
      eM.symm inferInstance
  letI hFiberH : Subsingleton (CategoryTheory.Sheaf.H MF.sheaf (q + 1)) := by
    cases q with
    | zero =>
        dsimp only [MF]
        simpa using h.sectionPoleSheafPower_fiber_subsingleton_H_one z hz s hn
    | succ q =>
        dsimp only [MF]
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          h.sectionPoleSheafPower_fiber_subsingleton_H_add_two z hz s n q
  have hPullbackH : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf (q + 1)) := by
    let eH :=
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) (q + 1)).mapIso
          ((Scheme.Modules.toSheaf (π.fiber s)).mapIso eM)
    change Subsingleton ↑((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (π.fiber s)) (q + 1)).obj
        ((Scheme.Modules.toSheaf (π.fiber s)).obj
          ((Scheme.Modules.pullback (pullback.fst π t)).obj M)))
    letI : Subsingleton ↑((CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) (q + 1)).obj
      ((Scheme.Modules.toSheaf (π.fiber s)).obj MF)) := by
      change Subsingleton (CategoryTheory.Sheaf.H MF.sheaf (q + 1))
      exact hFiberH
    exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  have hNativeExact :
      ((cechComplexFunctor Uf).obj
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf.obj).ExactAt
          (q + 1) := by
    exact Scheme.Modules.cechComplex_exactAt_succ_of_affine_openCover
      (U := Uf) ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
        hUf hUfaff q hPullbackH
  have hFiberExact :
      (Scheme.Modules.baseCechComplex (pullback.snd π t)
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M) Uf).ExactAt
          (q + 1) := by
    exact (Scheme.Modules.baseCechComplex_exactAt_iff
      (pullback.snd π t)
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
      Uf (q + 1)).mpr hNativeExact
  exact hFiberExact.of_iso
    (Scheme.Modules.baseCechComplexBaseChangeIso
      π t M U hUaff).symm

/-- After extension to a residue field, the bounded ordered Cech complex of
`O(n[0])` is exact in every positive degree for `n ≥ 1` on a fibrewise
elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_exactAt_succ
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.orderedBaseCechComplex π
        (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) := by
  let F := (ModuleCat.extendScalars
    (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex (.up ℕ)
  have hbase :=
    FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_exactAt_succ
      hsm z hz h U hU hUaff s hn q
  change (F.obj (Scheme.Modules.orderedBaseCechComplex π
    (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1)
  change (F.obj (Scheme.Modules.baseCechComplex π
    (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) at hbase
  exact hbase.of_retract
    (F.map (Scheme.Modules.orderedToBaseCechAlternating π
      (sectionPoleSheafPower π z hz n) U))
    (F.map (Scheme.Modules.baseCechToOrdered π
      (sectionPoleSheafPower π z hz n) U))
    (by
      rw [← F.map_comp,
        Scheme.Modules.orderedToBaseCechAlternating_comp_baseCechToOrdered,
        F.map_id])

end ModularCurves
