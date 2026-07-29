import ModularCurves.ForMathlib.SheafCechFlasqueHOne
import ModularCurves.ForMathlib.SheafCohomologyCokernel

/-!
# Degree-one Cech comparison

For an open cover whose degree-zero sheaf Cech term is acyclic in degree one,
degree-one homology of the native Cech complex computes genuine sheaf cohomology.
The proof compares the cycle kernel preserved by global sections and the cokernel
description supplied by the long exact cohomology sequence.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private abbrev globalSections (X : TopCat.{u}) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

noncomputable local instance : PreservesLimitsOfSize.{u, u} (globalSections X) :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).rightAdjoint_preservesLimits

private noncomputable def HZeroGlobalSectionsIso
    (G : Sheaf AddCommGrpCat.{u} X) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 0).obj (toSiteSheaf G) ≅
      (globalSections X).obj (toSiteSheaf G) :=
  (CategoryTheory.Sheaf.H.equiv₀ (toSiteSheaf G) isTerminalTop).toAddCommGrpIso ≪≫
    (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).symm.app
        (toSiteSheaf G)

private theorem HZeroGlobalSectionsIso_naturality
    {G H : Sheaf AddCommGrpCat.{u} X} (f : G ⟶ H) :
    (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 0).map f ≫
        (HZeroGlobalSectionsIso H).hom =
      (HZeroGlobalSectionsIso G).hom ≫ (globalSections X).map f := by
  ext x
  apply (AddCommGrpCat.mono_iff_injective
    ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
        (toSiteSheaf H))).mp inferInstance
  let f' : toSiteSheaf G ⟶ toSiteSheaf H := f
  simp [HZeroGlobalSectionsIso]
  change
    CategoryTheory.Sheaf.H.equiv₀ (toSiteSheaf H) isTerminalTop
        (CategoryTheory.Sheaf.H.map f' 0 x) =
      f'.hom.app (op (⊤ : Opens X))
        (CategoryTheory.Sheaf.H.equiv₀ (toSiteSheaf G) isTerminalTop x)
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop f' x).symm

private noncomputable def cechGlobalCyclesIso :
    (globalSections X).obj (cechOneShortComplex F U).cycles ≅
      ((cechOneShortComplex F U).map (globalSections X)).cycles := by
  let T := cechOneShortComplex F U
  exact IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit
      (KernelFork.ofι T.iCycles T.iCycles_g) T.cyclesIsKernel (globalSections X))
    (T.map (globalSections X)).cyclesIsKernel

@[reassoc]
private theorem cechGlobalCyclesIso_hom_iCycles :
    (cechGlobalCyclesIso F U).hom ≫
        ((cechOneShortComplex F U).map (globalSections X)).iCycles =
      (globalSections X).map (cechOneShortComplex F U).iCycles := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

private theorem cechBoundary_comm :
    (globalSections X).map (cechCycleShortComplex F U).g ≫
        (cechGlobalCyclesIso F U).hom =
      ((cechOneShortComplex F U).map (globalSections X)).toCycles := by
  let T := cechOneShortComplex F U
  let A := cechCycleShortComplex F U
  rw [← cancel_mono (T.map (globalSections X)).iCycles]
  rw [Category.assoc, cechGlobalCyclesIso_hom_iCycles]
  change (globalSections X).map T.toCycles ≫
      (globalSections X).map T.iCycles =
    (T.map (globalSections X)).toCycles ≫
      (T.map (globalSections X)).iCycles
  rw [← (globalSections X).map_comp]
  rw [T.toCycles_i, (T.map (globalSections X)).toCycles_i]
  rfl

private noncomputable def cechCokernelLeftHomologyIso :
    cokernel ((cechOneShortComplex F U).map (globalSections X)).toCycles ≅
      ((cechOneShortComplex F U).map (globalSections X)).leftHomology :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel
      ((cechOneShortComplex F U).map (globalSections X)).toCycles)
    ((cechOneShortComplex F U).map (globalSections X)).leftHomologyIsCokernel

private noncomputable def cechBoundaryCokernelIso :
    cokernel ((globalSections X).map (cechCycleShortComplex F U).g) ≅
      ((cechOneShortComplex F U).map (globalSections X)).homology :=
  cokernel.mapIso
      (f := (globalSections X).map (cechCycleShortComplex F U).g)
      ((cechOneShortComplex F U).map (globalSections X)).toCycles
      (Iso.refl _) (cechGlobalCyclesIso F U) (cechBoundary_comm F U) ≪≫
    cechCokernelLeftHomologyIso F U ≪≫
    ((cechOneShortComplex F U).map (globalSections X)).leftHomologyIso

private abbrev cechHZeroBoundary :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) 0).obj (cechCycleShortComplex F U).X₂ ⟶
        (CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology X) 0).obj (cechCycleShortComplex F U).X₃ :=
  (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) 0).map (cechCycleShortComplex F U).g

private abbrev cechGlobalBoundary :
    (globalSections X).obj (cechCycleShortComplex F U).X₂ ⟶
      (globalSections X).obj (cechCycleShortComplex F U).X₃ :=
  (globalSections X).map (cechCycleShortComplex F U).g

private noncomputable def cechHZeroCokernelIso :
    cokernel (cechHZeroBoundary F U) ≅ cokernel (cechGlobalBoundary F U) :=
  cokernel.mapIso
    (f := cechHZeroBoundary F U) (cechGlobalBoundary F U)
    (HZeroGlobalSectionsIso (cechCycleShortComplex F U).X₂)
    (HZeroGlobalSectionsIso (cechCycleShortComplex F U).X₃)
    (HZeroGlobalSectionsIso_naturality (cechCycleShortComplex F U).g)

private noncomputable def cechGlobalHomologyOneIso
    (hU : ⨆ i, U i = ⊤)
    [Subsingleton (H (cechTerm F U 0) 1)] :
    ((cechOneShortComplex F U).map (globalSections X)).homology ≅
      AddCommGrpCat.of (H F 1) :=
  (cechBoundaryCokernelIso F U).symm ≪≫
    (cechHZeroCokernelIso F U).symm ≪≫
    CategoryTheory.Sheaf.H.cokernelMapZeroIsoOne
      (cechCycleShortComplex_shortExact F U hU)

private noncomputable def cechOneShortComplexIso :
    cechOneShortComplex F U ≅ (cechComplex F U).sc' 0 1 2 :=
  ShortComplex.isoMk
    (eqToIso (cechComplex_X F U 0).symm)
    (eqToIso (cechComplex_X F U 1).symm)
    (eqToIso (cechComplex_X F U 2).symm)
    (by
      simp [cechOneShortComplex, HomologicalComplex.sc',
        HomologicalComplex.shortComplexFunctor',
        cechComplex_X, cechComplex_d])
    (by
      simp [cechOneShortComplex, HomologicalComplex.sc',
        HomologicalComplex.shortComplexFunctor',
        cechComplex_X, cechComplex_d])

private noncomputable def cechGlobalOneShortComplexIso :
    (cechOneShortComplex F U).map (globalSections X) ≅
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (cechComplex F U)).sc' 0 1 2 := by
  exact (globalSections X).mapShortComplex.mapIso (cechOneShortComplexIso F U)

private noncomputable def cechMappedComplexHomologyOneIso
    (hU : ⨆ i, U i = ⊤)
    [Subsingleton (H (cechTerm F U 0) 1)] :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (cechComplex F U)).homology 1 ≅ AddCommGrpCat.of (H F 1) :=
  (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (cechComplex F U)).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (ShortComplex.homologyMapIso (cechGlobalOneShortComplexIso F U)).symm ≪≫
    cechGlobalHomologyOneIso F U hU

/-- If the degree-zero sheaf Cech term is `H¹`-acyclic, degree-one homology of the
native Cech complex computes genuine sheaf cohomology. -/
noncomputable def cechHomologyOneIso
    (hU : ⨆ i, U i = ⊤)
    [Subsingleton (H (cechTerm F U 0) 1)] :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅ AddCommGrpCat.of (H F 1) :=
  HomologicalComplex.homologyMapIso (cechGlobalSectionsComplexIso F U).symm 1 ≪≫
    cechMappedComplexHomologyOneIso F U hU

/-- Under degree-one acyclicity of the first sheaf Cech term, genuine `H¹` vanishes
exactly when the native Cech complex is exact in degree one. -/
theorem subsingleton_H_one_iff_cechComplex_exactAt_one
    (hU : ⨆ i, U i = ⊤)
    [Subsingleton (H (cechTerm F U 0) 1)] :
    Subsingleton (H F 1) ↔ ((cechComplexFunctor U).obj F.obj).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  constructor
  · intro h
    have hH : IsZero (AddCommGrpCat.of (H F 1)) :=
      AddCommGrpCat.isZero_of_subsingleton _
    exact IsZero.of_iso hH (cechHomologyOneIso F U hU)
  · intro h
    have hH : IsZero (AddCommGrpCat.of (H F 1)) :=
      IsZero.of_iso h (cechHomologyOneIso F U hU).symm
    exact AddCommGrpCat.subsingleton_of_isZero
      hH

end
end TopCat.Sheaf
