import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import ModularCurves.Picard.InvertibleSheaf

/-!
# Invertible sheaves are locally free

This file connects the project's open-cover definition of an invertible scheme module
to mathlib's `SheafOfModules.IsLocallyFree`. The bridge makes mathlib's existing
locally-free-implies-quasicoherent instance available to the pole sheaves used in the
fibrewise-to-Weierstrass comparison.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private noncomputable def unitPUnitCofan (U : X.Opens) : Limits.Cofan
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  Limits.Cofan.mk (SheafOfModules.unit (X.ringCatSheaf.over U)) (fun _ => 𝟙 _)

private noncomputable def unitPUnitCofanIsColimit (U : X.Opens) :
    Limits.IsColimit (unitPUnitCofan U) :=
  Limits.Cofan.IsColimit.mk (unitPUnitCofan U)
    (fun t => t.inj PUnit.unit)
    (fun t j => by cases j; exact Category.id_comp _)
    (fun t m h => by
      rw [← Category.id_comp m]
      exact h PUnit.unit)

private noncomputable def freePUnitIsoUnit (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.isColimitFreeCofan PUnit.{u + 1}).coconePointUniqueUpToIso
    (unitPUnitCofanIsColimit U)

private noncomputable def localFreeTrivializationIso (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ≅ M.over U :=
  freePUnitIsoUnit U ≪≫
    (overTrivializationOfRestrictIso M U (restrictIsoOfPullbackIso M U e)).symm

private noncomputable def localGeneratorsOfTrivialization (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (M.over U).GeneratingSections :=
  (SheafOfModules.free.generatingSections PUnit.{u + 1}).ofEpi
    (localFreeTrivializationIso M U e).hom

private theorem localGeneratorsOfTrivialization_π (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (localGeneratorsOfTrivialization M U e).π =
      (SheafOfModules.free.generatingSections PUnit.{u + 1}).π ≫
        (localFreeTrivializationIso M U e).hom :=
  SheafOfModules.GeneratingSections.ofEpi_π
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over U) PUnit.{u + 1})
    (localFreeTrivializationIso M U e).hom

private noncomputable instance localGeneratorsOfTrivialization_isIso
    (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    IsIso (localGeneratorsOfTrivialization M U e).π := by
  let p := localFreeTrivializationIso M U e
  refine ⟨⟨p.inv, ?_, ?_⟩⟩
  · rw [localGeneratorsOfTrivialization_π,
      SheafOfModules.free.generatingSections_π (R := X.ringCatSheaf.over U)]
    exact p.hom_inv_id
  · rw [localGeneratorsOfTrivialization_π,
      SheafOfModules.free.generatingSections_π (R := X.ringCatSheaf.over U)]
    exact p.inv_hom_id

private instance localGeneratorsOfTrivialization_isFiniteType
    (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (localGeneratorsOfTrivialization M U e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{u + 1})

private structure InvertibleTrivializationData (M : X.Modules) where
  I : Type u
  U : I → X.Opens
  iSup_eq_top : iSup U = ⊤
  e (i : I) : (pullback (U i).ι).obj M ≅ unitObj (U i).toScheme

private theorem nonempty_invertibleTrivializationData {M : X.Modules}
    (hM : IsInvertible M) : Nonempty (InvertibleTrivializationData M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  exact ⟨⟨ι, U, hU, fun i => (htriv i).some⟩⟩

private noncomputable def invertibleTrivializationData {M : X.Modules}
    (hM : IsInvertible M) : InvertibleTrivializationData M :=
  (nonempty_invertibleTrivializationData hM).some

private noncomputable def invertibleLocalGeneratorsData {M : X.Modules}
    (hM : IsInvertible M) : M.LocalGeneratorsData :=
  { I := (invertibleTrivializationData hM).I
    X := (invertibleTrivializationData hM).U
    coversTop := (Opens.coversTop_iff (T := X) _).2
      (invertibleTrivializationData hM).iSup_eq_top
    generators i := localGeneratorsOfTrivialization M
      ((invertibleTrivializationData hM).U i)
      ((invertibleTrivializationData hM).e i) }

private instance invertibleLocalGeneratorsData_isLocallyFreeData {M : X.Modules}
    (hM : IsInvertible M) : (invertibleLocalGeneratorsData hM).IsLocallyFreeData where
  isIso _ := localGeneratorsOfTrivialization_isIso _ _ _

private instance invertibleLocalGeneratorsData_isFiniteType {M : X.Modules}
    (hM : IsInvertible M) : (invertibleLocalGeneratorsData hM).IsFiniteType where
  isFiniteType _ := localGeneratorsOfTrivialization_isFiniteType _ _ _

private instance invertibleQuasicoherentData_isFinitePresentation {M : X.Modules}
    (hM : IsInvertible M) :
    (invertibleLocalGeneratorsData hM).quasiCoherentData.IsFinitePresentation where
  isFinite_presentation i := by
    constructor
    · exact (invertibleLocalGeneratorsData_isFiniteType hM).isFiniteType i
    · constructor
      dsimp [SheafOfModules.LocalGeneratorsData.quasiCoherentData]
      infer_instance

/-- An invertible scheme module is locally free in mathlib's sheaf-theoretic sense. -/
theorem IsInvertible.isLocallyFree {M : X.Modules} (hM : IsInvertible M) :
    M.IsLocallyFree :=
  (invertibleLocalGeneratorsData hM).isLocallyFree

set_option backward.isDefEq.respectTransparency.types false in
/-- An invertible scheme module is quasicoherent. -/
theorem IsInvertible.isQuasicoherent {M : X.Modules} (hM : IsInvertible M) :
    M.IsQuasicoherent := by
  letI : M.IsLocallyFree := hM.isLocallyFree
  infer_instance

/-- An invertible scheme module is finitely presented in mathlib's sheaf-theoretic sense. -/
theorem IsInvertible.isFinitePresentation {M : X.Modules} (hM : IsInvertible M) :
    M.IsFinitePresentation :=
  { exists_quasicoherentData :=
      ⟨(invertibleLocalGeneratorsData hM).quasiCoherentData, inferInstance⟩ }

end AlgebraicGeometry.Scheme.Modules
