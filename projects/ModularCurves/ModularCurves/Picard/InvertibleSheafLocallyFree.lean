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

private noncomputable def freeCokernelPresentation (U : X.Opens)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1}) :
    (Limits.cokernel f).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree f (Limits.cokernel.π f)
    (Limits.cokernel.condition f) (Limits.cokernelIsCokernel f)

private instance freeCokernelPresentation_isFinite (U : X.Opens)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1}) :
    (freeCokernelPresentation U f).IsFinite where
  isFiniteType_generators := by
    constructor
    dsimp only [freeCokernelPresentation,
      SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree]
    infer_instance
  isFiniteType_relations := by
    constructor
    dsimp only [freeCokernelPresentation,
      SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.relationsOfIsCokernelFree]
    infer_instance

private noncomputable def localFreeMap {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (eM : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (eN : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} :=
  (localFreeTrivializationIso M U eM).hom ≫ f.over U ≫
    (localFreeTrivializationIso N U eN).inv

private noncomputable def localCokernelIso {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (eM : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (eN : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    Limits.cokernel (localFreeMap f U eM eN) ≅ (Limits.cokernel f).over U := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  exact Limits.cokernel.mapIso (f := localFreeMap f U eM eN) (f.over U)
      (localFreeTrivializationIso M U eM)
      (localFreeTrivializationIso N U eN) (by simp [localFreeMap]) ≪≫
    (Limits.PreservesCokernel.iso F f).symm

private noncomputable def localCokernelPresentation {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (eM : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (eN : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    ((Limits.cokernel f).over U).Presentation :=
  SheafOfModules.Presentation.ofIsIso (localCokernelIso f U eM eN).hom
    (freeCokernelPresentation U (localFreeMap f U eM eN))

private instance localCokernelPresentation_isFinite {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (eM : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (eN : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    (localCokernelPresentation f U eM eN).IsFinite := by
  dsimp only [localCokernelPresentation]
  infer_instance

/-- The cokernel of a morphism between invertible scheme modules is finitely presented. -/
theorem IsInvertible.cokernel_isFinitePresentation {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) (f : M ⟶ N) :
    (Limits.cokernel f).IsFinitePresentation := by
  obtain ⟨ι, U, hU, htrivM⟩ := hM
  obtain ⟨κ, V, hV, htrivN⟩ := hN
  let W : ι × κ → X.Opens := fun ij => U ij.1 ⊓ V ij.2
  have hW : iSup W = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hxU : x ∈ iSup U := by rw [hU]; trivial
      have hxV : x ∈ iSup V := by rw [hV]; trivial
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxU
      obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxV
      exact Opens.mem_iSup.mpr ⟨(i, j), hxi, hxj⟩
  let q : (Limits.cokernel f).QuasicoherentData :=
    { I := ι × κ
      X := W
      coversTop := (Opens.coversTop_iff (T := X) W).2 hW
      presentation ij := localCokernelPresentation f (W ij)
        (restrictTrivialization (show W ij ≤ U ij.1 from inf_le_left)
          (htrivM ij.1).some)
        (restrictTrivialization (show W ij ≤ V ij.2 from inf_le_right)
          (htrivN ij.2).some) }
  refine { exists_quasicoherentData := ⟨q, ?_⟩ }
  constructor
  intro ij
  dsimp only [q]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
