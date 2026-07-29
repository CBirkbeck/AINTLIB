/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Quasicoherence after tensoring by an invertible sheaf

An invertible sheaf is trivial on an open cover. Refining that cover by affine
opens identifies the restriction of its tensor product with the restriction of
the other factor, so quasicoherence descends from the affine refinement.
-/

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

noncomputable local instance invertibleSheafTensorMonoidal
    (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  monoidalCategory Y

private noncomputable def tensorRestrictIso
    {M L : X.Modules} (U : X.Opens)
    (eL : L.restrict U.ι ≅ unitObj U.toScheme) :
    (M ⊗ L).restrict U.ι ≅ M.restrict U.ι := by
  letI : (Scheme.Modules.pullback U.ι).Monoidal :=
    pullbackMonoidal U.ι
  exact
    (restrictFunctorIsoPullback U.ι).app (M ⊗ L) ≪≫
      (Functor.Monoidal.μIso
        (Scheme.Modules.pullback U.ι) M L).symm ≪≫
      ((restrictFunctorIsoPullback U.ι).symm.app M ⊗ᵢ
        (restrictFunctorIsoPullback U.ι).symm.app L) ≪≫
      (Iso.refl _ ⊗ᵢ eL) ≪≫
      (Iso.refl _ ⊗ᵢ
        (sheafifyValIso (unitObj U.toScheme)).symm) ≪≫
      ρ_ (M.restrict U.ι)

/-- Tensoring a quasicoherent scheme module by an invertible scheme module
preserves quasicoherence. -/
theorem IsInvertible.tensorObj_isQuasicoherent
    {M L : X.Modules} [M.IsQuasicoherent]
    (hL : IsInvertible L) : (M ⊗ L).IsQuasicoherent := by
  let ML : X.Modules := M ⊗ L
  change ML.IsQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  have hlocal (j : J) :
      (ML.over (W j)).IsQuasicoherent := by
    letI : IsAffine (W j).toScheme := j.2.1
    obtain ⟨eL⟩ := htriv j.1.2
    let eL' : L.restrict (W j).ι ≅ unitObj (W j).toScheme :=
      restrictIsoOfPullbackIso L (W j)
        (restrictTrivialization j.2.2 eL)
    let e :
        ML.restrict (W j).ι ≅ M.restrict (W j).ι :=
      tensorRestrictIso (M := M) (L := L) (W j) eL'
    have hRestrict :
        (ML.restrict (W j).ι).IsQuasicoherent :=
      (isQuasicoherent (W j).toScheme).prop_of_iso
        e.symm inferInstance
    letI : (ML.restrict (W j).ι).IsQuasicoherent :=
      hRestrict
    exact
      isQuasicoherent_over_of_restrict_of_isAffineOpen
        ML (W j)
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ML _ W hcover hlocal

/-- Tensoring a finite-type quasicoherent scheme module by an invertible
scheme module preserves finite type. -/
theorem IsInvertible.tensorObj_isFiniteType
    {M L : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (hL : IsInvertible L) : (M ⊗ L).IsFiniteType := by
  let ML : X.Modules := M ⊗ L
  letI : ML.IsQuasicoherent :=
    hL.tensorObj_isQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  choose G hG using fun j : J =>
    exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M ⟨W j, j.2.1⟩
  let e (j : J) : ML.restrict (W j).ι ≅ M.restrict (W j).ι := by
    let eL := Classical.choice (htriv j.1.2)
    let eL' : L.restrict (W j).ι ≅ unitObj (W j).toScheme :=
      restrictIsoOfPullbackIso L (W j)
        (restrictTrivialization j.2.2 eL)
    exact tensorRestrictIso (M := M) (L := L) (W j) eL'
  let GML (j : J) : (ML.restrict (W j).ι).GeneratingSections :=
    (SheafOfModules.GeneratingSections.equivOfIso (e j)).symm (G j)
  have hGML (j : J) : (GML j).IsFiniteType := by
    constructor
    change Finite (G j).I
    exact (hG j).finite
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  let q : ML.LocalGeneratorsData :=
    { I := J
      X := W
      coversTop := hcover
      generators := fun j =>
        generatingSectionsOverOfRestrict ML (W j) (GML j) }
  have hq : q.IsFiniteType := by
    constructor
    intro j
    letI : (GML j).IsFiniteType := hGML j
    exact generatingSectionsOverOfRestrict_isFiniteType
      ML (W j) (GML j)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro j
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType j.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

end

end AlgebraicGeometry.Scheme.Modules
