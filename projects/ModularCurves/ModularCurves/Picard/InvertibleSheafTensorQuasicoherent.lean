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

noncomputable local instance (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  monoidalCategory Y

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
    letI : (Scheme.Modules.pullback (W j).ι).Monoidal :=
      pullbackMonoidal (W j).ι
    let eTensor :
        ML.restrict (W j).ι ≅
          M.restrict (W j).ι ⊗ L.restrict (W j).ι :=
      (restrictFunctorIsoPullback (W j).ι).app (M ⊗ L) ≪≫
        (Functor.Monoidal.μIso
          (Scheme.Modules.pullback (W j).ι) M L).symm ≪≫
        ((restrictFunctorIsoPullback (W j).ι).symm.app M ⊗ᵢ
          (restrictFunctorIsoPullback (W j).ι).symm.app L)
    let e :
        ML.restrict (W j).ι ≅ M.restrict (W j).ι :=
      eTensor ≪≫
        (Iso.refl _ ⊗ᵢ eL') ≪≫
        (Iso.refl _ ⊗ᵢ
          (sheafifyValIso (unitObj (W j).toScheme)).symm) ≪≫
        ρ_ (M.restrict (W j).ι)
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

end

end AlgebraicGeometry.Scheme.Modules
