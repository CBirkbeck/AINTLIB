import ModularCurves.EllipticCurve.PoleSheafModelHOne
import ModularCurves.EllipticCurve.PoleSheafPointedIso
import ModularCurves.ForMathlib.SheafCohomologyIso
import ModularCurves.ForMathlib.SchemeModuleSheaf

/-!
# First cohomology of pole sheaves on residue fibres

This file transports model-side vanishing of `H¹(O(n[0]))` across the pointed
isomorphism supplied by `FibrewiseElliptic`.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private def opensFunctorIsoMapInv {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.hom.opensFunctor ≅ Opens.map e.inv.base :=
  NatIso.ofComponents (fun U ↦ eqToIso (by
    change e.hom ''ᵁ U = e.inv ⁻¹ᵁ U
    simpa using Scheme.Hom.inv_image e.symm U)) (fun _ ↦ Subsingleton.elim _ _)

private noncomputable def restrictSheafIsoPushforward {X Y : Scheme.{u}}
    (e : X ≅ Y) (M : Y.Modules) :
    (M.restrict e.hom).sheaf ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat e.inv.base).obj M.sheaf := by
  exact (Functor.sheafPushforwardContinuousIso (opensFunctorIsoMapInv e)
    AddCommGrpCat (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)).app M.sheaf

private noncomputable def pullbackSheafIsoPushforward {X Y : Scheme.{u}}
    (e : X ≅ Y) (M : Y.Modules) :
    (TopCat.Sheaf.pushforward AddCommGrpCat e.inv.base).obj M.sheaf ≅
      ((pullback e.hom).obj M).sheaf :=
  (restrictSheafIsoPushforward e M).symm ≪≫
    (toSheaf X).mapIso ((restrictFunctorIsoPullback e.hom).app M)

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

private noncomputable def sectionPoleSheafPowerPointedSheafIso
    {C C' S : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S ⟶ C') (hz' : z' ≫ π' = 𝟙 S)
    (hsm' : SmoothOfRelativeDimension 1 π')
    (e : C ≅ C') (hez : z ≫ e.hom = z') (n : ℕ) :
    (TopCat.Sheaf.pushforward AddCommGrpCat e.inv.base).obj
        (sectionPoleSheafPower π' z' hz' n).sheaf ≅
      (sectionPoleSheafPower π z hz n).sheaf :=
  Scheme.Modules.pullbackSheafIsoPushforward e _ ≪≫
    (Scheme.Modules.toSheaf C).mapIso
      (sectionPoleSheafPowerPointedIso z hz z' hz' hsm' e hez n)

/-- For `n >= 1`, `H¹(O(n[0]))` vanishes on every residue fibre of a fibrewise
elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_fiber_subsingleton_H_one
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (h : FibrewiseElliptic π z hz)
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    letI : IsSeparated (π.fiberToSpecResidueField s) :=
      by
        change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
        infer_instance
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower (π.fiberToSpecResidueField s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n).sheaf 1) := by
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
    by
      change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
      infer_instance
  obtain ⟨W, hW, e, _, hez⟩ := h s
  letI : W.IsElliptic := hW
  letI : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) n).sheaf 1) :=
    sectionPoleSheafPower_projModel_subsingleton_H_one W n hn
  let hSheaf := @sectionPoleSheafPowerPointedSheafIso
    (π.fiber s) (projModel W) (Spec (CommRingCat.of (S.residueField s)))
    (π.fiberToSpecResidueField s) (projModelπ W)
    hsepFiber (by infer_instance)
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _)
    (projModelZero W) (projModelZero_projModelπ W) (projModel_smooth W)
    e hez n
  exact TopCat.Sheaf.subsingleton_H_of_iso
    (Scheme.forgetToTop.mapIso e.symm) hSheaf 1

end ModularCurves
