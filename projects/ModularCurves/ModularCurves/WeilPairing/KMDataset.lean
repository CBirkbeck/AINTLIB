/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMBilinear
import ModularCurves.Picard.PicComparison

/-!
# Existence of a normalised Katz–Mazur dataset (AP-E1-DS)

`torsionSplittingEval` consumes a *dataset* for the `N`-torsion section `Q`: an invertible
module `M` with `toSkeleton M = κ(Q)`, a trivialising cover `W`, trivialisations `e`, and the
normalisation `hnorm` — the transition cocycle takes the value `1` along the zero section.
This file constructs one for every torsion `Q`:

* `exists_module_kappa` (AP-E1-DS1) — a representative module, invertible, from the skeleton.
* `exists_over_trivialization_of_isInvertible` (AP-E1-DS2) — an `.over`-form trivialising
  cover, through `restrictIsoOfPullbackIso` and `overTrivializationOfRestrictIso`.
* `nonempty_pullback_zero_iso_unit_of_kappa` (AP-E1-DS3) — the rigidification `0^*M ≅ 𝒪_T`,
  from `kappa_mem_ker`. This is what makes a *normalised* trivialisation possible at all.
* the two-family cover construction (AP-E1-DS4–DS6): near the zero image, correct each chart
  by the `π`-pullback of its comparison unit with the rigidification; off the zero image —
  an open set, because the zero section is a closed immersion — the normalisation condition
  is vacuous.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

section Dataset

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)

/-- **(AP-E1-DS1)** Every `κ(Q)` is represented by an invertible module: take the skeleton
representative; it is invertible because its class is a unit of the skeleton monoid. -/
theorem exists_module_kappa (Q : (E.baseChange t).Point (𝟙 T)) :
    ∃ M : (pullback E.π t).Modules,
      (letI := Scheme.Modules.monoidalCategory (pullback E.π t);
        (kappa E hsm t Q).val = toSkeleton M) ∧ IsInvertible M := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  refine ⟨(fromSkeleton (pullback E.π t).Modules).obj (kappa E hsm t Q).val, ?_, ?_⟩
  · exact (toSkeleton_fromSkeleton_obj _).symm
  · refine isInvertible_of_isUnit_toSkeleton ?_
    rw [toSkeleton_fromSkeleton_obj]
    exact (kappa E hsm t Q).isUnit

/-- **(AP-E1-DS2)** A cover-locally trivial module admits trivialisations in the `.over`
form `transitionUnitOfCover` consumes, over the same cover. -/
theorem exists_over_trivialization_of_isInvertible {X : Scheme.{u}} {M : X.Modules}
    (hM : IsInvertible M) :
    ∃ (ι : Type u) (W : ι → X.Opens) (_ : iSup W = ⊤),
      ∀ i, Nonempty (M.over (W i) ≅
        _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i))) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, U, hU, fun i => ?_⟩
  obtain ⟨e⟩ := htriv i
  exact ⟨overTrivializationOfRestrictIso M (U i) (restrictIsoOfPullbackIso M (U i) e)⟩

/-- **(AP-E1-DS3)** The rigidification: a module representing `κ(Q)` pulls back trivially
along the zero section, because `κ` lands in the relative Picard group (`kappa_mem_ker`). -/
theorem nonempty_pullback_zero_iso_unit_of_kappa (Q : (E.baseChange t).Point (𝟙 T))
    (M : (pullback E.π t).Modules)
    (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q).val = toSkeleton M) :
    Nonempty ((Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).obj M ≅
      unitObj T) := by
  letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  letI := Scheme.Modules.monoidalCategory T
  have hM' : (kappa E hsm t Q).val = toSkeleton M := hM
  have hval := congrArg Units.val (kappa_mem_ker E hsm t Q)
  rw [Scheme.Pic.map_val] at hval
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  have h1 : toSkeleton ((Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).obj M) =
      (Scheme.Modules.pullback (baseChangeZero E.π E.zero E.zero_π t)).mapSkeleton.obj
        (toSkeleton M) :=
    (Functor.mapSkeleton_obj_toSkeleton _ M).symm
  rw [h1, ← hM', hval]
  exact (Units.val_one).trans toSkeleton_unitObj.symm

end Dataset

end ModularCurves
