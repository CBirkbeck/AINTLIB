/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.Bootstrap
import ModularCurves.Moduli.QuotientStack
import ModularCurves.ForMathlib.EtaleSectionsCount

/-!
# The level-4 `TorsorData` package (STREAM-E4, E4-B)

**(B2 resolution of record — board v10.342.)** KM 4.7.0's engine axiom 2 for
`δ = ` naive level 4: for every `E/S` with `2` invertible, the relative level-4 space is
a finite étale `GL₂(ℤ/4)`-torsor under the genuine global re-marking action
`gammaFullNaiveGlAction R 4`.

Per the LevelThreeTorsor generality audit (decomposition-e4.md §3): every mathematical
component is already general-`N` or general-group — `gammaFullNaive_relRepData`,
`isFinite_fullLevelSpaceStruct`, `levelSpaceΓπ_etale`, `gammaFullNaiveGl_freeAction`,
`exists_isNaiveFullLevel_of_isAlgClosed`, `exists_glSmul_eq` (needs `2 ≤ N`),
`glSmul_eq_one_of_eq_self`, and the abstract torsor-iso engine
`isIso_torsorSigmaDesc_of_existsUnique` (any finite group, any finite-étale morphism).
The rank-two torsion input `addEquiv_pi_fin_two_zmod_of_natCard` is pure group theory —
**no `ZMod 4`-vs-field obstruction exists**. This file's ticket (E4B) copies the ~10
`levelThree*` wrappers of `Moduli/LevelThreeTorsor.lean` at `N = 4`, keeping the
γ⁻¹-twisted equivariance convention ([B2-TD-CONV]) and the `ULift`/`MulEquiv.ulift`/
`Sigma.whiskerEquiv` universe transport for the `Type u` export.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits Scheme

/-- **(E4B, Type-0 export)** The level-4 `TorsorData` package at universe zero: the
naive level-4 problem's relative representing scheme is a finite étale
`GL₂(ℤ/4)`-torsor under the global re-marking action. Mirror of
`exists_levelThreeTorsorData`. -/
theorem exists_levelFourTorsorData (R : CommRingCat.{0}) (hinv : IsUnit (4 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData (gammaFullNaiveGlAction R 4) X) := by sorry

/-- **(E4B, the `Type u` export consumed by the engine's D(2) leg)** The level-4
`TorsorData` package with the group `ULift`ed to `Type u`. Mirror of
`exists_levelThreeTorsorData_ulift`. -/
theorem exists_levelFourTorsorData_ulift (R : CommRingCat.{u}) (hinv : IsUnit (4 : R))
    (X : EllObj R) :
    Nonempty (ModuliProblem.TorsorData
      ((gammaFullNaiveGlAction R 4).comp MulEquiv.ulift.toMonoidHom) X) := by sorry

end ModularCurves
