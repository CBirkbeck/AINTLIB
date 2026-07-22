/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.EngineMouth
import ModularCurves.Moduli.LevelThreeTorsor
import ModularCurves.Moduli.LevelFourTorsor
import ModularCurves.Moduli.UniversalLevelFour
import ModularCurves.Moduli.Recollement
import ModularCurves.Moduli.Bootstrap

/-!
# [:324 WIRING] The KM 4.7.0 engine ⇐ direction, downstream of the mouth + torsor packages

`representable_iff_rigidNoeth` (`Moduli/EllCategory.lean`) cannot be proven in place — its
proof needs the engine mouth (`representable_of_rigidNoeth_of_torsor`), the two `TorsorData`
packages (`exists_levelThreeTorsorData_ulift`, `exists_legendreTorsorData_ulift`), and the
recollement (`representable_of_baseChange_cover`), all of which live *downstream* of
`EllCategory` — proving it there would be an import cycle. This file, downstream of all of
them, proves the ⇐ direction as `representable_of_affineOverEll_of_rigidNoeth`; the receipt
sites re-point here.

The two torsor legs `ULift` their `Type 0` groups to `Type u` (the universe wall of
`TorsorData`), instantiate the mouth twice (level 3 over `R[1/3]`, Legendre over `R[1/2]`),
and glue by recollement over `D(2) ∪ D(3) = Spec R` (`-1·2 + 1·3 = 1`).
-/

universe u
open CategoryTheory AlgebraicGeometry ModularCurves ModularCurves.ModuliProblem

namespace ModularCurves.ModuliProblem

/-- The base-change map along the localization at `a` (`R ⟶ R[1/a]`). -/
noncomputable def awayHomWire (R : CommRingCat.{u}) (a : R) :
    R ⟶ CommRingCat.of (Localization.Away a) :=
  CommRingCat.ofHom (algebraMap R (Localization.Away a))

/-- **[:324 ⇐, D(3) leg]** representability over `R[1/3]` via the level-3 `GL₂(𝔽₃)`-torsor
engine (`exists_levelThreeTorsorData_ulift`). -/
theorem representable_baseChange_three (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.AffineOverEll) (hrig : P.RigidNoeth) :
    (P.baseChange (awayHomWire R 3)).Representable := by
  set R3 := CommRingCat.of (Localization.Away (3:R)) with hR3
  have hinv3 : IsUnit (3 : R3) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (3:R)) (3 : R)
    rw [map_ofNat] at h; exact h
  haveI : Finite (ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) := inferInstance
  set φ3 : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) →*
      Aut (gammaFullNaiveProblem R3 3) :=
    (gammaFullNaiveGlAction R3 3).comp MulEquiv.ulift.toMonoidHom with hφ3
  obtain ⟨X0, hX0aff, ⟨rX0⟩⟩ := naiveLevelThree_representable_by_affine R3 hinv3
  have hQaff3 : ∀ {XQ : EllObj R3},
      (gammaFullNaiveProblem R3 3).RepresentableBy XQ → IsAffine XQ.base := by
    intro XQ rXQ; haveI := hX0aff
    let e : XQ ≅ X0 := rXQ.uniqueUpToIso rX0
    haveI : IsIso e.hom.baseHom := ⟨e.inv.baseHom,
      congrArg EllHom.baseHom e.hom_inv_id, congrArg EllHom.baseHom e.inv_hom_id⟩
    exact IsAffine.of_isIso e.hom.baseHom
  have hPaff3 : ∀ X : EllObj R3,
      ∃ d : RelRepData (P.baseChange (awayHomWire R 3)) X, IsAffineHom d.f := by
    intro X
    obtain ⟨Z, f, hf, eqv, nat⟩ := AffineOverEll.baseChange (awayHomWire R 3) hP X
    exact ⟨⟨Z, f, eqv, nat⟩, hf⟩
  exact representable_of_rigidNoeth_of_torsor (P.baseChange (awayHomWire R 3))
    (gammaFullNaiveProblem R3 3) φ3 ⟨⟨X0, ⟨rX0⟩⟩⟩ hQaff3 hPaff3
    (fun X => exists_levelThreeTorsorData_ulift R3 hinv3 X)
    (RigidNoeth.baseChange (awayHomWire R 3) hrig)

/-- **[:324 ⇐, D(2) leg]** representability over `R[1/2]` via the level-4
`GL₂(ℤ/4)`-torsor engine (`exists_levelFourTorsorData_ulift` over the genuine global
re-marking action `gammaFullNaiveGlAction R 4`, with the `ℰ₄` bootstrap object
`naiveLevelFour_representable_by_affine` as KM axiom 1) — the B2 resolution of record
(board v10.342/v10.343, b2_log `B2-DECISION`): the Legendre instantiation is quarantined
(`legendreDeltaGAction` is impossible — KM 4.6.2's constant-group torsor claim fails; the
honest Legendre torsor group is a twisted `μ₂`-extension). -/
theorem representable_baseChange_two (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.AffineOverEll) (hrig : P.RigidNoeth) :
    (P.baseChange (awayHomWire R 2)).Representable := by
  set R2 := CommRingCat.of (Localization.Away (2:R)) with hR2
  have hinv2 : IsUnit (2 : R2) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (2:R)) (2 : R)
    rw [map_ofNat] at h; exact h
  have hinv4 : IsUnit (4 : R2) := by
    have := hinv2.mul hinv2
    rwa [show (2 : R2) * 2 = 4 by norm_num] at this
  haveI : Finite (ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4))) := inferInstance
  set φ4 : ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod 4)) →*
      Aut (gammaFullNaiveProblem R2 4) :=
    (gammaFullNaiveGlAction R2 4).comp
      (MulEquiv.ulift (α := Matrix.GeneralLinearGroup (Fin 2) (ZMod 4))).toMonoidHom with hφ4
  obtain ⟨X0, hX0aff, ⟨rX0⟩⟩ := naiveLevelFour_representable_by_affine R2 hinv2
  have hQaff4 : ∀ {XQ : EllObj R2},
      (gammaFullNaiveProblem R2 4).RepresentableBy XQ → IsAffine XQ.base := by
    intro XQ rXQ; haveI := hX0aff
    let e : XQ ≅ X0 := rXQ.uniqueUpToIso rX0
    haveI : IsIso e.hom.baseHom := ⟨e.inv.baseHom,
      congrArg EllHom.baseHom e.hom_inv_id, congrArg EllHom.baseHom e.inv_hom_id⟩
    exact IsAffine.of_isIso e.hom.baseHom
  have hPaff2 : ∀ X : EllObj R2,
      ∃ d : RelRepData (P.baseChange (awayHomWire R 2)) X, IsAffineHom d.f := by
    intro X
    obtain ⟨Z, f, hf, eqv, nat⟩ := AffineOverEll.baseChange (awayHomWire R 2) hP X
    exact ⟨⟨Z, f, eqv, nat⟩, hf⟩
  exact representable_of_rigidNoeth_of_torsor (P.baseChange (awayHomWire R 2))
    (gammaFullNaiveProblem R2 4) φ4 ⟨⟨X0, ⟨rX0⟩⟩⟩ hQaff4 hPaff2
    (fun X => exists_levelFourTorsorData_ulift R2 hinv4 X)
    (RigidNoeth.baseChange (awayHomWire R 2) hrig)

/-- **[:324 ⇐, the KM 4.7.0 SCHOLIE engine]** affine-over-`(Ell)` + relatively representable +
noetherian-local rigidity ⟹ representable. The engine of Katz–Mazur pp. 112–116, instantiated
at `δ = ` naive level 3 (`GL₂(𝔽₃)`, over `R[1/3]`) and `δ = ` Legendre (`GL₂(𝔽₂)×ℤˣ`, over
`R[1/2]`), glued by recollement over the cover `D(2) ∪ D(3) = Spec R`. This is the proven form
of `representable_iff_rigidNoeth`'s ⇐; the receipts re-point here. -/
theorem representable_of_affineOverEll_of_rigidNoeth {R : CommRingCat.{u}} (P : ModuliProblem R)
    (hP : P.AffineOverEll) (hrel : P.RelativelyRepresentable) (hrig : P.RigidNoeth) :
    P.Representable :=
  representable_of_baseChange_cover P 2 3 ⟨-1, 1, by ring⟩ hrel
    (representable_baseChange_two R P hP hrig)
    (representable_baseChange_three R P hP hrig)


/-- **[Y0-AFF3] `∃`-affine form of the D(3) leg.** -/
theorem exists_representableBy_isAffine_baseChange_three (R : CommRingCat.{u})
    (P : ModuliProblem R) (hP : P.AffineOverEll) (hrig : P.RigidNoeth) :
    ∃ X₀ : EllObj (CommRingCat.of (Localization.Away (3 : R))),
      IsAffine X₀.base ∧
      Nonempty ((P.baseChange (awayHomWire R 3)).RepresentableBy X₀) := by
  sorry

/-- **[Y0-AFF2] `∃`-affine form of the D(2) leg.** -/
theorem exists_representableBy_isAffine_baseChange_two (R : CommRingCat.{u})
    (P : ModuliProblem R) (hP : P.AffineOverEll) (hrig : P.RigidNoeth) :
    ∃ X₀ : EllObj (CommRingCat.of (Localization.Away (2 : R))),
      IsAffine X₀.base ∧
      Nonempty ((P.baseChange (awayHomWire R 2)).RepresentableBy X₀) := by
  sorry

end ModularCurves.ModuliProblem
