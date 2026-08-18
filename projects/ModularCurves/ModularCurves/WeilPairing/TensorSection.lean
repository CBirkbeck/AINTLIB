/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.InvertibleSheaf

/-!
# Sections of the sheafified tensor product (`AP2-B1a-iii`)

`tensorObj A B` is the sheafification of the presheaf tensor (`Picard/InvertibleSheaf.lean:71`), whose
per-open value is the module tensor `Γ(A,U) ⊗[Γ(T,U)] Γ(B,U)` — the constructor `evPre`
(`Picard/Evaluation.lean:170`) computes against. This file exposes the missing sections API: the image
of `a ⊗ₜ b` under the sheafification unit, with its restriction naturality. Consumed by `AP2-B1a`'s
glue obligation (`WeilPairing/RelPicLocal.lean`).
-/

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite
open scoped TensorProduct

namespace ModularCurves

/-- The `⊗ₜ`-section of the sheafified tensor product: the image of `a ⊗ₜ b` under the
sheafification unit's component at `U`. -/
noncomputable def tensorSection {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    Γ(AlgebraicGeometry.Scheme.Modules.tensorObj A B, U) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U) (a ⊗ₜ b)

/-- `tensorSection` is natural in the open: restriction of a `⊗ₜ`-section is the `⊗ₜ`-section of the
restrictions.

Proof shape (goal read via LSP, 2026-08-07): the sheafification unit's `.naturality (homOfLE h).op`
gives `unit_{U'} ∘ (A.val ⊗ B.val).map = (sheafified).map ∘ unit_U` **through `restrictScalars`
conjugation** (PresheafOfModules maps between opens are restrictScalars-conjugated); the two remaining
unfoldings are (i) `(A.tensorObj B).presheaf.map = (sheafified …).map` on elements and (ii) the
presheaf-tensor restriction on a pure tensor `(A.val ⊗ B.val).map h (a ⊗ₜ b) = map a ⊗ₜ map b`
(the `ModuleCat` monoidal `tensorHom`/`map_tmul` family + restrictScalars). Mechanical; names to hunt:
`PresheafOfModules` tensor `map_tmul`-shaped simp lemmas. -/
theorem tensorSection_restrict {T : Scheme.{u}} (A B : T.Modules) {U' U : T.Opens} (h : U' ≤ U)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorObj A B).presheaf.map (homOfLE h).op
        (tensorSection A B U a b) =
      tensorSection A B U' (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) := by
  have h1 := ConcreteCategory.congr_hom
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).naturality (homOfLE h).op)
    (show ↑((A.val ⊗ B.val).obj (op U)) from a ⊗ₜ b)
  simp only [tensorSection]
  exact h1.symm

/-- Scalars move out of the first slot of `tensorSection`. Proved (probe 20, 2026-08-08) by the
`dsimp +instances` normalisation mathlib's own `tensorObjMap` proofs use
(`Presheaf/Monoidal.lean:44-57`): after normalising the instance diamonds, `erw` closes over the
defeq scalar spellings. -/
theorem tensorSection_smul_left {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U (r • a) b = r • tensorSection A B U a b := by
  have h1 : ((r • a) ⊗ₜ b : ↑((A.val ⊗ B.val).obj (op U))) =
      (show ↑((T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) from r) •
        ((a ⊗ₜ b : ↑((A.val ⊗ B.val).obj (op U)))) := by
    dsimp +instances
    erw [TensorProduct.smul_tmul']
    rfl
  have h2 : tensorSection A B U (r • a) b =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U)
        ((show ↑((T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) from r) •
          ((a ⊗ₜ b : ↑((A.val ⊗ B.val).obj (op U))))) :=
    congrArg (fun z : ↑((A.val ⊗ B.val).obj (op U)) =>
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U) z) h1
  refine h2.trans ?_
  exact map_smul (CategoryTheory.ConcreteCategory.hom
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U))) _ _

/-- Scalars move out of the second slot of `tensorSection`. The heterogeneous
`TensorProduct.tmul_smul` route demands an unsynthesisable mixed `CompatibleSMul`; instead seed
with `one_smul` and use the homogeneous `smul_tmul_smul`, closing the `1 * r` residue with
`congr 1` (which reuses the goal's own instance where no tactic can rebuild it). -/
theorem tensorSection_smul_right {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U a (r • b) = r • tensorSection A B U a b := by
  have h1 : ((a ⊗ₜ (r • b)) : ↑((A.val ⊗ B.val).obj (op U))) =
      (show ↑((T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) from r) •
        ((a ⊗ₜ b : ↑((A.val ⊗ B.val).obj (op U)))) := by
    dsimp +instances
    conv_lhs => rw [← one_smul ↑Γ(T, U) a]
    erw [TensorProduct.smul_tmul_smul]
    congr 1
    exact one_mul r
  have h2 : tensorSection A B U a (r • b) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U)
        ((show ↑((T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) from r) •
          ((a ⊗ₜ b : ↑((A.val ⊗ B.val).obj (op U))))) :=
    congrArg (fun z : ↑((A.val ⊗ B.val).obj (op U)) =>
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U) z) h1
  refine h2.trans ?_
  exact map_smul (CategoryTheory.ConcreteCategory.hom
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app (A.val ⊗ B.val)).app (op U))) _ _

end ModularCurves
