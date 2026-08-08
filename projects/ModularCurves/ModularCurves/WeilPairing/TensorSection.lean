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

/-- Scalars move out of the first slot of `tensorSection`.

Fill status (19 probe-cycles, capped 2026-08-08): the underlying facts are two one-liners —
`(r • a) ⊗ₜ b = r' • (a ⊗ₜ b)` in `(A.val ⊗ B.val).obj (op U)` and `map_smul` of the
sheafification-unit component — but the instance alignment is expert-grade. New findings
(cycles 17–19, this file's history has 1–16): (i) THREE carrier spellings circulate —
`↑Γ(A,U)` (statement, mathlib `Module Γ(T,U) Γ(A,U)` from `Modules/Sheaf.lean:94`),
`↑(A.val.obj (op U))` (isModule keyed at `T.ringCatSheaf.obj.obj`), and the tensor's internal
`(T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj` (mathlib registers `CommRing` there,
`Presheaf/Monoidal.lean:34`); `inferInstanceAs`-letIs bridge Module across spellings BUT
(ii) `TensorProduct.smul_tmul'` then demands `SMulCommClass` KEYED on the monoidal structure's
internal instance terms, which letI-fvar instances never match — synthesis fails even with all
bridges in place. (iii) The composed-linear-map route (`map_smul` of
`(hom unit-component).comp ((TensorProduct.mk …).flip b)`) fails earlier: `comp` cannot unify
the `𝟭`-wrapped unit-component source with the `TensorProduct`-typed mk target.
NEXT TOOLS for a fresh pass: `dsimp +instances` (mathlib's own `tensorObjMap` proofs use it to
normalise exactly these instance diamonds, `Presheaf/Monoidal.lean:44-57`), possibly under
`set_option backward.isDefEq.respectTransparency false`; or prove a `tensor_ext`-mate through
`ModuleCat.MonoidalCategory.tensorLift`. Consumers wired: `hcompat` (proved, cites the pair)
and `hbij` (route recipe on the board). -/
theorem tensorSection_smul_left {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U (r • a) b = r • tensorSection A B U a b := by
  sorry

/-- Scalars move out of the second slot of `tensorSection`. Same status and recipe as
`tensorSection_smul_left`, with `TensorProduct.tmul_smul` bridging the slots. -/
theorem tensorSection_smul_right {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U a (r • b) = r • tensorSection A B U a b := by
  sorry

end ModularCurves
