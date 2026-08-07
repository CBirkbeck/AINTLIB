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

Fill recipe (4 cycles spent, capped): the blocker is `TensorProduct.smul_tmul'` needing
`SMulCommClass` over the `forget₂`-ring — supply it locally exactly as `evPre` does
(`Picard/Evaluation.lean:178-184`, the three-line `letI : SMulCommClass … := ⟨fun a b c => by
show a * (b * c) = b * (a * c); rw [← mul_assoc, mul_comm' a b, mul_assoc]⟩`), retype `r` by
`show ↑((T.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) from r`, then
`rw [key]; exact map_smul _ _ _`. Cycle-6 findings (2026-08-07): additionally needed —
`dsimp only [CategoryTheory.Functor.id_obj]` after `unfold` (the `𝟭`-wrapper blocks the carrier's
SMul instance), and `letI : Module forget₂carrier ↑Γ(A,U) := inferInstanceAs (Module ↑Γ(T,U) _)` (+ the
`B` twin): `Γ(A,U)`'s module instance is keyed on the CommRingCat carrier, `smul_tmul'` wants the
forget₂ one; the rings are defeq so `inferInstanceAs` bridges. Cycle-8 finding: after those, TWO blockers remain —
(i) `smul_tmul'` asks a MIXED `SMulCommClass forget₂ring ↑Γ(T,U) ↑Γ(A,U)` because the statement's
`r • a` is Γ(T,U)-keyed: first rewrite `(r • a) = ((show forget₂ from r) • a)` by `rfl`, THEN
`smul_tmul'`; (ii) the tensor carrier's `SMul forget₂ring carrier` is keyed on
`T.ringCatSheaf.obj.obj (op U)`, not on the `(T.sheaf.obj ⋙ forget₂ …)` spelling — bridge with one more
`inferInstanceAs`, or restate the lemmas with `r : ↑(T.ringCatSheaf.obj.obj (op U))` and add Γ-form
`rfl`-wrappers. Consider also proving a single `tensorSection_units_cancel`
(`tensorSection (u•x) (u⁻¹•y) = tensorSection x y`) instead — it is all `hcompat` consumes. -/
theorem tensorSection_smul_left {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U (r • a) b = r • tensorSection A B U a b := by
  sorry

/-- Scalars move out of the second slot of `tensorSection`. Same fill recipe as
`tensorSection_smul_left`, with `TensorProduct.smul_tmul` bridging the slots. -/
theorem tensorSection_smul_right {T : Scheme.{u}} (A B : T.Modules) (U : T.Opens)
    (r : ↑Γ(T, U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    tensorSection A B U a (r • b) = r • tensorSection A B U a b := by
  sorry

end ModularCurves
