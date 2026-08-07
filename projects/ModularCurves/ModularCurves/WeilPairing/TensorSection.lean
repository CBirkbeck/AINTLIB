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

end ModularCurves
