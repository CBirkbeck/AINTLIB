/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential

/-!
# ω-adapted Weierstrass models (T-E12, KM 2.2.5)

**(T-E12 `/develop --decompose` 2026-07-14, STREAM-OMEGA — board [T-E12].)**

The **basis unit** of a chart presentation: an `S`-basis `b` of `ω_{E/S}` compares to
the standard chart differential of any local Weierstrass presentation `P` by a unique
unit `basisUnitAt P b ∈ Γ(V)ˣ` — glued from `b`'s atlas components twisted by the
chart-comparison transition units. A presentation is **`b`-adapted** when this unit
is `1`: KM 2.2.5's "Weierstrass model adapted to ω", chart-locally.

This is the layer that makes the KM 4.6.2 Legendre problem statable (its adaptedness
condition `x(P₂) = 0, x(Q₂) = 1` refers to an adapted model — board correction
2026-07-14) and drives T-E12's `(g₂, g₃)`-normalisation: over `ℤ[1/6]` every `(E, ω)`
has unique adapted short-normal-form presentations (E12-B), whose coefficients glue to
the classifying map into `M₁ = Spec ℤ[1/6][g₂, g₃][Δ⁻¹]` (E12-C/D).

Stage 1 (`basisUnitOn`): glue the data over a fixed chart-overlap `V ⊓ U i` from its
affine subopens (`exists_unit_glue`). Stage 2 (`basisUnitAt`): glue over the atlas.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme

namespace ModularCurves

namespace LocalPresentation

variable {S : Scheme.{u}} {G : EllipticCurveGeom S}

open Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-A, stage 1)** The basis unit of `P` against `b` over the part of `P`'s
domain inside atlas chart `i`: on every affine `W ≤ V ⊓ U i` it is
`b`'s `i`-component (a unit, restricted) times the chart comparison
`transUnit (P|_W) (Pᵢ|_W)`. -/
noncomputable def basisUnitOn {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) (i : G.atlas.ι) :
    { g : Γ(S, V.1 ⊓ (G.atlas.U i).1)ˣ //
      ∀ (W : S.affineOpens) (hW : W.1 ≤ V.1 ⊓ (G.atlas.U i).1),
        Scheme.resUnit hW g =
          Scheme.resUnit (le_inf le_top (hW.trans inf_le_right)) (b.2 i).unit *
          ((P.restrict (hW.trans inf_le_left)).transUnit
            ((G.atlas.presentation i).restrict (hW.trans inf_le_right))) } := by
  have hglue := Scheme.exists_unit_glue S (V.1 ⊓ (G.atlas.U i).1)
    (fun W hW =>
      Scheme.resUnit (le_inf le_top (hW.trans inf_le_right)) (b.2 i).unit *
      ((P.restrict (hW.trans inf_le_left)).transUnit
        ((G.atlas.presentation i).restrict (hW.trans inf_le_right))))
    (fun W W' hW h => by
      rw [map_mul, Scheme.resUnit_resUnit, ← transUnit_restrict _ _ h,
        transUnit_restrict_restrict])
  exact ⟨hglue.choose, hglue.choose_spec.1⟩

end LocalPresentation

end ModularCurves
