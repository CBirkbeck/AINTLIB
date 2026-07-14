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

open Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(E12-A)** The per-chart basis units agree on chart overlaps: the `b`-compatibility
cocycle is exactly the chart-comparison cocycle (`omegaCocycle_res`), and the
comparisons compose (`transUnit_trans`). -/
private theorem basisUnitOn_agree {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) (i j : G.atlas.ι) (W : S.affineOpens)
    (hWi : W.1 ≤ V.1 ⊓ (G.atlas.U i).1) (hWj : W.1 ≤ V.1 ⊓ (G.atlas.U j).1) :
    Scheme.resUnit hWi (P.basisUnitOn b i).1 =
      Scheme.resUnit hWj (P.basisUnitOn b j).1 := by
  rw [(P.basisUnitOn b i).2 W hWi, (P.basisUnitOn b j).2 W hWj]
  -- the `b`-cocycle compatibility, as units over `W`
  have hb : Scheme.resUnit (le_inf le_top (hWi.trans inf_le_right)) (b.2 i).unit =
      ((P.restrict (hWi.trans inf_le_left)).transUnit
          ((G.atlas.presentation i).restrict (hWi.trans inf_le_right)))⁻¹ *
        ((P.restrict (hWj.trans inf_le_left)).transUnit
          ((G.atlas.presentation j).restrict (hWj.trans inf_le_right))) *
        Scheme.resUnit (le_inf le_top (hWj.trans inf_le_right)) (b.2 j).unit := by
    -- value level: b's compatibility restricted to `W`, with the cocycle read as
    -- the chart comparison
    have hcompat := congrArg (⇑(Scheme.resLE (X := S)
      (show W.1 ≤ (⊤ : S.Opens) ⊓ (omegaCocycle G).U i ⊓ (omegaCocycle G).U j from
        le_inf (le_inf le_top (hWi.trans inf_le_right)) (hWj.trans inf_le_right))))
      (b.1.2 i j)
    simp only [Scheme.resUnit_val, Scheme.resLE_resLE, map_mul] at hcompat
    have hcoc := congrArg Units.val (omegaCocycle_res G i j W
      (le_inf (hWi.trans inf_le_right) (hWj.trans inf_le_right)))
    simp only [Scheme.resUnit_val, Scheme.resLE_resLE] at hcoc
    have htrans := congrArg Units.val (transUnit_trans
      (P.restrict (hWi.trans inf_le_left))
      ((G.atlas.presentation i).restrict (hWi.trans inf_le_right))
      ((G.atlas.presentation j).restrict (hWj.trans inf_le_right)))
    -- assemble at the value level
    refine Units.ext ?_
    simp only [Units.val_mul, Scheme.resUnit_val]
    rw [show ((b.2 i).unit : Γ(S, (⊤ : S.Opens) ⊓ (omegaCocycle G).U i)) = b.1.1 i from
        (b.2 i).unit_spec,
      show ((b.2 j).unit : Γ(S, (⊤ : S.Opens) ⊓ (omegaCocycle G).U j)) = b.1.1 j from
        (b.2 j).unit_spec]
    -- hcompat : b_i|_W = u_{ij}|_W · b_j|_W (values)
    rw [show Scheme.resLE (le_inf le_top (hWi.trans inf_le_right)) (b.1.1 i) =
        Scheme.resLE (le_inf (hWi.trans inf_le_right) (hWj.trans inf_le_right))
          ((omegaCocycle G).u i j).val *
        Scheme.resLE (le_inf le_top (hWj.trans inf_le_right)) (b.1.1 j) from hcompat]
    rw [hcoc]
    -- now: tU(Pᵢ|)(Pⱼ|)·b_j| = tU(P|Pᵢ|)⁻¹·tU(P|Pⱼ|)·b_j|; cancel via transUnit_trans
    have := congrArg
      (fun t => (((P.restrict (hWi.trans inf_le_left)).transUnit
        ((G.atlas.presentation i).restrict (hWi.trans inf_le_right)))⁻¹ : _).val * t)
      htrans
    simp only [Units.val_mul] at this
    rw [← mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_left] at this
    rw [← mul_assoc, ← this]
    ring
  rw [hb]
  ring

open Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(E12-A, KM 2.2.5)** The **basis unit** of a presentation: the unique unit of
`Γ(V)` comparing the `ω`-basis `b` with the standard chart differential of `P` —
glued over the atlas from `basisUnitOn`. -/
noncomputable def basisUnitAt {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) :
    { g : Γ(S, V.1)ˣ // ∀ (i : G.atlas.ι),
        Scheme.resUnit (inf_le_left : V.1 ⊓ (G.atlas.U i).1 ≤ V.1) g =
          (P.basisUnitOn b i).1 } := by
  classical
  set 𝒰 : G.atlas.ι → S.Opens := fun i => V.1 ⊓ (G.atlas.U i).1 with h𝒰
  have hcover : V.1 ≤ iSup 𝒰 := by
    intro x hxV
    obtain ⟨i, hxi⟩ := G.atlas.covers x
    exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩
  have hcoverInf : ∀ p q : G.atlas.ι, 𝒰 p ⊓ 𝒰 q ≤
      iSup (fun r : {W : S.affineOpens // W.1 ≤ 𝒰 p ⊓ 𝒰 q} => r.1.1) := by
    intro p q x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible S.sheaf.1 𝒰
      (fun i => ((P.basisUnitOn b i).1 : Γ(S, 𝒰 i))) := by
    intro p q
    refine TopCat.Sheaf.eq_of_locally_eq' S.sheaf
      (fun r : {W : S.affineOpens // W.1 ≤ 𝒰 p ⊓ 𝒰 q} => r.1.1) (𝒰 p ⊓ 𝒰 q)
      (fun r => homOfLE r.2) (hcoverInf p q) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (P.basisUnitOn b p).1.val) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (P.basisUnitOn b q).1.val)
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact congrArg Units.val (basisUnitOn_agree P b p q r.1
      (r.2.trans inf_le_left) (r.2.trans inf_le_right))
  obtain ⟨g₀, hg₀, hg₀uniq⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf 𝒰 V.1
    (fun i => homOfLE inf_le_left) hcover
    (fun i => ((P.basisUnitOn b i).1 : Γ(S, 𝒰 i))) hpair
  have hunit : IsUnit g₀ := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hxV
    obtain ⟨i, hxi⟩ := G.atlas.covers x
    have hgerm : S.presheaf.germ V.1 x hxV g₀ =
        S.presheaf.germ (𝒰 i) x ⟨hxV, hxi⟩
          (Scheme.resLE inf_le_left g₀) := by
      rw [show Scheme.resLE (inf_le_left : 𝒰 i ≤ V.1) g₀ =
        (S.presheaf.map (homOfLE (inf_le_left : 𝒰 i ≤ V.1)).op).hom g₀ from rfl]
      exact (S.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hxV, hxi⟩ g₀).symm
    rw [hgerm, hg₀ i]
    exact ((P.basisUnitOn b i).1.isUnit).map _
  refine ⟨hunit.unit, fun i => Units.ext ?_⟩
  rw [Scheme.resUnit_val, IsUnit.unit_spec]
  exact hg₀ i

/-- **(E12-A, KM 2.2.5)** `P` is **adapted** to the `ω`-basis `b` when its standard
chart differential IS `b`: the basis unit is `1`. -/
def IsAdapted {V : S.affineOpens} (P : LocalPresentation G V) (b : OmegaBasis G) :
    Prop :=
  (P.basisUnitAt b).1 = 1

end LocalPresentation

end ModularCurves
