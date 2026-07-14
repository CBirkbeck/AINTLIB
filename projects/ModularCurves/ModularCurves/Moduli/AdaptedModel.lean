/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
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
  -- `b`'s compatibility over `W`, value level
  have hcompat := congrArg (⇑(Scheme.resLE (X := S)
    (show W.1 ≤ (⊤ : S.Opens) ⊓ (omegaCocycle G).U i ⊓ (omegaCocycle G).U j from
      le_inf (le_inf le_top (hWi.trans inf_le_right)) (hWj.trans inf_le_right))))
    (b.1.2 i j)
  simp only [Scheme.resUnit_val, Scheme.resLE_resLE, map_mul] at hcompat
  -- the cocycle is the chart comparison, value level
  have hcoc := congrArg Units.val (omegaCocycle_res G i j W
    (le_inf (hWi.trans inf_le_right) (hWj.trans inf_le_right)))
  simp only [Scheme.resUnit_val] at hcoc
  -- the comparisons compose, value level
  have htrans := congrArg Units.val (transUnit_trans
    (P.restrict (hWi.trans inf_le_left))
    ((G.atlas.presentation i).restrict (hWi.trans inf_le_right))
    ((G.atlas.presentation j).restrict (hWj.trans inf_le_right)))
  simp only [Units.val_mul] at htrans
  refine Units.ext ?_
  simp only [Units.val_mul, Scheme.resUnit_val]
  rw [show ((b.2 i).unit : Γ(S, (⊤ : S.Opens) ⊓ (omegaCocycle G).U i)) = b.1.1 i from
      (b.2 i).unit_spec,
    show ((b.2 j).unit : Γ(S, (⊤ : S.Opens) ⊓ (omegaCocycle G).U j)) = b.1.1 j from
      (b.2 j).unit_spec]
  rw [show Scheme.resLE (le_inf le_top (hWi.trans inf_le_right)) (b.1.1 i) =
      Scheme.resLE (le_inf (hWi.trans inf_le_right) (hWj.trans inf_le_right))
        ((omegaCocycle G).u i j).val *
      Scheme.resLE (le_inf le_top (hWj.trans inf_le_right)) (b.1.1 j) from hcompat]
  rw [hcoc]
  linear_combination
    Scheme.resLE (le_inf le_top (hWj.trans inf_le_right)) (b.1.1 j) * htrans

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
  have hcover : V.1 ≤ iSup (fun i : G.atlas.ι => V.1 ⊓ (G.atlas.U i).1) := by
    intro x hxV
    obtain ⟨i, hxi⟩ := G.atlas.covers x
    exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩
  have hcoverInf : ∀ p q : G.atlas.ι,
      (V.1 ⊓ (G.atlas.U p).1) ⊓ (V.1 ⊓ (G.atlas.U q).1) ≤
      iSup (fun r : {W : S.affineOpens //
          W.1 ≤ (V.1 ⊓ (G.atlas.U p).1) ⊓ (V.1 ⊓ (G.atlas.U q).1)} => r.1.1) := by
    intro p q x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible S.sheaf.1
      (fun i : G.atlas.ι => V.1 ⊓ (G.atlas.U i).1)
      (fun i => ((P.basisUnitOn b i).1 : Γ(S, V.1 ⊓ (G.atlas.U i).1))) := by
    intro p q
    refine TopCat.Sheaf.eq_of_locally_eq' S.sheaf
      (fun r : {W : S.affineOpens //
          W.1 ≤ (V.1 ⊓ (G.atlas.U p).1) ⊓ (V.1 ⊓ (G.atlas.U q).1)} => r.1.1)
      ((V.1 ⊓ (G.atlas.U p).1) ⊓ (V.1 ⊓ (G.atlas.U q).1))
      (fun r => homOfLE r.2) (hcoverInf p q) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (P.basisUnitOn b p).1.val) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (P.basisUnitOn b q).1.val)
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact congrArg Units.val (basisUnitOn_agree P b p q r.1
      (r.2.trans inf_le_left) (r.2.trans inf_le_right))
  have hglue := TopCat.Sheaf.existsUnique_gluing' S.sheaf
    (fun i : G.atlas.ι => V.1 ⊓ (G.atlas.U i).1) V.1
    (fun i => homOfLE inf_le_left) hcover
    (fun i => ((P.basisUnitOn b i).1 : Γ(S, V.1 ⊓ (G.atlas.U i).1))) hpair
  have hunit : IsUnit hglue.choose := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hxV
    obtain ⟨i, hxi⟩ := G.atlas.covers x
    have hgerm : S.presheaf.germ V.1 x hxV hglue.choose =
        S.presheaf.germ (V.1 ⊓ (G.atlas.U i).1) x ⟨hxV, hxi⟩
          (Scheme.resLE inf_le_left hglue.choose) := by
      rw [show Scheme.resLE (inf_le_left : V.1 ⊓ (G.atlas.U i).1 ≤ V.1) hglue.choose =
        (S.presheaf.map
          (homOfLE (inf_le_left : V.1 ⊓ (G.atlas.U i).1 ≤ V.1)).op).hom hglue.choose
        from rfl]
      exact (S.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hxV, hxi⟩
        hglue.choose).symm
    have hspec : Scheme.resLE (inf_le_left : V.1 ⊓ (G.atlas.U i).1 ≤ V.1)
        hglue.choose = (P.basisUnitOn b i).1.val := hglue.choose_spec.1 i
    rw [hgerm, hspec]
    exact ((P.basisUnitOn b i).1.isUnit).map _
  refine ⟨hunit.unit, fun i => Units.ext ?_⟩
  rw [Scheme.resUnit_val, IsUnit.unit_spec]
  exact hglue.choose_spec.1 i

/-- **(E12-A, KM 2.2.5)** `P` is **adapted** to the `ω`-basis `b` when its standard
chart differential IS `b`: the basis unit is `1`. -/
def IsAdapted {V : S.affineOpens} (P : LocalPresentation G V) (b : OmegaBasis G) :
    Prop :=
  (P.basisUnitAt b).1 = 1
open Scheme WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(E12-B)** Twisting scales the basis unit by the `u`-component of the twist:
`basisUnitAt (P.ofVC C) b = C.u · basisUnitAt P b`. -/
theorem basisUnitAt_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) (b : OmegaBasis G) :
    ((P.ofVC C).basisUnitAt b).1 = C.u * (P.basisUnitAt b).1 := by
  -- separation over the chart cover of `V`, then over affines
  refine Scheme.unit_ext_of_res_cover S
    (fun i : G.atlas.ι => V.1 ⊓ (G.atlas.U i).1) (fun i => inf_le_left)
    (fun x hxV => by
      obtain ⟨i, hxi⟩ := G.atlas.covers x
      exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩) (fun i => ?_)
  rw [((P.ofVC C).basisUnitAt b).2 i, map_mul, (P.basisUnitAt b).2 i]
  refine Scheme.unit_ext_of_affine_res S (fun W hW => ?_)
  rw [((P.ofVC C).basisUnitOn b i).2 W hW, map_mul, Scheme.resUnit_resUnit,
    (P.basisUnitOn b i).2 W hW]
  -- the twisted comparison splits off `C.u` (`transUnit_trans` +
  -- `transVC_restrict_ofVC` + `transVC_ofVC`-restricted)
  have hsplit : ((P.ofVC C).restrict (hW.trans inf_le_left)).transUnit
      ((G.atlas.presentation i).restrict (hW.trans inf_le_right)) =
    ((P.ofVC C).restrict (hW.trans inf_le_left)).transUnit
      (P.restrict (hW.trans inf_le_left)) *
    (P.restrict (hW.trans inf_le_left)).transUnit
      ((G.atlas.presentation i).restrict (hW.trans inf_le_right)) :=
    (transUnit_trans _ _ _).symm
  have hu : ((P.ofVC C).restrict (hW.trans inf_le_left)).transUnit
      (P.restrict (hW.trans inf_le_left)) =
    Scheme.resUnit (hW.trans inf_le_left) C.u := by
    rw [transUnit, transVC_restrict_ofVC]
    rfl
  rw [hsplit, hu]
  exact mul_left_comm _ _ _

/-- **(E12-B)** The canonical adaptation: twist by the inverse basis unit. -/
noncomputable def adapt {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) : LocalPresentation G V :=
  P.ofVC ⟨((P.basisUnitAt b).1)⁻¹, 0, 0, 0⟩

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B ★)** The canonical adaptation IS adapted: every `(E, ω)` admits an
`ω`-adapted Weierstrass presentation over every chart-supported affine — the
existence half of KM 2.2.5. -/
theorem isAdapted_adapt {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) : (P.adapt b).IsAdapted b := by
  show ((P.adapt b).basisUnitAt b).1 = 1
  rw [show P.adapt b = P.ofVC ⟨((P.basisUnitAt b).1)⁻¹, 0, 0, 0⟩ from rfl,
    basisUnitAt_ofVC]
  exact inv_mul_cancel _

open Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(E12-B)** The basis unit is a `transUnit`-cocycle in the presentation: comparing
through any second presentation over the same affine splits off their comparison
unit. -/
theorem basisUnitAt_transUnit {V : S.affineOpens} (P Q : LocalPresentation G V)
    (b : OmegaBasis G) :
    (P.basisUnitAt b).1 = P.transUnit Q * (Q.basisUnitAt b).1 := by
  refine Scheme.unit_ext_of_res_cover S
    (fun i : G.atlas.ι => V.1 ⊓ (G.atlas.U i).1) (fun i => inf_le_left)
    (fun x hxV => by
      obtain ⟨i, hxi⟩ := G.atlas.covers x
      exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩) (fun i => ?_)
  rw [(P.basisUnitAt b).2 i, map_mul, (Q.basisUnitAt b).2 i]
  refine Scheme.unit_ext_of_affine_res S (fun W hW => ?_)
  rw [(P.basisUnitOn b i).2 W hW, map_mul, Scheme.resUnit_resUnit,
    (Q.basisUnitOn b i).2 W hW]
  have hsplit : (P.restrict (hW.trans inf_le_left)).transUnit
      ((G.atlas.presentation i).restrict (hW.trans inf_le_right)) =
    (P.restrict (hW.trans inf_le_left)).transUnit
      (Q.restrict (hW.trans inf_le_left)) *
    (Q.restrict (hW.trans inf_le_left)).transUnit
      ((G.atlas.presentation i).restrict (hW.trans inf_le_right)) :=
    (transUnit_trans _ _ _).symm
  rw [hsplit, transUnit_restrict P Q (hW.trans inf_le_left)]
  exact mul_left_comm _ _ _

/-- **(E12-B, KM 2.2.5 uniqueness half)** Two `b`-adapted presentations over the same
affine compare by a variable change of unit `1`: the `ω`-datum pins the model up to
the translations `(r, s, t)`. -/
theorem transUnit_eq_one_of_isAdapted {V : S.affineOpens}
    {P Q : LocalPresentation G V} {b : OmegaBasis G}
    (hP : P.IsAdapted b) (hQ : Q.IsAdapted b) : P.transUnit Q = 1 := by
  have h := basisUnitAt_transUnit P Q b
  rw [hP, hQ, mul_one] at h
  exact h.symm

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B ★, KM 2.2.5 uniqueness)** Over a base with `2` and `3` invertible, two
`b`-adapted short-normal-form presentations over the same affine have EQUAL comparison:
the `ω`-datum pins `u = 1` and short normal form pins the translations. Hence the
`(g₂, g₃)`-normalised adapted model is unique. -/
theorem transVC_eq_one_of_isAdapted {V : S.affineOpens}
    {P Q : LocalPresentation G V} {b : OmegaBasis G}
    (hP : P.IsAdapted b) (hQ : Q.IsAdapted b)
    (hPW : P.W.IsShortNF) (hQW : Q.W.IsShortNF)
    (h2 : IsUnit (2 : Γ(S, V.1))) (h3 : IsUnit (3 : Γ(S, V.1))) :
    P.transVC Q = 1 := by
  have hu : (P.transVC Q).u = 1 := transUnit_eq_one_of_isAdapted hP hQ
  have hsmul := P.transVC_smul Q
  set C := P.transVC Q with hC
  -- coefficient equations of `C • Q.W = P.W` in short normal form
  have ha₁ : C.u⁻¹.val * (Q.W.a₁ + 2 * C.s) = P.W.a₁ := by
    rw [← variableChange_a₁, hsmul]
  have hs : C.s = 0 := by
    rw [hPW.a₁, hQW.a₁, hu, inv_one, Units.val_one, one_mul, zero_add] at ha₁
    exact (h2.mul_right_eq_zero).mp ha₁
  have ha₃ : C.u⁻¹.val ^ 3 * (Q.W.a₃ + C.r * Q.W.a₁ + 2 * C.t) = P.W.a₃ := by
    rw [← variableChange_a₃, hsmul]
  have ha₂ : C.u⁻¹.val ^ 2 * (Q.W.a₂ - C.s * Q.W.a₁ + 3 * C.r - C.s ^ 2) = P.W.a₂ := by
    rw [← variableChange_a₂, hsmul]
  have hr : C.r = 0 := by
    rw [hPW.a₂, hQW.a₂, hu, inv_one, Units.val_one, one_pow, one_mul, hs] at ha₂
    rw [show (0 : Γ(S, V.1)) - 0 * Q.W.a₁ + 3 * C.r - 0 ^ 2 = 3 * C.r by ring] at ha₂
    exact (h3.mul_right_eq_zero).mp ha₂
  have ht : C.t = 0 := by
    rw [hPW.a₃, hQW.a₃, hu, inv_one, Units.val_one, one_pow, one_mul, hQW.a₁, hr,
      mul_zero, zero_add, zero_add] at ha₃
    exact (h2.mul_right_eq_zero).mp ha₃
  ext
  · exact congrArg Units.val hu
  · exact hr
  · exact hs
  · exact ht

open WeierstrassCurve in
/-- A pure-`u` variable change preserves short normal form. -/
theorem isShortNF_smul_units {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (hW : W.IsShortNF) (u : Rˣ) :
    ((⟨u, 0, 0, 0⟩ : VariableChange R) • W).IsShortNF := by
  constructor <;>
    simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁, hW.a₂, hW.a₃]

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B ★★, KM 2.2.5 / GME 2.2.3 local form)** Over a base with `2` and `3`
invertible, every `(E, ω)` admits, over every chart-supported affine, a presentation
that is BOTH in short normal form and `ω`-adapted — and by
`transVC_eq_one_of_isAdapted` it is unique. The `(g₂, g₄?, g₆)`-coefficients of its
curve are T-E12's classifying functions. -/
noncomputable def adaptShortNF {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) [Invertible (2 : Γ(S, V.1))] [Invertible (3 : Γ(S, V.1))] :
    LocalPresentation G V :=
  (P.ofVC P.W.toShortNF).adapt b

set_option backward.isDefEq.respectTransparency false in
theorem isAdapted_adaptShortNF {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) [Invertible (2 : Γ(S, V.1))] [Invertible (3 : Γ(S, V.1))] :
    (P.adaptShortNF b).IsAdapted b :=
  isAdapted_adapt _ b

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
theorem isShortNF_adaptShortNF {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) [Invertible (2 : Γ(S, V.1))] [Invertible (3 : Γ(S, V.1))] :
    (P.adaptShortNF b).W.IsShortNF := by
  have h0 : (P.ofVC P.W.toShortNF).W.IsShortNF := by
    rw [ofVC_W]
    exact P.W.toShortNF_spec
  show ((P.ofVC P.W.toShortNF).adapt b).W.IsShortNF
  rw [show ((P.ofVC P.W.toShortNF).adapt b).W =
    (⟨(((P.ofVC P.W.toShortNF).basisUnitAt b).1)⁻¹, 0, 0, 0⟩ :
      VariableChange Γ(S, V.1)) • (P.ofVC P.W.toShortNF).W from rfl]
  exact isShortNF_smul_units h0 _

open Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(E12-C)** The basis unit restricts: adaptedness is a local property. -/
theorem basisUnitAt_restrict {V : S.affineOpens} (P : LocalPresentation G V)
    (b : OmegaBasis G) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    Scheme.resUnit h (P.basisUnitAt b).1 = ((P.restrict h).basisUnitAt b).1 := by
  refine Scheme.unit_ext_of_res_cover S
    (fun i : G.atlas.ι => V'.1 ⊓ (G.atlas.U i).1) (fun i => inf_le_left)
    (fun x hxV => by
      obtain ⟨i, hxi⟩ := G.atlas.covers x
      exact Opens.mem_iSup.mpr ⟨i, hxV, hxi⟩) (fun i => ?_)
  rw [Scheme.resUnit_resUnit, ((P.restrict h).basisUnitAt b).2 i]
  refine Scheme.unit_ext_of_affine_res S (fun W hW => ?_)
  rw [Scheme.resUnit_resUnit, ((P.restrict h).basisUnitOn b i).2 W hW]
  have hWV : W.1 ≤ V.1 ⊓ (G.atlas.U i).1 :=
    le_inf ((hW.trans inf_le_left).trans h) (hW.trans inf_le_right)
  rw [show Scheme.resUnit ((hW.trans inf_le_left).trans h) (P.basisUnitAt b).1 =
      Scheme.resUnit hWV
        (Scheme.resUnit (inf_le_left : V.1 ⊓ (G.atlas.U i).1 ≤ V.1)
          (P.basisUnitAt b).1) from by
      rw [Scheme.resUnit_resUnit],
    (P.basisUnitAt b).2 i, (P.basisUnitOn b i).2 W hWV]
  refine congrArg₂ (· * ·) rfl ?_
  exact (transUnit_restrict_restrict_left P
    ((G.atlas.presentation i).restrict (hW.trans inf_le_right)) h
    (hW.trans inf_le_left)).symm

/-- **(E12-C)** Adaptedness restricts. -/
theorem IsAdapted.restrict {V : S.affineOpens} {P : LocalPresentation G V}
    {b : OmegaBasis G} (hP : P.IsAdapted b) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    (P.restrict h).IsAdapted b := by
  show ((P.restrict h).basisUnitAt b).1 = 1
  rw [← basisUnitAt_restrict, hP, map_one]

end LocalPresentation

end ModularCurves
