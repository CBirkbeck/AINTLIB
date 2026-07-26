/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldPairing
import HasseWeil.HasseBound.WeilPairing.DivisorGalois
import HasseWeil.Foundation.Curves.Valuation.NoFinitePolesBridge
import HasseWeil.HasseBound.WeilPairing.HfactLemma
import HasseWeil.HasseBound.WeilPairing.Scaling.FrobeniusGalois

/-!
# The Galois action on the function field of a base-changed curve (DS4 M1b-3a)

DS4's field-level construction needs the Weil pairing to be `Gal(k̄/k)`-equivariant. The
`HasseWeil` project proves the analogous statement for the **arithmetic Frobenius** over a
*finite* field (`HasseBound/WeilPairing/FrobeniusFunctionFieldEquiv.lean`), and its proofs
are parametric in the field automorphism — but that file's context fixes `[Fintype K]`, so
the lemmas are unavailable over `ℚ`.

This file redevelops the same construction for an **arbitrary base field `k`** and an
arbitrary `σ : k̄ ≃ₐ[k] k̄`:

* `coordRingMap_surjective_of_ringEquiv` / `..._bijective_of_ringEquiv` — `CoordinateRing.map`
  along a ring equivalence of the base is bijective;
* `map_algEquiv_baseChange_eq` — a `k`-algebra automorphism of `k̄` fixes `W ⊗ k̄`;
* `galoisCoordRingEquiv` / `galoisFunctionFieldEquiv` — the induced automorphisms of the
  coordinate ring and of the function field.

These are the transport maps along which the Weil function (hence the pairing) will be
compared in M1b-3b.
-/

universe u v

open Polynomial WeierstrassCurve

namespace ModularCurves

variable {k : Type u} [Field k] (W : WeierstrassCurve k)

/-- `CoordinateRing.map` along a ring **equivalence** of the base field is surjective. -/
theorem coordRingMap_surjective_of_ringEquiv {L : Type v} [Field L] [Algebra k L]
    (e : L ≃+* L) :
    Function.Surjective
      (WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine
        (e : L →+* L)) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨AdjoinRoot.mk _ (q.map (Polynomial.mapRingHom (e.symm : L →+* L))), ?_⟩
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  congr 1
  rw [Polynomial.map_map]
  have hid : (Polynomial.mapRingHom (e : L →+* L)).comp
      (Polynomial.mapRingHom (e.symm : L →+* L)) = RingHom.id L[X] := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RingHom.id_apply, RingHom.coe_coe]
      rw [RingEquiv.apply_symm_apply]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        RingHom.id_apply]
  rw [hid, Polynomial.map_id]

/-- `CoordinateRing.map` along a ring equivalence of the base field is bijective. -/
theorem coordRingMap_bijective_of_ringEquiv {L : Type v} [Field L] [Algebra k L]
    (e : L ≃+* L) :
    Function.Bijective
      (WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine
        (e : L →+* L)) :=
  ⟨WeierstrassCurve.Affine.CoordinateRing.map_injective
      (W' := (W.baseChange L).toAffine) (EquivLike.injective e),
    coordRingMap_surjective_of_ringEquiv W e⟩

/-- A `k`-algebra automorphism of an extension `L` fixes the base-changed curve `W ⊗ L`. -/
theorem map_algEquiv_baseChange_eq {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    (W.baseChange L).map (σ : L →+* L) = W.baseChange L := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext x
  show (σ : L →+* L).comp (algebraMap k L) x = algebraMap k L x
  simpa using σ.commutes x

/-- **(M1b-3a)** The coordinate-ring automorphism induced by `σ : L ≃ₐ[k] L`. -/
noncomputable def galoisCoordRingEquiv {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    (W.baseChange L).toAffine.CoordinateRing ≃+*
      ((W.baseChange L).map (σ : L →+* L)).toAffine.CoordinateRing :=
  RingEquiv.ofBijective _
    (coordRingMap_bijective_of_ringEquiv W (σ : L ≃+* L))

/-- **(M1b-3a)** The function-field automorphism induced by `σ : L ≃ₐ[k] L`: lift
`galoisCoordRingEquiv` to fraction fields and cast the codomain back along
`map_algEquiv_baseChange_eq`. -/
noncomputable def galoisFunctionFieldEquiv {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) :
    (W.baseChange L).toAffine.FunctionField ≃+* (W.baseChange L).toAffine.FunctionField :=
  (IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ)).trans
    (RingEquiv.cast (R := fun (V : WeierstrassCurve L) => V.toAffine.FunctionField)
      (map_algEquiv_baseChange_eq W σ))

/-- **(M1b-3b-i)** The maximal ideal at a smooth point transports along the σ-induced
coordinate-ring equivalence: `σ_*(𝔪_P) = 𝔪_Q` whenever `Q`'s coordinates are the
`σ`-images of `P`'s. Port of HasseWeil's `map_maximalIdealAt_crFrobEquiv` (whose proof is
already parametric in the base automorphism) to an arbitrary base field and an arbitrary
`σ : L ≃ₐ[k] L`. -/
theorem map_maximalIdealAt_galoisCoordRingEquiv {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint)
    (Q : (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint)
    (hQx : Q.x = σ P.x) (hQy : Q.y = σ P.y) :
    Ideal.map (galoisCoordRingEquiv W σ).toRingHom
        ((⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).maximalIdealAt P) =
      (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).maximalIdealAt Q := by
  have hcr : (galoisCoordRingEquiv W σ).toRingHom =
      WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine
        (σ : L →+* L) := rfl
  rw [hcr]
  change Ideal.map _
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal (W.baseChange L).toAffine
        P.x (Polynomial.C P.y)) = _
  rw [HasseWeil.WeilPairing.map_XYIdeal (W.baseChange L).toAffine _ P.x (Polynomial.C P.y)]
  change _ = WeierstrassCurve.Affine.CoordinateRing.XYIdeal _ Q.x (Polynomial.C Q.y)
  rw [hQx, hQy, Polynomial.map_C]
  rfl

/-- The smooth point of the σ-mapped curve with the same coordinates (nonsingularity
transported across `map_algEquiv_baseChange_eq`). Port of HasseWeil's `pointOnMapped`. -/
noncomputable def pointOnMappedGal {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint where
  x := P.x
  y := P.y
  nonsingular := by
    have hM : ((W.baseChange L).map (σ : L →+* L)).toAffine =
        (W.baseChange L).toAffine := by rw [map_algEquiv_baseChange_eq W σ]
    rw [hM]
    exact P.nonsingular

@[simp] theorem pointOnMappedGal_x {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (pointOnMappedGal W σ P).x = P.x := rfl

@[simp] theorem pointOnMappedGal_y {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (pointOnMappedGal W σ P).y = P.y := rfl

/-- **(M1b-3b-ii)** Affine order transport along `σ`: for smooth points `P`, `Q` with
`P.x = σ Q.x`, `P.y = σ Q.y`, the point valuation of `σ·g` at `P` equals that of `g` at
`Q`. Port of HasseWeil's `pointValuation_frobeniusFunctionFieldEquiv`. -/
theorem pointValuation_galoisFunctionFieldEquiv {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (P Q : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint)
    (hPx : P.x = σ Q.x) (hPy : P.y = σ Q.y)
    (g : (W.baseChange L).toAffine.FunctionField) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).pointValuation P
        (galoisFunctionFieldEquiv W σ g) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).pointValuation Q g := by
  haveI hMell : ((W.baseChange L).map (σ : L →+* L)).toAffine.IsElliptic := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  haveI hMic : IsIntegrallyClosed (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  haveI hMdd : IsDedekindDomain (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing :=
    HasseWeil.Curves.SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  haveI hEdd : IsDedekindDomain (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing :=
    HasseWeil.Curves.SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  rw [galoisFunctionFieldEquiv, RingEquiv.trans_apply,
    HasseWeil.WeilPairing.pointValuation_ringEquivCast _ _ (map_algEquiv_baseChange_eq W σ)
      (pointOnMappedGal W σ P) P
      (HasseWeil.WeilPairing.heq_smoothPoint _ _ (map_algEquiv_baseChange_eq W σ) _ _ rfl rfl)]
  rw [HasseWeil.Curves.pointValuation_eq_heightOneValuation _ (pointOnMappedGal W σ P)
      (IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ) g),
    HasseWeil.Curves.pointValuation_eq_heightOneValuation _ Q g]
  exact HasseWeil.WeilPairing.valuation_map_ringEquiv (galoisCoordRingEquiv W σ)
    (HasseWeil.Curves.smoothPointToHeightOne (W.baseChange L).toAffine Q)
    (HasseWeil.Curves.smoothPointToHeightOne
      ((W.baseChange L).map (σ : L →+* L)).toAffine (pointOnMappedGal W σ P))
    (by
      rw [HasseWeil.Curves.smoothPointToHeightOne_asIdeal,
        HasseWeil.Curves.smoothPointToHeightOne_asIdeal]
      exact (map_maximalIdealAt_galoisCoordRingEquiv W σ Q (pointOnMappedGal W σ P)
        (by rw [pointOnMappedGal_x, hPx]) (by rw [pointOnMappedGal_y, hPy])).symm) g

/-- **(M1b-3b-iii)** The `σ`-image of a smooth point of `W ⊗ L` (nonsingularity moves by
`map_nonsingular` along the injective `σ`, then back along `map_algEquiv_baseChange_eq`). -/
noncomputable def galoisSmoothPoint {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint where
  x := σ P.x
  y := σ P.y
  nonsingular := by
    have hmap := (WeierstrassCurve.Affine.map_nonsingular
      (W := (W.baseChange L).toAffine) (f := (σ : L →+* L)) (EquivLike.injective σ)
      P.x P.y).mpr P.nonsingular
    rwa [show ((W.baseChange L).toAffine.map (σ : L →+* L)) =
      (W.baseChange L).toAffine from by
        rw [show (W.baseChange L).toAffine.map (σ : L →+* L) =
          ((W.baseChange L).map (σ : L →+* L)).toAffine from rfl,
          map_algEquiv_baseChange_eq W σ]] at hmap

@[simp] theorem galoisSmoothPoint_x {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (galoisSmoothPoint W σ P).x = σ P.x := rfl

@[simp] theorem galoisSmoothPoint_y {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (galoisSmoothPoint W σ P).y = σ P.y := rfl

/-- **(M1b-3b-iii)** Affine order transport in the form the divisor comparison consumes:
the order of `σ·g` at `σ·P` is the order of `g` at `P`. -/
theorem ord_P_galoisFunctionFieldEquiv {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint)
    (g : (W.baseChange L).toAffine.FunctionField) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ord_P (galoisSmoothPoint W σ P)
        (galoisFunctionFieldEquiv W σ g) =
      (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).ord_P P g := by
  unfold HasseWeil.Curves.SmoothPlaneCurve.ord_P
  rw [pointValuation_galoisFunctionFieldEquiv W σ (galoisSmoothPoint W σ P) P rfl rfl g]

/-- `galoisSmoothPoint` is injective (its coordinates are `σ`-images). -/
theorem galoisSmoothPoint_injective {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    Function.Injective (galoisSmoothPoint W σ) := by
  intro P Q h
  refine HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext ?_ ?_
  · exact σ.injective (congrArg HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.x h)
  · exact σ.injective (congrArg HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.y h)

/-- **(M1b-3b-iv)** The affine divisor transports by relabelling the points along `σ`:
`div(σ·g)` at `σ·P` is `div(g)` at `P`. -/
theorem divisorOf_galoisFunctionFieldEquiv_apply {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (g : (W.baseChange L).toAffine.FunctionField)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    (⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).divisorOf
          (galoisFunctionFieldEquiv W σ g) (galoisSmoothPoint W σ P) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).divisorOf g P := by
  show ((⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).ord_P (galoisSmoothPoint W σ P)
        (galoisFunctionFieldEquiv W σ g)).untopD 0 = _
  rw [ord_P_galoisFunctionFieldEquiv W σ P g]
  rfl

/-- **(M1b-3b-v-a)** `galoisCoordRingEquiv` on the standard basis presentation. Port of
HasseWeil's `crFrobEquiv_smul_basis`. -/
theorem galoisCoordRingEquiv_smul_basis {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (p q : Polynomial L) :
    galoisCoordRingEquiv W σ
        (p • (1 : (W.baseChange L).toAffine.CoordinateRing) +
          q • WeierstrassCurve.Affine.CoordinateRing.mk (W.baseChange L).toAffine
            Polynomial.X) =
      (p.map (σ : L →+* L)) •
          (1 : ((W.baseChange L).map (σ : L →+* L)).toAffine.CoordinateRing) +
        (q.map (σ : L →+* L)) •
          WeierstrassCurve.Affine.CoordinateRing.mk
            ((W.baseChange L).map (σ : L →+* L)).toAffine Polynomial.X := by
  have hcr : ∀ z, galoisCoordRingEquiv W σ z =
      WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine (σ : L →+* L) z :=
    fun _ => rfl
  rw [hcr, map_add, WeierstrassCurve.Affine.CoordinateRing.map_smul,
    WeierstrassCurve.Affine.CoordinateRing.map_smul, map_one]
  congr 2
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]

/-- **(M1b-3b-v-a)** Norm transport: `N(σ·u) = σ·(N u)`. Port of HasseWeil's
`norm_crFrobEquiv`. -/
theorem norm_galoisCoordRingEquiv {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (u : (W.baseChange L).toAffine.CoordinateRing) :
    Algebra.norm (Polynomial L) (galoisCoordRingEquiv W σ u) =
      (Algebra.norm (Polynomial L) u).map (σ : L →+* L) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  rw [galoisCoordRingEquiv_smul_basis, WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis,
    WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- **(M1b-3b-v-a)** `ord_∞` of an integral element transports under
`galoisCoordRingEquiv`. Port of HasseWeil's `ordAtInfty_algebraMap_crFrobEquiv`. -/
theorem ordAtInfty_algebraMap_galoisCoordRingEquiv {L : Type v} [Field L] [DecidableEq L]
    [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (u : (W.baseChange L).toAffine.CoordinateRing) :
    (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty
        (algebraMap _ _ (galoisCoordRingEquiv W σ u)) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty (algebraMap _ _ u) := by
  haveI hMell : ((W.baseChange L).map (σ : L →+* L)).toAffine.IsElliptic := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  by_cases hu : u = 0
  · subst hu
    rw [map_zero, map_zero, map_zero,
      HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero,
      HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero]
  · have hcu : galoisCoordRingEquiv W σ u ≠ 0 := fun h =>
      hu ((EquivLike.injective (galoisCoordRingEquiv W σ)) (by rw [h, map_zero]))
    rw [(⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_algebraMap_coordinateRing _ hcu,
      (⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_algebraMap_coordinateRing _ hu,
      norm_galoisCoordRingEquiv,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective (σ : L →+* L))]

/-- **(M1b-3b-v-b)** `ord_∞` transport for the raw fraction-field lift: extend
`ordAtInfty_algebraMap_galoisCoordRingEquiv` to quotients. Port of HasseWeil's
`ordAtInfty_ffFrobEquivRaw`. -/
theorem ordAtInfty_galoisFractionLift {L : Type v} [Field L] [DecidableEq L]
    [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (z : (W.baseChange L).toAffine.FunctionField) :
    (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty
        (IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ) z) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty z := by
  haveI hMell : ((W.baseChange L).map (σ : L →+* L)).toAffine.IsElliptic := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  by_cases hz : z = 0
  · subst hz
    rw [map_zero, HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero,
      HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_zero]
  obtain ⟨u, v, hv_nzd, heq⟩ :=
    IsFractionRing.div_surjective (A := (W.baseChange L).toAffine.CoordinateRing) z
  have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_nzd
  have hv_map_ne :
      algebraMap _ (W.baseChange L).toAffine.FunctionField v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hv_ne
  have hu_ne : u ≠ 0 := by
    intro h
    exact hz (by rw [← heq, h, map_zero, zero_div])
  have hu_map_ne :
      algebraMap _ (W.baseChange L).toAffine.FunctionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu_ne
  have hcu_map_ne :
      algebraMap _ ((W.baseChange L).map (σ : L →+* L)).toAffine.FunctionField
        (galoisCoordRingEquiv W σ u) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hu_ne ((EquivLike.injective (galoisCoordRingEquiv W σ))
        (by rw [h, map_zero])))
  have hcv_map_ne :
      algebraMap _ ((W.baseChange L).map (σ : L →+* L)).toAffine.FunctionField
        (galoisCoordRingEquiv W σ v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hv_ne ((EquivLike.injective (galoisCoordRingEquiv W σ))
        (by rw [h, map_zero])))
  rw [← heq, (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_div_eq_mul_inv _ hu_map_ne hv_map_ne,
    (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_inv]
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rw [(⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_div_eq_mul_inv _ hcu_map_ne hcv_map_ne,
    (⟨((W.baseChange L).map (σ : L →+* L)).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty_inv,
    ordAtInfty_algebraMap_galoisCoordRingEquiv, ordAtInfty_algebraMap_galoisCoordRingEquiv]

/-- **(M1b-3b-v ★)** The order at infinity is `σ`-invariant:
`ord_∞(σ·g) = ord_∞(g)`. Port of HasseWeil's `ordAtInfty_frobeniusFunctionFieldEquiv`. -/
theorem ordAtInfty_galoisFunctionFieldEquiv {L : Type v} [Field L] [DecidableEq L]
    [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (g : (W.baseChange L).toAffine.FunctionField) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty
        (galoisFunctionFieldEquiv W σ g) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty g := by
  rw [galoisFunctionFieldEquiv, RingEquiv.trans_apply,
    HasseWeil.WeilPairing.ordAtInfty_ringEquivCast _ _ (map_algEquiv_baseChange_eq W σ),
    ordAtInfty_galoisFractionLift]

/-- **(M1b-3b-vi)** The `σ`-action on smooth points as an equivalence (inverse given by
`σ⁻¹`). -/
noncomputable def galoisSmoothPointEquiv {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) :
    (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint ≃
      (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint where
  toFun := galoisSmoothPoint W σ
  invFun := galoisSmoothPoint W σ.symm
  left_inv P := HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext
    (by simp [galoisSmoothPoint]) (by simp [galoisSmoothPoint])
  right_inv P := HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext
    (by simp [galoisSmoothPoint]) (by simp [galoisSmoothPoint])

@[simp] theorem galoisSmoothPointEquiv_apply {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    galoisSmoothPointEquiv W σ P = galoisSmoothPoint W σ P := rfl

/-- **(M1b-3b-vi ★)** The affine divisor of `σ·g` is the `σ`-relabelling of the affine
divisor of `g`. -/
theorem divisorOf_galoisFunctionFieldEquiv {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (g : (W.baseChange L).toAffine.FunctionField) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).divisorOf (galoisFunctionFieldEquiv W σ g) =
      Finsupp.equivMapDomain (galoisSmoothPointEquiv W σ)
        ((⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).divisorOf g) := by
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.equivMapDomain_apply]
  have hP : galoisSmoothPoint W σ ((galoisSmoothPointEquiv W σ).symm P) = P :=
    (galoisSmoothPointEquiv W σ).apply_symm_apply P
  conv_lhs => rw [← hP]
  rw [divisorOf_galoisFunctionFieldEquiv_apply W σ g]

/-- **(M1b-3b-vii)** The `σ`-action on projective smooth points: `σ` on the affine part,
fixing the point at infinity. -/
noncomputable def galoisProjPointEquiv {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) :
    HasseWeil.Curves.ProjectiveSmoothPoint
        (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) ≃
      HasseWeil.Curves.ProjectiveSmoothPoint
        (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L) where
  toFun v := match v with
    | .affine P => .affine (galoisSmoothPoint W σ P)
    | .infinity => .infinity
  invFun v := match v with
    | .affine P => .affine (galoisSmoothPoint W σ.symm P)
    | .infinity => .infinity
  left_inv v := by
    cases v with
    | affine P =>
      exact congrArg HasseWeil.Curves.ProjectiveSmoothPoint.affine
        ((galoisSmoothPointEquiv W σ).left_inv P)
    | infinity => rfl
  right_inv v := by
    cases v with
    | affine P =>
      exact congrArg HasseWeil.Curves.ProjectiveSmoothPoint.affine
        ((galoisSmoothPointEquiv W σ).right_inv P)
    | infinity => rfl

@[simp] theorem galoisProjPointEquiv_affine {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L)
    (P : (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L).SmoothPoint) :
    galoisProjPointEquiv W σ (HasseWeil.Curves.ProjectiveSmoothPoint.affine P) =
      HasseWeil.Curves.ProjectiveSmoothPoint.affine (galoisSmoothPoint W σ P) := rfl

@[simp] theorem galoisProjPointEquiv_infinity {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) :
    galoisProjPointEquiv W σ
        (HasseWeil.Curves.ProjectiveSmoothPoint.infinity
          (C := (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L))) =
      HasseWeil.Curves.ProjectiveSmoothPoint.infinity := rfl

/-- **(M1b-3b, Lemma A)** Relabelling commutes with the affine-to-projective inclusion. -/
theorem toProjective_equivMapDomain {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (D : HasseWeil.Curves.Divisor
      (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L)) :
    HasseWeil.Curves.Divisor.toProjective
        (Finsupp.equivMapDomain (galoisSmoothPointEquiv W σ) D) =
      Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (HasseWeil.Curves.Divisor.toProjective D) := by
  classical
  refine Finsupp.ext fun v => ?_
  rw [Finsupp.equivMapDomain_apply]
  show Finsupp.mapDomain HasseWeil.Curves.ProjectiveSmoothPoint.affine
      (Finsupp.equivMapDomain (galoisSmoothPointEquiv W σ) D) v =
    Finsupp.mapDomain HasseWeil.Curves.ProjectiveSmoothPoint.affine D
      ((galoisProjPointEquiv W σ).symm v)
  rw [Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  cases v with
  | affine P =>
    rw [show ((galoisProjPointEquiv W σ).symm
        (HasseWeil.Curves.ProjectiveSmoothPoint.affine P)) =
      HasseWeil.Curves.ProjectiveSmoothPoint.affine
        ((galoisSmoothPointEquiv W σ).symm P) from rfl]
    have hinj : Function.Injective (HasseWeil.Curves.ProjectiveSmoothPoint.affine ∘
        (galoisSmoothPointEquiv W σ)) := fun A B h =>
      (galoisSmoothPointEquiv W σ).injective
        (HasseWeil.Curves.ProjectiveSmoothPoint.affine_injective h)
    have hval := Finsupp.mapDomain_apply hinj D ((galoisSmoothPointEquiv W σ).symm P)
    rw [show (HasseWeil.Curves.ProjectiveSmoothPoint.affine ∘
        (galoisSmoothPointEquiv W σ)) ((galoisSmoothPointEquiv W σ).symm P) =
      HasseWeil.Curves.ProjectiveSmoothPoint.affine P from by
        simp only [Function.comp_apply, Equiv.apply_symm_apply]] at hval
    rw [hval, Finsupp.mapDomain_apply
      (fun _ _ h => HasseWeil.Curves.ProjectiveSmoothPoint.affine_injective h)]
  | infinity =>
    rw [show ((galoisProjPointEquiv W σ).symm
        (HasseWeil.Curves.ProjectiveSmoothPoint.infinity
          (C := (⟨(W.baseChange L).toAffine⟩ :
            HasseWeil.Curves.SmoothPlaneCurve L)))) =
      HasseWeil.Curves.ProjectiveSmoothPoint.infinity from rfl]
    rw [Finsupp.mapDomain_notin_range, Finsupp.mapDomain_notin_range]
    · rintro ⟨P, hP⟩
      exact absurd hP (by simp)
    · rintro ⟨P, hP⟩
      exact absurd hP (by simp)

/-- **(M1b-3b, Lemma B)** The relabelling fixes the divisor supported at infinity. -/
theorem equivMapDomain_single_infinity {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (c : ℤ) :
    Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (Finsupp.single
          (HasseWeil.Curves.ProjectiveSmoothPoint.infinity
            (C := (⟨(W.baseChange L).toAffine⟩ :
              HasseWeil.Curves.SmoothPlaneCurve L))) c) =
      Finsupp.single HasseWeil.Curves.ProjectiveSmoothPoint.infinity c := by
  classical
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]
  rfl

/-- **(M1b-3b ★)** The projective divisor transports by the `σ`-relabelling of points. -/
theorem projectiveDivisorOf_galoisFunctionFieldEquiv {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (g : (W.baseChange L).toAffine.FunctionField) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).projectiveDivisorOf
        (galoisFunctionFieldEquiv W σ g) =
      Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        ((⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).projectiveDivisorOf g) := by
  classical
  show HasseWeil.Curves.Divisor.toProjective
        ((⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).divisorOf
          (galoisFunctionFieldEquiv W σ g)) +
      Finsupp.single HasseWeil.Curves.ProjectiveSmoothPoint.infinity
        (((⟨(W.baseChange L).toAffine⟩ :
          HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty
            (galoisFunctionFieldEquiv W σ g)).untopD 0) = _
  rw [divisorOf_galoisFunctionFieldEquiv W σ g, toProjective_equivMapDomain,
    ordAtInfty_galoisFunctionFieldEquiv W σ g, ← equivMapDomain_single_infinity W σ
      (((⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).ordAtInfty g).untopD 0)]
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_add]
  rfl

/-- **(M1b-3b-viii, step a)** The `σ`-action on smooth points agrees with mathlib's
`Affine.Point.map σ` under `toProjectiveSmoothPoint`: relabelling a point's projective
class is the projective class of the `σ`-image point. -/
theorem galoisProjPointEquiv_toProjectiveSmoothPoint {L : Type v} [Field L] [DecidableEq L]
    [Algebra k L] (σ : L ≃ₐ[k] L) (P : (W.baseChange L).toAffine.Point) :
    galoisProjPointEquiv W σ
        (WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint P) =
      WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint
        (WeierstrassCurve.Affine.Point.map (W' := W) (F := L) (K := L)
          (σ.toAlgHom : L →ₐ[k] L) P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    refine congrArg HasseWeil.Curves.ProjectiveSmoothPoint.affine ?_
    exact HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext rfl rfl

/-- **(M1b-3b-viii, step b)** The `κ`-divisor transports: relabelling `κ(P)` by `σ` gives
`κ(σ·P)`. -/
theorem equivMapDomain_kappaDivisor {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    (σ : L ≃ₐ[k] L) [(W.baseChange L).toAffine.IsElliptic]
    (P : (W.baseChange L).toAffine.Point) :
    Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (HasseWeil.Curves.kappaDivisor (W.baseChange L).toAffine P) =
      HasseWeil.Curves.kappaDivisor (W.baseChange L).toAffine
        (WeierstrassCurve.Affine.Point.map (W' := W) (F := L) (K := L)
          (σ.toAlgHom : L →ₐ[k] L) P) := by
  classical
  show Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
      (Finsupp.single (WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint P) 1 -
        Finsupp.single HasseWeil.Curves.ProjectiveSmoothPoint.infinity 1) = _
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_sub,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    galoisProjPointEquiv_toProjectiveSmoothPoint W σ P]
  rfl

/-- The `σ`-action on points as an additive equivalence (mathlib's `Affine.Point.map`
in both directions). -/
noncomputable def galoisPointEquiv {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) :
    (W.baseChange L).toAffine.Point ≃+ (W.baseChange L).toAffine.Point where
  toFun := WeierstrassCurve.Affine.Point.map (W' := W) (F := L) (K := L)
    (σ.toAlgHom : L →ₐ[k] L)
  invFun := WeierstrassCurve.Affine.Point.map (W' := W) (F := L) (K := L)
    (σ.symm.toAlgHom : L →ₐ[k] L)
  left_inv P := by
    rw [WeierstrassCurve.Affine.Point.map_map]
    rw [show (σ.symm.toAlgHom : L →ₐ[k] L).comp (σ.toAlgHom : L →ₐ[k] L) =
        (AlgHom.id k L) from AlgHom.ext fun a => by simp]
    cases P <;> rfl
  right_inv P := by
    rw [WeierstrassCurve.Affine.Point.map_map]
    rw [show (σ.toAlgHom : L →ₐ[k] L).comp (σ.symm.toAlgHom : L →ₐ[k] L) =
        (AlgHom.id k L) from AlgHom.ext fun a => by simp]
    cases P <;> rfl
  map_add' P Q := map_add _ P Q

/-- **(M1b-3b-viii, step d)** The `σ`-action permutes the fibres of `[N]`: `σ` restricts to
an equivalence `{P // N • P = Q} ≃ {P // N • P = σ·Q}` (it is additive, so it commutes with
`N • ·`). -/
noncomputable def galoisFiberEquiv {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) (N : ℤ)
    (Q : (W.baseChange L).toAffine.Point) :
    { P : (W.baseChange L).toAffine.Point // N • P = Q } ≃
      { P : (W.baseChange L).toAffine.Point // N • P = galoisPointEquiv W σ Q } where
  toFun P := ⟨galoisPointEquiv W σ P.1, by
    rw [← map_zsmul (galoisPointEquiv W σ), P.2]⟩
  invFun P := ⟨(galoisPointEquiv W σ).symm P.1, by
    rw [← map_zsmul (galoisPointEquiv W σ).symm, P.2,
      (galoisPointEquiv W σ).symm_apply_apply]⟩
  left_inv P := Subtype.ext ((galoisPointEquiv W σ).symm_apply_apply P.1)
  right_inv P := Subtype.ext ((galoisPointEquiv W σ).apply_symm_apply P.1)

/-- **(M1b-3b-viii, step e)** The multiplicity-free pullback divisor transports:
relabelling `f*((Q))` by `σ` gives `f*((σ·Q))`. -/
theorem equivMapDomain_pullbackDiv {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra k L] [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) (N : ℤ)
    (hN : Finite (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom.ker)
    (Q : (W.baseChange L).toAffine.Point) :
    Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (HasseWeil.WeilPairing.pullbackDiv
          (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN Q) =
      HasseWeil.WeilPairing.pullbackDiv
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (galoisPointEquiv W σ Q) := by
  classical
  letI : Fintype { P : (W.baseChange L).toAffine.Point //
      (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom P = Q } :=
    @Fintype.ofFinite _ (HasseWeil.WeilPairing.fiber_finite _ hN Q)
  letI : Fintype { P : (W.baseChange L).toAffine.Point //
      (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom P =
        galoisPointEquiv W σ Q } :=
    @Fintype.ofFinite _ (HasseWeil.WeilPairing.fiber_finite _ hN (galoisPointEquiv W σ Q))
  unfold HasseWeil.WeilPairing.pullbackDiv
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_finset_sum]
  refine Finset.sum_nbij'
    (i := fun P => (⟨galoisPointEquiv W σ P.1, by
        have hP : N • P.1 = Q := P.2
        show N • galoisPointEquiv W σ P.1 = galoisPointEquiv W σ Q
        rw [← map_zsmul (galoisPointEquiv W σ), hP]⟩ :
      { P : (W.baseChange L).toAffine.Point //
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom P =
          galoisPointEquiv W σ Q }))
    (j := fun P => (⟨(galoisPointEquiv W σ).symm P.1, by
        have hP : N • P.1 = galoisPointEquiv W σ Q := P.2
        show N • (galoisPointEquiv W σ).symm P.1 = Q
        rw [← map_zsmul (galoisPointEquiv W σ).symm, hP,
          (galoisPointEquiv W σ).symm_apply_apply]⟩ :
      { P : (W.baseChange L).toAffine.Point //
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom P = Q })) ?_ ?_ ?_ ?_ ?_
  · intro P _
    exact Finset.mem_univ _
  · intro P _
    exact Finset.mem_univ _
  · intro P _
    exact Subtype.ext ((galoisPointEquiv W σ).symm_apply_apply P.1)
  · intro P _
    exact Subtype.ext ((galoisPointEquiv W σ).apply_symm_apply P.1)
  · intro P _
    rw [Finsupp.mapDomain_single, galoisProjPointEquiv_toProjectiveSmoothPoint]
    rfl

/-- **(M1b-3b-viii, step f-0)** The relabelling commutes with `toAffinePoint`. -/
theorem toAffinePoint_galoisProjPointEquiv {L : Type v} [Field L] [DecidableEq L]
    [Algebra k L] [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L)
    (v : HasseWeil.Curves.ProjectiveSmoothPoint
      (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L)) :
    HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint
        (galoisProjPointEquiv W σ v) =
      galoisPointEquiv W σ
        (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v) := by
  cases v with
  | affine P => rfl
  | infinity => rfl

/-- **(M1b-3b-viii, step f)** The full pullback of a projective divisor transports:
`σ·(f*(D)) = f*(σ·D)`. -/
theorem equivMapDomain_pullbackDivisor {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra k L] [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) (N : ℤ)
    (hN : Finite (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom.ker)
    (D : HasseWeil.Curves.ProjectiveDivisor
      (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L)) :
    Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (HasseWeil.WeilPairing.DivisorPullback.pullbackDivisor
          (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN D) =
      HasseWeil.WeilPairing.DivisorPullback.pullbackDivisor
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (Finsupp.equivMapDomain (galoisProjPointEquiv W σ) D) := by
  classical
  show Finsupp.domCongr (M := ℤ) (galoisProjPointEquiv W σ)
      (D.sum fun v n => n • HasseWeil.WeilPairing.pullbackDiv
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v)) = _
  rw [map_finsuppSum]
  show (D.sum fun v n => Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
      (n • HasseWeil.WeilPairing.pullbackDiv
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v))) = _
  have hterm : ∀ (v : HasseWeil.Curves.ProjectiveSmoothPoint
        (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L)) (n : ℤ),
      Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (n • HasseWeil.WeilPairing.pullbackDiv
          (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
          (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v)) =
      n • HasseWeil.WeilPairing.pullbackDiv
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint
          (galoisProjPointEquiv W σ v)) := by
    intro v n
    rw [show Finsupp.equivMapDomain (galoisProjPointEquiv W σ)
        (n • HasseWeil.WeilPairing.pullbackDiv
          (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
          (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v)) =
      Finsupp.domCongr (M := ℤ) (galoisProjPointEquiv W σ)
        (n • HasseWeil.WeilPairing.pullbackDiv
          (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
          (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v)) from rfl,
      map_zsmul, toAffinePoint_galoisProjPointEquiv W σ v]
    exact congrArg (n • ·) (equivMapDomain_pullbackDiv W σ N hN _)
  simp only [hterm]
  rw [show Finsupp.equivMapDomain (galoisProjPointEquiv W σ) D =
      Finsupp.mapDomain (galoisProjPointEquiv W σ) D from
    Finsupp.equivMapDomain_eq_mapDomain _ _]
  exact (Finsupp.sum_mapDomain_index_addMonoidHom (f := galoisProjPointEquiv W σ) (s := D)
    (h := fun v => (smulAddHom ℤ (HasseWeil.Curves.ProjectiveDivisor
        (⟨(W.baseChange L).toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve L))).flip
      (HasseWeil.WeilPairing.pullbackDiv
        (HasseWeil.mulByInt (W.baseChange L).toAffine N).toAddMonoidHom hN
        (HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint v)))).symm

/-- **(M1b-3b ★★★)** The Weil-function divisor comparison:
`div(σ·g_T) = div(g_{σ·T})`. This is the σ-analogue (arbitrary base field, arbitrary
automorphism) of HasseWeil's Frobenius divisor descent, and the last geometric input to
the Galois equivariance of the Weil pairing. -/
theorem projectiveDivisorOf_galois_weilFunction {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L)
    (N : ℤ) (hN : (N : L) ≠ 0) (T : (W.baseChange L).toAffine.Point) (hT : N • T = 0)
    (hσT : N • (galoisPointEquiv W σ T) = 0) :
    (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).projectiveDivisorOf
        (galoisFunctionFieldEquiv W σ
          (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT)) =
      (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L).projectiveDivisorOf
        (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN
          (galoisPointEquiv W σ T) hσT) := by
  rw [projectiveDivisorOf_galoisFunctionFieldEquiv W σ,
    HasseWeil.WeilPairing.weilFunction_divisor_eq_pullbackDivisor_kappaDivisor
      (W.baseChange L) N hN T hT,
    HasseWeil.WeilPairing.weilFunction_divisor_eq_pullbackDivisor_kappaDivisor
      (W.baseChange L) N hN (galoisPointEquiv W σ T) hσT,
    equivMapDomain_pullbackDivisor W σ N
      (HasseWeil.WeilPairing.mulByInt_ker_finite (W.baseChange L) N hN),
    equivMapDomain_kappaDivisor W σ T]
  rfl

/-- **(M1b-3b-ix, the general-automorphism core)** The `σ₀`-analogue of HasseWeil's
`weilPairing_galois_core`: with the same three hypotheses but the constants law
`Φ(algebraMap a) = algebraMap (σ₀ a)` for a field automorphism `σ₀` (instead of the
`q`-power), the pairing is `σ₀`-equivariant.

The proof is the same constant-ratio computation: apply `Φ` to `τ_S g_T = e(S,T)·g_T`,
rewrite the left side by the conjugation and the right by the constants law, substitute
`Φ g_T = c·g_{T'}`, and cancel the nonzero factor `c·g_{T'}`. -/
theorem weilPairing_galois_core_of_algEquiv {F : Type v} [Field F] [DecidableEq F]
    [IsAlgClosed F] (V : WeierstrassCurve F) [V.toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).CoordinateRing]
    (N : ℤ) (hN : (N : F) ≠ 0) (σ₀ : F →+* F)
    (Φ : (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).FunctionField ≃+*
      (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).FunctionField)
    (S T S' T' : V.toAffine.Point)
    (hS : N • S = 0) (hT : N • T = 0) (hS' : N • S' = 0) (hT' : N • T' = 0)
    (hconj : Φ (HasseWeil.translateAlgEquivOfPoint V S
        (HasseWeil.WeilPairing.weilFunction V N hN T hT)) =
      HasseWeil.translateAlgEquivOfPoint V S'
        (Φ (HasseWeil.WeilPairing.weilFunction V N hN T hT)))
    {c : F} (hc : c ≠ 0)
    (hnat : Φ (HasseWeil.WeilPairing.weilFunction V N hN T hT) =
      algebraMap F _ c * HasseWeil.WeilPairing.weilFunction V N hN T' hT')
    (hconst : ∀ a : F, Φ (algebraMap F _ a) = algebraMap F _ (σ₀ a)) :
    HasseWeil.WeilPairing.weilPairing V N hN S' T' hS' hT' =
      σ₀ (HasseWeil.WeilPairing.weilPairing V N hN S T hS hT) := by
  set e := HasseWeil.WeilPairing.weilPairing V N hN S T hS hT
  set e' := HasseWeil.WeilPairing.weilPairing V N hN S' T' hS' hT'
  set gT := HasseWeil.WeilPairing.weilFunction V N hN T hT
  set gT' := HasseWeil.WeilPairing.weilFunction V N hN T' hT'
  have hgT'_ne : gT' ≠ 0 := HasseWeil.WeilPairing.weilFunction_ne_zero V N hN T' hT'
  have hc_ne : algebraMap F
      (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).FunctionField c ≠ 0 :=
    (map_ne_zero_iff (algebraMap F
      (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).FunctionField)
      (algebraMap F _).injective).mpr hc
  have hrel : Φ (HasseWeil.translateAlgEquivOfPoint V S gT) =
      Φ (algebraMap F _ e * gT) := by
    rw [HasseWeil.WeilPairing.weilPairing_translate V N hN S T hS hT]
  rw [hconj] at hrel
  rw [map_mul, hconst] at hrel
  rw [hnat] at hrel
  rw [map_mul, (HasseWeil.translateAlgEquivOfPoint V S').commutes,
    HasseWeil.WeilPairing.weilPairing_translate V N hN S' T' hS' hT'] at hrel
  have hcancel : algebraMap F _ e' * (algebraMap F _ c * gT') =
      algebraMap F _ (σ₀ e) * (algebraMap F _ c * gT') := by
    rw [← hrel]; ring
  exact (algebraMap F _).injective (mul_right_cancel₀ (mul_ne_zero hc_ne hgT'_ne) hcancel)

/-- **(M1b-3b-ix, brick i-raw)** The raw fraction-field lift acts on constants by `σ`. -/
theorem galoisFractionLift_algebraMap {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L)
    (a : L) :
    IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ)
        (algebraMap L (W.baseChange L).toAffine.FunctionField a) =
      algebraMap L ((W.baseChange L).map (σ : L →+* L)).toAffine.FunctionField (σ a) := by
  rw [show (algebraMap L (W.baseChange L).toAffine.FunctionField a) =
      algebraMap (W.baseChange L).toAffine.CoordinateRing
        (W.baseChange L).toAffine.FunctionField
        (algebraMap L (W.baseChange L).toAffine.CoordinateRing a) from by
    rw [← IsScalarTower.algebraMap_apply]]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    show galoisCoordRingEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.CoordinateRing a) =
      WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine (σ : L →+* L)
        (algebraMap L (W.baseChange L).toAffine.CoordinateRing a) from rfl,
    HasseWeil.WeilPairing.coordRingMap_algebraMap_base, ← IsScalarTower.algebraMap_apply]
  rfl

/-- **(M1b-3b-ix, brick i)** The constants law: `Φ_σ (algebraMap a) = algebraMap (σ a)`. -/
theorem galoisFunctionFieldEquiv_algebraMap {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (a : L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField a) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (σ a) := by
  rw [galoisFunctionFieldEquiv, RingEquiv.trans_apply, galoisFractionLift_algebraMap]
  have key : ∀ (V : WeierstrassCurve L) (h : V = W.baseChange L),
      (RingEquiv.cast (R := fun (U : WeierstrassCurve L) => U.toAffine.FunctionField) h)
        (algebraMap L V.toAffine.FunctionField (σ a)) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (σ a) := by
    intro V h
    subst h
    rfl
  exact key _ (map_algEquiv_baseChange_eq W σ)

/-- **(M1b-3b-x, helper)** `div(f/g) = div f − div g` for nonzero `f, g` (HasseWeil has
the `mul` and `inv` forms but not the quotient one).

The two structural hypotheses are taken **explicitly**: at a base-changed curve the
elaborator unfolds `⟨(W ⊗ L).toAffine⟩` into a record literal and instance search then
fails, so callers pass the instances directly. -/
theorem projectiveDivisorOf_div {F : Type v} [Field F] [DecidableEq F]
    {C : HasseWeil.Curves.SmoothPlaneCurve F} (hell : C.toAffine.IsElliptic)
    (hic : IsIntegrallyClosed C.CoordinateRing)
    {f g : C.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    C.projectiveDivisorOf (f / g) = C.projectiveDivisorOf f - C.projectiveDivisorOf g := by
  letI := hell
  letI := hic
  rw [div_eq_mul_inv, HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_mul hf
      (inv_ne_zero hg),
    HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_inv hg, sub_eq_add_neg]

/-- **(M1b-3b-x ★)** From the divisor comparison, `Φ_σ g_T` and `g_{σT}` differ by a
nonzero constant — the σ-naturality input of `weilPairing_galois_core_of_algEquiv`. -/
theorem exists_const_galois_weilFunction {L : Type v} [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra k L] [(W.baseChange L).toAffine.IsElliptic]
    (hic : IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing)
    (σ : L ≃ₐ[k] L) (N : ℤ) (hN : (N : L) ≠ 0)
    (T : (W.baseChange L).toAffine.Point) (hT : N • T = 0)
    (hσT : N • galoisPointEquiv W σ T = 0) :
    ∃ c : L, c ≠ 0 ∧
      galoisFunctionFieldEquiv W σ
          (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT) =
        algebraMap L (W.baseChange L).toAffine.FunctionField c *
          HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN
            (galoisPointEquiv W σ T) hσT := by
  letI := hic
  have hgσT_ne : HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN
      (galoisPointEquiv W σ T) hσT ≠ 0 :=
    HasseWeil.WeilPairing.weilFunction_ne_zero (W.baseChange L) N hN _ hσT
  have hΦg_ne : galoisFunctionFieldEquiv W σ
      (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT) ≠ 0 :=
    (map_ne_zero_iff _ (galoisFunctionFieldEquiv W σ).injective).mpr
      (HasseWeil.WeilPairing.weilFunction_ne_zero (W.baseChange L) N hN T hT)
  have hratio : (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).projectiveDivisorOf
      (galoisFunctionFieldEquiv W σ
        (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT) /
        HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN
          (galoisPointEquiv W σ T) hσT) = 0 := by
    rw [projectiveDivisorOf_div (C := (⟨(W.baseChange L).toAffine⟩ :
        HasseWeil.Curves.SmoothPlaneCurve L))
        (inferInstanceAs (W.baseChange L).toAffine.IsElliptic) hic hΦg_ne hgσT_ne,
      projectiveDivisorOf_galois_weilFunction W σ N hN T hT hσT, sub_self]
  obtain ⟨c, hc, hcval⟩ :=
    HasseWeil.WeilPairing.const_unit_of_projectiveDivisorOf_eq_zero
      (W := (W.baseChange L).toAffine) _ (div_ne_zero hΦg_ne hgσT_ne) hratio
  exact ⟨c, hc, (div_eq_iff hgσT_ne).mp hcval⟩

/-- **(M1b-3b ★★★★)** The Weil pairing is `σ`-equivariant, **conditional only on the
translation conjugation** `Φ_σ ∘ τ_S = τ_{σS} ∘ Φ_σ` at `g_T`. Every other input is
supplied: the σ-naturality of the Weil function (`exists_const_galois_weilFunction`, from
the divisor transport) and the constants law (`galoisFunctionFieldEquiv_algebraMap`). -/
theorem weilPairing_galois_of_conj {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra k L] [(W.baseChange L).toAffine.IsElliptic]
    (hic : IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing)
    (σ : L ≃ₐ[k] L) (N : ℤ) (hN : (N : L) ≠ 0)
    (S T : (W.baseChange L).toAffine.Point) (hS : N • S = 0) (hT : N • T = 0)
    (hσS : N • galoisPointEquiv W σ S = 0) (hσT : N • galoisPointEquiv W σ T = 0)
    (hconj : galoisFunctionFieldEquiv W σ
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange L) S
          (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT)) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange L) (galoisPointEquiv W σ S)
        (galoisFunctionFieldEquiv W σ
          (HasseWeil.WeilPairing.weilFunction (W.baseChange L) N hN T hT))) :
    HasseWeil.WeilPairing.weilPairing (W.baseChange L) N hN
        (galoisPointEquiv W σ S) (galoisPointEquiv W σ T) hσS hσT =
      σ (HasseWeil.WeilPairing.weilPairing (W.baseChange L) N hN S T hS hT) := by
  letI := hic
  obtain ⟨c, hc, hcval⟩ := exists_const_galois_weilFunction W hic σ N hN T hT hσT
  exact weilPairing_galois_core_of_algEquiv (W.baseChange L) N hN (σ : L →+* L)
    (galoisFunctionFieldEquiv W σ) S T (galoisPointEquiv W σ S) (galoisPointEquiv W σ T)
    hS hT hσS hσT hconj hc hcval (galoisFunctionFieldEquiv_algebraMap W σ)

/-- **(M1b-3b leaf, brick 1)** Ring-hom extensionality on the function field: two ring
homomorphisms agreeing on the base constants and on the two generic coordinates are equal.

This is the semilinear analogue of HasseWeil's `algHom_ext_x_y_gen` — needed because the
Galois automorphism `Φ_σ` is only a *ring* equivalence (it moves the `L`-coefficients), so
the `L`-algebra extensionality does not apply to composites involving it. -/
theorem ringHom_ext_const_x_y_gen {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic]
    {ψ₁ ψ₂ : (W.baseChange L).toAffine.FunctionField →+*
      (W.baseChange L).toAffine.FunctionField}
    (hconst : ∀ a : L, ψ₁ (algebraMap L _ a) = ψ₂ (algebraMap L _ a))
    (hx : ψ₁ (HasseWeil.x_gen (W.baseChange L)) = ψ₂ (HasseWeil.x_gen (W.baseChange L)))
    (hy : ψ₁ (HasseWeil.y_gen (W.baseChange L)) = ψ₂ (HasseWeil.y_gen (W.baseChange L))) :
    ψ₁ = ψ₂ := by
  refine IsLocalization.ringHom_ext
    (nonZeroDivisors (W.baseChange L).toAffine.CoordinateRing) ?_
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext ?_ ?_
    · intro a
      exact hconst a
    · exact hx
  · exact hy

/-- **(M1b-3b leaf, brick 2-raw)** The raw fraction-field lift fixes the generic
`x`-coordinate (the coordinate-ring map sends `X ↦ X`). -/
theorem galoisFractionLift_x_gen {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) :
    IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ)
        (HasseWeil.x_gen (W.baseChange L)) =
      HasseWeil.x_gen ((W.baseChange L).map (σ : L →+* L)) := by
  rw [HasseWeil.x_gen, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  refine congrArg (algebraMap _ _) ?_
  show WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine (σ : L →+* L)
      (algebraMap (Polynomial L) _ Polynomial.X) = _
  rw [show (algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X) =
      WeierstrassCurve.Affine.CoordinateRing.mk (W.baseChange L).toAffine
        (Polynomial.C Polynomial.X) from rfl,
    WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show Polynomial.map (Polynomial.mapRingHom (σ : L →+* L))
      (Polynomial.C (Polynomial.X : Polynomial L)) =
    Polynomial.C (Polynomial.X : Polynomial L) from by
      rw [Polynomial.map_C]
      exact congrArg Polynomial.C (Polynomial.map_X _)]
  rfl

/-- **(M1b-3b leaf, brick 2-raw)** The raw σ-lift sends the generic `y`-coordinate of the
curve to that of the mapped curve (the coordinate-ring map sends the adjoined root to the
adjoined root). -/
theorem galoisFractionLift_y_gen {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) :
    IsFractionRing.ringEquivOfRingEquiv (galoisCoordRingEquiv W σ)
        (HasseWeil.y_gen (W.baseChange L)) =
      HasseWeil.y_gen ((W.baseChange L).map (σ : L →+* L)) := by
  rw [HasseWeil.y_gen, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  refine congrArg (algebraMap _ _) ?_
  show WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange L).toAffine (σ : L →+* L)
      (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) = _
  rw [show (AdjoinRoot.root (W.baseChange L).toAffine.polynomial) =
      WeierstrassCurve.Affine.CoordinateRing.mk (W.baseChange L).toAffine Polynomial.X from rfl,
    WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]
  rfl

/-- The curve-equality cast sends the generic `x`-coordinate to the generic
`x`-coordinate. -/
theorem cast_x_gen {L : Type v} [Field L] [DecidableEq L] (V₁ V₂ : WeierstrassCurve L)
    [V₁.toAffine.IsElliptic] [V₂.toAffine.IsElliptic] (h : V₁ = V₂) :
    (RingEquiv.cast (R := fun (U : WeierstrassCurve L) => U.toAffine.FunctionField) h)
        (HasseWeil.x_gen V₁) = HasseWeil.x_gen V₂ := by
  subst h
  rfl

/-- The curve-equality cast sends the generic `y`-coordinate to the generic
`y`-coordinate. -/
theorem cast_y_gen {L : Type v} [Field L] [DecidableEq L] (V₁ V₂ : WeierstrassCurve L)
    [V₁.toAffine.IsElliptic] [V₂.toAffine.IsElliptic] (h : V₁ = V₂) :
    (RingEquiv.cast (R := fun (U : WeierstrassCurve L) => U.toAffine.FunctionField) h)
        (HasseWeil.y_gen V₁) = HasseWeil.y_gen V₂ := by
  subst h
  rfl

/-- **(M1b-3b leaf, brick 2)** `Φ_σ` fixes the generic `x`-coordinate. -/
theorem galoisFunctionFieldEquiv_x_gen {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ (HasseWeil.x_gen (W.baseChange L)) =
      HasseWeil.x_gen (W.baseChange L) := by
  haveI : ((W.baseChange L).map (σ : L →+* L)).toAffine.IsElliptic := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  rw [galoisFunctionFieldEquiv, RingEquiv.trans_apply, galoisFractionLift_x_gen,
    cast_x_gen _ _ (map_algEquiv_baseChange_eq W σ)]

/-- **(M1b-3b leaf, brick 2)** `Φ_σ` fixes the generic `y`-coordinate. -/
theorem galoisFunctionFieldEquiv_y_gen {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ (HasseWeil.y_gen (W.baseChange L)) =
      HasseWeil.y_gen (W.baseChange L) := by
  haveI : ((W.baseChange L).map (σ : L →+* L)).toAffine.IsElliptic := by
    rw [map_algEquiv_baseChange_eq W σ]; infer_instance
  rw [galoisFunctionFieldEquiv, RingEquiv.trans_apply, galoisFractionLift_y_gen,
    cast_y_gen _ _ (map_algEquiv_baseChange_eq W σ)]

/-- **(M1b-3b leaf, brick 3)** `Φ_σ` fixes every constant coming from the base field `k` —
in particular the Weierstrass coefficients of `W ⊗ L`, since `σ` is a `k`-algebra map. -/
theorem galoisFunctionFieldEquiv_algebraMap_base {L : Type v} [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (a : k) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (algebraMap k L a)) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (algebraMap k L a) := by
  rw [galoisFunctionFieldEquiv_algebraMap W σ, σ.commutes]

/-- The Weierstrass coefficients of `W ⊗ L` are base constants, hence `Φ_σ`-fixed. -/
theorem galoisFunctionFieldEquiv_a₁ {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₁) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₁ :=
  galoisFunctionFieldEquiv_algebraMap_base W σ W.a₁

theorem galoisFunctionFieldEquiv_a₂ {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₂) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₂ :=
  galoisFunctionFieldEquiv_algebraMap_base W σ W.a₂

theorem galoisFunctionFieldEquiv_a₃ {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₃) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₃ :=
  galoisFunctionFieldEquiv_algebraMap_base W σ W.a₃

theorem galoisFunctionFieldEquiv_a₄ {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₄) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₄ :=
  galoisFunctionFieldEquiv_algebraMap_base W σ W.a₄

theorem galoisFunctionFieldEquiv_a₆ {L : Type v} [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    galoisFunctionFieldEquiv W σ
        (algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₆) =
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₆ :=
  galoisFunctionFieldEquiv_algebraMap_base W σ W.a₆

section TranslationTransport

variable {L : Type v} [Field L] [DecidableEq L] [Algebra k L]
  [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L)

/-- **(M1b-3b leaf, brick 4a)** `Φ_σ` transports the translation slope: the secant slope
through `(x_gen, y_gen)` and `(xk, yk)` maps to the one through `(x_gen, y_gen)` and
`(σ xk, σ yk)`. Uses the branch-free form `translateSlope_xy_eq` (the generic `x` is
transcendental, so the secant branch always applies) and bricks 2–3. -/
theorem galoisFunctionFieldEquiv_translateSlope (xk yk : L) :
    galoisFunctionFieldEquiv W σ (HasseWeil.translateSlope_xy (W.baseChange L) xk yk) =
      HasseWeil.translateSlope_xy (W.baseChange L) (σ xk) (σ yk) := by
  rw [HasseWeil.translateSlope_xy_eq, HasseWeil.translateSlope_xy_eq, map_div₀, map_sub,
    map_sub, galoisFunctionFieldEquiv_x_gen, galoisFunctionFieldEquiv_y_gen,
    galoisFunctionFieldEquiv_algebraMap, galoisFunctionFieldEquiv_algebraMap]

/-- `Φ_σ` fixes the `a₁`-coefficient of the generic base change `W_KE`. -/
theorem galoisFunctionFieldEquiv_WKE_a₁ :
    galoisFunctionFieldEquiv W σ ((HasseWeil.W_KE (W.baseChange L)).a₁) =
      (HasseWeil.W_KE (W.baseChange L)).a₁ := by
  rw [HasseWeil.W_KE, WeierstrassCurve.map_a₁]
  exact galoisFunctionFieldEquiv_a₁ W σ

/-- `Φ_σ` fixes the `a₂`-coefficient of `W_KE`. -/
theorem galoisFunctionFieldEquiv_WKE_a₂ :
    galoisFunctionFieldEquiv W σ ((HasseWeil.W_KE (W.baseChange L)).a₂) =
      (HasseWeil.W_KE (W.baseChange L)).a₂ := by
  rw [HasseWeil.W_KE, WeierstrassCurve.map_a₂]
  exact galoisFunctionFieldEquiv_a₂ W σ

/-- `Φ_σ` fixes the `a₃`-coefficient of `W_KE`. -/
theorem galoisFunctionFieldEquiv_WKE_a₃ :
    galoisFunctionFieldEquiv W σ ((HasseWeil.W_KE (W.baseChange L)).a₃) =
      (HasseWeil.W_KE (W.baseChange L)).a₃ := by
  rw [HasseWeil.W_KE, WeierstrassCurve.map_a₃]
  exact galoisFunctionFieldEquiv_a₃ W σ

end TranslationTransport

end ModularCurves
