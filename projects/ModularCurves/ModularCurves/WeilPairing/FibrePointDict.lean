/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldPairing
import ModularCurves.Moduli.E3DatumAssembly

/-!
# The geometric-fibre point dictionary and the Weil pairing on scheme points (DS4 M1b-1/2)

`fieldWeilPairing` (M1a) lives on mathlib's affine Weierstrass points. The DS4 descent
input (`exists_pairingAlgebraHom_of_galoisEquivariant`) lives on the *scheme* points
`E.Point t` at a geometric point `t`. This file bridges the two through a chart:

* `chartAffinePointEquiv` — for a local presentation `Pr` of `E` over an affine open `V`
  and a field `K` over `Γ(S, V)`, the scheme points of `E` at the induced `K`-point are
  additively equivalent to the affine Weierstrass points of `Pr.W ⊗ K`
  (`chartPointsEquiv` ∘ `modelPointAddEquiv`);
* `fibreWeilPairing` — the Weil pairing transported along it, with bilinearity,
  alternation and nondegeneracy inherited from `WeilPairing/FieldPairing.lean`.

This is the M1b input: everything here is sorry-free, so the remaining DS4 field-level
work is Galois equivariance (M1b-3) plus the descent call (M1c).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

open LocalPresentation

variable {S : Scheme.{u}} {E : EllipticCurve S} {V : S.affineOpens}
  (Pr : LocalPresentation E.toEllipticCurveGeom V)
  (K : Type u) [Field K] [DecidableEq K] [Algebra Γ(S, V.1) K]

/-- The base change of an elliptic Weierstrass curve is elliptic, in the `toAffine`
spelling the affine point group needs (`baseChange` is `map (algebraMap …)`). -/
instance baseChange_toAffine_isElliptic {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] (K : Type u) [Field K] [Algebra R K] :
    (W.baseChange K).toAffine.IsElliptic :=
  inferInstanceAs (W.map (algebraMap R K)).IsElliptic

/-- **(M1b-1)** The geometric-fibre point dictionary: through a chart, the scheme points
of `E` at a `K`-point of the chart are mathlib's affine points of the base-changed
Weierstrass model. -/
noncomputable def chartAffinePointEquiv :
    letI := Pr.elliptic
    E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V) ≃+
      (Pr.W.baseChange K).toAffine.Point :=
  letI := Pr.elliptic
  (chartPointsEquiv Pr (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)))).trans
    (modelPointAddEquiv Pr.W)

variable [IsAlgClosed K] (N : ℕ) (hN : (N : K) ≠ 0)

/-- **(M1b-2)** The Weil pairing on the scheme points of `E` at a geometric fibre,
computed through a chart. -/
noncomputable def fibreWeilPairing
    (P Q : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) : { u : K // u ^ N = 1 } :=
  letI := Pr.elliptic
  fieldWeilPairing (Pr.W.baseChange K) N hN
    (chartAffinePointEquiv Pr K P) (chartAffinePointEquiv Pr K Q)
    (by rw [← map_zsmul, hP, map_zero]) (by rw [← map_zsmul, hQ, map_zero])

/-- **(M1b-2)** Bilinearity in the first slot, transported from the field-level pairing. -/
theorem fibreWeilPairing_mul_left
    (P P' Q : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hP : (N : ℤ) • P = 0) (hP' : (N : ℤ) • P' = 0) (hQ : (N : ℤ) • Q = 0)
    (hPP' : (N : ℤ) • (P + P') = 0) :
    (fibreWeilPairing Pr K N hN (P + P') Q hPP' hQ : K) =
      (fibreWeilPairing Pr K N hN P Q hP hQ : K) *
        (fibreWeilPairing Pr K N hN P' Q hP' hQ : K) := by
  letI := Pr.elliptic
  have hadd : (chartAffinePointEquiv Pr K) (P + P') =
      (chartAffinePointEquiv Pr K) P + (chartAffinePointEquiv Pr K) P' := map_add _ _ _
  have hsum : (N : ℤ) • ((chartAffinePointEquiv Pr K) P +
      (chartAffinePointEquiv Pr K) P') = 0 := by
    rw [← hadd, ← map_zsmul, hPP', map_zero]
  calc (fibreWeilPairing Pr K N hN (P + P') Q hPP' hQ : K)
      = (fieldWeilPairing (Pr.W.baseChange K) N hN
          ((chartAffinePointEquiv Pr K) P + (chartAffinePointEquiv Pr K) P')
          ((chartAffinePointEquiv Pr K) Q) hsum
          (by rw [← map_zsmul, hQ, map_zero]) : K) :=
        fieldWeilPairing_congr (Pr.W.baseChange K) N hN _ _ _ _ hadd rfl
    _ = _ := fieldWeilPairing_mul_left (Pr.W.baseChange K) N hN _ _ _
        (by rw [← map_zsmul, hP, map_zero]) (by rw [← map_zsmul, hP', map_zero])
        (by rw [← map_zsmul, hQ, map_zero]) hsum

/-- **(M1b-2)** The pairing is alternating. -/
theorem fibreWeilPairing_self
    (P : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hP : (N : ℤ) • P = 0) :
    (fibreWeilPairing Pr K N hN P P hP hP : K) = 1 :=
  letI := Pr.elliptic
  fieldWeilPairing_self (Pr.W.baseChange K) N hN _ _

/-- **(M1b-2)** Nondegeneracy: a point pairing trivially with all `N`-torsion is zero. -/
theorem fibreWeilPairing_eq_zero_of_forall
    (Q : letI := Pr.elliptic
      E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
    (hQ : (N : ℤ) • Q = 0)
    (h : ∀ (P : letI := Pr.elliptic
        E.Point (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ chartρ V))
        (hP : (N : ℤ) • P = 0),
      (fibreWeilPairing Pr K N hN P Q hP hQ : K) = 1) :
    Q = 0 := by
  letI := Pr.elliptic
  have hzero : chartAffinePointEquiv Pr K Q = 0 := by
    refine fieldWeilPairing_eq_zero_of_forall (Pr.W.baseChange K) N hN _ ?_ ?_
    · rw [← map_zsmul, hQ, map_zero]
    · intro A hA
      have hsym : (N : ℤ) • (chartAffinePointEquiv Pr K).symm A = 0 := by
        refine (chartAffinePointEquiv Pr K).injective ?_
        rw [map_zsmul, (chartAffinePointEquiv Pr K).apply_symm_apply, hA, map_zero]
      have hpre := h ((chartAffinePointEquiv Pr K).symm A) hsym
      refine Eq.trans ?_ hpre
      exact fieldWeilPairing_congr (Pr.W.baseChange K) N hN _ _ _ _
        ((chartAffinePointEquiv Pr K).apply_symm_apply A).symm rfl
  exact (chartAffinePointEquiv Pr K).injective (by rw [hzero, map_zero])

end ModularCurves
