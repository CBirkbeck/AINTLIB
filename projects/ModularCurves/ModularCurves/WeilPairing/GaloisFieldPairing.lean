/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.GaloisFunctionField

/-!
# Galois equivariance of the bundled field Weil pairing (DS4 M1b-4)

`WeilPairing/GaloisFunctionField.lean` proves the `σ`-equivariance of HasseWeil's
`ℤ`-indexed Weil pairing (`weilPairing_galois`). This file repackages it in the shape the
DS4 descent input wants: the `ℕ`-indexed, `μ_N`-bundled `fieldWeilPairing` of
`WeilPairing/FieldPairing.lean`, with the `σ`-action on points given by
`galoisPointEquiv`.

Everything here is a thin wrapper — the mathematical content is `weilPairing_galois`.
-/

universe u v

open WeierstrassCurve

namespace ModularCurves

variable {k : Type u} [Field k] (W : WeierstrassCurve k)
  {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L]
  [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L)

/-- The coordinate ring of a base-changed elliptic curve, read in the
`SmoothPlaneCurve` spelling `weilPairing_galois` uses, is integrally closed
(HasseWeil's `isIntegrallyClosed_coordinateRing`, an instance on the affine curve). -/
theorem isIntegrallyClosed_baseChange_coordinateRing :
    IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ :
      HasseWeil.Curves.SmoothPlaneCurve L).CoordinateRing :=
  inferInstanceAs (IsIntegrallyClosed (W.baseChange L).toAffine.CoordinateRing)

/-- **(M1b-4 ★)** `σ`-equivariance of the bundled `μ_N`-valued Weil pairing:
`e_N(σP, σQ) = σ(e_N(P, Q))`. -/
theorem fieldWeilPairing_galois (N : ℕ) (hN : (N : L) ≠ 0)
    (P Q : (W.baseChange L).toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (hσP : (N : ℤ) • galoisPointEquiv W σ P = 0)
    (hσQ : (N : ℤ) • galoisPointEquiv W σ Q = 0) :
    (fieldWeilPairing (W.baseChange L) N hN
        (galoisPointEquiv W σ P) (galoisPointEquiv W σ Q) hσP hσQ : L) =
      σ (fieldWeilPairing (W.baseChange L) N hN P Q hP hQ : L) := by
  rw [fieldWeilPairing_val, fieldWeilPairing_val]
  exact weilPairing_galois W σ (isIntegrallyClosed_baseChange_coordinateRing W)
    (N : ℤ) (by simpa using hN) P Q hP hQ hσP hσQ

/-- **(M1b-4)** The `σ`-image torsion hypotheses come for free: `galoisPointEquiv` is
additive, so it preserves `N`-torsion. -/
theorem zsmul_galoisPointEquiv_eq_zero (N : ℤ) {P : (W.baseChange L).toAffine.Point}
    (hP : N • P = 0) : N • galoisPointEquiv W σ P = 0 := by
  rw [← map_zsmul (galoisPointEquiv W σ), hP, map_zero]

/-- **(M1b-4 ★, hypothesis-free form)** `σ`-equivariance of the bundled Weil pairing with
the `σ`-side torsion hypotheses supplied automatically. -/
theorem fieldWeilPairing_galois' (N : ℕ) (hN : (N : L) ≠ 0)
    (P Q : (W.baseChange L).toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (fieldWeilPairing (W.baseChange L) N hN
        (galoisPointEquiv W σ P) (galoisPointEquiv W σ Q)
        (zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hP)
        (zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hQ) : L) =
      σ (fieldWeilPairing (W.baseChange L) N hN P Q hP hQ : L) :=
  fieldWeilPairing_galois W σ N hN P Q hP hQ _ _

end ModularCurves
