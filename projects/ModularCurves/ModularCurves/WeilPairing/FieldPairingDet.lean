/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.PairingAdjoint
import ModularCurves.ForMathlib.RootOfUnityIntPow
import ModularCurves.WeilPairing.FieldPairing

/-!
# The determinant law of the field-level Weil pairing (WP-A1)

Route A builds the relative Weil pairing by descending the determinant model along a
trivialising cover, and the descent works only if the root of unity attached to a
trivialisation transforms by the inverse determinant of the transition
(`WeilPairing/RootSplitting.lean`, and the plan entry "route A properly"). The
transformation law comes from the **field-level** pairing, which AINTLIB already has
sorry-free (`HasseWeil.WeilPairing.weilPairing`, Silverman *AEC* III.8).

This file proves that law: re-marking a pair `(P, Q)` of `ℓ`-torsion points by an integer
matrix raises the pairing to the determinant. It is stated multiplicatively —
`e(aP+bQ, cP+dQ) · e(P,Q)^{bc} = e(P,Q)^{ad}` — so that no inverses or `zpow` appear;
the `ZMod`-exponent form used by the descent is derived from it downstream.

Source: Silverman, *AEC* III.8.1 — (a) bilinearity, (b) alternation, (c) antisymmetry.
-/

universe u

open WeierstrassCurve HasseWeil.WeilPairing

namespace ModularCurves

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A1)** The determinant law of the Weil pairing: re-marking `(P, Q)` by the integer
matrix `!![a, b; c, d]` raises the pairing to `ad - bc`. Stated multiplicatively to avoid
inverses: `e(aP+bQ, cP+dQ) · e(P,Q)^{bc} = e(P,Q)^{ad}`.

This is the transformation law that forces the det twist in the descent construction of the
relative pairing: a change of trivialisation by `g` multiplies the determinant model by
`det g`, so the root of unity must change by `(det g)⁻¹`.

Source: Silverman, *AEC* III.8.1 (a) bilinearity, (b) alternation, (c) antisymmetry. -/
theorem weilPairing_gl2 (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P Q : W.toAffine.Point) (hP : ℓ • P = 0) (hQ : ℓ • Q = 0)
    (a b c d : ℕ)
    (h₁ : ℓ • (a • P + b • Q) = 0) (h₂ : ℓ • (c • P + d • Q) = 0) :
    weilPairing W ℓ hℓ (a • P + b • Q) (c • P + d • Q) h₁ h₂ *
        weilPairing W ℓ hℓ P Q hP hQ ^ (b * c) =
      weilPairing W ℓ hℓ P Q hP hQ ^ (a * d) := by
  -- torsion hypotheses for the pieces
  have haP : ℓ • (a • P) = 0 := smul_nsmul_eq_zero W ℓ P hP a
  have hbQ : ℓ • (b • Q) = 0 := smul_nsmul_eq_zero W ℓ Q hQ b
  have hcP : ℓ • (c • P) = 0 := smul_nsmul_eq_zero W ℓ P hP c
  have hdQ : ℓ • (d • Q) = 0 := smul_nsmul_eq_zero W ℓ Q hQ d
  -- split the left slot, then each right slot
  rw [weilPairing_mul_left W ℓ hℓ (a • P) (b • Q) (c • P + d • Q) haP hbQ h₂ h₁,
    weilPairing_mul_right W ℓ hℓ (a • P) (c • P) (d • Q) haP hcP hdQ,
    weilPairing_mul_right W ℓ hℓ (b • Q) (c • P) (d • Q) hbQ hcP hdQ]
  -- evaluate the four terms
  rw [weilPairing_nsmul_left W ℓ hℓ P (c • P) hP hcP a haP,
    weilPairing_nsmul_left W ℓ hℓ P (d • Q) hP hdQ a haP,
    weilPairing_nsmul_left W ℓ hℓ Q (c • P) hQ hcP b hbQ,
    weilPairing_nsmul_left W ℓ hℓ Q (d • Q) hQ hdQ b hbQ,
    weilPairing_nsmul_right W ℓ hℓ P P hP hP c hcP,
    weilPairing_nsmul_right W ℓ hℓ P Q hP hQ d hdQ,
    weilPairing_nsmul_right W ℓ hℓ Q P hQ hP c hcP,
    weilPairing_nsmul_right W ℓ hℓ Q Q hQ hQ d hdQ]
  -- the diagonal terms are `1`
  rw [weilPairing_self W ℓ hℓ P hP, weilPairing_self W ℓ hℓ Q hQ]
  -- and `e(Q,P) · e(P,Q) = 1`
  have hanti := weilPairing_antisymm W ℓ hℓ Q P hQ hP
  have hcollect : (weilPairing W ℓ hℓ Q P hQ hP * weilPairing W ℓ hℓ P Q hP hQ) ^ (b * c)
      = 1 := by rw [hanti, one_pow]
  rw [mul_pow] at hcollect
  calc ((1 : F) ^ c) ^ a * (weilPairing W ℓ hℓ P Q hP hQ ^ d) ^ a *
        ((weilPairing W ℓ hℓ Q P hQ hP ^ c) ^ b * ((1 : F) ^ d) ^ b) *
        weilPairing W ℓ hℓ P Q hP hQ ^ (b * c)
      = weilPairing W ℓ hℓ P Q hP hQ ^ (a * d) *
        (weilPairing W ℓ hℓ Q P hQ hP ^ (b * c) *
          weilPairing W ℓ hℓ P Q hP hQ ^ (b * c)) := by
        rw [one_pow, one_pow, one_pow, one_pow, one_mul, mul_one, ← pow_mul, ← pow_mul,
          mul_comm d a, mul_comm c b]
        ring
    _ = weilPairing W ℓ hℓ P Q hP hQ ^ (a * d) := by rw [hcollect, mul_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A2)** The determinant law in the `μ_N`-bundled packaging: the same identity for
`fieldWeilPairing`, which is the form the descent's root-of-unity datum uses. -/
theorem fieldWeilPairing_gl2 (N : ℕ) (hN : (N : F) ≠ 0)
    (P Q : W.toAffine.Point) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (a b c d : ℕ)
    (h₁ : (N : ℤ) • (a • P + b • Q) = 0) (h₂ : (N : ℤ) • (c • P + d • Q) = 0) :
    (fieldWeilPairing W N hN (a • P + b • Q) (c • P + d • Q) h₁ h₂ : F) *
        (fieldWeilPairing W N hN P Q hP hQ : F) ^ (b * c) =
      (fieldWeilPairing W N hN P Q hP hQ : F) ^ (a * d) := by
  have hz : ((N : ℤ) : F) ≠ 0 := by simpa using hN
  simp only [fieldWeilPairing_val]
  exact weilPairing_gl2 W (N : ℤ) hz P Q hP hQ a b c d h₁ h₂

/- `pow_eq_pow_of_nat_modEq`, `pow_val_add` and `pow_val_mul` moved to
`ForMathlib/RootOfUnityIntPow.lean`, so that the DS4 register in `WeilPairing/Basic.lean`
can share them without importing this file (which pulls in HasseWeil). -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A3)** The determinant law with a `GL₂(ℤ/N)` matrix: re-marking `(P, Q)` by `g`
raises the pairing to `det g`. This is the exact form the descent's cocycle consumes — the
root of unity attached to a trivialisation must transform by `(det g)⁻¹`, so this law is
what makes the det twist a *theorem* rather than an assumption. -/
theorem fieldWeilPairing_gl2_zmod (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)
    (P Q : W.toAffine.Point) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (g : Matrix (Fin 2) (Fin 2) (ZMod N))
    (h₁ : (N : ℤ) • ((g 0 0).val • P + (g 0 1).val • Q) = 0)
    (h₂ : (N : ℤ) • ((g 1 0).val • P + (g 1 1).val • Q) = 0) :
    (fieldWeilPairing W N hN ((g 0 0).val • P + (g 0 1).val • Q)
        ((g 1 0).val • P + (g 1 1).val • Q) h₁ h₂ : F) =
      (fieldWeilPairing W N hN P Q hP hQ : F) ^
        (g 0 0 * g 1 1 - g 0 1 * g 1 0).val := by
  set e : F := (fieldWeilPairing W N hN P Q hP hQ : F) with he
  have heN : e ^ N = 1 := (fieldWeilPairing W N hN P Q hP hQ).2
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne N)] at heN
    exact zero_ne_one heN
  have hmain := fieldWeilPairing_gl2 W N hN P Q hP hQ
    (g 0 0).val (g 0 1).val (g 1 0).val (g 1 1).val h₁ h₂
  refine mul_right_cancel₀ (pow_ne_zero ((g 0 1).val * (g 1 0).val) hne) ?_
  rw [hmain]
  calc e ^ ((g 0 0).val * (g 1 1).val)
      = e ^ (g 0 0 * g 1 1).val := (pow_val_mul heN _ _).symm
    _ = e ^ ((g 0 0 * g 1 1 - g 0 1 * g 1 0) + g 0 1 * g 1 0).val := by ring_nf
    _ = e ^ (g 0 0 * g 1 1 - g 0 1 * g 1 0).val * e ^ (g 0 1 * g 1 0).val :=
        (pow_val_add heN _ _).symm
    _ = e ^ (g 0 0 * g 1 1 - g 0 1 * g 1 0).val * e ^ ((g 0 1).val * (g 1 0).val) := by
        rw [pow_val_mul heN]

end ModularCurves
