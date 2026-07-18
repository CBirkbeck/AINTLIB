/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# The second Bosma–Lenstra law lands on the curve, over a field (T-W7.0c-c5α, field layer)

The on-curve identity for law 2 is deliberately NOT a `linear_combination` certificate
(cofactors ≈ 4–8k terms; see the module docstring of `AdditionLaw.lean`). This file proves its
**field case** with no new polynomial computation, from the six kernel-checked certificates of
`AdditionLaw.lean` plus mathlib's representative-level `nonsingular_add`:

* on the diagonal class (`P ≈ Q`), law 2 rescales (`dblAddXYZ_smul`) to its diagonal, which
  **is** mathlib's doubling (`dblAddXYZ_self`), and `W.add P P = W.dblXYZ P` is nonsingular;
* off the diagonal class, `W.add P Q = W.addXYZ P Q` is nonsingular — in particular nonzero
  and on the curve — and the three cross-law minors force `dblAddXYZ P Q` to be a scalar
  multiple of it (or zero, where the equation is trivial).

The scheme-level c5α statement (vanishing of `F(dblAdd)` in the biprojective coordinate ring
of `E_U ×_U E_U`) follows from this field case by evaluation at maximal ideals through
`eq_zero_of_forall_isMaximal_mem` (proven in `AdditionLaw.lean`) — that wiring is the next
c5α increment.
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

namespace WeierstrassCurve.Projective

section CommRing

variable {R : Type*} [CommRing R] {W' : Projective R}

lemma dblAddXYZ_x (P Q : Fin 3 → R) : W'.dblAddXYZ P Q x = W'.dblAddX P Q := rfl

lemma dblAddXYZ_y (P Q : Fin 3 → R) : W'.dblAddXYZ P Q y = W'.dblAddY P Q := rfl

lemma dblAddXYZ_z (P Q : Fin 3 → R) : W'.dblAddXYZ P Q z = W'.dblAddZ P Q := rfl

lemma dblAddX_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.dblAddX (u • P) Q = u ^ 2 * W'.dblAddX P Q := by
  simpa using W'.dblAddX_smul P Q u 1

lemma dblAddY_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.dblAddY (u • P) Q = u ^ 2 * W'.dblAddY P Q := by
  simpa using W'.dblAddY_smul P Q u 1

lemma dblAddZ_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.dblAddZ (u • P) Q = u ^ 2 * W'.dblAddZ P Q := by
  simpa using W'.dblAddZ_smul P Q u 1

lemma dblAddXYZ_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.dblAddXYZ (u • P) Q = u ^ 2 • W'.dblAddXYZ P Q := by
  funext i
  fin_cases i <;>
    simp [dblAddXYZ, dblAddX_smul_left, dblAddY_smul_left, dblAddZ_smul_left]

/-- The zero triple satisfies the homogeneous Weierstrass equation (trivially — the cubic form
has no constant term). This is the degenerate case of the on-curve statement for law 2. -/
lemma equation_zero_triple : W'.Equation (0 : Fin 3 → R) := by
  simp [equation_iff]

/-- A nonsingular point representative is a nonzero triple: all three partial derivatives of
the Weierstrass cubic vanish at the zero triple. -/
lemma Nonsingular.ne_zero {P : Fin 3 → R} (hP : W'.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  rcases (nonsingular_iff _).mp hP with ⟨-, h | h | h⟩ <;> simp at h

end CommRing

section Field

variable {F : Type*} [Field F] {W : Projective F}

/-- Two vectors in `F³` with vanishing pairwise cross terms (`2 × 2` minors) are proportional,
provided the second is nonzero. -/
lemma exists_eq_smul_of_cross_eq_zero {v w : Fin 3 → F} (hw : w ≠ 0)
    (h01 : v x * w y = v y * w x) (h02 : v x * w z = v z * w x)
    (h12 : v y * w z = v z * w y) : ∃ c : F, v = c • w := by
  rcases eq_or_ne (w x) 0 with hwx | hwx
  · rcases eq_or_ne (w y) 0 with hwy | hwy
    · rcases eq_or_ne (w z) 0 with hwz | hwz
      · refine absurd (funext fun j => ?_) hw
        fin_cases j
        exacts [hwx, hwy, hwz]
      · refine ⟨v z / w z, funext fun j => ?_⟩
        fin_cases j
        · show v x = v z / w z * w x
          rw [div_mul_eq_mul_div, eq_div_iff hwz]
          linear_combination h02
        · show v y = v z / w z * w y
          rw [div_mul_eq_mul_div, eq_div_iff hwz]
          linear_combination h12
        · show v z = v z / w z * w z
          rw [div_mul_cancel₀ _ hwz]
    · refine ⟨v y / w y, funext fun j => ?_⟩
      fin_cases j
      · show v x = v y / w y * w x
        rw [div_mul_eq_mul_div, eq_div_iff hwy]
        linear_combination h01
      · show v y = v y / w y * w y
        rw [div_mul_cancel₀ _ hwy]
      · show v z = v y / w y * w z
        rw [div_mul_eq_mul_div, eq_div_iff hwy]
        linear_combination -h12
  · refine ⟨v x / w x, funext fun j => ?_⟩
    fin_cases j
    · show v x = v x / w x * w x
      rw [div_mul_cancel₀ _ hwx]
    · show v y = v x / w x * w y
      rw [div_mul_eq_mul_div, eq_div_iff hwx]
      linear_combination -h01
    · show v z = v x / w x * w z
      rw [div_mul_eq_mul_div, eq_div_iff hwx]
      linear_combination -h02

/-- **(T-W7.0c-c5α, field layer)** Over a field, the second Bosma–Lenstra addition law lands
on the curve: no polynomial certificate — the diagonal class reduces to mathlib's doubling via
`dblAddXYZ_self`, and off the diagonal the three certified minors make `dblAddXYZ` proportional
to mathlib's `addXYZ`, whose nonsingularity is `nonsingular_add`. -/
theorem equation_dblAddXYZ {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Equation (W.dblAddXYZ P Q) := by
  classical
  by_cases hPQ : P ≈ Q
  · rcases hPQ with ⟨u, rfl⟩
    show W.Equation (W.dblAddXYZ ((u : F) • Q) Q)
    rw [dblAddXYZ_smul_left, equation_smul _ (u.isUnit.pow 2), dblAddXYZ_self hQ.left]
    have h := (nonsingular_add hQ hQ).left
    rwa [add_of_equiv (Setoid.refl Q)] at h
  · have hNS := nonsingular_add hP hQ
    rw [add_of_not_equiv hPQ] at hNS
    by_cases hv : W.dblAddXYZ P Q = 0
    · rw [hv]
      exact equation_zero_triple
    · have h01 : W.dblAddXYZ P Q x * W.addXYZ P Q y
          = W.dblAddXYZ P Q y * W.addXYZ P Q x := by
        simp only [dblAddXYZ_x, dblAddXYZ_y, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination -W.addX_mul_dblAddY hP.left hQ.left
      have h02 : W.dblAddXYZ P Q x * W.addXYZ P Q z
          = W.dblAddXYZ P Q z * W.addXYZ P Q x := by
        simp only [dblAddXYZ_x, dblAddXYZ_z, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        linear_combination -W.addX_mul_dblAddZ hP.left hQ.left
      have h12 : W.dblAddXYZ P Q y * W.addXYZ P Q z
          = W.dblAddXYZ P Q z * W.addXYZ P Q y := by
        simp only [dblAddXYZ_y, dblAddXYZ_z, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        linear_combination -W.addY_mul_dblAddZ hP.left hQ.left
      obtain ⟨c, hc⟩ := exists_eq_smul_of_cross_eq_zero hNS.ne_zero h01 h02 h12
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hv hc
      rw [hc]
      exact (equation_smul _ (isUnit_iff_ne_zero.mpr hc0)).mpr hNS.left

/-- **(T-W7.0c·c2, field-case non-vanishing — the two laws cover)** Over a field the two
Bosma–Lenstra laws never both degenerate: for nonsingular `P`, `Q` either law 1 (`addXYZ`) or
law 2 (`dblAddXYZ`) is a nonzero triple. Off the diagonal `add P Q = addXYZ P Q` is nonsingular
(`nonsingular_add`) hence nonzero; on it (`P ≈ Q`) `dblAddXYZ` rescales to `u² • dblXYZ Q` with
`dblXYZ Q = add Q Q` nonsingular. This is the field layer of `blOpenZ ⊔ blOpenY = ⊤`: it forces
`span (range lawOneTriple ∪ range lawTwoTriple)` to have no common zero, hence to be the unit ideal
(via `regularityOpen_sup_eq_top_iff` + Jacobson evaluation at maximal ideals). -/
theorem addXYZ_ne_zero_or_dblAddXYZ_ne_zero {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ∨ W.dblAddXYZ P Q ≠ 0 := by
  classical
  by_cases hPQ : P ≈ Q
  · right
    rcases hPQ with ⟨u, rfl⟩
    show W.dblAddXYZ ((u : F) • Q) Q ≠ 0
    rw [dblAddXYZ_smul_left, dblAddXYZ_self hQ.left]
    have hdbl : W.dblXYZ Q ≠ 0 := by
      have h := nonsingular_add hQ hQ
      rw [add_of_equiv (Setoid.refl Q)] at h
      exact h.ne_zero
    exact smul_ne_zero (pow_ne_zero 2 u.ne_zero) hdbl
  · left
    have hNS := nonsingular_add hP hQ
    rw [add_of_not_equiv hPQ] at hNS
    exact hNS.ne_zero

end Field

end WeierstrassCurve.Projective
