/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.EllipticCurve.PoleSheafMonomialAway

/-!
# Ordered monomials in the model pole filtration

The model monomials `1, x, y, x², xy, x³, ...`, ordered by pole order,
give exactly the generators in each positive stage of `poleOrderFiltration`.
-/

open AlgebraicGeometry

universe u

namespace ModularCurves

/-- The even terms of the positive-pole monomial sequence are powers of `x`. -/
theorem positivePoleMonomial_even
    {M : Type*} [Monoid M] (x y : M) (n : ℕ) :
    positivePoleMonomial x y (2 * n) = x ^ (n + 1) := by
  induction n with
  | zero =>
      simp [positivePoleMonomial]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        positivePoleMonomial, ih]
      simp only [pow_succ]

/-- The odd terms of the positive-pole monomial sequence are `y * xⁿ`. -/
theorem positivePoleMonomial_odd
    {M : Type*} [Monoid M] (x y : M) (n : ℕ) :
    positivePoleMonomial x y (2 * n + 1) = y * x ^ n := by
  induction n with
  | zero =>
      simp [positivePoleMonomial]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
        positivePoleMonomial, ih, pow_succ, mul_assoc]

/-- The affine model monomials in increasing pole order:
`1, x, y, x², xy, x³, ...`. -/
noncomputable def poleOrderMonomialSequence
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    ℕ → W.toAffine.CoordinateRing
  | 0 => 1
  | n + 1 => positivePoleMonomial (coordX W) (coordY W) n

@[simp]
theorem poleOrderMonomialSequence_zero
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    poleOrderMonomialSequence W 0 = 1 :=
  rfl

/-- The terms of odd positive index are the pure powers of `x`. -/
theorem poleOrderMonomialSequence_odd
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :
    poleOrderMonomialSequence W (2 * n + 1) = coordX W ^ (n + 1) := by
  rw [show 2 * n + 1 = 2 * n + 1 by rfl,
    poleOrderMonomialSequence, positivePoleMonomial_even]

/-- The terms of even positive index are the monomials `xⁿy`. -/
theorem poleOrderMonomialSequence_even
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :
    poleOrderMonomialSequence W (2 * n + 2) =
      coordX W ^ n * coordY W := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
    poleOrderMonomialSequence, positivePoleMonomial_odd, mul_comm]

/-- At every positive pole order, the ordered model monomials have exactly
the range used to define the pole-order filtration. -/
theorem range_poleOrderMonomialSequence
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    Set.range (fun i : Fin n => poleOrderMonomialSequence W i) =
      {g | ∃ i : ℕ, 2 * i ≤ n ∧ g = coordX W ^ i} ∪
        {g | ∃ i : ℕ, 2 * i + 3 ≤ n ∧ g = coordX W ^ i * coordY W} := by
  ext g
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    rcases i with _ | i
    · exact Or.inl ⟨0, by omega, by simp⟩
    · rcases i.even_or_odd' with ⟨j, rfl | rfl⟩
      · exact Or.inl
          ⟨j + 1, by omega, poleOrderMonomialSequence_odd W j⟩
      · exact Or.inr
          ⟨j, by omega, poleOrderMonomialSequence_even W j⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · rcases i with _ | i
      · exact ⟨⟨0, by omega⟩, by simp⟩
      · refine ⟨⟨2 * i + 1, by omega⟩, ?_⟩
        exact poleOrderMonomialSequence_odd W i
    · refine ⟨⟨2 * i + 2, by omega⟩, ?_⟩
      exact poleOrderMonomialSequence_even W i

/-- The first `n` ordered model monomials span the model filtration `Fₙ`. -/
theorem span_poleOrderMonomialSequence
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    Submodule.span R
        (Set.range (fun i : Fin n => poleOrderMonomialSequence W i)) =
      poleOrderFiltration W n := by
  rw [range_poleOrderMonomialSequence W hn]
  rfl

/-- Each of the first `n` ordered model monomials belongs to `Fₙ`. -/
theorem poleOrderMonomialSequence_mem
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    poleOrderMonomialSequence W i ∈ poleOrderFiltration W n := by
  rw [← span_poleOrderMonomialSequence W hn]
  exact Submodule.subset_span ⟨i, rfl⟩

end ModularCurves
