/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The universal naive level-4 object `ℰ₄` over `ℤ[1/2]` (STREAM-E4, E4-A)

**(B2 resolution of record — board v10.342, b2_log `B2-DECISION`.)** The D(2) mouth of the
KM 4.7.0 engine is re-instantiated at `δ = ` naive level 4 (KM 4.6: a genuine finite étale
`GL₂(ℤ/4)`-torsor over `S[1/2]` with the global re-marking action `gammaFullNaiveGlAction`),
replacing the Legendre problem whose constant-group torsor claim (KM 4.6.2) is refuted.

The bootstrap object: the moduli ring

  `E4ModuliRing = R[B, u, v][1/(B(1−16B))] / (v² + uv + Bv − u³ − Bu², e4Rel)`,
  `e4Rel = 2u⁴ + u³ + 3Bu² + 4B²u + 2B³`,

carrying the universal Tate-normal-form curve `y² + xy + By = x³ + Bx²`
(`⟨1, B, B, 0, 0⟩`, Loeffler Prop 3.3.4 / Cor 3.3.5 at the order-4 locus `A = 1`),
with `P = (0, 0)` of exact order 4 (`2P = (−B, 0)` is visibly 2-torsion) and
`Q = (u, v)` with `2Q` on the complementary 2-torsion pair
(`ψ₂²(x) = (x + B)(4x² + x + B)`; `e4Rel` is the cleared form of
`4·x(2Q)² + x(2Q) + B = 0` via the master identity
`ψ₂(Q)³ · ψ₂(2Q) ≡ u(2B + u) · e4Rel (mod curve)`).

Sympy-verified certificates (2026-07-20, to be `ring`-certified per ticket):
`Δ = −B⁴(16B − 1)`; `e4Rel(B,0) = 2B³`, `e4Rel(B,−2B) = 2B³(16B−1)` (so `u`, `u + 2B`
are units — `Q ∉ ⟨P⟩` and `2Q ≠ 2P` automatic); `res_u(e4Rel, ψ₂²-abscissa) = 8B⁸(16B−1)²`
(so `ψ₂(Q)` is a unit — `2Q ≠ 0` automatic); `disc_u(e4Rel) = 4B⁶(16B−1)³` (étale fibres,
`4 × 2 = 8 = |GL₂(ℤ/4)| / #{order-4 points}`).

Decomposition of record: `.mathlib-quality/decomposition-e4.md` §2 (E4A-1 … E4A-14),
with verbatim KM/Loeffler quotes in §0. The construction mirrors the landed ℰ₃ machine
(`Moduli/UniversalLevelThree.lean`) leaf-for-leaf; the classifying chain (E4A-12) and
round-trip lemmas (E4A-13) are added by their tickets following the ℰ₃ literal pattern.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits Scheme MvPolynomial LocalPresentation

variable (R : CommRingCat.{u})

/-! ### E4A-1 — the moduli ring, the universal curve, and the marked sections -/

/-- **(E4A-1)** The curve relation `v² + uv + Bv − u³ − Bu²` in `R[B, u, v]`
(`X 0 = B`, `X 1 = u`, `X 2 = v`): `Q = (u, v)` lies on `y² + xy + By = x³ + Bx²`. -/
def e4CurveRel : MvPolynomial (Fin 3) R :=
  X 2 ^ 2 + X 1 * X 2 + X 0 * X 2 - X 1 ^ 3 - X 0 * X 1 ^ 2

/-- **(E4A-1)** The order-4 relation `2u⁴ + u³ + 3Bu² + 4B²u + 2B³`: the cleared form of
"`x([2]Q)` satisfies the complementary 2-torsion quadratic `4x² + x + B`". -/
def e4OrderRel : MvPolynomial (Fin 3) R :=
  2 * X 1 ^ 4 + X 1 ^ 3 + 3 * X 0 * X 1 ^ 2 + 4 * X 0 ^ 2 * X 1 + 2 * X 0 ^ 3

/-- **(E4A-1)** The quotient `R[B, u, v]/(curve, e4Rel)`. -/
abbrev E4Quotient : Type u :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {e4CurveRel R, e4OrderRel R}

/-- **(E4A-1)** The inverted element `B(1 − 16B)` (the discriminant up to the unit `−B³`
and sign: `Δ = −B⁴(16B − 1)`). -/
def e4Delta : E4Quotient R :=
  Ideal.Quotient.mk _ (X 0 * (1 - 16 * X 0))

/-- **(E4A-1)** The `ℰ₄` moduli ring `R[B, u, v][(B(1−16B))⁻¹]/(curve, e4Rel)`. -/
abbrev E4ModuliRing : Type u := Localization.Away (e4Delta R)

/-- **(E4A-1)** The image of `B` in the moduli ring. -/
def e4B : E4ModuliRing R :=
  algebraMap (E4Quotient R) (E4ModuliRing R) (Ideal.Quotient.mk _ (X 0))

/-- **(E4A-1)** The image of `u = x(Q)` in the moduli ring. -/
def e4U : E4ModuliRing R :=
  algebraMap (E4Quotient R) (E4ModuliRing R) (Ideal.Quotient.mk _ (X 1))

/-- **(E4A-1)** The image of `v = y(Q)` in the moduli ring. -/
def e4V : E4ModuliRing R :=
  algebraMap (E4Quotient R) (E4ModuliRing R) (Ideal.Quotient.mk _ (X 2))

/-- **(E4A-1)** The universal level-4 Tate-normal-form curve `y² + xy + By = x³ + Bx²`
(Loeffler Prop 3.3.4 at the order-4 locus `a₁ = 1`; KM 2.2.10-11 method at level 4). -/
def universalE4 : WeierstrassCurve (E4ModuliRing R) :=
  ⟨1, e4B R, e4B R, 0, 0⟩

/-! ### E4A-2/E4A-3 — ellipticity and the automatic units -/

/-- The composite `R[B,u,v] → E4Quotient → E4ModuliRing`. -/
def e4Map : MvPolynomial (Fin 3) R →+* E4ModuliRing R :=
  (algebraMap (E4Quotient R) (E4ModuliRing R)).comp
    (Ideal.Quotient.mk (Ideal.span {e4CurveRel R, e4OrderRel R}))

@[simp] theorem e4Map_X0 : e4Map R (X 0) = e4B R := rfl
@[simp] theorem e4Map_X1 : e4Map R (X 1) = e4U R := rfl
@[simp] theorem e4Map_X2 : e4Map R (X 2) = e4V R := rfl

/-- The curve relation vanishes in the moduli ring. -/
theorem e4CurveRel_map_eq_zero : e4Map R (e4CurveRel R) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {e4CurveRel R, e4OrderRel R}))
      (e4CurveRel R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  rw [e4Map, RingHom.comp_apply, h, map_zero]

/-- The order-4 relation vanishes in the moduli ring. -/
theorem e4OrderRel_map_eq_zero : e4Map R (e4OrderRel R) = 0 := by
  have h : (Ideal.Quotient.mk (Ideal.span {e4CurveRel R, e4OrderRel R}))
      (e4OrderRel R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [e4Map, RingHom.comp_apply, h, map_zero]

/-- The curve relation among `e4B, e4U, e4V`. -/
theorem e4_curve_rel :
    e4V R ^ 2 + e4U R * e4V R + e4B R * e4V R - e4U R ^ 3 - e4B R * e4U R ^ 2 = 0 := by
  have h := e4CurveRel_map_eq_zero R
  simp only [e4CurveRel, map_add, map_sub, map_mul, map_pow,
    e4Map_X0, e4Map_X1, e4Map_X2] at h
  linear_combination h

/-- The order-4 relation among `e4B, e4U`. -/
theorem e4_order_rel :
    2 * e4U R ^ 4 + e4U R ^ 3 + 3 * e4B R * e4U R ^ 2 + 4 * e4B R ^ 2 * e4U R
      + 2 * e4B R ^ 3 = 0 := by
  have h := e4OrderRel_map_eq_zero R
  simp only [e4OrderRel, map_add, map_sub, map_mul, map_pow, map_ofNat,
    e4Map_X0, e4Map_X1, e4Map_X2] at h
  linear_combination h

/-- The localized element `B(1 − 16B)` is a unit. -/
theorem isUnit_e4B_mul_one_sub : IsUnit (e4B R * (1 - 16 * e4B R)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := E4ModuliRing R) (e4Delta R)
  have heq : algebraMap (E4Quotient R) (E4ModuliRing R) (e4Delta R)
      = e4B R * (1 - 16 * e4B R) := by
    simp only [e4Delta, e4B, map_mul, map_sub, map_one, map_ofNat]
  rwa [heq] at h

/-- **(E4A-3)** `B` is a unit in the moduli ring. -/
theorem isUnit_e4B : IsUnit (e4B R) :=
  isUnit_of_mul_isUnit_left (isUnit_e4B_mul_one_sub R)

/-- **(E4A-3)** `1 − 16B` is a unit in the moduli ring. -/
theorem isUnit_one_sub_sixteen_e4B : IsUnit (1 - 16 * e4B R) :=
  isUnit_of_mul_isUnit_right (isUnit_e4B_mul_one_sub R)

/-- **(E4A-2)** `Δ(universalE4) = B⁴(1 − 16B)` is a unit (sympy-certified identity,
`ring`-checked below). -/
theorem isUnit_universalE4_Δ : IsUnit (universalE4 R).Δ := by
  have hΔ : (universalE4 R).Δ = e4B R ^ 4 * (1 - 16 * e4B R) := by
    rw [WeierstrassCurve.Δ]
    show -(universalE4 R).b₂ ^ 2 * (universalE4 R).b₈ - 8 * (universalE4 R).b₄ ^ 3
        - 27 * (universalE4 R).b₆ ^ 2 + 9 * (universalE4 R).b₂ * (universalE4 R).b₄
          * (universalE4 R).b₆ = _
    rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    show -((1:E4ModuliRing R) ^ 2 + 4 * e4B R) ^ 2 * (1 ^ 2 * 0 + 4 * (e4B R) * 0
        - 1 * (e4B R) * 0 + (e4B R) * (e4B R) ^ 2 - 0 ^ 2)
      - 8 * (2 * 0 + 1 * (e4B R)) ^ 3 - 27 * ((e4B R) ^ 2 + 4 * 0) ^ 2
      + 9 * (1 ^ 2 + 4 * e4B R) * (2 * 0 + 1 * (e4B R)) * ((e4B R) ^ 2 + 4 * 0) = _
    ring
  rw [hΔ]
  exact ((isUnit_e4B R).pow 4).mul (isUnit_one_sub_sixteen_e4B R)

instance : (universalE4 R).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]; exact isUnit_universalE4_Δ R

/-- **(E4A-3)** `u = x(Q)` is a unit (needs `2` invertible): from `e4Rel`,
`u·(2u³ + u² + 3Bu + 4B²) = −2B³` is a unit (`Q ∉ {±P}` automatic). -/
theorem isUnit_e4U (hR : IsUnit (2 : R)) : IsUnit (e4U R) := by
  have h2 : IsUnit (2 : E4ModuliRing R) := by
    have := hR.map (algebraMap R (E4ModuliRing R))
    rwa [map_ofNat] at this
  apply isUnit_of_mul_isUnit_left
    (y := 2 * e4U R ^ 3 + e4U R ^ 2 + 3 * e4B R * e4U R + 4 * e4B R ^ 2)
  rw [show e4U R * (2 * e4U R ^ 3 + e4U R ^ 2 + 3 * e4B R * e4U R + 4 * e4B R ^ 2)
      = -(2 * e4B R ^ 3) by linear_combination e4_order_rel R]
  exact ((h2.mul ((isUnit_e4B R).pow 3))).neg

/-- **(E4A-3)** `u + 2B` is a unit (needs `2` invertible): substituting `u = −2B` into
`e4Rel` leaves the unit `2B³(16B − 1)` (`2Q ≠ 2P` automatic — the locus `{2Q = 2P}` is
`{x(Q) ∈ {0, −2B}}`). -/
theorem isUnit_e4U_add_two_e4B (hR : IsUnit (2 : R)) :
    IsUnit (e4U R + 2 * e4B R) := by
  have h2 : IsUnit (2 : E4ModuliRing R) := by
    have := hR.map (algebraMap R (E4ModuliRing R))
    rwa [map_ofNat] at this
  apply isUnit_of_mul_isUnit_left
    (y := 2 * e4U R ^ 3 + (1 - 4 * e4B R) * e4U R ^ 2
      + (e4B R + 8 * e4B R ^ 2) * e4U R + 2 * e4B R ^ 2 * (1 - 8 * e4B R))
  rw [show (e4U R + 2 * e4B R) * (2 * e4U R ^ 3 + (1 - 4 * e4B R) * e4U R ^ 2
      + (e4B R + 8 * e4B R ^ 2) * e4U R + 2 * e4B R ^ 2 * (1 - 8 * e4B R))
      = 2 * e4B R ^ 3 * (1 - 16 * e4B R)
        + (2 * e4U R ^ 4 + e4U R ^ 3 + 3 * e4B R * e4U R ^ 2
          + 4 * e4B R ^ 2 * e4U R + 2 * e4B R ^ 3) by ring]
  rw [e4_order_rel R, add_zero]
  exact (h2.mul ((isUnit_e4B R).pow 3)).mul (isUnit_one_sub_sixteen_e4B R)

/-- **(E4A-3)** `ψ₂(Q) = 2v + u + B` is a unit (needs `2` invertible): the square
`ψ₂(Q)² = 4u³ + (1+4B)u² + 2Bu + B²` (mod the curve relation), and the sympy-solved
Bezout identity `B₀·ψ₂² = 4B⁶(16B−1) + A₀·e4Rel` exhibits `ψ₂(Q)²` as a divisor of the
unit `4B⁶(16B−1)` (`2Q ≠ 0` automatic). -/
theorem isUnit_psiTwo_e4Q (hR : IsUnit (2 : R)) :
    IsUnit (2 * e4V R + e4U R + e4B R) := by
  have h2 : IsUnit (2 : E4ModuliRing R) := by
    have := hR.map (algebraMap R (E4ModuliRing R))
    rwa [map_ofNat] at this
  set B := e4B R
  set U := e4U R
  have hsq : (2 * e4V R + U + B) ^ 2
      = 4 * U ^ 3 + (1 + 4 * B) * U ^ 2 + 2 * B * U + B ^ 2 := by
    linear_combination (4 : E4ModuliRing R) * e4_curve_rel R
  have hsqUnit : IsUnit ((2 * e4V R + U + B) ^ 2) := by
    apply isUnit_of_mul_isUnit_left
      (y := 92 * B ^ 4 - 16 * B ^ 3 * U ^ 2 + 40 * B ^ 3 * U - 36 * B ^ 3
        + 48 * B ^ 2 * U ^ 3 + 52 * B ^ 2 * U ^ 2 - 32 * B ^ 2 * U + 2 * B ^ 2
        - 32 * B * U ^ 3 - 18 * B * U ^ 2 + 2 * B * U + 2 * U ^ 3 + U ^ 2)
    have key : (2 * e4V R + U + B) ^ 2
        * (92 * B ^ 4 - 16 * B ^ 3 * U ^ 2 + 40 * B ^ 3 * U - 36 * B ^ 3
          + 48 * B ^ 2 * U ^ 3 + 52 * B ^ 2 * U ^ 2 - 32 * B ^ 2 * U + 2 * B ^ 2
          - 32 * B * U ^ 3 - 18 * B * U ^ 2 + 2 * B * U + 2 * U ^ 3 + U ^ 2)
        = 4 * B ^ 6 * (16 * B - 1) := by
      linear_combination
        (92 * B ^ 4 - 16 * B ^ 3 * U ^ 2 + 40 * B ^ 3 * U - 36 * B ^ 3
          + 48 * B ^ 2 * U ^ 3 + 52 * B ^ 2 * U ^ 2 - 32 * B ^ 2 * U + 2 * B ^ 2
          - 32 * B * U ^ 3 - 18 * B * U ^ 2 + 2 * B * U + 2 * U ^ 3 + U ^ 2) * hsq
        + (-32 * B ^ 4 + 64 * B ^ 3 * U + 48 * B ^ 3 + 96 * B ^ 2 * U ^ 2
          + 16 * B ^ 2 * U - 18 * B ^ 2 - 64 * B * U ^ 2 - 16 * B * U + B
          + 4 * U ^ 2 + U) * e4_order_rel R
    rw [key, show (4 : E4ModuliRing R) = 2 ^ 2 by norm_num]
    have h16 : IsUnit (16 * B - 1) := by
      have := (isUnit_one_sub_sixteen_e4B R).neg
      rwa [neg_sub] at this
    exact (((h2.pow 2).mul ((isUnit_e4B R).pow 6)).mul h16)
  rw [sq] at hsqUnit
  exact isUnit_of_mul_isUnit_left hsqUnit

/-! ### E4A-4 — equation witnesses, the marked sections, and the killing -/

/-- **(E4A-4)** `(0, 0)` lies on the universal curve (`a₆ = 0`). -/
theorem universalE4_equation_zero :
    (universalE4 R).toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show (0 : E4ModuliRing R) ^ 2 + (universalE4 R).a₁ * 0 * 0 +
    (universalE4 R).a₃ * 0 =
    0 ^ 3 + (universalE4 R).a₂ * 0 ^ 2 + (universalE4 R).a₄ * 0 + (universalE4 R).a₆
  show (0 : E4ModuliRing R) ^ 2 + 1 * 0 * 0 + e4B R * 0
    = 0 ^ 3 + e4B R * 0 ^ 2 + 0 * 0 + 0
  ring

/-- **(E4A-4)** `Q = (u, v)` lies on the universal curve: the affine equation at
`(u, v)` is exactly the curve relation `e4CurveRel`. -/
theorem universalE4_equation_Q :
    (universalE4 R).toAffine.Equation (e4U R) (e4V R) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show e4V R ^ 2 + (universalE4 R).a₁ * e4U R * e4V R + (universalE4 R).a₃ * e4V R
    = e4U R ^ 3 + (universalE4 R).a₂ * e4U R ^ 2 + (universalE4 R).a₄ * e4U R
      + (universalE4 R).a₆
  show e4V R ^ 2 + 1 * e4U R * e4V R + e4B R * e4V R
    = e4U R ^ 3 + e4B R * e4U R ^ 2 + 0 * e4U R + 0
  linear_combination e4_curve_rel R

/-- **(E4A-1)** The universal `Ell/R`-object `ℰ₄`. -/
def universalE4Obj : EllObj R where
  base := Spec (CommRingCat.of (E4ModuliRing R))
  structMap := Spec.map (CommRingCat.ofHom (algebraMap R (E4ModuliRing R)))
  curve := modelEllipticCurve (universalE4 R)

/-- **(E4A-1)** The universally marked `P = (0, 0)` (order 4: `2P = (−B, 0)` is
2-torsion). -/
def universalE4P : (universalE4Obj R).curve.Section :=
  ⟨projModelAffineSection (universalE4 R) 0 0 (universalE4_equation_zero R),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(E4A-1)** The universally marked `Q = (u, v)`. -/
def universalE4Q : (universalE4Obj R).curve.Section :=
  ⟨projModelAffineSection (universalE4 R) (e4U R) (e4V R) (universalE4_equation_Q R),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(E4A-4)** The section-level killing `[4]P = 0`: `2P = (−B, 0)` satisfies
`ψ₂ = 2y + x + B` identically. Route: the ℰ₃ Stage-D pattern (reduced universal base
`ℤ[1/2]` + `nsmul_section_eq_zero_of_forall_specPoint` + Stage-D transport). -/
theorem four_zsmul_universalE4P_of_isUnit (hR : IsUnit (2 : R)) :
    (4 : ℤ) • universalE4P R = 0 := by sorry

/-- **(E4A-4)** The section-level killing `[4]Q = 0`: `e4Rel` puts `x([2]Q)` on the
complementary 2-torsion quadratic, whose `y`-fibre is the degenerate (double) point. -/
theorem four_zsmul_universalE4Q_of_isUnit (hR : IsUnit (2 : R)) :
    (4 : ℤ) • universalE4Q R = 0 := by sorry

/-! ### E4A-5/E4A-6 — the generation keystone -/

/-- **(E4A-5, NEW group theory)** For `P, Q` in an abelian group with `4P = 4Q = 0`,
`2P ≠ 0`, `2Q ≠ 0`, `2Q ≠ 2P`, every nontrivial `(ℤ/4)²`-combination `aP + bQ` is
nonzero. (The level-3 collapse `2x = −x` is unavailable at 4; the proof is the four-case
parity analysis — see decomposition-e4.md §2 E4A-5. Reconciled with
`pair_generates_iff_combos_ne_zero` at ticket time.) -/
theorem combos4_ne_zero {G : Type*} [AddCommGroup G] {P Q : G}
    (hP4 : (4 : ℤ) • P = 0) (hQ4 : (4 : ℤ) • Q = 0)
    (hP2 : (2 : ℤ) • P ≠ 0) (hQ2 : (2 : ℤ) • Q ≠ 0)
    (hPQ : (2 : ℤ) • Q ≠ (2 : ℤ) • P)
    (a b : ZMod 4) (hab : ¬(a = 0 ∧ b = 0)) :
    (a.val : ℤ) • P + (b.val : ℤ) • Q ≠ 0 := by sorry

/-- **(E4A-6, the keystone)** Geometric generation: over every algebraically closed
field point of the moduli ring, the pulled pair `(P̄, Q̄)` generates the 4-torsion.
Mirror of `universalE3_generation` with `torsion_geometricFibre_rank_two 4` +
`pair_generates_iff_combos_ne_zero 4` + `combos4_ne_zero`; fibre facts from the unit
lemmas (E4A-3). -/
theorem universalE4_generation (hR : IsUnit (2 : R)) (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (E4ModuliRing R)))
    (x : (universalE4Obj R).curve.Point t) (hx : ((4 : ℕ) : ℤ) • x = 0) :
    x ∈ AddSubgroup.closure
      {EllipticCurve.Point.pull (universalE4Obj R).curve t (universalE4P R),
       EllipticCurve.Point.pull (universalE4Obj R).curve t (universalE4Q R)} := by sorry

/-! ### E4A-7 — the `ℰ₄`-form and the `ℰ₄`-datum -/

/-- **(E4A-7)** The level-4 Tate-normal-form shape: `a₁ = 1`, `a₂ = a₃ = B`,
`a₄ = a₆ = 0` (Loeffler Prop 3.3.4 with the order-4 pin `a₁ = 1`). -/
def IsE4Form {A : Type u} [CommRing A] (W : WeierstrassCurve A) (B : A) : Prop :=
  W.a₁ = 1 ∧ W.a₂ = B ∧ W.a₃ = B ∧ W.a₄ = 0 ∧ W.a₆ = 0

/-- The universal curve is of `ℰ₄`-form at the universal parameter. -/
theorem universalE4_isE4Form : IsE4Form (universalE4 R) (e4B R) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **(E4A-7)** `IsE4Form` is functorial under a ring hom. -/
theorem IsE4Form.map {A B' : Type u} [CommRing A] [CommRing B'] (f : A →+* B')
    {W : WeierstrassCurve A} {B : A} (h : IsE4Form W B) :
    IsE4Form (W.map f) (f B) := by sorry

open LocalPresentation in
/-- **(E4A-7, the KM-2.2.11-analogue datum at level 4)** An `ℰ₄` datum on `E/S`: a naive
full level-4 structure `(P, Q)` such that, locally on the base, there is a chart
presentation of `ℰ₄`-form marking `P` at `(0, 0)` and `Q` at `(u, v)`, with `B` a unit
and the order-4 relation `e4Rel(B, u) = 0`. (The units `u`, `u + 2B`, `ψ₂(Q)` and
`1 − 16B` are consequences — decomposition-e4.md §2.) -/
def IsE4Datum {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) : Prop :=
  ∀ s : X.base, ∃ (V : X.base.affineOpens) (_ : s ∈ V.1)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (B u v : Γ(X.base, V.1)),
      IsE4Form Pr.W B ∧ Pr.MarksAt L.1.1.2 0 0 ∧ Pr.MarksAt L.1.2.2 u v ∧
      IsUnit B ∧
      2 * u ^ 4 + u ^ 3 + 3 * B * u ^ 2 + 4 * B ^ 2 * u + 2 * B ^ 3 = 0

/-! ### E4A-8/9/10/11 — the bridges (every naive level-4 structure is an `ℰ₄`-datum) -/

open LocalPresentation in
/-- **(E4A-9, bridge A)** On a Tate-normal-form chart (`a₄ = a₆ = 0`, `a₂ = a₃`) marking
the 4-torsion section `P` at the origin, the order-4 condition forces `a₁ = 1`:
`2P = (−a₂, 0)`, `−2P = (−a₂, a₁a₂ − a₂)`, so `4•P = 0` gives `a₂(a₁ − 1) = 0` with
`a₂` a unit (`2P ≠ ±P` fibrewise). Via the RING-DBL doubling identity
(`two_zsmul_affineSection` + `equation_dblXY`, the `hdbl_of_marked_three_torsion`
pattern at 4-torsion). -/
theorem bridgeA_holds {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (2 : R))
    (L : X.curve.FullLevelPt 4)
    (V : X.base.affineOpens) (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (ha₄ : Pr.W.a₄ = 0) (ha₆ : Pr.W.a₆ = 0) (ha₂₃ : Pr.W.a₂ = Pr.W.a₃)
    (hM : Pr.MarksAt L.1.1.2 0 0) :
    Pr.W.a₁ = 1 := by sorry

open LocalPresentation in
/-- **(E4A-10, bridge Q)** On an `ℰ₄`-form chart marking `P` at the origin and `Q` at
`(u, v)`, the order-4 condition on `Q` forces the `e4Rel` relation, via the master
identity `ψ₂(Q)³ · ψ₂(2Q) ≡ u(2B + u) · e4Rel (mod curve)` (sympy-certified) and the
unit certificates for `u` and `u + 2B` (fibrewise `2Q ≠ 2P`, the
`isUnit_x_of_marked_pair` pattern). Nilpotent-safe: only the LINEAR `ψ₂`-condition at
the section `2Q` is consumed, never the squared abscissa relation. -/
theorem bridgeQ4_holds {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (2 : R))
    (L : X.curve.FullLevelPt 4)
    (V : X.base.affineOpens) (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (B : Γ(X.base, V.1)) (hE4 : IsE4Form Pr.W B) (hB : IsUnit B)
    (hMP : Pr.MarksAt L.1.1.2 0 0)
    (u v : Γ(X.base, V.1)) (hMQ : Pr.MarksAt L.1.2.2 u v) :
    2 * u ^ 4 + u ^ 3 + 3 * B * u ^ 2 + 4 * B ^ 2 * u + 2 * B ^ 3 = 0 := by sorry

open LocalPresentation in
/-- **(E4A-11, the datum assembly)** Every naive full level-4 structure is an
`ℰ₄`-datum: atlas charts + the (N-agnostic) marking pipeline + `ofNeZero`/`toTateNF`
normalization (`ForMathlib/TateNormalForm.lean` — applicable since an order-4 point has
`P, 2P, 3P ≠ 0`, unlike level 3) + bridge A + bridge Q. Mirror of
`isE3Datum_of_bridges`. -/
theorem isE4Datum_of_bridges {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (2 : R))
    (L : X.curve.FullLevelPt 4) :
    IsE4Datum X L := by sorry

/-! ### E4A-12/13/14 — the classifying morphism and the `RepresentableBy` packaging -/

/-- **(E4A-12, the classifying chain — expanded by its ticket into the
`e4BGlued/e4UGlued/e4VGlued → e4ClassifyingRingHom → e4ClassifyingMap → e4Top`
chain, the ℰ₃ literal pattern)** The classifying `Ell/R`-morphism of an `ℰ₄`-datum. -/
def e4ClassifyingEllHom {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) : X ⟶ universalE4Obj R := sorry

/-- **(E4A-14, the raw naive-functor `RepresentableBy` — expanded by its ticket with the
rt1/rt2 round-trip lemmas `pullSection_e4ClassifyingEllHom_P/_Q` and
`e4ClassifyingEllHom_pulled`, the ℰ₃ literal pattern)** Given `hL` (the universal marked
pair is a level-4 structure) and `hArb` (every naive level-4 structure is an
`ℰ₄`-datum), the raw naive level-4 functor is representable by `universalE4Obj`. -/
def naiveLevelFourRepresentableBy (R : CommRingCat.{u}) (hR : IsUnit (2 : R))
    (hL : (universalE4Obj R).curve.IsNaiveFullLevel 4
      (universalE4P R) (universalE4Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 4), IsE4Datum X L) :
    (gammaFullNaiveProblem R 4).RepresentableBy (universalE4Obj R) := sorry

/-- **(E4A-14)** The conditional affine representability, mirroring
`naiveLevelThree_representable_by_affine_of_conditions`. -/
theorem naiveLevelFour_representable_by_affine_of_conditions
    (R : CommRingCat.{u}) (hR : IsUnit (2 : R))
    (hL : (universalE4Obj R).curve.IsNaiveFullLevel 4
      (universalE4P R) (universalE4Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 4), IsE4Datum X L) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((gammaFullNaiveProblem R 4).RepresentableBy X) :=
  ⟨universalE4Obj R,
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (E4ModuliRing R)))),
    ⟨naiveLevelFourRepresentableBy R hR hL hArb⟩⟩

/-- **(E4A-14 headline; KM 4.7.0 engine axiom 1 for `δ = ` naive level 4)** Over a base
in which `2` is invertible, the naive level-4 problem is representable by an object
whose base is affine — `Y(4) = Spec E4ModuliRing`. The level-4 instance of KM
COROLLARY 4.7.2 proved BY HAND (not via 4.7.1, which would be circular: this object is
what 4.7.1's D(2) leg bootstraps). Discharged from `_of_conditions` once `hL`
(E4A-4 killing + E4A-6 generation) and `hArb` (E4A-11) land. -/
theorem naiveLevelFour_representable_by_affine (hR : IsUnit (2 : R)) :
    ∃ X : EllObj R, IsAffine X.base ∧
      Nonempty ((gammaFullNaiveProblem R 4).RepresentableBy X) := by sorry

end ModularCurves
