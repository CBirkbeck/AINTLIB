/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.BridgeAssembly
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

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-4)** The section-level killing `[4]P = 0`, by the DIRECT section route:
`RING-DBL` (`two_zsmul_affineSection`, tangent denominator `ψ₂(P) = a₃ = B` a unit)
lands `2 • P` at the doubling-coordinate section `(−B, 0)`, which is negation-symmetric
(`negY(−B, 0) = 0` — a pure `ring` identity), so `negModelHom` fixes it
(`negModelHom_affineSection`) and `[−1] = negModelHom` (`modelEllipticCurve_mulByHom_neg_one`)
gives `[2](2 • P) = 0`. No base reducedness is consumed (the ℰ₃ Stage-D detour is not
needed at level 4); `hR` is not consumed either — the killing of `P` is unconditional. -/
theorem four_zsmul_universalE4P_of_isUnit (hR : IsUnit (2 : R)) :
    (4 : ℤ) • universalE4P R = 0 := by
  obtain ⟨b, hb⟩ := (isUnit_e4B R).exists_right_inv
  have he : (universalE4 R).tangentDen 0 0 * b = 1 := by
    rw [show (universalE4 R).tangentDen 0 0 = e4B R from by
      simp only [WeierstrassCurve.tangentDen, show (universalE4 R).a₁ = 1 from rfl,
        show (universalE4 R).a₃ = e4B R from rfl]
      ring]
    exact hb
  have heqd : (universalE4 R).toAffine.Equation
      ((universalE4 R).dblX 0 0 b) ((universalE4 R).dblY 0 0 b) :=
    equation_dblXY (universalE4 R) 0 0 b (universalE4_equation_zero R) he
  have hdbl : (2 : ℤ) • universalE4P R
      = (⟨projModelAffineSection (universalE4 R) ((universalE4 R).dblX 0 0 b)
            ((universalE4 R).dblY 0 0 b) heqd,
          projModelAffineSection_projModelπ _ _ _ _⟩ :
        (universalE4Obj R).curve.Section) :=
    two_zsmul_affineSection (universalE4 R) 0 0 b (universalE4_equation_zero R) he heqd
  have hsym : -(universalE4 R).dblY 0 0 b
      - (universalE4 R).a₁ * (universalE4 R).dblX 0 0 b - (universalE4 R).a₃
      = (universalE4 R).dblY 0 0 b := by
    simp only [WeierstrassCurve.dblY, WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
      WeierstrassCurve.tangentNum, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY, show (universalE4 R).a₁ = 1 from rfl,
      show (universalE4 R).a₂ = e4B R from rfl,
      show (universalE4 R).a₃ = e4B R from rfl,
      show (universalE4 R).a₄ = 0 from rfl]
    ring
  have hneg := negModelHom_affineSection (universalE4 R) _ _ heqd hsym
  set τ : (universalE4Obj R).curve.Section :=
    ⟨projModelAffineSection (universalE4 R) ((universalE4 R).dblX 0 0 b)
        ((universalE4 R).dblY 0 0 b) heqd,
      projModelAffineSection_projModelπ _ _ _ _⟩ with hτdef
  have hτneg : -τ = τ := by
    refine Subtype.ext ?_
    have hv : (-τ).1 = τ.1 ≫ (modelEllipticCurve (universalE4 R)).mulByHom (-1) := by
      rw [show -τ = (-1 : ℤ) • τ from (neg_one_zsmul τ).symm]
      exact (modelEllipticCurve (universalE4 R)).point_smul_eq_comp_mulBy _ (-1) τ
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hτdef]
    exact hneg
  have hτ2 : (2 : ℤ) • τ = 0 := by
    calc (2 : ℤ) • τ = τ + τ := two_zsmul τ
      _ = τ + -τ := by rw [hτneg]
      _ = 0 := add_neg_cancel τ
  rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul, hdbl]
  exact hτ2

set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-4)** The section-level killing `[4]Q = 0`, by the DIRECT section route:
`RING-DBL` (`two_zsmul_affineSection`, tangent denominator `ψ₂(Q)` a unit by
`isUnit_psiTwo_e4Q`) lands `2 • Q` at the doubling-coordinate section, and the
`linear_combination` certificate of the master identity
`ψ₂(Q)³ · ψ₂(2Q) ≡ u(2B + u) · e4Rel (mod curve)` against
`e4_curve_rel`/`e4_order_rel` (with the inverse witness `ψ₂(Q)·e = 1` collapsing the
`e`-powers) shows `ψ₂(2Q) = 0`: the double is negation-fixed, so `[2](2 • Q) = 0`. -/
theorem four_zsmul_universalE4Q_of_isUnit (hR : IsUnit (2 : R)) :
    (4 : ℤ) • universalE4Q R = 0 := by
  obtain ⟨e, he'⟩ := (isUnit_psiTwo_e4Q R hR).exists_right_inv
  have he : (universalE4 R).tangentDen (e4U R) (e4V R) * e = 1 := by
    rw [show (universalE4 R).tangentDen (e4U R) (e4V R)
        = 2 * e4V R + e4U R + e4B R from by
      simp only [WeierstrassCurve.tangentDen, show (universalE4 R).a₁ = 1 from rfl,
        show (universalE4 R).a₃ = e4B R from rfl]
      ring]
    exact he'
  have heqd : (universalE4 R).toAffine.Equation
      ((universalE4 R).dblX (e4U R) (e4V R) e)
      ((universalE4 R).dblY (e4U R) (e4V R) e) :=
    equation_dblXY (universalE4 R) (e4U R) (e4V R) e (universalE4_equation_Q R) he
  have hdbl : (2 : ℤ) • universalE4Q R
      = (⟨projModelAffineSection (universalE4 R)
            ((universalE4 R).dblX (e4U R) (e4V R) e)
            ((universalE4 R).dblY (e4U R) (e4V R) e) heqd,
          projModelAffineSection_projModelπ _ _ _ _⟩ :
        (universalE4Obj R).curve.Section) :=
    two_zsmul_affineSection (universalE4 R) (e4U R) (e4V R) e
      (universalE4_equation_Q R) he heqd
  have hsym : -(universalE4 R).dblY (e4U R) (e4V R) e
      - (universalE4 R).a₁ * (universalE4 R).dblX (e4U R) (e4V R) e
      - (universalE4 R).a₃
      = (universalE4 R).dblY (e4U R) (e4V R) e := by
    simp only [WeierstrassCurve.dblY, WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
      WeierstrassCurve.tangentNum, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY, show (universalE4 R).a₁ = 1 from rfl,
      show (universalE4 R).a₂ = e4B R from rfl,
      show (universalE4 R).a₃ = e4B R from rfl,
      show (universalE4 R).a₄ = 0 from rfl]
    linear_combination
      e ^ 3 * (16 * e4V R ^ 2 + 16 * e4U R * e4V R + 16 * e4B R * e4V R
          - 56 * e4U R ^ 3 - 56 * e4B R * e4U R ^ 2 - 16 * e4B R ^ 2 * e4U R
          - 10 * e4U R ^ 2 - 4 * e4B R * e4U R + 4 * e4B R ^ 2 - e4U R - e4B R)
        * e4_curve_rel R
      - e ^ 3 * e4U R * (2 * e4B R + e4U R) * e4_order_rel R
      + (-(3 * (3 * e4U R ^ 2 + 2 * e4B R * e4U R - e4V R) ^ 2 * e ^ 2)
          + (2 * e4B R + 6 * e4U R - 1) * (3 * e4U R ^ 2 + 2 * e4B R * e4U R - e4V R)
            * e * ((2 * e4V R + e4U R + e4B R) * e + 1)
          - (2 * e4V R - 2 * e4U R)
            * (((2 * e4V R + e4U R + e4B R) * e) ^ 2
              + (2 * e4V R + e4U R + e4B R) * e + 1)) * he'
  have hneg := negModelHom_affineSection (universalE4 R) _ _ heqd hsym
  set τ : (universalE4Obj R).curve.Section :=
    ⟨projModelAffineSection (universalE4 R) ((universalE4 R).dblX (e4U R) (e4V R) e)
        ((universalE4 R).dblY (e4U R) (e4V R) e) heqd,
      projModelAffineSection_projModelπ _ _ _ _⟩ with hτdef
  have hτneg : -τ = τ := by
    refine Subtype.ext ?_
    have hv : (-τ).1 = τ.1 ≫ (modelEllipticCurve (universalE4 R)).mulByHom (-1) := by
      rw [show -τ = (-1 : ℤ) • τ from (neg_one_zsmul τ).symm]
      exact (modelEllipticCurve (universalE4 R)).point_smul_eq_comp_mulBy _ (-1) τ
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hτdef]
    exact hneg
  have hτ2 : (2 : ℤ) • τ = 0 := by
    calc (2 : ℤ) • τ = τ + τ := two_zsmul τ
      _ = τ + -τ := by rw [hτneg]
      _ = 0 := add_neg_cancel τ
  rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul, hdbl]
  exact hτ2

/-! ### E4A-5/E4A-6 — the generation keystone -/

/-- **(E4A-5 core)** The `ℕ`-representative form of `combos4_ne_zero`: the 15 nontrivial
combinations `mP + nQ` (`m, n < 4`) are nonzero. Doubling any vanishing combination
reduces it (via `4P = 4Q = 0`) to one of the excluded relations `2P = 0`, `2Q = 0`,
`2P + 2Q = 0` (the last contradicts `2Q ≠ 2P` since `−2P = 2P`); the 16-fold case split
is discharged by `linear_combination (norm := module)`. -/
private theorem combos4_ne_zero_aux {G : Type*} [AddCommGroup G] {P Q : G}
    (hP4 : (4 : ℤ) • P = 0) (hQ4 : (4 : ℤ) • Q = 0)
    (hP2 : (2 : ℤ) • P ≠ 0) (hQ2 : (2 : ℤ) • Q ≠ 0)
    (hPQ : (2 : ℤ) • Q ≠ (2 : ℤ) • P)
    {m n : ℕ} (hm : m < 4) (hn : n < 4) (hmn : ¬(m = 0 ∧ n = 0)) :
    (m : ℤ) • P + (n : ℤ) • Q ≠ 0 := by
  intro h
  have hPP : -((2 : ℤ) • P) = (2 : ℤ) • P := by
    apply neg_eq_of_add_eq_zero_left
    linear_combination (norm := module) hP4
  have hsum : (2 : ℤ) • P + (2 : ℤ) • Q ≠ 0 := by
    intro hc
    apply hPQ
    have h1 : (2 : ℤ) • Q = -((2 : ℤ) • P) := eq_neg_of_add_eq_zero_right hc
    rw [h1, hPP]
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hm' with rfl | rfl | rfl | rfl <;> rcases hn' with rfl | rfl | rfl | rfl <;>
    push_cast at h
  · exact hmn ⟨rfl, rfl⟩
  · exact hQ2 (by linear_combination (norm := module) (2 : ℤ) • h)
  · exact hQ2 (by linear_combination (norm := module) h)
  · exact hQ2 (by linear_combination (norm := module) (2 : ℤ) • h - hQ4)
  · exact hP2 (by linear_combination (norm := module) (2 : ℤ) • h)
  · exact hsum (by linear_combination (norm := module) (2 : ℤ) • h)
  · exact hP2 (by linear_combination (norm := module) (2 : ℤ) • h - hQ4)
  · exact hsum (by linear_combination (norm := module) (2 : ℤ) • h - hQ4)
  · exact hP2 (by linear_combination (norm := module) h)
  · exact hQ2 (by linear_combination (norm := module) (2 : ℤ) • h - hP4)
  · exact hsum (by linear_combination (norm := module) h)
  · exact hQ2 (by linear_combination (norm := module) (2 : ℤ) • h - hP4 - hQ4)
  · exact hP2 (by linear_combination (norm := module) (2 : ℤ) • h - hP4)
  · exact hsum (by linear_combination (norm := module) (2 : ℤ) • h - hP4)
  · exact hP2 (by linear_combination (norm := module) (2 : ℤ) • h - hP4 - hQ4)
  · exact hsum (by linear_combination (norm := module) (2 : ℤ) • h - hP4 - hQ4)

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
    (a.val : ℤ) • P + (b.val : ℤ) • Q ≠ 0 := by
  refine combos4_ne_zero_aux hP4 hQ4 hP2 hQ2 hPQ (ZMod.val_lt a) (ZMod.val_lt b) ?_
  rintro ⟨h1, h2⟩
  exact hab ⟨(ZMod.val_eq_zero a).mp h1, (ZMod.val_eq_zero b).mp h2⟩

/-- The doubling `X`-coordinate, written out: `dblX = (N·e)² + a₁·(N·e) − a₂ − 2p`
with `N` the tangent numerator. -/
private theorem dblX_expand {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (p q e : A) :
    W.dblX p q e = (W.tangentNum p q * e) ^ 2 + W.a₁ * (W.tangentNum p q * e)
      - W.a₂ - 2 * p := by
  simp only [WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
    WeierstrassCurve.Affine.addX]
  ring

/-- The doubling `Y`-coordinate, written out through `dblX`:
`dblY = −(N·e·(dblX − p) + q) − a₁·dblX − a₃`. -/
private theorem dblY_expand {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (p q e : A) :
    W.dblY p q e = -(W.tangentNum p q * e * (W.dblX p q e - p) + q)
      - W.a₁ * W.dblX p q e - W.a₃ := by
  simp only [WeierstrassCurve.dblY, WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]

/-- The universal tangent numerator vanishes at the origin (`a₄ = 0`). -/
private theorem universalE4_tangentNum_zero :
    (universalE4 R).tangentNum 0 0 = 0 := by
  simp only [WeierstrassCurve.tangentNum, show (universalE4 R).a₁ = 1 from rfl,
    show (universalE4 R).a₂ = e4B R from rfl, show (universalE4 R).a₄ = 0 from rfl]
  ring

/-- The universal double of `P = (0,0)` has `x`-coordinate `−B`. -/
private theorem universalE4_dblX_P (b : E4ModuliRing R) :
    (universalE4 R).dblX 0 0 b = -e4B R := by
  rw [dblX_expand, universalE4_tangentNum_zero,
    show (universalE4 R).a₁ = 1 from rfl, show (universalE4 R).a₂ = e4B R from rfl]
  ring

/-- The universal tangent numerator at `Q = (u, v)`: `3u² + 2Bu − v`. -/
private theorem universalE4_tangentNum_Q :
    (universalE4 R).tangentNum (e4U R) (e4V R)
      = 3 * e4U R ^ 2 + 2 * e4B R * e4U R - e4V R := by
  simp only [WeierstrassCurve.tangentNum, show (universalE4 R).a₁ = 1 from rfl,
    show (universalE4 R).a₂ = e4B R from rfl, show (universalE4 R).a₄ = 0 from rfl]
  ring

/-- The universal double of `Q` has expanded `x`-coordinate
`((3u²+2Bu−v)e)² + (3u²+2Bu−v)e − B − 2u`. -/
private theorem universalE4_dblX_Q (e : E4ModuliRing R) :
    (universalE4 R).dblX (e4U R) (e4V R) e
      = ((3 * e4U R ^ 2 + 2 * e4B R * e4U R - e4V R) * e) ^ 2
        + (3 * e4U R ^ 2 + 2 * e4B R * e4U R - e4V R) * e - e4B R - 2 * e4U R := by
  rw [dblX_expand, universalE4_tangentNum_Q,
    show (universalE4 R).a₁ = 1 from rfl, show (universalE4 R).a₂ = e4B R from rfl]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-6, the keystone)** Geometric generation: over every algebraically closed
field point of the moduli ring, the pulled pair `(P̄, Q̄)` generates the 4-torsion.
Mirror of `universalE3_generation` with `torsion_geometricFibre_rank_two 4` +
`pair_generates_iff_combos_ne_zero 4` + `combos4_ne_zero`; fibre facts from the unit
lemmas (E4A-3): the doubles evaluate through `RING-DBL` + the Stage-B dictionary to
`some(−B̄, 0)` resp. `some(x(2Q̄), y(2Q̄))`, giving `2P̄ ≠ 0 ≠ 2Q̄` (a `some` is never
zero), and `2Q̄ = 2P̄` would force `x(2Q̄) = −B̄` on the complementary `2`-torsion
quadratic `4x² + x + B̄ = 0` — the contradiction `4B̄² = 0`. -/
theorem universalE4_generation (hR : IsUnit (2 : R)) (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (E4ModuliRing R)))
    (x : (universalE4Obj R).curve.Point t) (hx : ((4 : ℕ) : ℤ) • x = 0) :
    x ∈ AddSubgroup.closure
      {EllipticCurve.Point.pull (universalE4Obj R).curve t (universalE4P R),
       EllipticCurve.Point.pull (universalE4Obj R).curve t (universalE4Q R)} := by
  letI : DecidableEq k := Classical.decEq k
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of (E4ModuliRing R) ⟶ CommRingCat.of k,
      Spec.map φ = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
  letI : Algebra (E4ModuliRing R) k := φ.hom.toAlgebra
  haveI : (((universalE4 R).baseChange k)).IsElliptic :=
    inferInstanceAs (((universalE4 R).map (algebraMap (E4ModuliRing R) k)).IsElliptic)
  -- the evaluated marked points
  set PP := EllipticCurve.Point.pull (universalE4Obj R).curve (Spec.map φ)
    (universalE4P R) with hPP
  set QQ := EllipticCurve.Point.pull (universalE4Obj R).curve (Spec.map φ)
    (universalE4Q R) with hQQ
  -- fibre killing through the section-level killing
  have h4P : (4 : ℤ) • PP = 0 := by
    rw [hPP, ← EllipticCurve.Point.pull_zsmul, four_zsmul_universalE4P_of_isUnit R hR,
      EllipticCurve.Point.pull_zero]
  have h4Q : (4 : ℤ) • QQ = 0 := by
    rw [hQQ, ← EllipticCurve.Point.pull_zsmul, four_zsmul_universalE4Q_of_isUnit R hR,
      EllipticCurve.Point.pull_zero]
  -- the ring-level doubles (RING-DBL, as in the killing proofs)
  obtain ⟨b, hb⟩ := (isUnit_e4B R).exists_right_inv
  have heb : (universalE4 R).tangentDen 0 0 * b = 1 := by
    rw [show (universalE4 R).tangentDen 0 0 = e4B R from by
      simp only [WeierstrassCurve.tangentDen, show (universalE4 R).a₁ = 1 from rfl,
        show (universalE4 R).a₃ = e4B R from rfl]
      ring]
    exact hb
  have heqdP : (universalE4 R).toAffine.Equation
      ((universalE4 R).dblX 0 0 b) ((universalE4 R).dblY 0 0 b) :=
    equation_dblXY (universalE4 R) 0 0 b (universalE4_equation_zero R) heb
  have hdblP : (2 : ℤ) • universalE4P R
      = (⟨projModelAffineSection (universalE4 R) ((universalE4 R).dblX 0 0 b)
            ((universalE4 R).dblY 0 0 b) heqdP,
          projModelAffineSection_projModelπ _ _ _ _⟩ :
        (universalE4Obj R).curve.Section) :=
    two_zsmul_affineSection (universalE4 R) 0 0 b (universalE4_equation_zero R) heb heqdP
  obtain ⟨e, he'⟩ := (isUnit_psiTwo_e4Q R hR).exists_right_inv
  have hee : (universalE4 R).tangentDen (e4U R) (e4V R) * e = 1 := by
    rw [show (universalE4 R).tangentDen (e4U R) (e4V R)
        = 2 * e4V R + e4U R + e4B R from by
      simp only [WeierstrassCurve.tangentDen, show (universalE4 R).a₁ = 1 from rfl,
        show (universalE4 R).a₃ = e4B R from rfl]
      ring]
    exact he'
  have heqdQ : (universalE4 R).toAffine.Equation
      ((universalE4 R).dblX (e4U R) (e4V R) e) ((universalE4 R).dblY (e4U R) (e4V R) e) :=
    equation_dblXY (universalE4 R) (e4U R) (e4V R) e (universalE4_equation_Q R) hee
  have hdblQ : (2 : ℤ) • universalE4Q R
      = (⟨projModelAffineSection (universalE4 R)
            ((universalE4 R).dblX (e4U R) (e4V R) e)
            ((universalE4 R).dblY (e4U R) (e4V R) e) heqdQ,
          projModelAffineSection_projModelπ _ _ _ _⟩ :
        (universalE4Obj R).curve.Section) :=
    two_zsmul_affineSection (universalE4 R) (e4U R) (e4V R) e
      (universalE4_equation_Q R) hee heqdQ
  -- nonsingularity witnesses
  have hnsP : ((universalE4 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E4ModuliRing R) k 0) (algebraMap (E4ModuliRing R) k 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ (universalE4_equation_zero R))
  have hnsQ : ((universalE4 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E4ModuliRing R) k (e4U R))
      (algebraMap (E4ModuliRing R) k (e4V R)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ (universalE4_equation_Q R))
  have hnsP2 : ((universalE4 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E4ModuliRing R) k ((universalE4 R).dblX 0 0 b))
      (algebraMap (E4ModuliRing R) k ((universalE4 R).dblY 0 0 b)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqdP)
  have hnsQ2 : ((universalE4 R).baseChange k).toAffine.Nonsingular
      (algebraMap (E4ModuliRing R) k ((universalE4 R).dblX (e4U R) (e4V R) e))
      (algebraMap (E4ModuliRing R) k ((universalE4 R).dblY (e4U R) (e4V R) e)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqdQ)
  -- dictionary values of the four points
  have hPval : modelPointAddEquiv (universalE4 R) PP
      = WeierstrassCurve.Affine.Point.some _ _ hnsP := by
    show projModelPointsEquiv (universalE4 R) k
      (affineSectionSpecPoint (universalE4 R) k 0 0 (universalE4_equation_zero R)) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE4 R) 0 0
      (universalE4_equation_zero R) hnsP
  have hQval : modelPointAddEquiv (universalE4 R) QQ
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ := by
    show projModelPointsEquiv (universalE4 R) k
      (affineSectionSpecPoint (universalE4 R) k (e4U R) (e4V R)
        (universalE4_equation_Q R)) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE4 R) _ _
      (universalE4_equation_Q R) hnsQ
  have h2Pval : modelPointAddEquiv (universalE4 R) ((2 : ℤ) • PP)
      = WeierstrassCurve.Affine.Point.some _ _ hnsP2 := by
    rw [hPP, ← EllipticCurve.Point.pull_zsmul, hdblP]
    show projModelPointsEquiv (universalE4 R) k
      (affineSectionSpecPoint (universalE4 R) k _ _ heqdP) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE4 R) _ _ heqdP hnsP2
  have h2Qval : modelPointAddEquiv (universalE4 R) ((2 : ℤ) • QQ)
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ2 := by
    rw [hQQ, ← EllipticCurve.Point.pull_zsmul, hdblQ]
    show projModelPointsEquiv (universalE4 R) k
      (affineSectionSpecPoint (universalE4 R) k _ _ heqdQ) = _
    exact projModelPointsEquiv_affineSectionSpecPoint (universalE4 R) _ _ heqdQ hnsQ2
  -- fibre facts: `2P̄ ≠ 0`, `2Q̄ ≠ 0`, `2Q̄ ≠ 2P̄`
  have hP2 : (2 : ℤ) • PP ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsP2
      (by rw [← h2Pval, hc, map_zero])
  have hQ2 : (2 : ℤ) • QQ ≠ 0 := by
    intro hc
    exact WeierstrassCurve.Affine.Point.some_ne_zero hnsQ2
      (by rw [← h2Qval, hc, map_zero])
  have h2k : IsUnit (2 : k) := by
    have hu := hR.map ((algebraMap (E4ModuliRing R) k).comp
      (algebraMap R (E4ModuliRing R)))
    rwa [map_ofNat] at hu
  have hPQ : (2 : ℤ) • QQ ≠ (2 : ℤ) • PP := by
    intro hc
    have h := h2Qval.symm.trans
      ((congrArg (modelPointAddEquiv (universalE4 R)) hc).trans h2Pval)
    injection h with h1 h2
    -- `x(2Q̄) = x(2P̄) = −B̄`, but `x(2Q̄)` satisfies `4x² + x + B̄ = 0`
    rw [universalE4_dblX_P, map_neg] at h1
    -- mapped ring identities
    have hcvk := congrArg (algebraMap (E4ModuliRing R) k) (e4_curve_rel R)
    have hork := congrArg (algebraMap (E4ModuliRing R) k) (e4_order_rel R)
    have hDek := congrArg (algebraMap (E4ModuliRing R) k) he'
    have hxdefk := congrArg (algebraMap (E4ModuliRing R) k) (universalE4_dblX_Q R e)
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, map_one]
      at hcvk hork hDek hxdefk
    set bB := algebraMap (E4ModuliRing R) k (e4B R) with hbB
    set bU := algebraMap (E4ModuliRing R) k (e4U R) with hbU
    set bV := algebraMap (E4ModuliRing R) k (e4V R) with hbV
    set bE := algebraMap (E4ModuliRing R) k e with hbE
    set bX := algebraMap (E4ModuliRing R) k ((universalE4 R).dblX (e4U R) (e4V R) e)
      with hbX
    -- stage 1: `D̄²·x(2Q̄) = P̄` (clearing the `e`-powers)
    have h1k : (2 * bV + bU + bB) ^ 2 * bX
        = (3 * bU ^ 2 + 2 * bB * bU - bV) ^ 2
          + (3 * bU ^ 2 + 2 * bB * bU - bV) * (2 * bV + bU + bB)
          - (bB + 2 * bU) * (2 * bV + bU + bB) ^ 2 := by
      linear_combination (2 * bV + bU + bB) ^ 2 * hxdefk
        + (4 * bB ^ 3 * bE * bU ^ 2 + 16 * bB ^ 2 * bE * bU ^ 3
          + 8 * bB ^ 2 * bE * bU ^ 2 * bV - 4 * bB ^ 2 * bE * bU * bV
          + 4 * bB ^ 2 * bU ^ 2 + 2 * bB ^ 2 * bU + 21 * bB * bE * bU ^ 4
          + 24 * bB * bE * bU ^ 3 * bV - 10 * bB * bE * bU ^ 2 * bV
          - 8 * bB * bE * bU * bV ^ 2 + bB * bE * bV ^ 2 + 12 * bB * bU ^ 3
          + 5 * bB * bU ^ 2 - bB * bV + 9 * bE * bU ^ 5 + 18 * bE * bU ^ 4 * bV
          - 6 * bE * bU ^ 3 * bV - 12 * bE * bU ^ 2 * bV ^ 2 + bE * bU * bV ^ 2
          + 2 * bE * bV ^ 3 + 9 * bU ^ 4 + 3 * bU ^ 3 - bU * bV - bV ^ 2) * hDek
    -- stage 2: the `e`-free quadratic certificate (sympy `S2`, cofactor of `e4Rel` is
    -- `e4Rel` itself)
    have h2R : 4 * ((3 * bU ^ 2 + 2 * bB * bU - bV) ^ 2
          + (3 * bU ^ 2 + 2 * bB * bU - bV) * (2 * bV + bU + bB)
          - (bB + 2 * bU) * (2 * bV + bU + bB) ^ 2) ^ 2
        + ((3 * bU ^ 2 + 2 * bB * bU - bV) ^ 2
          + (3 * bU ^ 2 + 2 * bB * bU - bV) * (2 * bV + bU + bB)
          - (bB + 2 * bU) * (2 * bV + bU + bB) ^ 2) * (2 * bV + bU + bB) ^ 2
        + bB * (2 * bV + bU + bB) ^ 4 = 0 := by
      linear_combination (32 * bB ^ 4 - 64 * bB ^ 3 * bU ^ 2 + 128 * bB ^ 3 * bU
          + 64 * bB ^ 3 * bV + 8 * bB ^ 3 - 320 * bB ^ 2 * bU ^ 3
          + 144 * bB ^ 2 * bU ^ 2 + 320 * bB ^ 2 * bU * bV + 8 * bB ^ 2 * bU
          + 64 * bB ^ 2 * bV ^ 2 + 32 * bB ^ 2 * bV - bB ^ 2 - 544 * bB * bU ^ 4
          - 16 * bB * bU ^ 3 + 512 * bB * bU ^ 2 * bV - 12 * bB * bU ^ 2
          + 256 * bB * bU * bV ^ 2 + 64 * bB * bU * bV - 2 * bB * bU
          + 32 * bB * bV ^ 2 - 320 * bU ^ 5 - 68 * bU ^ 4 + 256 * bU ^ 3 * bV
          - 12 * bU ^ 3 + 256 * bU ^ 2 * bV ^ 2 + 32 * bU ^ 2 * bV - bU ^ 2
          + 32 * bU * bV ^ 2) * hcvk
        + (2 * bU ^ 4 + bU ^ 3 + 3 * bB * bU ^ 2 + 4 * bB ^ 2 * bU
          + 2 * bB ^ 3) * hork
    -- substitute `x(2Q̄) = −B̄` and derive `4B̄²·D̄⁴ = 0`
    rw [h1] at h1k
    have hzero : (4 : k) * (bB ^ 2 * (2 * bV + bU + bB) ^ 4) = 0 := by
      linear_combination h2R
        + (4 * ((3 * bU ^ 2 + 2 * bB * bU - bV) ^ 2
            + (3 * bU ^ 2 + 2 * bB * bU - bV) * (2 * bV + bU + bB)
            - (bB + 2 * bU) * (2 * bV + bU + bB) ^ 2)
          - 4 * bB * (2 * bV + bU + bB) ^ 2 + (2 * bV + bU + bB) ^ 2) * h1k
    have hDu : IsUnit (2 * bV + bU + bB) :=
      isUnit_of_mul_isUnit_left (y := bE) (by rw [hDek]; exact isUnit_one)
    have hBu : IsUnit bB := (isUnit_e4B R).map (algebraMap (E4ModuliRing R) k)
    have h4u : IsUnit ((4 : k) * (bB ^ 2 * (2 * bV + bU + bB) ^ 4)) := by
      refine IsUnit.mul ?_ ((hBu.pow 2).mul (hDu.pow 4))
      rw [show (4 : k) = 2 * 2 by norm_num]
      exact h2k.mul h2k
    exact h4u.ne_zero hzero
  -- the torsion subgroup, its count, and the criterion of record
  have h4k : ((4 : ℕ) : k) ≠ 0 := by
    have := (h2k.mul h2k).ne_zero
    rwa [show ((4 : ℕ) : k) = 2 * 2 by norm_num]
  obtain ⟨eqv⟩ := (universalE4Obj R).curve.torsion_geometricFibre_rank_two 4 k
    (Spec.map φ) h4k
  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ)) = 4 ^ 2 := by
    rw [Nat.card_congr eqv.toEquiv]
    simp [Nat.card_pi, Nat.card_zmod]
  have hmemP : PP ∈ Submodule.torsionBy ℤ
      ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h4P)
  have hmemQ : QQ ∈ Submodule.torsionBy ℤ
      ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast h4Q)
  have hmemX : x ∈ Submodule.torsionBy ℤ
      ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast hx)
  have hkillT : ∀ g : Submodule.torsionBy ℤ
      ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ),
      ((4 : ℕ) : ℤ) • g = 0 := fun g => Submodule.smul_torsionBy _ _
  have hcombosT : ∀ ab : ZMod 4 × ZMod 4, ab ≠ 0 →
      ((ab.1.val : ℤ)) • (⟨PP, hmemP⟩ : Submodule.torsionBy ℤ
          ((universalE4Obj R).curve.Point (Spec.map φ)) ((4 : ℕ) : ℤ))
        + ((ab.2.val : ℤ)) • ⟨QQ, hmemQ⟩ ≠ 0 := by
    intro ab hab hc
    refine combos4_ne_zero h4P h4Q hP2 hQ2 hPQ ab.1 ab.2
      (fun h0 => hab (Prod.ext h0.1 h0.2)) ?_
    have := congrArg (Subtype.val) hc
    simpa using this
  have hgen := (pair_generates_iff_combos_ne_zero 4 hcard hkillT
    ⟨PP, hmemP⟩ ⟨QQ, hmemQ⟩).mp hcombosT ⟨x, hmemX⟩
  -- transport the closure membership down the subtype
  have hmap := AddMonoidHom.map_closure
    ((Submodule.torsionBy ℤ ((universalE4Obj R).curve.Point (Spec.map φ))
      ((4 : ℕ) : ℤ)).subtype.toAddMonoidHom)
    ({⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩} : Set _)
  have hx' : x ∈ AddSubgroup.map
      ((Submodule.torsionBy ℤ ((universalE4Obj R).curve.Point (Spec.map φ))
        ((4 : ℕ) : ℤ)).subtype.toAddMonoidHom)
      (AddSubgroup.closure {⟨PP, hmemP⟩, ⟨QQ, hmemQ⟩}) :=
    ⟨⟨x, hmemX⟩, hgen, rfl⟩
  rw [hmap] at hx'
  simpa [Set.image_insert_eq] using hx'

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
    IsE4Form (W.map f) (f B) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.map_a₁, ha₁, map_one]
  · rw [WeierstrassCurve.map_a₂, ha₂]
  · rw [WeierstrassCurve.map_a₃, ha₃]
  · rw [WeierstrassCurve.map_a₄, ha₄, map_zero]
  · rw [WeierstrassCurve.map_a₆, ha₆, map_zero]

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

/-! #### Private fibrewise helpers: the `(ℤ/4)²`-combination exclusions

At every geometric point of a naive full level-4 structure, every nonzero
`(ℤ/4)²`-combination of the pulled pair is nonzero — the REVERSE direction of
`pair_generates_iff_combos_ne_zero` fed by the generation clause. Specialized to the
exclusions the bridges consume: `2P̄ ≠ 0`, `2Q̄ ≠ 0`, `3P̄ ≠ 0`, `2Q̄ ≠ 2P̄`. -/

set_option backward.isDefEq.respectTransparency false in
/-- At a geometric point of a naive full level-4 structure, every nonzero
`(ℤ/4)²`-combination of the pulled pair is nonzero. -/
private theorem pull_combo_ne_zero_of_isNaiveFullLevel {S : Scheme.{u}}
    (E : EllipticCurve S) (hN : NIsInvertible S 4) {P Q : E.Section}
    (hL : E.IsNaiveFullLevel 4 P Q)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S)
    (a b : ZMod 4) (hab : ¬(a = 0 ∧ b = 0)) :
    (a.val : ℤ) • EllipticCurve.Point.pull E t P
      + (b.val : ℤ) • EllipticCurve.Point.pull E t Q ≠ 0 := by
  obtain ⟨⟨hPk, hQk⟩, hgen⟩ := hL
  have hNk : ((4 : ℕ) : k) ≠ 0 :=
    (nIsInvertible_spec_iff k 4).mp (hN.of_hom t)
  obtain ⟨eqv⟩ := E.torsion_geometricFibre_rank_two 4 k t hNk
  have hcard : Nat.card (Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ)) = 4 ^ 2 := by
    rw [Nat.card_congr eqv.toEquiv]
    simp [Nat.card_pi, Nat.card_zmod]
  have hPN : ((4 : ℕ) : ℤ) • EllipticCurve.Point.pull E t P = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hPk, EllipticCurve.Point.pull_zero]
  have hQN : ((4 : ℕ) : ℤ) • EllipticCurve.Point.pull E t Q = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hQk, EllipticCurve.Point.pull_zero]
  have hmemP : EllipticCurve.Point.pull E t P
      ∈ Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr hPN
  have hmemQ : EllipticCurve.Point.pull E t Q
      ∈ Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr hQN
  have hkillT : ∀ g : Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ),
      ((4 : ℕ) : ℤ) • g = 0 := fun g => Submodule.smul_torsionBy _ _
  have hgenT : ∀ x : Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ),
      x ∈ AddSubgroup.closure
        ({⟨EllipticCurve.Point.pull E t P, hmemP⟩,
          ⟨EllipticCurve.Point.pull E t Q, hmemQ⟩} :
          Set (Submodule.torsionBy ℤ (E.Point t) ((4 : ℕ) : ℤ))) := by
    intro y
    have hy4 : ((4 : ℕ) : ℤ) • (y : E.Point t) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp y.2
    have hmem := hgen k t y.1 hy4
    rw [AddSubgroup.mem_closure_pair] at hmem
    obtain ⟨m, n, hmn⟩ := hmem
    rw [AddSubgroup.mem_closure_pair]
    refine ⟨m, n, Subtype.ext ?_⟩
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
    exact hmn
  have hcombos := (pair_generates_iff_combos_ne_zero 4 hcard hkillT
    ⟨EllipticCurve.Point.pull E t P, hmemP⟩
    ⟨EllipticCurve.Point.pull E t Q, hmemQ⟩).mpr hgenT
  intro hc
  refine hcombos (a, b) (fun h0 => hab ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩)
    (Subtype.ext ?_)
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  simpa using hc

/-- `2P̄ ≠ 0` at every geometric point (the combination `(2, 0)`). -/
private theorem pull_two_zsmul_left_ne_zero {S : Scheme.{u}}
    (E : EllipticCurve S) (hN : NIsInvertible S 4) {P Q : E.Section}
    (hL : E.IsNaiveFullLevel 4 P Q)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    (2 : ℤ) • EllipticCurve.Point.pull E t P ≠ 0 := by
  have h := pull_combo_ne_zero_of_isNaiveFullLevel E hN hL k t 2 0 (by decide)
  rwa [show ((2 : ZMod 4).val : ℤ) = 2 from by decide,
    show ((0 : ZMod 4).val : ℤ) = 0 from by decide, zero_smul, add_zero] at h

/-- `2Q̄ ≠ 0` at every geometric point (the combination `(0, 2)`). -/
private theorem pull_two_zsmul_right_ne_zero {S : Scheme.{u}}
    (E : EllipticCurve S) (hN : NIsInvertible S 4) {P Q : E.Section}
    (hL : E.IsNaiveFullLevel 4 P Q)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    (2 : ℤ) • EllipticCurve.Point.pull E t Q ≠ 0 := by
  have h := pull_combo_ne_zero_of_isNaiveFullLevel E hN hL k t 0 2 (by decide)
  rwa [show ((2 : ZMod 4).val : ℤ) = 2 from by decide,
    show ((0 : ZMod 4).val : ℤ) = 0 from by decide, zero_smul, zero_add] at h

/-- `3P̄ ≠ 0` at every geometric point (the combination `(3, 0)`). -/
private theorem pull_three_zsmul_left_ne_zero {S : Scheme.{u}}
    (E : EllipticCurve S) (hN : NIsInvertible S 4) {P Q : E.Section}
    (hL : E.IsNaiveFullLevel 4 P Q)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    (3 : ℤ) • EllipticCurve.Point.pull E t P ≠ 0 := by
  have h := pull_combo_ne_zero_of_isNaiveFullLevel E hN hL k t 3 0 (by decide)
  rwa [show ((3 : ZMod 4).val : ℤ) = 3 from by decide,
    show ((0 : ZMod 4).val : ℤ) = 0 from by decide, zero_smul, add_zero] at h

/-- `2Q̄ ≠ 2P̄` at every geometric point (the combination `(2, 2)` plus `4P̄ = 0`). -/
private theorem pull_two_zsmul_ne {S : Scheme.{u}}
    (E : EllipticCurve S) (hN : NIsInvertible S 4) {P Q : E.Section}
    (hL : E.IsNaiveFullLevel 4 P Q)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    (2 : ℤ) • EllipticCurve.Point.pull E t Q
      ≠ (2 : ℤ) • EllipticCurve.Point.pull E t P := by
  intro hc
  have hsum := pull_combo_ne_zero_of_isNaiveFullLevel E hN hL k t 2 2 (by decide)
  rw [show ((2 : ZMod 4).val : ℤ) = 2 from by decide] at hsum
  apply hsum
  rw [hc]
  have hP4 : (4 : ℤ) • EllipticCurve.Point.pull E t P = 0 := by
    have h : ((4 : ℕ) : ℤ) • EllipticCurve.Point.pull E t P = 0 := by
      rw [← EllipticCurve.Point.pull_zsmul, hL.1.1, EllipticCurve.Point.pull_zero]
    exact_mod_cast h
  linear_combination (norm := module) hP4

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(the level-4 tangent-denominator certificate)** On a chart marking a section
whose DOUBLE is fibrewise nonzero at `(p, q)`, the tangent denominator `ψ₂(p,q)` is a
unit: a vanishing residue value would make the marked model point `2`-torsion at that
geometric point. The 4-torsion analogue of `isUnit_tangentDen_of_marked` (which used
`3 ∧ 2`-torsion ⟹ zero — unavailable at 4; here the input is directly `2P̄ ≠ 0`). -/
private theorem isUnit_tangentDen_of_marked_two_ne {S : Scheme.{u}}
    {E : EllipticCurve S} {V : S.affineOpens}
    (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {p q : Γ(S, V.1)} (heq : Pr.W.toAffine.Equation p q)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heq)
    (h2ne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      (2 : ℤ) • EllipticCurve.Point.pull E t ⟨σ, hσ⟩ ≠ 0) :
    IsUnit (Pr.W.tangentDen p q) := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro hd0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  set x := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩) with hx
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hns : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb p) (algebraMap ↑Γ(S, V.1) Kb q) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heq)
  have hxpkg : x = ⟨(affineSectionSpecPoint Pr.W Kb p q heq).1,
      (affineSectionSpecPoint Pr.W Kb p q heq).2⟩ := by
    refine Subtype.ext ?_
    rw [hx, chartPointsEquiv_pull_marked Pr tVb heq hMeq]
    rfl
  set y := modelPointAddEquiv Pr.W (K' := Kb) x with hy
  have hyval : y = WeierstrassCurve.Affine.Point.some _ _ hns := by
    rw [hy, hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb p q heq) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W p q heq hns
  -- the vanishing denominator makes `y` two-torsion
  have hdKb : algebraMap ↑Γ(S, V.1) Kb (Pr.W.tangentDen p q) = 0 := by
    rw [halgKb, hd0, map_zero]
  have hyeq : algebraMap ↑Γ(S, V.1) Kb q
      = (Pr.W.baseChange Kb).toAffine.negY
        (algebraMap ↑Γ(S, V.1) Kb p) (algebraMap ↑Γ(S, V.1) Kb q) := by
    rw [WeierstrassCurve.Affine.negY]
    rw [show ((Pr.W.baseChange Kb)).toAffine.a₁
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₁ from rfl,
      show ((Pr.W.baseChange Kb)).toAffine.a₃
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl]
    have hexp : algebraMap ↑Γ(S, V.1) Kb (2 * q + Pr.W.a₁ * p + Pr.W.a₃) = 0 := by
      rw [show (2 * q + Pr.W.a₁ * p + Pr.W.a₃ : ↑Γ(S, V.1))
        = Pr.W.tangentDen p q from rfl]
      exact hdKb
    rw [map_add, map_add, map_mul, map_mul, map_ofNat] at hexp
    linear_combination hexp
  have hy2 : (2 : ℤ) • y = 0 := by
    rw [hyval, two_zsmul]
    exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hyeq
  -- transport back: `2•(pulled point) = 0`, contradicting the fibre hypothesis
  have h2x : (2 : ℤ) • x = 0 := by
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [map_zsmul, map_zero, ← hy]
    exact hy2
  have h2pull : (2 : ℤ) • EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    have h := h2x
    rw [hx, ← map_zsmul] at h
    exact (chartPointsEquiv Pr tVb).map_eq_zero_iff.mp h
  exact h2ne Kb (tVb ≫ chartρ V) h2pull

open LocalPresentation in
/-- `NIsInvertible` at 4 from `IsUnit (2 : R)` on an `Ell/R`-object's base. -/
private theorem nIsInvertible_four_of_isUnit_two {R : CommRingCat.{u}} (X : EllObj R)
    (hR : IsUnit (2 : R)) : NIsInvertible X.base 4 := by
  have h4R : IsUnit (4 : R) := by
    have := hR.mul hR
    rwa [show (2 : R) * 2 = 4 by norm_num] at this
  have h0 : NIsInvertible (Spec R) 4 := by
    rw [NIsInvertible, Nat.cast_ofNat]
    have := h4R.map (Scheme.ΓSpecIso R).inv.hom
    rwa [map_ofNat] at this
  exact h0.of_hom X.structMap

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
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
    Pr.W.a₁ = 1 := by
  letI := Pr.elliptic
  obtain ⟨heq, hMeq⟩ := id hM
  -- fibrewise `2P̄ ≠ 0` and the `a₃`-unit
  have hN : NIsInvertible X.base 4 := nIsInvertible_four_of_isUnit_two X hR
  have h2ne := pull_two_zsmul_left_ne_zero X.curve hN L.2
  have hden : IsUnit (Pr.W.tangentDen 0 0) :=
    isUnit_tangentDen_of_marked_two_ne Pr heq hMeq h2ne
  have ha₃u : IsUnit Pr.W.a₃ := by
    rwa [show Pr.W.tangentDen 0 0 = Pr.W.a₃ from by
      simp only [WeierstrassCurve.tangentDen]
      ring] at hden
  -- RING-DBL at the marked origin
  obtain ⟨e, he'⟩ := hden.exists_right_inv
  have heqd : Pr.W.toAffine.Equation (Pr.W.dblX 0 0 e) (Pr.W.dblY 0 0 e) :=
    equation_dblXY Pr.W 0 0 e heq he'
  -- the model section of the marked point and its 4-torsion
  set σm := chartPointsEquiv Pr (𝟙 (Spec Γ(X.base, V.1)))
    (EllipticCurve.Point.pull X.curve (𝟙 (Spec Γ(X.base, V.1)) ≫ chartρ V)
      ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩) with hσm
  have hσmval : σm = ⟨projModelAffineSection Pr.W 0 0 heq,
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    rw [hσm, chartPointsEquiv_pull_marked Pr (𝟙 _) heq hMeq]
    exact Category.id_comp _
  have hkill : (4 : ℤ) • (⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ : X.curve.Section) = 0 := by
    have h := L.2.1.1
    exact_mod_cast h
  have hkillE : (4 : ℤ) • EllipticCurve.Point.pull X.curve
      (𝟙 (Spec Γ(X.base, V.1)) ≫ chartρ V) ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have h4 : (4 : ℤ) • σm = 0 := by
    rw [hσm, ← map_zsmul, hkillE, map_zero]
  -- the double and its 2-torsion
  have hdbl := two_zsmul_affineSection Pr.W 0 0 e heq he' heqd
  set τ : (modelEllipticCurve Pr.W).Section :=
    ⟨projModelAffineSection Pr.W (Pr.W.dblX 0 0 e) (Pr.W.dblY 0 0 e) heqd,
      projModelAffineSection_projModelπ _ _ _ _⟩ with hτdef
  have hτ2 : (2 : ℤ) • τ = 0 := by
    have h := h4
    rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul, hσmval, hdbl] at h
    exact h
  have hτneg : -τ = τ := by
    refine neg_eq_of_add_eq_zero_left ?_
    rw [← two_zsmul]
    exact hτ2
  -- coordinates of the negated double
  have hnegval : -τ = ⟨projModelAffineSection Pr.W (Pr.W.dblX 0 0 e)
      (Pr.W.toAffine.negY (Pr.W.dblX 0 0 e) (Pr.W.dblY 0 0 e))
      ((Pr.W.toAffine.equation_neg _ _).mpr heqd),
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    have hv : (-τ).1 = τ.1 ≫ (modelEllipticCurve Pr.W).mulByHom (-1) := by
      rw [show -τ = (-1 : ℤ) • τ from (neg_one_zsmul τ).symm]
      exact (modelEllipticCurve Pr.W).point_smul_eq_comp_mulBy _ (-1) τ
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hτdef]
    exact negModelHom_affineSection_general Pr.W _ _ heqd
  have hvals : projModelAffineSection Pr.W (Pr.W.dblX 0 0 e)
      (Pr.W.toAffine.negY (Pr.W.dblX 0 0 e) (Pr.W.dblY 0 0 e))
      ((Pr.W.toAffine.equation_neg _ _).mpr heqd)
      = projModelAffineSection Pr.W (Pr.W.dblX 0 0 e) (Pr.W.dblY 0 0 e) heqd :=
    congrArg Subtype.val (hnegval.symm.trans (hτneg.trans hτdef))
  have hpsi := (projModelAffineSection_injective Pr.W (heq := hvals)).2
  -- read the coefficients off the negation-symmetry
  have hN0 : Pr.W.tangentNum 0 0 = 0 := by
    simp only [WeierstrassCurve.tangentNum, ha₄]
    ring
  have hx2 : Pr.W.dblX 0 0 e = -Pr.W.a₂ := by
    rw [dblX_expand, hN0]
    ring
  have hy2 : Pr.W.dblY 0 0 e = Pr.W.a₁ * Pr.W.a₂ - Pr.W.a₃ := by
    rw [dblY_expand, hx2, hN0]
    ring
  have key : Pr.W.a₃ * (Pr.W.a₁ - 1) = 0 := by
    rw [WeierstrassCurve.Affine.negY, hx2, hy2] at hpsi
    linear_combination -hpsi - Pr.W.a₁ * ha₂₃
  have h1 := (ha₃u.mul_right_eq_zero).mp key
  linear_combination h1

/-- **(E4A-10 helper, the field-arithmetic core of the `u + 2B` exclusion)** In any field,
given the curve relation, the tangent-denominator unit relation `(2V+U+B)·E = 1`, the two
RING-DBL coordinate expansions for `Q̄ = (X, Y)`, and the residue-point hypothesis
`U + 2B = 0`, the doubling coordinates of `Q̄` collapse onto those of `P̄`: `X = −B` and
`Y = 0` (the sympy `EXCL-X` / `EXCL-Y` certificates). Extracted as a barrier lemma so the
two heavy polynomial `linear_combination`s are checked once over a variable field, keeping
the scheme-level wrapper under the default heartbeat budget. -/
private theorem e4_double_collapse {k : Type u} [Field k] (B U V E X Y : k)
    (hcv : V ^ 2 + U * V + B * V - U ^ 3 - B * U ^ 2 = 0)
    (heR : (2 * V + U + B) * E = 1)
    (hX : X = ((3 * U ^ 2 + 2 * B * U - V) * E) ^ 2
      + (3 * U ^ 2 + 2 * B * U - V) * E - B - 2 * U)
    (hY : Y = -((3 * U ^ 2 + 2 * B * U - V) * E * (X - U) + V) - X - B)
    (hu2B : U + 2 * B = 0) :
    X = -B ∧ Y = 0 := by
  have hDne : (2 * V + U + B) ≠ 0 :=
    (isUnit_of_mul_isUnit_left (y := E)
      (by rw [heR]; exact isUnit_one)).ne_zero
  have hstepX : (2 * V + U + B) ^ 2 * (X + B) = 0 := by
    linear_combination (2 * V + U + B) ^ 2 * hX
      + (-8 * U - 1) * hcv + (2 * B * U ^ 2 + U ^ 3) * hu2B
      + (4 * B ^ 3 * E * U ^ 2 + 16 * B ^ 2 * E * U ^ 3
        + 8 * B ^ 2 * E * U ^ 2 * V - 4 * B ^ 2 * E * U * V
        + 4 * B ^ 2 * U ^ 2 + 2 * B ^ 2 * U + 21 * B * E * U ^ 4
        + 24 * B * E * U ^ 3 * V - 10 * B * E * U ^ 2 * V
        - 8 * B * E * U * V ^ 2 + B * E * V ^ 2 + 12 * B * U ^ 3
        + 5 * B * U ^ 2 - B * V + 9 * E * U ^ 5 + 18 * E * U ^ 4 * V
        - 6 * E * U ^ 3 * V - 12 * E * U ^ 2 * V ^ 2 + E * U * V ^ 2
        + 2 * E * V ^ 3 + 9 * U ^ 4 + 3 * U ^ 3 - U * V - V ^ 2) * heR
  have hxeq : X = -B := by
    rcases mul_eq_zero.mp hstepX with h | h
    · exact absurd h (pow_ne_zero 2 hDne)
    · linear_combination h
  have hstepY : (2 * V + U + B) * Y = 0 := by
    linear_combination (2 * V + U + B) * hY
      + (-(2 * V + U + B) * (3 * U ^ 2 + 2 * B * U - V) * E
        - (2 * V + U + B)) * hxeq
      + (-2 : k) * hcv + (B * U + U ^ 2) * hu2B
      + (2 * B ^ 2 * U + 5 * B * U ^ 2 - B * V + 3 * U ^ 3
        - U * V) * heR
  have hyeq : Y = 0 := by
    rcases mul_eq_zero.mp hstepY with h | h
    · exact absurd h hDne
    · exact h
  exact ⟨hxeq, hyeq⟩

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-10 helper, the `u + 2B` exclusion ★★)** On an `ℰ₄`-form chart marking `P` at
the origin and `Q` at `(u, v)`, with the pulled doubles fibrewise distinct
(`2Q̄ ≠ 2P̄`), `u + 2B` is a unit: at a residue point with `ū = −2B̄`, the RING-DBL
doubling coordinates of `Q̄` collapse onto those of `P̄` (`x(2Q̄) = −B̄`, `y(2Q̄) = 0` —
the sympy `EXCL-X`/`EXCL-Y` certificates), so `2Q̄ = 2P̄`. -/
private theorem isUnit_x_add_twoB_of_marked_pair {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {B u v : Γ(S, V.1)}
    (ha₁ : Pr.W.a₁ = 1) (ha₂ : Pr.W.a₂ = B) (ha₃ : Pr.W.a₃ = B) (ha₄ : Pr.W.a₄ = 0)
    (ha₆ : Pr.W.a₆ = 0) (hBu : IsUnit B)
    {σP : S ⟶ E.toEllipticCurveGeom.E} {hσP : σP ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {σQ : S ⟶ E.toEllipticCurveGeom.E} {hσQ : σQ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    (heqP : Pr.W.toAffine.Equation 0 0)
    (hMeqP : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσP V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W 0 0 heqP)
    (heqQ : Pr.W.toAffine.Equation u v)
    (hMeqQ : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσQ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W u v heqQ)
    (hDu : IsUnit (Pr.W.tangentDen u v))
    (h2QP : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      (2 : ℤ) • EllipticCurve.Point.pull E t ⟨σQ, hσQ⟩ ≠
        (2 : ℤ) • EllipticCurve.Point.pull E t ⟨σP, hσP⟩) :
    IsUnit (u + 2 * B) := by
  letI := Pr.elliptic
  -- the ring-level doubles
  obtain ⟨e, he'⟩ := hDu.exists_right_inv
  obtain ⟨bP, hbP'⟩ := hBu.exists_right_inv
  have hbP : Pr.W.tangentDen 0 0 * bP = 1 := by
    rw [show Pr.W.tangentDen 0 0 = B from by
      simp only [WeierstrassCurve.tangentDen, ha₃]
      ring]
    exact hbP'
  have heqdQ : Pr.W.toAffine.Equation (Pr.W.dblX u v e) (Pr.W.dblY u v e) :=
    equation_dblXY Pr.W u v e heqQ he'
  have heqdP : Pr.W.toAffine.Equation (Pr.W.dblX 0 0 bP) (Pr.W.dblY 0 0 bP) :=
    equation_dblXY Pr.W 0 0 bP heqP hbP
  have hdblQ := two_zsmul_affineSection Pr.W u v e heqQ he' heqdQ
  have hdblP := two_zsmul_affineSection Pr.W 0 0 bP heqP hbP heqdP
  -- chart-ring coefficient normal forms
  have hN0 : Pr.W.tangentNum 0 0 = 0 := by
    simp only [WeierstrassCurve.tangentNum, ha₄]
    ring
  have hXP : Pr.W.dblX 0 0 bP = -B := by
    rw [dblX_expand, hN0, ha₂]
    ring
  have hYP : Pr.W.dblY 0 0 bP = 0 := by
    rw [dblY_expand, hXP, hN0, ha₁, ha₃]
    ring
  have hNQ : Pr.W.tangentNum u v = 3 * u ^ 2 + 2 * B * u - v := by
    simp only [WeierstrassCurve.tangentNum, ha₁, ha₂, ha₄]
    ring
  have hx2R : Pr.W.dblX u v e = ((3 * u ^ 2 + 2 * B * u - v) * e) ^ 2
      + (3 * u ^ 2 + 2 * B * u - v) * e - B - 2 * u := by
    rw [dblX_expand, hNQ, ha₁, ha₂]
    ring
  have hy2R : Pr.W.dblY u v e = -((3 * u ^ 2 + 2 * B * u - v) * e
      * (Pr.W.dblX u v e - u) + v) - Pr.W.dblX u v e - B := by
    rw [dblY_expand, hNQ, ha₁, ha₃]
    ring
  have hcvR : v ^ 2 + u * v + B * v - u ^ 3 - B * u ^ 2 = 0 := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp heqQ
    rw [ha₁, ha₂, ha₃, ha₄, ha₆] at h
    linear_combination h
  have heR : (2 * v + u + B) * e = 1 := by
    rw [show (2 * v + u + B : Γ(S, V.1)) = Pr.W.tangentDen u v from by
      simp only [WeierstrassCurve.tangentDen, ha₁, ha₃]
      ring]
    exact he'
  -- the residue-field certificate
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro hu2B0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hnsQ2 : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblX u v e))
      (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblY u v e)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqdQ)
  have hnsP2 : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblX 0 0 bP))
      (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblY 0 0 bP)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqdP)
  -- the pulled marked points and their doubled dictionary values
  set xQ := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σQ, hσQ⟩) with hxQ
  set xP := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σP, hσP⟩) with hxP
  have hxQpkg : xQ = ⟨(affineSectionSpecPoint Pr.W Kb u v heqQ).1,
      (affineSectionSpecPoint Pr.W Kb u v heqQ).2⟩ := by
    refine Subtype.ext ?_
    rw [hxQ, chartPointsEquiv_pull_marked Pr tVb heqQ hMeqQ]
    rfl
  have hxPpkg : xP = ⟨(affineSectionSpecPoint Pr.W Kb 0 0 heqP).1,
      (affineSectionSpecPoint Pr.W Kb 0 0 heqP).2⟩ := by
    refine Subtype.ext ?_
    rw [hxP, chartPointsEquiv_pull_marked Pr tVb heqP hMeqP]
    rfl
  have h2xQ : (2 : ℤ) • xQ = ⟨(affineSectionSpecPoint Pr.W Kb
      (Pr.W.dblX u v e) (Pr.W.dblY u v e) heqdQ).1,
      (affineSectionSpecPoint Pr.W Kb _ _ heqdQ).2⟩ := by
    rw [hxQpkg]
    show (2 : ℤ) • EllipticCurve.Point.pull (modelEllipticCurve Pr.W) tVb
      ⟨projModelAffineSection Pr.W u v heqQ,
        projModelAffineSection_projModelπ _ _ _ _⟩ = _
    rw [← EllipticCurve.Point.pull_zsmul, hdblQ]
    rfl
  have h2xP : (2 : ℤ) • xP = ⟨(affineSectionSpecPoint Pr.W Kb
      (Pr.W.dblX 0 0 bP) (Pr.W.dblY 0 0 bP) heqdP).1,
      (affineSectionSpecPoint Pr.W Kb _ _ heqdP).2⟩ := by
    rw [hxPpkg]
    show (2 : ℤ) • EllipticCurve.Point.pull (modelEllipticCurve Pr.W) tVb
      ⟨projModelAffineSection Pr.W 0 0 heqP,
        projModelAffineSection_projModelπ _ _ _ _⟩ = _
    rw [← EllipticCurve.Point.pull_zsmul, hdblP]
    rfl
  have hval2Q : modelPointAddEquiv Pr.W (K' := Kb) ((2 : ℤ) • xQ)
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ2 := by
    rw [h2xQ]
    show projModelPointsEquiv Pr.W Kb
      (affineSectionSpecPoint Pr.W Kb _ _ heqdQ) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W _ _ heqdQ hnsQ2
  have hval2P : modelPointAddEquiv Pr.W (K' := Kb) ((2 : ℤ) • xP)
      = WeierstrassCurve.Affine.Point.some _ _ hnsP2 := by
    rw [h2xP]
    show projModelPointsEquiv Pr.W Kb
      (affineSectionSpecPoint Pr.W Kb _ _ heqdP) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W _ _ heqdP hnsP2
  -- the transported fibre inequality
  have hne : (2 : ℤ) • xQ ≠ (2 : ℤ) • xP := by
    intro hc
    refine h2QP Kb (tVb ≫ chartρ V) ((chartPointsEquiv Pr tVb).injective ?_)
    rw [map_zsmul, map_zsmul, ← hxQ, ← hxP]
    exact hc
  -- mapped hypotheses in `Kb`
  have hu2Bk : algebraMap ↑Γ(S, V.1) Kb u + 2 * algebraMap ↑Γ(S, V.1) Kb B = 0 := by
    have h : algebraMap ↑Γ(S, V.1) Kb (u + 2 * B) = 0 := by
      rw [halgKb, hu2B0, map_zero]
    rw [map_add, map_mul, map_ofNat] at h
    exact h
  have hcvk := congrArg (algebraMap ↑Γ(S, V.1) Kb) hcvR
  have heRk := congrArg (algebraMap ↑Γ(S, V.1) Kb) heR
  have hxdefk := congrArg (algebraMap ↑Γ(S, V.1) Kb) hx2R
  have hydefk := congrArg (algebraMap ↑Γ(S, V.1) Kb) hy2R
  have hXPk := congrArg (algebraMap ↑Γ(S, V.1) Kb) hXP
  have hYPk := congrArg (algebraMap ↑Γ(S, V.1) Kb) hYP
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, map_one,
    map_neg] at hcvk heRk hxdefk hydefk hXPk hYPk
  -- the two coordinate collapses (sympy `EXCL-X` / `EXCL-Y`), factored through the
  -- pure field-arithmetic barrier `e4_double_collapse`
  obtain ⟨hxeq2, hyeq2⟩ := e4_double_collapse
    (algebraMap ↑Γ(S, V.1) Kb B) (algebraMap ↑Γ(S, V.1) Kb u)
    (algebraMap ↑Γ(S, V.1) Kb v) (algebraMap ↑Γ(S, V.1) Kb e)
    (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblX u v e))
    (algebraMap ↑Γ(S, V.1) Kb (Pr.W.dblY u v e))
    hcvk heRk hxdefk hydefk hu2Bk
  -- assemble the contradiction: the two doubles coincide
  apply hne
  apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
  rw [hval2Q, hval2P]
  congr 1
  · linear_combination hxeq2 - hXPk
  · linear_combination hyeq2 - hYPk

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
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
    2 * u ^ 4 + u ^ 3 + 3 * B * u ^ 2 + 4 * B ^ 2 * u + 2 * B ^ 3 = 0 := by
  letI := Pr.elliptic
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hE4
  obtain ⟨heqQ, hMeqQ⟩ := id hMQ
  obtain ⟨heqP, hMeqP⟩ := id hMP
  -- the fibrewise inputs
  have hN : NIsInvertible X.base 4 := nIsInvertible_four_of_isUnit_two X hR
  have h2neQ := pull_two_zsmul_right_ne_zero X.curve hN L.2
  have h2QP := pull_two_zsmul_ne X.curve hN L.2
  have hpm : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (t : Spec (CommRingCat.of k) ⟶ X.base),
      EllipticCurve.Point.pull X.curve t ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩
        ≠ EllipticCurve.Point.pull X.curve t ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ ∧
      EllipticCurve.Point.pull X.curve t ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩
        ≠ -EllipticCurve.Point.pull X.curve t ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ := by
    intro k _ _ t
    exact X.curve.pull_ne_pm_of_isNaiveFullLevel 4 (by norm_num) hN L.2 k t
  -- the three unit certificates
  have hDu : IsUnit (Pr.W.tangentDen u v) :=
    isUnit_tangentDen_of_marked_two_ne Pr heqQ hMeqQ h2neQ
  have hu : IsUnit u :=
    isUnit_x_of_marked_pair Pr heqP hMeqP heqQ hMeqQ hpm
  have hu2B : IsUnit (u + 2 * B) :=
    isUnit_x_add_twoB_of_marked_pair Pr ha₁ ha₂ ha₃ ha₄ ha₆ hB heqP hMeqP heqQ hMeqQ
      hDu h2QP
  -- RING-DBL at the marked `Q` and the 4-torsion negation-fixedness of the double
  obtain ⟨e, he'⟩ := hDu.exists_right_inv
  have heqd : Pr.W.toAffine.Equation (Pr.W.dblX u v e) (Pr.W.dblY u v e) :=
    equation_dblXY Pr.W u v e heqQ he'
  set σm := chartPointsEquiv Pr (𝟙 (Spec Γ(X.base, V.1)))
    (EllipticCurve.Point.pull X.curve (𝟙 (Spec Γ(X.base, V.1)) ≫ chartρ V)
      ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩) with hσm
  have hσmval : σm = ⟨projModelAffineSection Pr.W u v heqQ,
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    rw [hσm, chartPointsEquiv_pull_marked Pr (𝟙 _) heqQ hMeqQ]
    exact Category.id_comp _
  have hkill : (4 : ℤ) • (⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩ : X.curve.Section) = 0 := by
    have h := L.2.1.2
    exact_mod_cast h
  have hkillE : (4 : ℤ) • EllipticCurve.Point.pull X.curve
      (𝟙 (Spec Γ(X.base, V.1)) ≫ chartρ V) ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have h4 : (4 : ℤ) • σm = 0 := by
    rw [hσm, ← map_zsmul, hkillE, map_zero]
  have hdbl := two_zsmul_affineSection Pr.W u v e heqQ he' heqd
  set τ : (modelEllipticCurve Pr.W).Section :=
    ⟨projModelAffineSection Pr.W (Pr.W.dblX u v e) (Pr.W.dblY u v e) heqd,
      projModelAffineSection_projModelπ _ _ _ _⟩ with hτdef
  have hτ2 : (2 : ℤ) • τ = 0 := by
    have h := h4
    rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul, hσmval, hdbl] at h
    exact h
  have hτneg : -τ = τ := by
    refine neg_eq_of_add_eq_zero_left ?_
    rw [← two_zsmul]
    exact hτ2
  have hnegval : -τ = ⟨projModelAffineSection Pr.W (Pr.W.dblX u v e)
      (Pr.W.toAffine.negY (Pr.W.dblX u v e) (Pr.W.dblY u v e))
      ((Pr.W.toAffine.equation_neg _ _).mpr heqd),
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    have hv : (-τ).1 = τ.1 ≫ (modelEllipticCurve Pr.W).mulByHom (-1) := by
      rw [show -τ = (-1 : ℤ) • τ from (neg_one_zsmul τ).symm]
      exact (modelEllipticCurve Pr.W).point_smul_eq_comp_mulBy _ (-1) τ
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hτdef]
    exact negModelHom_affineSection_general Pr.W _ _ heqd
  have hvals : projModelAffineSection Pr.W (Pr.W.dblX u v e)
      (Pr.W.toAffine.negY (Pr.W.dblX u v e) (Pr.W.dblY u v e))
      ((Pr.W.toAffine.equation_neg _ _).mpr heqd)
      = projModelAffineSection Pr.W (Pr.W.dblX u v e) (Pr.W.dblY u v e) heqd :=
    congrArg Subtype.val (hnegval.symm.trans (hτneg.trans hτdef))
  have hpsi := (projModelAffineSection_injective Pr.W (heq := hvals)).2
  -- the coordinate normal forms and the master identity (sympy `LC2`/`LC3`/`LC4`)
  have hNQ : Pr.W.tangentNum u v = 3 * u ^ 2 + 2 * B * u - v := by
    simp only [WeierstrassCurve.tangentNum, ha₁, ha₂, ha₄]
    ring
  have hx2R : Pr.W.dblX u v e = ((3 * u ^ 2 + 2 * B * u - v) * e) ^ 2
      + (3 * u ^ 2 + 2 * B * u - v) * e - B - 2 * u := by
    rw [dblX_expand, hNQ, ha₁, ha₂]
    ring
  have hy2R : Pr.W.dblY u v e = -((3 * u ^ 2 + 2 * B * u - v) * e
      * (Pr.W.dblX u v e - u) + v) - Pr.W.dblX u v e - B := by
    rw [dblY_expand, hNQ, ha₁, ha₃]
    ring
  have hcvR : v ^ 2 + u * v + B * v - u ^ 3 - B * u ^ 2 = 0 := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp heqQ
    rw [ha₁, ha₂, ha₃, ha₄, ha₆] at h
    linear_combination h
  have heR : (2 * v + u + B) * e = 1 := by
    rw [show (2 * v + u + B : Γ(X.base, V.1)) = Pr.W.tangentDen u v from by
      simp only [WeierstrassCurve.tangentDen, ha₁, ha₃]
      ring]
    exact he'
  -- the linear `ψ₂`-condition at the double
  have hpsi' : 2 * Pr.W.dblY u v e + Pr.W.dblX u v e + B = 0 := by
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃] at hpsi
    linear_combination -hpsi
  -- stage 1: clear the `e`-powers off the abscissa (sympy `LC2`)
  have h1 : (2 * v + u + B) ^ 2 * Pr.W.dblX u v e
      = (3 * u ^ 2 + 2 * B * u - v) ^ 2
        + (3 * u ^ 2 + 2 * B * u - v) * (2 * v + u + B)
        - (B + 2 * u) * (2 * v + u + B) ^ 2 := by
    linear_combination (2 * v + u + B) ^ 2 * hx2R
      + (4 * B ^ 3 * e * u ^ 2 + 16 * B ^ 2 * e * u ^ 3
        + 8 * B ^ 2 * e * u ^ 2 * v - 4 * B ^ 2 * e * u * v
        + 4 * B ^ 2 * u ^ 2 + 2 * B ^ 2 * u + 21 * B * e * u ^ 4
        + 24 * B * e * u ^ 3 * v - 10 * B * e * u ^ 2 * v
        - 8 * B * e * u * v ^ 2 + B * e * v ^ 2 + 12 * B * u ^ 3
        + 5 * B * u ^ 2 - B * v + 9 * e * u ^ 5 + 18 * e * u ^ 4 * v
        - 6 * e * u ^ 3 * v - 12 * e * u ^ 2 * v ^ 2 + e * u * v ^ 2
        + 2 * e * v ^ 3 + 9 * u ^ 4 + 3 * u ^ 3 - u * v - v ^ 2) * heR
  -- stage 2: the `x2`-linear consequence of the `ψ₂`-condition (sympy `LC3`)
  have hlin : (2 * (3 * u ^ 2 + 2 * B * u - v) + (2 * v + u + B)) * Pr.W.dblX u v e
      = 2 * (3 * u ^ 2 + 2 * B * u - v) * u - 2 * v * (2 * v + u + B)
        - B * (2 * v + u + B) := by
    linear_combination (-(2 * v + u + B)) * hpsi' + 2 * (2 * v + u + B) * hy2R
      + (-2 * (3 * u ^ 2 + 2 * B * u - v) * (Pr.W.dblX u v e - u)) * heR
  -- the master identity (sympy `LC4`): `u(2B+u)·e4Rel = 0`
  have hfin : (u * (2 * B + u))
      * (2 * u ^ 4 + u ^ 3 + 3 * B * u ^ 2 + 4 * B ^ 2 * u + 2 * B ^ 3) = 0 := by
    linear_combination (2 * (3 * u ^ 2 + 2 * B * u - v) + (2 * v + u + B)) * h1
      - (2 * v + u + B) ^ 2 * hlin
      + (-16 * B ^ 2 * u + 4 * B ^ 2 - 56 * B * u ^ 2 - 4 * B * u + 16 * B * v
        - B - 56 * u ^ 3 - 10 * u ^ 2 + 16 * u * v - u + 16 * v ^ 2) * hcvR
  -- cancel the unit `u(2B + u)`
  have huu : IsUnit (u * (2 * B + u)) := by
    refine hu.mul ?_
    rwa [show (2 * B + u : Γ(X.base, V.1)) = u + 2 * B by ring]
  exact (huu.mul_right_eq_zero).mp hfin

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-11 helper, the `a₂`-unit certificate ★★)** On an `a₄ = a₆ = 0` chart with
unit `a₃` marking a fibrewise `3P̄ ≠ 0` section at the origin, `a₂` is a unit: at a
residue point with `ā₂ = 0` the fibre curve is in FLEX normal form, so the origin is
`3`-torsion (`three_zsmul_some_origin`) — contradicting `3P̄ ≠ 0`. (The `μ`-quantity of
the Tate-normal-form chain, certified fibrewise; the order-4 replacement of E3's
`isUnit_a₃_of_marked_origin` pattern.) -/
private theorem isUnit_a₂_of_marked_origin_four {S : Scheme.{u}}
    {E : EllipticCurve S} {V : S.affineOpens}
    (Pr : LocalPresentation E.toEllipticCurveGeom V)
    (ha₄ : Pr.W.a₄ = 0) (ha₆ : Pr.W.a₆ = 0) (ha₃u : IsUnit Pr.W.a₃)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    (heq : Pr.W.toAffine.Equation 0 0)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W 0 0 heq)
    (h3ne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      (3 : ℤ) • EllipticCurve.Point.pull E t ⟨σ, hσ⟩ ≠ 0) :
    IsUnit Pr.W.a₂ := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro ha₂0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  set x := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩) with hx
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hns : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb 0) (algebraMap ↑Γ(S, V.1) Kb 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heq)
  have hxpkg : x = ⟨(affineSectionSpecPoint Pr.W Kb 0 0 heq).1,
      (affineSectionSpecPoint Pr.W Kb 0 0 heq).2⟩ := by
    refine Subtype.ext ?_
    rw [hx, chartPointsEquiv_pull_marked Pr tVb heq hMeq]
    rfl
  set y := modelPointAddEquiv Pr.W (K' := Kb) x with hy
  have hyval : y = WeierstrassCurve.Affine.Point.some _ _ hns := by
    rw [hy, hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb 0 0 heq) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W 0 0 heq hns
  -- the fibre curve is flex-normal-form at this residue point
  have hflex : ((Pr.W.baseChange Kb)).IsFlexNF := by
    refine ⟨?_, ?_, ?_⟩
    · rw [show ((Pr.W.baseChange Kb)).a₂
          = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₂ from rfl]
      rw [halgKb, ha₂0, map_zero]
    · rw [show ((Pr.W.baseChange Kb)).a₄
          = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₄ from rfl, ha₄, map_zero]
    · rw [show ((Pr.W.baseChange Kb)).a₆
          = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₆ from rfl, ha₆, map_zero]
  have ha₃Kb : ((Pr.W.baseChange Kb)).a₃ ≠ 0 := by
    rw [show ((Pr.W.baseChange Kb)).a₃
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl]
    exact (ha₃u.map _).ne_zero
  -- the origin is `3`-torsion on a flex curve
  have hns0 : (Pr.W.baseChange Kb).toAffine.Nonsingular 0 0 := by
    simpa only [map_zero] using hns
  have h3y : (3 : ℤ) • y = 0 := by
    rw [hyval]
    have h := WeierstrassCurve.Affine.Point.three_zsmul_some_origin hflex ha₃Kb hns0
    simpa only [map_zero] using h
  -- transport back and contradict `3P̄ ≠ 0`
  have h3x : (3 : ℤ) • x = 0 := by
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [map_zsmul, map_zero, ← hy]
    exact h3y
  have h3pull : (3 : ℤ) • EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    have h := h3x
    rw [hx, ← map_zsmul] at h
    exact (chartPointsEquiv Pr tVb).map_eq_zero_iff.mp h
  exact h3ne Kb (tVb ≫ chartρ V) h3pull

open WeierstrassCurve in
/-- The `⟨w,0,0,0⟩`-scaling with `w·a₂ = a₃` equalizes `a₂` and `a₃`. -/
private theorem scale_vc_a₂₃ {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (w : Aˣ) (hspec : (w : A) * W.a₂ = W.a₃) :
    ((⟨w, 0, 0, 0⟩ : VariableChange A) • W).a₂
      = ((⟨w, 0, 0, 0⟩ : VariableChange A) • W).a₃ := by
  have hui : ((w⁻¹ : Aˣ) : A) * (w : A) = 1 := w.inv_mul
  rw [variableChange_a₂, variableChange_a₃]
  linear_combination ((w⁻¹ : Aˣ) : A) ^ 3 * hspec
    - ((w⁻¹ : Aˣ) : A) ^ 2 * W.a₂ * hui

open WeierstrassCurve in
/-- The `⟨w,0,0,0⟩`-scaling preserves `a₄ = 0`. -/
private theorem scale_vc_a₄ {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (w : Aˣ) (ha₄ : W.a₄ = 0) :
    ((⟨w, 0, 0, 0⟩ : VariableChange A) • W).a₄ = 0 := by
  rw [variableChange_a₄, ha₄]
  ring

open WeierstrassCurve in
/-- The `⟨w,0,0,0⟩`-scaling preserves `a₆ = 0`. -/
private theorem scale_vc_a₆ {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (w : Aˣ) (ha₆ : W.a₆ = 0) :
    ((⟨w, 0, 0, 0⟩ : VariableChange A) • W).a₆ = 0 := by
  rw [variableChange_a₆, ha₆]
  ring

open WeierstrassCurve in
/-- The `⟨w,0,0,0⟩`-scaled `a₂` is a unit when `a₂` is. -/
private theorem scale_vc_a₂_isUnit {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (w : Aˣ) (ha₂u : IsUnit W.a₂) :
    IsUnit (((⟨w, 0, 0, 0⟩ : VariableChange A) • W).a₂) := by
  rw [variableChange_a₂]
  refine IsUnit.mul ((w⁻¹).isUnit.pow 2) ?_
  rwa [show W.a₂ - (0 : A) * W.a₁ + 3 * 0 - (0 : A) ^ 2 = W.a₂ by ring]

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-11, the datum assembly)** Every naive full level-4 structure is an
`ℰ₄`-datum: atlas charts + the (N-agnostic) marking pipeline
(`marksAt_of_forall_pull_ne_zero`), translation of `P` to the origin
(`marksAt_origin_ofVC`), the `a₄`-killing shear (with the `ψ₂(P) = a₃`-unit from
fibrewise `2P̄ ≠ 0`), the `a₂`-unit from fibrewise `3P̄ ≠ 0`
(`isUnit_a₂_of_marked_origin_four` — the Tate-normal-form `μ`), the `a₂ = a₃` scaling,
then bridge A (`a₁ = 1`) and bridge Q (`e4Rel`). Mirror of `isE3Datum_of_bridges`
with the Tate normalization replacing the flex normalization. -/
theorem isE4Datum_of_bridges {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (2 : R))
    (L : X.curve.FullLevelPt 4) :
    IsE4Datum X L := by
  intro s
  classical
  -- the atlas chart at `s`
  obtain ⟨i, hsi⟩ := X.curve.toEllipticCurveGeom.atlas.covers s
  -- fibrewise nonvanishing of the two marked sections and the torsion exclusions
  have hN : NIsInvertible X.base 4 := nIsInvertible_four_of_isUnit_two X hR
  have hneP := X.curve.pull_ne_zero_left_of_isNaiveFullLevel 4 (by norm_num) hN L.2
  have hneQ := X.curve.pull_ne_zero_right_of_isNaiveFullLevel 4 (by norm_num) hN L.2
  have h2neP := pull_two_zsmul_left_ne_zero X.curve hN L.2
  have h3neP := pull_three_zsmul_left_ne_zero X.curve hN L.2
  -- markings on the atlas chart
  obtain ⟨p₀, q₀, hMP₀⟩ :=
    (X.curve.toEllipticCurveGeom.atlas.presentation i).marksAt_of_forall_pull_ne_zero
      L.1.1.2 hneP
  obtain ⟨p₁, q₁, hMQ₀⟩ :=
    (X.curve.toEllipticCurveGeom.atlas.presentation i).marksAt_of_forall_pull_ne_zero
      L.1.2.2 hneQ
  -- translate `P` to the origin
  set C₁ : VariableChange ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    ⟨1, p₀, 0, q₀⟩ with hC₁
  set Pr₁ := (X.curve.toEllipticCurveGeom.atlas.presentation i).ofVC C₁ with hPr₁
  have hMP₁ : Pr₁.MarksAt L.1.1.2 0 0 :=
    marksAt_origin_ofVC (X.curve.toEllipticCurveGeom.atlas.presentation i) hMP₀
  have hMQ₁ := marksAt_ofVC_vc (X.curve.toEllipticCurveGeom.atlas.presentation i)
    hMQ₀ C₁
  -- the `a₃`-unit on the origin-marked chart (`ψ₂(P) = a₃`, fibrewise `2P̄ ≠ 0`)
  obtain ⟨heq₁, hMeq₁⟩ := id hMP₁
  have ha₃ : IsUnit Pr₁.W.a₃ := by
    have hden := isUnit_tangentDen_of_marked_two_ne Pr₁ heq₁ hMeq₁ h2neP
    rwa [show Pr₁.W.tangentDen 0 0 = Pr₁.W.a₃ from by
      simp only [WeierstrassCurve.tangentDen]
      ring] at hden
  -- the `a₄`-killing shear
  set sSh : ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    Pr₁.W.a₄ * ((ha₃.unit⁻¹ : _ˣ) : _) with hsSh
  set C₂ : VariableChange ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    ⟨1, 0, sSh, 0⟩ with hC₂
  set Pr₂ := Pr₁.ofVC C₂ with hPr₂
  have hMP₂ : Pr₂.MarksAt L.1.1.2 0 0 := by
    have h := marksAt_ofVC_vc Pr₁ hMP₁ C₂
    have hx : C₂.vcX 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcX, hC₂]
    have hy : C₂.vcY 0 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcY, hC₂]
    rwa [hx, hy] at h
  have hMQ₂ := marksAt_ofVC_vc Pr₁ hMQ₁ C₂
  -- the sheared chart coefficients
  have ha₃₂ : Pr₂.W.a₃ = Pr₁.W.a₃ := by
    show (C₂ • Pr₁.W).a₃ = Pr₁.W.a₃
    rw [WeierstrassCurve.variableChange_a₃]
    simp [hC₂]
  have ha₄₂ : Pr₂.W.a₄ = 0 := by
    show (C₂ • Pr₁.W).a₄ = 0
    rw [WeierstrassCurve.variableChange_a₄]
    simp only [hC₂, hsSh]
    rw [show ((⟨1, 0, sSh, 0⟩ : VariableChange _).u⁻¹ : _) = (1 : _ˣ) from by
      simp [hC₂]]
    push_cast
    rw [show Pr₁.W.a₄ - Pr₁.W.a₄ * ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃
        = Pr₁.W.a₄ * (1 - ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃) from by ring]
    rw [show ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃
        = ((ha₃.unit⁻¹ * ha₃.unit : _ˣ) : _) from by
      rw [Units.val_mul, IsUnit.unit_spec]]
    simp
  have ha₆₂ : Pr₂.W.a₆ = 0 := by
    obtain ⟨heq₂, -⟩ := id hMP₂
    exact (WeierstrassCurve.Affine.equation_zero).mp heq₂
  have ha₃u₂ : IsUnit Pr₂.W.a₃ := by rw [ha₃₂]; exact ha₃
  -- the `a₂`-unit (the Tate `μ`, from fibrewise `3P̄ ≠ 0`)
  obtain ⟨heq₂, hMeq₂⟩ := id hMP₂
  have ha₂u : IsUnit Pr₂.W.a₂ :=
    isUnit_a₂_of_marked_origin_four Pr₂ ha₄₂ ha₆₂ ha₃u₂ heq₂ hMeq₂ h3neP
  -- the `a₂ = a₃` scaling
  obtain ⟨b₂, hb₂⟩ := ha₂u.exists_right_inv
  have hb₂u : IsUnit b₂ :=
    isUnit_of_mul_isUnit_right (y := b₂) (by rw [hb₂]; exact isUnit_one)
  have hwu : IsUnit (Pr₂.W.a₃ * b₂) := ha₃u₂.mul hb₂u
  have hwspec : ((hwu.unit : _ˣ) : ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1))
      * Pr₂.W.a₂ = Pr₂.W.a₃ := by
    rw [IsUnit.unit_spec]
    linear_combination Pr₂.W.a₃ * hb₂
  set C₃ : VariableChange ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    ⟨hwu.unit, 0, 0, 0⟩ with hC₃
  set Pr₃ := Pr₂.ofVC C₃ with hPr₃
  have hMP₃ : Pr₃.MarksAt L.1.1.2 0 0 := by
    have h := marksAt_ofVC_vc Pr₂ hMP₂ C₃
    have hx : C₃.vcX 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcX, hC₃]
    have hy : C₃.vcY 0 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcY, hC₃]
    rwa [hx, hy] at h
  have hMQ₃ := marksAt_ofVC_vc Pr₂ hMQ₂ C₃
  -- the scaled chart shape
  have ha₂₃eq : Pr₃.W.a₂ = Pr₃.W.a₃ := by
    show (C₃ • Pr₂.W).a₂ = (C₃ • Pr₂.W).a₃
    exact scale_vc_a₂₃ Pr₂.W hwu.unit hwspec
  have ha₄₃ : Pr₃.W.a₄ = 0 := by
    show (C₃ • Pr₂.W).a₄ = 0
    exact scale_vc_a₄ Pr₂.W hwu.unit ha₄₂
  have ha₆₃ : Pr₃.W.a₆ = 0 := by
    show (C₃ • Pr₂.W).a₆ = 0
    exact scale_vc_a₆ Pr₂.W hwu.unit ha₆₂
  have hBu : IsUnit Pr₃.W.a₂ := by
    show IsUnit ((C₃ • Pr₂.W).a₂)
    exact scale_vc_a₂_isUnit Pr₂.W hwu.unit ha₂u
  -- bridge A: `a₁ = 1`
  have ha₁₃ : Pr₃.W.a₁ = 1 :=
    bridgeA_holds X hR L _ Pr₃ ha₄₃ ha₆₃ ha₂₃eq hMP₃
  -- the `ℰ₄`-form with `B := a₂`
  have hE4 : IsE4Form Pr₃.W Pr₃.W.a₂ :=
    ⟨ha₁₃, rfl, ha₂₃eq.symm, ha₄₃, ha₆₃⟩
  -- bridge Q: the order-4 relation
  have hrel := bridgeQ4_holds X hR L _ Pr₃ Pr₃.W.a₂ hE4 hBu hMP₃ _ _ hMQ₃
  exact ⟨_, hsi, Pr₃, Pr₃.W.a₂, _, _, hE4, hMP₃, hMQ₃, hBu, hrel⟩

/-! ### E4A-12/13/14 — the classifying morphism and the `RepresentableBy` packaging -/

/-- **(E4A-12 kernel)** From `IsE4Form` + ellipticity: `B` and `1 − 16B` are units
(the two factors of the discriminant `Δ = B⁴(1 − 16B)`). Mirror of `e3form_units`. -/
theorem e4form_units {A : Type u} [CommRing A] {W : WeierstrassCurve A} {B : A}
    (hW : IsE4Form W B) (hell : W.IsElliptic) :
    IsUnit B ∧ IsUnit (1 - 16 * B) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hW
  have hΔ : W.Δ = B ^ 4 * (1 - 16 * B) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₂, ha₃, ha₄, ha₆]
    ring
  have hu : IsUnit (B ^ 4 * (1 - 16 * B)) := by
    rw [← hΔ]
    exact (WeierstrassCurve.isElliptic_iff W).mp hell
  exact ⟨(isUnit_pow_iff (n := 4) (by norm_num)).mp (isUnit_of_mul_isUnit_left hu),
    isUnit_of_mul_isUnit_right hu⟩

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 kernel, the ring-level uniqueness certificate ★★)** A variable change
between marked `ℰ₄`-forms is trivial and identifies the parameters — the Tate normal
form (with the order-4 pin `a₁ = 1`) is UNIQUE: `r = t = 0` from the `P`-marking, the
`a₄`-transform gives `s·B₂ = 0` with `B₂` a unit so `s = 0`, the `a₁`-transform then
pins `u = 1`, and the `a₂`-transform plus the `Q`-marking chase identify `B, u, v`.
(Much simpler than E3's `e3_vc_marked` — no flex-cofactor CAS certificate needed;
the ℰ₄-analogue of `toTateNF_unique`.) -/
theorem e4_vc_marked {A : Type u} [CommRing A] {C : VariableChange A}
    {W₁ W₂ : WeierstrassCurve A} {B₁ u₁ v₁ B₂ u₂ v₂ : A}
    (hW₁ : IsE4Form W₁ B₁) (hW₂ : IsE4Form W₂ B₂)
    (hC : C • W₂ = W₁) (hr : C.r = 0) (ht : C.t = 0)
    (hu : (C.u : A) ^ 2 * u₁ = u₂)
    (hv : (C.u : A) ^ 3 * v₁ + C.s * (C.u : A) ^ 2 * u₁ = v₂)
    (hB₂ : IsUnit B₂) :
    C = 1 ∧ B₁ = B₂ ∧ u₁ = u₂ ∧ v₁ = v₂ := by
  obtain ⟨h₁a₁, h₁a₂, h₁a₃, h₁a₄, h₁a₆⟩ := hW₁
  obtain ⟨h₂a₁, h₂a₂, h₂a₃, h₂a₄, h₂a₆⟩ := hW₂
  have hcanc : (C.u : A) * ((C.u⁻¹ : Aˣ) : A) = 1 := C.u.mul_inv
  -- `s = 0` from the `a₄`-transform
  have ha₄ := congrArg WeierstrassCurve.a₄ hC
  rw [variableChange_a₄, hr, ht, h₁a₄, h₂a₄, h₂a₃, h₂a₁] at ha₄
  have hs : C.s = 0 := by
    have h'' : B₂ * C.s = 0 := by
      linear_combination (-(C.u : A) ^ 4) * ha₄
        - B₂ * C.s * (((C.u : A) * ((C.u⁻¹ : Aˣ) : A)) ^ 3
          + ((C.u : A) * ((C.u⁻¹ : Aˣ) : A)) ^ 2
          + (C.u : A) * ((C.u⁻¹ : Aˣ) : A) + 1) * hcanc
    exact (hB₂.mul_right_eq_zero).mp h''
  -- `u = 1` from the `a₁`-transform
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  rw [variableChange_a₁, hs, h₁a₁, h₂a₁] at ha₁
  have hu1 : (C.u : A) = 1 := by
    linear_combination (-(C.u : A)) * ha₁ + hcanc
  have huu1 : C.u = 1 := Units.ext hu1
  -- `B₁ = B₂` from the `a₂`-transform
  have ha₂ := congrArg WeierstrassCurve.a₂ hC
  rw [variableChange_a₂, hr, hs, h₁a₂, h₂a₂, huu1] at ha₂
  have hBeq : B₁ = B₂ := by
    simp only [inv_one, Units.val_one] at ha₂
    linear_combination -ha₂
  refine ⟨?_, hBeq, ?_, ?_⟩
  · ext
    · exact hu1
    · exact hr
    · exact hs
    · exact ht
  · rw [← hu, hu1]; ring
  · rw [← hv, hu1, hs]; ring

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 kernel ★★)** Tate-normal-form uniqueness at the presentation level: two
`ℰ₄`-form witnesses marking the same `P` at `(0,0)` and `Q` at `(uᵢ, vᵢ)` have
`transVC = 1` and equal parameters. Mirror of `e3_witness_transVC_eq_one` (the
`e3_markChase` marking chase is N-agnostic and reused verbatim). -/
theorem e4_witness_transVC_eq_one {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr Qr : LocalPresentation G V}
    {B₁ u₁ v₁ B₂ u₂ v₂ : Γ(S, V.1)}
    (hPrW : IsE4Form Pr.W B₁) (hQrW : IsE4Form Qr.W B₂)
    {σP σQ : S ⟶ G.E} {hσP : σP ≫ G.π = 𝟙 S} {hσQ : σQ ≫ G.π = 𝟙 S}
    (hPrP : Pr.MarksAt hσP 0 0) (hQrP : Qr.MarksAt hσP 0 0)
    (hPrQ : Pr.MarksAt hσQ u₁ v₁) (hQrQ : Qr.MarksAt hσQ u₂ v₂) :
    Pr.transVC Qr = 1 ∧ B₁ = B₂ ∧ u₁ = u₂ ∧ v₁ = v₂ := by
  set C := Pr.transVC Qr with hCdef
  have hPchase := e3_markChase hPrP hQrP
  have hQchase := e3_markChase hPrQ hQrQ
  have hr : C.r = 0 := by
    have h := hPchase.1
    simp only [mul_zero, zero_add] at h
    exact h
  have ht : C.t = 0 := by
    have h := hPchase.2
    simp only [mul_zero, zero_add] at h
    exact h
  have hu : (C.u : Γ(S, V.1)) ^ 2 * u₁ = u₂ := by
    have h := hQchase.1
    rwa [hr, add_zero] at h
  have hv : (C.u : Γ(S, V.1)) ^ 3 * v₁ + C.s * (C.u : Γ(S, V.1)) ^ 2 * u₁ = v₂ := by
    have h := hQchase.2
    rwa [ht, add_zero] at h
  have hB₂u : IsUnit B₂ := (e4form_units hQrW Qr.elliptic).1
  exact e4_vc_marked hPrW hQrW (Pr.transVC_smul Qr) hr ht hu hv hB₂u

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** `IsE4Form` restricts (coefficient-wise) with the restricted
parameter. Mirror of `restrict_W_e3form`. -/
theorem restrict_W_e4form {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} {Pr : LocalPresentation G V} {B : Γ(S, V.1)}
    (hW : IsE4Form Pr.W B) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    IsE4Form (Pr.restrict h).W (Scheme.resLE h B) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hW
  have hmap : ∀ x : Γ(S, V.1),
      (sectionsMapLE (𝟙 S) (show V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)) x =
        Scheme.resLE h x :=
    fun x => congrArg (fun (r : Γ(S, V.1) →+* Γ(S, V'.1)) => r x)
      (sectionsMapLE_id (by simpa using h))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₁ = _
    rw [WeierstrassCurve.map_a₁, ha₁, map_one]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₂ = _
    rw [WeierstrassCurve.map_a₂, ha₂, hmap]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₃ = _
    rw [WeierstrassCurve.map_a₃, ha₃, hmap]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₄ = _
    rw [WeierstrassCurve.map_a₄, ha₄, map_zero]
  · show (Pr.W.map (sectionsMapLE (𝟙 S) _)).a₆ = _
    rw [WeierstrassCurve.map_a₆, ha₆, map_zero]

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** Witness `(B, u, v)`-values agree on common affines: restrict both
witnesses and apply the Tate-normal-form uniqueness. Mirror of
`e3_witness_param_agree` (no `IsUnit 3`-style side condition needed at level 4). -/
theorem e4_witness_param_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4}
    {V₁ V₂ : X.base.affineOpens}
    {Pr₁ : LocalPresentation X.curve.toEllipticCurveGeom V₁}
    {Pr₂ : LocalPresentation X.curve.toEllipticCurveGeom V₂}
    {B₁ u₁ v₁ : Γ(X.base, V₁.1)} {B₂ u₂ v₂ : Γ(X.base, V₂.1)}
    (hW₁ : IsE4Form Pr₁.W B₁) (hW₂ : IsE4Form Pr₂.W B₂)
    (hP₁ : Pr₁.MarksAt L.1.1.2 0 0) (hP₂ : Pr₂.MarksAt L.1.1.2 0 0)
    (hQ₁ : Pr₁.MarksAt L.1.2.2 u₁ v₁) (hQ₂ : Pr₂.MarksAt L.1.2.2 u₂ v₂)
    {W : X.base.affineOpens} (hWV₁ : W.1 ≤ V₁.1) (hWV₂ : W.1 ≤ V₂.1) :
    Scheme.resLE hWV₁ B₁ = Scheme.resLE hWV₂ B₂ ∧
      Scheme.resLE hWV₁ u₁ = Scheme.resLE hWV₂ u₂ ∧
      Scheme.resLE hWV₁ v₁ = Scheme.resLE hWV₂ v₂ := by
  have hP₁' := hP₁.restrict hWV₁
  have hP₂' := hP₂.restrict hWV₂
  rw [map_zero] at hP₁' hP₂'
  have hQ₁' := hQ₁.restrict hWV₁
  have hQ₂' := hQ₂.restrict hWV₂
  have key := e4_witness_transVC_eq_one
    (restrict_W_e4form hW₁ hWV₁) (restrict_W_e4form hW₂ hWV₂)
    hP₁' hP₂' hQ₁' hQ₂'
  exact ⟨key.2.1, key.2.2.1, key.2.2.2⟩

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The glued `B` parameter of an `ℰ₄` datum. Mirror of `e3GammaGlued`. -/
noncomputable def e4BGlued {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (B u v : Γ(X.base, V.1)), IsE4Form Pr.W B →
        Pr.MarksAt L.1.1.2 0 0 → Pr.MarksAt L.1.2.2 u v →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = B } := by
  classical
  choose Vx hxVx Prx Bx ux vx hFx hPx hQx _hBux _hrelx using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => Bx x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (Bx x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (Bx y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact (e4_witness_param_agree (hFx x) (hFx y) (hPx x) (hPx y) (hQx x) (hQx y)
      (r.2.trans inf_le_left) (r.2.trans inf_le_right)).1
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => Bx x) hpair
  refine ⟨hglue.choose, fun V Pr B u v hF hP hQ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) B
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (Bx x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = Bx x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact (e4_witness_param_agree (hFx x) hF (hPx x) hP (hQx x) hQ
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)).1

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The glued `u` parameter of an `ℰ₄` datum. -/
noncomputable def e4UGlued {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (B u v : Γ(X.base, V.1)), IsE4Form Pr.W B →
        Pr.MarksAt L.1.1.2 0 0 → Pr.MarksAt L.1.2.2 u v →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = u } := by
  classical
  choose Vx hxVx Prx Bx ux vx hFx hPx hQx _hBux _hrelx using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => ux x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (ux x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (ux y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact (e4_witness_param_agree (hFx x) (hFx y) (hPx x) (hPx y) (hQx x) (hQx y)
      (r.2.trans inf_le_left) (r.2.trans inf_le_right)).2.1
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => ux x) hpair
  refine ⟨hglue.choose, fun V Pr B u v hF hP hQ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) u
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (ux x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = ux x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact (e4_witness_param_agree (hFx x) hF (hPx x) hP (hQx x) hQ
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)).2.1

open LocalPresentation TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The glued `v` parameter of an `ℰ₄` datum. -/
noncomputable def e4VGlued {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    { g : Γ(X.base, ⊤) //
      ∀ (V : X.base.affineOpens)
        (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
        (B u v : Γ(X.base, V.1)), IsE4Form Pr.W B →
        Pr.MarksAt L.1.1.2 0 0 → Pr.MarksAt L.1.2.2 u v →
        Scheme.resLE (le_top : V.1 ≤ ⊤) g = v } := by
  classical
  choose Vx hxVx Prx Bx ux vx hFx hPx hQx _hBux _hrelx using hD
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun x : X.base => (Vx x).1) :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxVx x⟩
  have hcoverInf : ∀ (V V' : X.base.Opens), V ⊓ V' ≤
      iSup (fun r : {W : X.base.affineOpens // W.1 ≤ V ⊓ V'} => r.1.1) := by
    intro V V' x hx
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W₀, hWaff⟩, hWle⟩, hxW⟩
  have hpair : TopCat.Presheaf.IsCompatible X.base.sheaf.1
      (fun x : X.base => (Vx x).1) (fun x => vx x) := by
    intro x y
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun r : {W : X.base.affineOpens // W.1 ≤ (Vx x).1 ⊓ (Vx y).1} => r.1.1)
      ((Vx x).1 ⊓ (Vx y).1) (fun r => homOfLE r.2) (hcoverInf _ _) _ _ (fun r => ?_)
    show Scheme.resLE r.2 (Scheme.resLE inf_le_left (vx x)) =
      Scheme.resLE r.2 (Scheme.resLE inf_le_right (vx y))
    rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    exact (e4_witness_param_agree (hFx x) (hFx y) (hPx x) (hPx y) (hQx x) (hQx y)
      (r.2.trans inf_le_left) (r.2.trans inf_le_right)).2.2
  have hglue := TopCat.Sheaf.existsUnique_gluing' X.base.sheaf
    (fun x : X.base => (Vx x).1) ⊤ (fun x => homOfLE le_top) hcover
    (fun x => vx x) hpair
  refine ⟨hglue.choose, fun V Pr B u v hF hP hQ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun w : {w : X.base.affineOpens × X.base // w.1.1 ≤ V.1 ⊓ (Vx w.2).1} =>
      w.1.1.1) V.1 (fun w => homOfLE (w.2.trans inf_le_left)) ?_ _ _ (fun w => ?_)
  · intro x hxV
    have hx : x ∈ V.1 ⊓ (Vx x).1 := ⟨hxV, hxVx x⟩
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨⟨W₀, hWaff⟩, x⟩, hWle⟩, hxW⟩
  · obtain ⟨⟨W, x⟩, hWle⟩ := w
    show Scheme.resLE (hWle.trans inf_le_left)
        (Scheme.resLE (le_top : V.1 ≤ ⊤) hglue.choose) =
      Scheme.resLE (hWle.trans inf_le_left) v
    rw [Scheme.resLE_resLE]
    have hg : Scheme.resLE ((hWle.trans inf_le_right).trans
        (le_top : (Vx x).1 ≤ ⊤)) hglue.choose =
        Scheme.resLE (hWle.trans inf_le_right) (vx x) := by
      have h : Scheme.resLE (le_top : (Vx x).1 ≤ ⊤) hglue.choose = vx x :=
        hglue.choose_spec.1 x
      have h' := congrArg (Scheme.resLE (hWle.trans inf_le_right)) h
      rwa [Scheme.resLE_resLE] at h'
    rw [show (hWle.trans inf_le_left).trans (le_top : V.1 ≤ ⊤) =
      ((hWle.trans inf_le_right).trans (le_top : (Vx x).1 ≤ ⊤)) from rfl, hg]
    exact (e4_witness_param_agree (hFx x) hF (hPx x) hP (hQx x) hQ
      (hWle.trans inf_le_right) (hWle.trans inf_le_left)).2.2

open LocalPresentation TopologicalSpace WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The glued parameters satisfy the curve relation
`v² + uv + Bv − u³ − Bu² = 0` (each witness marks `Q` on an `ℰ₄`-form chart).
Mirror of `e3_glued_flex`. -/
theorem e4_glued_curve_rel {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    (e4VGlued X L hD).1 ^ 2 + (e4UGlued X L hD).1 * (e4VGlued X L hD).1
      + (e4BGlued X L hD).1 * (e4VGlued X L hD).1 - (e4UGlued X L hD).1 ^ 3
      - (e4BGlued X L hD).1 * (e4UGlued X L hD).1 ^ 2 = 0 := by
  classical
  have hDc := hD
  choose Vx hxVx Prx Bx ux vx hFx hPx hQx _hBux _hrelx using hDc
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun s : X.base => (Vx s).1) :=
    fun s _ => Opens.mem_iSup.mpr ⟨s, hxVx s⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun s : X.base => (Vx s).1) ⊤ (fun s => homOfLE le_top) hcover _ _ (fun s => ?_)
  have hB := (e4BGlued X L hD).2 (Vx s) (Prx s) (Bx s) (ux s) (vx s)
    (hFx s) (hPx s) (hQx s)
  have hu := (e4UGlued X L hD).2 (Vx s) (Prx s) (Bx s) (ux s) (vx s)
    (hFx s) (hPx s) (hQx s)
  have hv := (e4VGlued X L hD).2 (Vx s) (Prx s) (Bx s) (ux s) (vx s)
    (hFx s) (hPx s) (hQx s)
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hFx s
  have hcvR : vx s ^ 2 + ux s * vx s + Bx s * vx s - ux s ^ 3
      - Bx s * ux s ^ 2 = 0 := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp (hQx s).choose
    rw [ha₁, ha₂, ha₃, ha₄, ha₆] at h
    linear_combination h
  show Scheme.resLE (le_top : (Vx s).1 ≤ ⊤) _ = Scheme.resLE le_top 0
  rw [map_zero, map_sub, map_sub, map_add, map_add, map_pow, map_pow, map_mul,
    map_mul, map_mul, map_pow, hB, hu, hv]
  linear_combination hcvR

open LocalPresentation TopologicalSpace WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The glued parameters satisfy the order-4 relation `e4Rel(B, u) = 0`
(each witness carries it). Mirror of `e3_glued_flex`. -/
theorem e4_glued_order_rel {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    2 * (e4UGlued X L hD).1 ^ 4 + (e4UGlued X L hD).1 ^ 3
      + 3 * (e4BGlued X L hD).1 * (e4UGlued X L hD).1 ^ 2
      + 4 * (e4BGlued X L hD).1 ^ 2 * (e4UGlued X L hD).1
      + 2 * (e4BGlued X L hD).1 ^ 3 = 0 := by
  classical
  have hDc := hD
  choose Vx hxVx Prx Bx ux vx hFx hPx hQx _hBux hrelx using hDc
  have hcover : (⊤ : X.base.Opens) ≤ iSup (fun s : X.base => (Vx s).1) :=
    fun s _ => Opens.mem_iSup.mpr ⟨s, hxVx s⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
    (fun s : X.base => (Vx s).1) ⊤ (fun s => homOfLE le_top) hcover _ _ (fun s => ?_)
  have hB := (e4BGlued X L hD).2 (Vx s) (Prx s) (Bx s) (ux s) (vx s)
    (hFx s) (hPx s) (hQx s)
  have hu := (e4UGlued X L hD).2 (Vx s) (Prx s) (Bx s) (ux s) (vx s)
    (hFx s) (hPx s) (hQx s)
  show Scheme.resLE (le_top : (Vx s).1 ≤ ⊤) _ = Scheme.resLE le_top 0
  simp only [map_zero, map_add, map_mul, map_pow, map_ofNat]
  rw [hB, hu]
  linear_combination hrelx s

open LocalPresentation TopologicalSpace WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** The localized element `B(1 − 16B)` at the glued parameters is a
global unit (germwise: the witness `IsUnit B` plus `e4form_units`). Mirror of
`e3Delta_glued_isUnit`. -/
theorem e4Delta_glued_isUnit {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    IsUnit ((e4BGlued X L hD).1 * (1 - 16 * (e4BGlued X L hD).1)) := by
  set gB := (e4BGlued X L hD).1 with hgB
  apply X.base.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨V, hxV, Pr, B, u, v, hF, hP, hQ, hBu, hrel⟩ := hD x
  set D := gB * (1 - 16 * gB) with hDdef
  have hgerm : X.base.presheaf.germ ⊤ x trivial D =
      X.base.presheaf.germ V.1 x hxV (Scheme.resLE (le_top : V.1 ≤ ⊤) D) := by
    rw [show Scheme.resLE (le_top : V.1 ≤ ⊤) D =
      (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom D from rfl]
    exact (X.base.presheaf.germ_res_apply (homOfLE le_top) x hxV _).symm
  rw [hgerm]
  refine IsUnit.map _ ?_
  have hB := (e4BGlued X L hD).2 V Pr B u v hF hP hQ
  have hres : Scheme.resLE (le_top : V.1 ≤ ⊤) D = B * (1 - 16 * B) := by
    rw [hDdef]
    simp only [map_mul, map_sub, map_one, map_ofNat]
    rw [hgB, hB]
  rw [hres]
  exact hBu.mul (e4form_units hF Pr.elliptic).2

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** The base ring map of an `ℰ₄` datum:
`MvPolynomial (Fin 3) R → Γ(X.base, ⊤)`, `X 0 ↦ BGlued, X 1 ↦ uGlued, X 2 ↦ vGlued`.
Mirror of `e3BaseMap`. -/
noncomputable def e4BaseMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    MvPolynomial (Fin 3) R →+* Γ(X.base, ⊤) :=
  eval₂Hom X.baseRingHom
    ![(e4BGlued X L hD).1, (e4UGlued X L hD).1, (e4VGlued X L hD).1]

open LocalPresentation MvPolynomial in
/-- The base map kills the curve relation. -/
theorem e4BaseMap_curveRel {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    e4BaseMap X L hD (e4CurveRel R) = 0 := by
  rw [e4BaseMap, show e4CurveRel R = MvPolynomial.X 2 ^ 2
      + MvPolynomial.X 1 * MvPolynomial.X 2 + MvPolynomial.X 0 * MvPolynomial.X 2
      - MvPolynomial.X 1 ^ 3 - MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 from rfl]
  simp only [map_sub, map_add, map_mul, map_pow, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination e4_glued_curve_rel X L hD

open LocalPresentation MvPolynomial in
/-- The base map kills the order-4 relation. -/
theorem e4BaseMap_orderRel {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    e4BaseMap X L hD (e4OrderRel R) = 0 := by
  rw [e4BaseMap, show e4OrderRel R = 2 * MvPolynomial.X 1 ^ 4 + MvPolynomial.X 1 ^ 3
      + 3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
      + 4 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1
      + 2 * MvPolynomial.X 0 ^ 3 from rfl]
  simp only [map_add, map_mul, map_pow, map_ofNat, eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linear_combination e4_glued_order_rel X L hD

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- The descended map on the quotient ring `R[B,u,v]/(curve, e4Rel)`. Mirror of
`e3QuotientMap` (two-generator span membership via `Ideal.mem_span_pair`). -/
noncomputable def e4QuotientMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    E4Quotient R →+* Γ(X.base, ⊤) :=
  Ideal.Quotient.lift _ (e4BaseMap X L hD) (by
    intro a ha
    rw [show ({e4CurveRel R, e4OrderRel R} : Set (MvPolynomial (Fin 3) R))
      = {e4CurveRel R, e4OrderRel R} from rfl, Ideal.mem_span_pair] at ha
    obtain ⟨c₁, c₂, rfl⟩ := ha
    rw [map_add, map_mul, map_mul, e4BaseMap_curveRel, e4BaseMap_orderRel,
      mul_zero, mul_zero, add_zero])

open LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** The classifying ring map of an `ℰ₄` datum:
`E4ModuliRing R → Γ(X.base, ⊤)`. Mirror of `e3ClassifyingRingHom`. -/
noncomputable def e4ClassifyingRingHom {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    E4ModuliRing R →+* Γ(X.base, ⊤) := by
  refine IsLocalization.Away.lift (e4Delta R) (g := e4QuotientMap X L hD) ?_
  rw [show e4QuotientMap X L hD (e4Delta R) =
      (e4BGlued X L hD).1 * (1 - 16 * (e4BGlued X L hD).1) from by
    show (e4QuotientMap X L hD).comp (Ideal.Quotient.mk _)
        (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0)) = _
    show e4BaseMap X L hD (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0)) = _
    rw [e4BaseMap]
    simp only [map_mul, map_sub, map_one, map_ofNat, eval₂Hom_X',
      Matrix.cons_val_zero]]
  exact e4Delta_glued_isUnit X L hD

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
/-- **(E4A-12)** The classifying morphism
`X.base ⟶ ℰ₄ = Spec E4ModuliRing`. Mirror of `e3ClassifyingMap`. -/
noncomputable def e4ClassifyingMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    X.base ⟶ Spec (CommRingCat.of (E4ModuliRing R)) :=
  X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD))

open AlgebraicGeometry CategoryTheory Scheme MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The classifying algebra restricts to the structure algebra on
`R`-scalars. Mirror of `e3ClassifyingRingHom_algebraMap`. -/
theorem e4ClassifyingRingHom_algebraMap {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) (r : R) :
    e4ClassifyingRingHom X L hD (algebraMap R (E4ModuliRing R) r) =
      X.baseRingHom r := by
  have h1 : algebraMap R (E4ModuliRing R) r =
      algebraMap (E4Quotient R) (E4ModuliRing R)
        (Ideal.Quotient.mk _ (MvPolynomial.C r)) := by
    rw [IsScalarTower.algebraMap_apply R (E4Quotient R) (E4ModuliRing R),
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 3) R) (E4Quotient R)]
    rfl
  rw [h1, e4ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e4QuotientMap X L hD (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
  show e4BaseMap X L hD (MvPolynomial.C r) = _
  rw [e4BaseMap, eval₂Hom_C]

open LocalPresentation MvPolynomial in
/-- The classifying map sends the universal `B` to `BGlued`. -/
theorem e4ClassifyingRingHom_B {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    e4ClassifyingRingHom X L hD (e4B R) = (e4BGlued X L hD).1 := by
  rw [e4B, e4ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e4QuotientMap X L hD (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = _
  show e4BaseMap X L hD (MvPolynomial.X 0) = _
  rw [e4BaseMap, eval₂Hom_X']
  rfl

open LocalPresentation MvPolynomial in
/-- The classifying map sends the universal `u` to `uGlued`. -/
theorem e4ClassifyingRingHom_U {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    e4ClassifyingRingHom X L hD (e4U R) = (e4UGlued X L hD).1 := by
  rw [e4U, e4ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e4QuotientMap X L hD (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = _
  show e4BaseMap X L hD (MvPolynomial.X 1) = _
  rw [e4BaseMap, eval₂Hom_X']
  rfl

open LocalPresentation MvPolynomial in
/-- The classifying map sends the universal `v` to `vGlued`. -/
theorem e4ClassifyingRingHom_V {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) :
    e4ClassifyingRingHom X L hD (e4V R) = (e4VGlued X L hD).1 := by
  rw [e4V, e4ClassifyingRingHom, IsLocalization.Away.lift_eq]
  show e4QuotientMap X L hD (Ideal.Quotient.mk _ (MvPolynomial.X 2)) = _
  show e4BaseMap X L hD (MvPolynomial.X 2) = _
  rw [e4BaseMap, eval₂Hom_X']
  rfl

open LocalPresentation MvPolynomial WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★, the coefficient match)** Specializing the universal `ℰ₄` curve along
the classifying map, restricted to a witness affine, recovers the witness chart curve.
Mirror of `universalE3_map_classifying`. -/
theorem universalE4_map_classifying {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) (hD : IsE4Datum X L) (V : X.base.affineOpens)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V) (B u v : Γ(X.base, V.1))
    (hF : IsE4Form Pr.W B) (hP : Pr.MarksAt L.1.1.2 0 0)
    (hQ : Pr.MarksAt L.1.2.2 u v) :
    (universalE4 R).map
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)) = Pr.W := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := hF
  have hB := (e4BGlued X L hD).2 V Pr B u v ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ hP hQ
  have hcB : ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (e4B R) = B := by
    rw [RingHom.comp_apply, e4ClassifyingRingHom_B]
    exact hB
  ext
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (universalE4 R).a₁ = _
    rw [show (universalE4 R).a₁ = 1 from rfl, map_one, ha₁]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (universalE4 R).a₂ = _
    rw [show (universalE4 R).a₂ = e4B R from rfl, hcB, ha₂]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (universalE4 R).a₃ = _
    rw [show (universalE4 R).a₃ = e4B R from rfl, hcB, ha₃]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (universalE4 R).a₄ = _
    rw [show (universalE4 R).a₄ = 0 from rfl, map_zero, ha₄]
  · show ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) (universalE4 R).a₆ = _
    rw [show (universalE4 R).a₆ = 0 from rfl, map_zero, ha₆]

/-- **(E4A-12)** A bundled `ℰ₄` witness. Mirror of `E3Witness`. -/
structure E4Witness {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 4) where
  V : X.base.affineOpens
  Pr : LocalPresentation X.curve.toEllipticCurveGeom V
  B : Γ(X.base, V.1)
  u : Γ(X.base, V.1)
  v : Γ(X.base, V.1)
  hF : IsE4Form Pr.W B
  hP : Pr.MarksAt L.1.1.2 0 0
  hQ : Pr.MarksAt L.1.2.2 u v

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The per-witness classifying piece. Mirror of `e3Piece`. -/
noncomputable def e4Piece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (w : E4Witness X L) :
    (pullback X.curve.toEllipticCurveGeom.π w.V.1.ι : Scheme.{u}) ⟶
      projModel (universalE4 R) :=
  w.Pr.e.hom ≫
    eqToHom (congrArg projModel
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v w.hF w.hP w.hQ).symm) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)) (universalE4 R)

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** Witnesses restrict. Mirror of `E3Witness.restrict`. -/
noncomputable def E4Witness.restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (w : E4Witness X L)
    {W : X.base.affineOpens} (h : W.1 ≤ w.V.1) : E4Witness X L where
  V := W
  Pr := w.Pr.restrict h
  B := Scheme.resLE h w.B
  u := Scheme.resLE h w.u
  v := Scheme.resLE h w.v
  hF := restrict_W_e4form w.hF h
  hP := by have := w.hP.restrict h; rwa [map_zero] at this
  hQ := w.hQ.restrict h

open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The pieces are compatible with restriction (Tate-normal-form
uniqueness). Mirror of `e3Piece_restrict`. -/
theorem e4Piece_restrict {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (w w' : E4Witness X L) (h : w'.V.1 ≤ w.V.1) :
    restrictTheta h ≫ e4Piece hD w = e4Piece hD w' := by
  have hPres := w.hP.restrict h; rw [map_zero] at hPres
  have hQres := w.hQ.restrict h
  have hVC : w'.Pr.transVC (w.Pr.restrict h) = 1 :=
    (e4_witness_transVC_eq_one w'.hF (restrict_W_e4form w.hF h)
      w'.hP hPres w'.hQ hQres).1
  have hWeq : (w.Pr.restrict h).W = w'.Pr.W := by
    have := w'.Pr.transVC_smul (w.Pr.restrict h)
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : (w.Pr.restrict h).e.hom =
      w'.Pr.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom =
        eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (w'.Pr.pointedIso (w.Pr.restrict h)).hom =
        w'.Pr.e.inv ≫ (w.Pr.restrict h).e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hσ : ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) =
    (sectionsMapLE (𝟙 X.base) h).comp
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)) := by
    rw [sectionsMapLE_id]
    show ((X.base.presheaf.map (homOfLE (le_top : w'.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD) =
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
        (X.base.presheaf.map (homOfLE (show w'.V.1 ≤ w.V.1 by
          simpa using h)).op)).hom).comp
        (e4ClassifyingRingHom X L hD)
    rw [← Functor.map_comp, ← op_comp]
    rfl
  rw [e4Piece, e4Piece, ← Category.assoc, ← restrict_e_baseChange, hE]
  simp only [Category.assoc]
  rw [cancel_epi (w'.Pr.e.hom)]
  rw [projModelBaseChange_congr'' (sectionsMapLE (𝟙 X.base) h)
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  rw [← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ.symm (universalE4 R),
    ← Category.assoc, eqToHom_trans]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E4A-12)** The witness cover of the total space. Mirror of `e3WitnessCover`. -/
noncomputable def e4WitnessCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    X.curve.toEllipticCurveGeom.E.OpenCover :=
  Scheme.Cover.mkOfCovers (E4Witness X L)
    (fun w => pullback X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun w => pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, B, u, v, hF, hP, hQ, _hBu, _hrel⟩ := hD
        (X.curve.toEllipticCurveGeom.π.base x)
      have hx : x ∈ Set.range (pullback.fst X.curve.toEllipticCurveGeom.π
          V.1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι,
          SetLike.mem_coe]
        exact hxV
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨V, Pr, B, u, v, hF, hP, hQ⟩, y, hy⟩)

open CategoryTheory Limits in
@[simp] theorem e4WitnessCover_f {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (w : E4Witness X L) :
    (e4WitnessCover hD).f w =
      pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι := rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The piece is witness-independent at a fixed affine. Mirror of
`e3Piece_congr`. -/
theorem e4Piece_congr {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (w₁ w₂ : E4Witness X L) (hV : w₁.V = w₂.V) :
    e4Piece hD w₁ = eqToHom (by rw [hV]) ≫ e4Piece hD w₂ := by
  obtain ⟨V₁, Pr₁, B₁, u₁, v₁, hF₁, hP₁, hQ₁⟩ := w₁
  obtain ⟨V₂, Pr₂, B₂, u₂, v₂, hF₂, hP₂, hQ₂⟩ := w₂
  obtain rfl : V₁ = V₂ := hV
  rw [eqToHom_refl, Category.id_comp]
  have hVC : Pr₂.transVC Pr₁ = 1 :=
    (e4_witness_transVC_eq_one hF₂ hF₁ hP₂ hP₁ hQ₂ hQ₁).1
  have hWeq : Pr₁.W = Pr₂.W := by
    have := Pr₂.transVC_smul Pr₁
    rwa [hVC, one_smul] at this
  have hIso := pointedIso_hom_of_transVC_eq_one hVC
  have hE : Pr₁.e.hom = Pr₂.e.hom ≫ eqToHom (congrArg projModel hWeq.symm) := by
    have h1 : Pr₂.e.inv ≫ Pr₁.e.hom = eqToHom (congrArg projModel hWeq.symm) := by
      have h0 := hIso
      rw [show (Pr₂.pointedIso Pr₁).hom = Pr₂.e.inv ≫ Pr₁.e.hom from rfl] at h0
      exact h0
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  show Pr₁.e.hom ≫ _ ≫ _ = Pr₂.e.hom ≫ _ ≫ _
  rw [hE]
  simp only [Category.assoc, eqToHom_trans_assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
private theorem e4Piece_agree {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (p q : E4Witness X L) :
    pullback.fst ((e4WitnessCover hD).f p) ((e4WitnessCover hD).f q) ≫
        e4Piece hD p =
      pullback.snd ((e4WitnessCover hD).f p) ((e4WitnessCover hD).f q) ≫
        e4Piece hD q := by
  haveI hOIp : IsOpenImmersion ((e4WitnessCover hD).f p) := by
    rw [e4WitnessCover_f]; infer_instance
  haveI hOIq : IsOpenImmersion ((e4WitnessCover hD).f q) := by
    rw [e4WitnessCover_f]; infer_instance
  have hchoice : ∀ z : (pullback ((e4WitnessCover hD).f p)
      ((e4WitnessCover hD).f q) : Scheme.{u}),
      ∃ (W : X.base.affineOpens), W.1 ≤ p.V.1 ⊓ q.V.1 ∧
        X.curve.toEllipticCurveGeom.π.base
          ((pullback.fst ((e4WitnessCover hD).f p)
            ((e4WitnessCover hD).f q) ≫
            (e4WitnessCover hD).f p).base z) ∈ W.1 := by
    intro z
    have hsp : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫
          (e4WitnessCover hD).f p).base z) ∈ p.V.1 := by
      have hr : ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π p.V.1.ι).base :=
        ⟨(pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    have hcond : (pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p).base z =
      (pullback.snd ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f q).base z := by
      have := congrArg (fun t => t.base z) (pullback.condition
        (f := (e4WitnessCover hD).f p) (g := (e4WitnessCover hD).f q))
      simpa using this
    have hsq : X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫
          (e4WitnessCover hD).f p).base z) ∈ q.V.1 := by
      have hr : ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p).base z) ∈
          Set.range (pullback.fst X.curve.toEllipticCurveGeom.π q.V.1.ι).base := by
        rw [hcond]
        exact ⟨(pullback.snd ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q)).base z, rfl⟩
      rw [Scheme.Pullback.range_fst] at hr
      simpa [Scheme.Opens.range_ι] using hr
    obtain ⟨W₀, hWaff, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
      (show X.curve.toEllipticCurveGeom.π.base
        ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫
          (e4WitnessCover hD).f p).base z) ∈ p.V.1 ⊓ q.V.1 from ⟨hsp, hsq⟩)
    exact ⟨⟨W₀, hWaff⟩, hWle, hxW⟩
  choose W hWle hmem using hchoice
  have hfsteq : ∀ z, (restrictTheta (G := X.curve.toEllipticCurveGeom)
      ((hWle z).trans inf_le_left) ≫ (e4WitnessCover hD).f p) =
    restrictTheta ((hWle z).trans inf_le_right) ≫ (e4WitnessCover hD).f q := by
    intro z
    rw [e4WitnessCover_f, e4WitnessCover_f, restrictTheta_fst,
      restrictTheta_fst]
  let hω : ∀ z, (pullback X.curve.toEllipticCurveGeom.π (W z).1.ι : Scheme.{u}) ⟶
      pullback ((e4WitnessCover hD).f p) ((e4WitnessCover hD).f q) :=
    fun z => pullback.lift (restrictTheta ((hWle z).trans inf_le_left))
      (restrictTheta ((hWle z).trans inf_le_right)) (hfsteq z)
  have hcomp : ∀ z, hω z ≫ pullback.fst ((e4WitnessCover hD).f p)
      ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p =
    pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι := by
    intro z
    rw [← Category.assoc, show hω z ≫ pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      e4WitnessCover_f, restrictTheta_fst]
  have hmapOI : ∀ z, IsOpenImmersion (hω z) := by
    intro z
    haveI : IsOpenImmersion (pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p) :=
      inferInstance
    haveI : IsOpenImmersion (hω z ≫ pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p) := by
      rw [hcomp z]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst ((e4WitnessCover hD).f p)
      ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p)
  refine (Scheme.Cover.mkOfCovers
    (X := (pullback ((e4WitnessCover hD).f p)
      ((e4WitnessCover hD).f q) : Scheme.{u}))
    (pullback ((e4WitnessCover hD).f p) ((e4WitnessCover hD).f q) :
      Scheme.{u})
    (fun z => pullback X.curve.toEllipticCurveGeom.π (W z).1.ι)
    (fun z => hω z) ?_ (fun z => hmapOI z)).hom_ext _ _ (fun z => ?_)
  · intro z
    have hz : (pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p).base z ∈
      Set.range (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base := by
      rw [Scheme.Pullback.range_fst]
      simpa [Scheme.Opens.range_ι] using hmem z
    obtain ⟨w, hw⟩ := hz
    refine ⟨z, w, ?_⟩
    have hinj : Function.Injective
        ((pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫ (e4WitnessCover hD).f p).base) :=
      (pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) ≫
        (e4WitnessCover hD).f p).isOpenEmbedding.injective
    apply hinj
    calc (pullback.fst ((e4WitnessCover hD).f p)
          ((e4WitnessCover hD).f q) ≫
          (e4WitnessCover hD).f p).base ((hω z).base w)
        = (hω z ≫ pullback.fst ((e4WitnessCover hD).f p)
            ((e4WitnessCover hD).f q) ≫
            (e4WitnessCover hD).f p).base w := rfl
      _ = (pullback.fst X.curve.toEllipticCurveGeom.π (W z).1.ι).base w := by
          rw [hcomp z]
      _ = _ := hw
  · show hω z ≫ pullback.fst _ _ ≫ e4Piece hD p =
      hω z ≫ pullback.snd _ _ ≫ e4Piece hD q
    rw [← Category.assoc, show hω z ≫ pullback.fst ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_left) from pullback.lift_fst _ _ _,
      ← Category.assoc, show hω z ≫ pullback.snd ((e4WitnessCover hD).f p)
        ((e4WitnessCover hD).f q) =
      restrictTheta ((hWle z).trans inf_le_right) from pullback.lift_snd _ _ _,
      e4Piece_restrict hD p (p.restrict ((hWle z).trans inf_le_left))
        ((hWle z).trans inf_le_left),
      e4Piece_restrict hD q (q.restrict ((hWle z).trans inf_le_right))
        ((hWle z).trans inf_le_right)]
    rw [e4Piece_congr hD (p.restrict ((hWle z).trans inf_le_left))
      (q.restrict ((hWle z).trans inf_le_right)) rfl, eqToHom_refl,
      Category.id_comp]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E4A-12)** The classifying morphism upstairs: the witness-glued map from the
total space to the universal `ℰ₄` model. Mirror of `e3Top`. -/
noncomputable def e4Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    X.curve.toEllipticCurveGeom.E ⟶ projModel (universalE4 R) :=
  (e4WitnessCover hD).glueMorphisms
    (fun w => e4Piece hD w)
    (e4Piece_agree hD)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
@[reassoc]
theorem e4Top_piece {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (w : E4Witness X L) :
    (e4WitnessCover hD).f w ≫ e4Top hD = e4Piece hD w :=
  (e4WitnessCover hD).ι_glueMorphisms _ _ w

set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The piece map lies over the restricted classifying map. Mirror of
`e3Piece_π`. -/
theorem e4Piece_π {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (w : E4Witness X L) :
    e4Piece hD w ≫ projModelπ (universalE4 R) =
      pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ w.V.2.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (e4ClassifyingRingHom X L hD))) := by
  have hw : projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)) (universalE4 R) ≫
      projModelπ (universalE4 R) =
    projModelπ ((universalE4 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) ≫
      Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))) := by
    letI : Algebra (E4ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))).toAlgebra
    exact (isPullback_projModelBaseChange (universalE4 R)).w
  rw [e4Piece, Category.assoc, Category.assoc, hw,
    reassoc_of% projModelπ_congr
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm]
  rw [← Category.assoc, w.Pr.compat_π, Category.assoc]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** The glued comparison lies over the classifying map. Mirror of
`e3Top_π_w`. -/
theorem e4Top_π_w {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    e4Top hD ≫ projModelπ (universalE4 R) =
      X.curve.toEllipticCurveGeom.π ≫ e4ClassifyingMap X L hD := by
  refine (e4WitnessCover hD).hom_ext _ _ (fun w => ?_)
  rw [← Category.assoc, e4Top_piece, e4Piece_π]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) =
    w.V.1.ι ≫ e4ClassifyingMap X L hD from by
    rw [Category.assoc]; rfl]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, e4WitnessCover_f]

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
/-- **(E4A-12)** The witness cover of the base. Mirror of `e3BaseCover`. -/
noncomputable def e4BaseCover {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) : X.base.OpenCover :=
  Scheme.Cover.mkOfCovers
    (E4Witness X L)
    (fun w => w.V.1.toScheme)
    (fun w => w.V.1.ι)
    (fun x => by
      obtain ⟨V, hxV, Pr, B, u, v, hF, hP, hQ, _hBu, _hrel⟩ := hD x
      exact ⟨⟨V, Pr, B, u, v, hF, hP, hQ⟩, ⟨x, hxV⟩, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★)** The glued comparison respects the zero sections. Mirror of
`e3Top_zero`. -/
theorem e4Top_zero {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    X.curve.toEllipticCurveGeom.zero ≫ e4Top hD =
      e4ClassifyingMap X L hD ≫ projModelZero (universalE4 R) := by
  refine (e4BaseCover hD).hom_ext _ _ (fun w => ?_)
  have hzfac : w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero =
      pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
        (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
          Category.comp_id, Category.id_comp]) ≫
      (e4WitnessCover hD).f w := by
    rw [e4WitnessCover_f, pullback.lift_fst]
  rw [show (e4BaseCover hD).f w = w.V.1.ι from rfl, ← Category.assoc, hzfac,
    Category.assoc, e4Top_piece]
  have hz := w.Pr.compat_zero
  have hlift : pullback.lift (w.V.1.ι ≫ X.curve.toEllipticCurveGeom.zero) (𝟙 _)
      (by rw [Category.assoc, X.curve.toEllipticCurveGeom.zero_π,
        Category.comp_id, Category.id_comp]) ≫ w.Pr.e.hom =
    w.V.2.isoSpec.hom ≫ projModelZero w.Pr.W := by
    rw [← Iso.inv_comp_eq, ← Category.assoc]
    exact hz
  rw [e4Piece, ← Category.assoc, hlift]
  rw [Category.assoc,
    show projModelZero w.Pr.W = projModelZero ((universalE4 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))) ≫
      eqToHom (congrArg projModel
        (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
          w.hF w.hP w.hQ)) from
      projModelZero_congr
        (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
          w.hF w.hP w.hQ).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hbc : projModelZero ((universalE4 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD)) (universalE4 R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) ≫
      projModelZero (universalE4 R) := by
    letI : Algebra (E4ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))).toAlgebra
    exact projModelZero_baseChange (universalE4 R)
  rw [hbc]
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hsplit,
    show w.V.2.isoSpec.hom = w.V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _]
  rw [show w.V.1.toSpecΓ ≫
      Spec.map (X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) =
    (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) from by
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]]
  rw [show (w.V.1.ι ≫ X.base.toSpecΓ) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) =
    w.V.1.ι ≫ e4ClassifyingMap X L hD from by rw [Category.assoc]; rfl]
  simp only [Category.assoc]

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The classifying map lies over `Spec R`. Mirror of
`e3ClassifyingMap_structMap`. -/
theorem e4ClassifyingMap_structMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    e4ClassifyingMap X L hD ≫ (universalE4Obj R).structMap = X.structMap := by
  show (X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (e4ClassifyingRingHom X L hD))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (E4ModuliRing R))) = X.structMap
  rw [Category.assoc, ← Spec.map_comp,
    show CommRingCat.ofHom (algebraMap R (E4ModuliRing R)) ≫
        CommRingCat.ofHom (e4ClassifyingRingHom X L hD) =
      CommRingCat.ofHom (X.baseRingHom) from by
      ext r
      exact e4ClassifyingRingHom_algebraMap X L hD r,
    show CommRingCat.ofHom X.baseRingHom =
      (Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop from rfl,
    Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom R,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The classifying map restricted to a witness affine. Mirror of
`restrict_e3ClassifyingMap`. -/
theorem restrict_e4ClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (V : X.base.affineOpens) :
    V.1.ι ≫ e4ClassifyingMap X L hD =
      V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))) := by
  have hsplit : Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) =
    Spec.map (X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op) ≫
      Spec.map (CommRingCat.ofHom (e4ClassifyingRingHom X L hD)) := by
    rw [← Spec.map_comp]
    rfl
  rw [hsplit, show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
    ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12, rt2c helper)** The `sectionsMapLE ∘ ΓSpecIso.inv` compatibility for the
classifying map. Mirror of `sectionsMapLE_e3ClassifyingMap`. -/
theorem sectionsMapLE_e4ClassifyingMap {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (V : X.base.affineOpens) (hTop : V.1 ≤ e4ClassifyingMap X L hD ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens)) :
    (sectionsMapLE (e4ClassifyingMap X L hD) hTop).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom) =
    ((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD) := by
  have hLm : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((sectionsMapLE (e4ClassifyingMap X L hD) hTop).comp
        ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom))) =
    V.1.ι ≫ e4ClassifyingMap X L hD := by
    rw [show CommRingCat.ofHom
        ((sectionsMapLE (e4ClassifyingMap X L hD) hTop).comp
          ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom)) =
      (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
        (e4ClassifyingMap X L hD).appLE ⊤ V.1 hTop from rfl,
      Spec.map_comp,
      show V.2.isoSpec.hom = V.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
      ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc]
    rw [show (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv =
      (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).ι from by
      rw [Scheme.Opens.toSpecΓ_top, Category.assoc, ← SpecMap_ΓSpecIso_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]]
    rw [Scheme.Hom.resLE_comp_ι]
  have hRm : V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) =
    V.1.ι ≫ e4ClassifyingMap X L hD :=
    (restrict_e4ClassifyingMap hD V).symm
  have hSpec := hLm.trans hRm.symm
  rw [cancel_epi] at hSpec
  have hofHom := Spec.map_injective hSpec
  exact congrArg CommRingCat.Hom.hom hofHom

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12)** The per-witness classifying square is cartesian. Mirror of
`e3Piece_isPullback`. -/
theorem e4Piece_isPullback {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (w : E4Witness X L) :
    IsPullback (e4Piece hD w)
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ (universalE4 R))
      (w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD)))) := by
  have hleft : IsPullback
      (w.Pr.e.hom ≫ eqToHom (congrArg projModel
        (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
          w.hF w.hP w.hQ).symm))
      (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι)
      (projModelπ ((universalE4 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))))
      w.V.2.isoSpec.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.assoc, projModelπ_congr
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm]
    exact w.Pr.compat_π
  have hright : IsPullback
      (projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD)) (universalE4 R))
      (projModelπ ((universalE4 R).map
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))))
      (projModelπ (universalE4 R))
      (Spec.map (CommRingCat.ofHom
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD)))) := by
    letI : Algebra (E4ModuliRing R) Γ(X.base, w.V.1) :=
      ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))).toAlgebra
    exact isPullback_projModelBaseChange (universalE4 R)
  have hpaste := hleft.paste_horiz hright
  rw [show (w.Pr.e.hom ≫ eqToHom (congrArg projModel
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm)) ≫
    projModelBaseChange
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)) (universalE4 R) =
    e4Piece hD w from by
    rw [e4Piece, Category.assoc]] at hpaste
  exact hpaste

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-12 ★★)** The classifying square is cartesian: `X` is the pullback of the
universal `ℰ₄` curve along the classifying map. Mirror of `isPullback_e3Top`. -/
theorem isPullback_e4Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) :
    IsPullback (e4Top hD) X.curve.toEllipticCurveGeom.π
      (projModelπ (universalE4 R)) (e4ClassifyingMap X L hD) := by
  refine (isPullback_of_iSup_eq_top (f := X.curve.toEllipticCurveGeom.π)
    (g := e4Top hD) (h := e4ClassifyingMap X L hD)
    (k := projModelπ (universalE4 R))
    (e4Top_π_w hD).symm
    (ι := E4Witness X L)
    (fun w => w.V.1) ?_ (fun w => ?_)).flip
  · rw [eq_top_iff]
    intro x _
    obtain ⟨V, hxV, Pr, B, u, v, hF, hP, hQ, _hBu, _hrel⟩ := hD x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨V, Pr, B, u, v, hF, hP, hQ⟩, hxV⟩
  · set fpre := (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι with hfpre
    have hcomm : fpre ≫ X.curve.toEllipticCurveGeom.π =
        (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) ≫ w.V.1.ι :=
      (morphismRestrict_ι X.curve.toEllipticCurveGeom.π w.V.1).symm
    set m := pullback.lift fpre (X.curve.toEllipticCurveGeom.π ∣_ w.V.1) hcomm
      with hm
    have hm₁ : m ≫ pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι = fpre :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι =
        X.curve.toEllipticCurveGeom.π ∣_ w.V.1 :=
      pullback.lift_snd _ _ _
    have hmiso : IsIso m := by
      refine (isPullback_morphismRestrict X.curve.toEllipticCurveGeom.π
        w.V.1).flip.isIso_of_isPullback
        (IsPullback.of_hasPullback X.curve.toEllipticCurveGeom.π w.V.1.ι) m hm₁ hm₂
    have hmsq : IsPullback m (X.curve.toEllipticCurveGeom.π ∣_ w.V.1)
        (pullback.snd X.curve.toEllipticCurveGeom.π w.V.1.ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hm₂, Category.comp_id]⟩
    have hp := hmsq.paste_horiz (e4Piece_isPullback hD w)
    rw [show m ≫ e4Piece hD w =
        (X.curve.toEllipticCurveGeom.π ⁻¹ᵁ w.V.1).ι ≫ e4Top hD from by
        rw [← e4Top_piece hD w, e4WitnessCover_f, ← Category.assoc,
          hm₁],
      show (𝟙 _) ≫ w.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
          (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
            (e4ClassifyingRingHom X L hD))) =
        w.V.1.ι ≫ e4ClassifyingMap X L hD from by
        rw [Category.id_comp, ← restrict_e4ClassifyingMap]] at hp
    exact hp.flip

open AlgebraicGeometry CategoryTheory Scheme in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- **(E4A-12 ★★)** The classifying morphism of an `ℰ₄`-datum in `Ell/R`: the
KM 2.2.10–11-method universal property at level 4, forward direction. Mirror of
`e3ClassifyingEllHom`. (The `h2`-hypothesis is not consumed — the Tate-normal-form
uniqueness needs no invertibility — but is kept for the board-protected signature.) -/
def e4ClassifyingEllHom {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) : X ⟶ universalE4Obj R where
  baseHom := e4ClassifyingMap X L hD
  base_w := e4ClassifyingMap_structMap hD
  top := e4Top hD
  isPullback := isPullback_e4Top hD
  zero_w := e4Top_zero hD

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt1)** The marking downstairs: a marked section composed with the glued
comparison is the classifying map followed by the universal marked point. Mirror of
`section_comp_e3Top`. -/
theorem section_comp_e4Top {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    {σ : X.base ⟶ X.curve.toEllipticCurveGeom.E}
    (hσ : σ ≫ X.curve.toEllipticCurveGeom.π = 𝟙 X.base) (p q : E4ModuliRing R)
    (hpq : (universalE4 R).toAffine.Equation p q)
    (hmark : ∀ w : E4Witness X L,
      w.Pr.MarksAt hσ
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (e4ClassifyingRingHom X L hD p))
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
          (e4ClassifyingRingHom X L hD q))) :
    σ ≫ e4Top hD =
      e4ClassifyingMap X L hD ≫
        projModelAffineSection (universalE4 R) p q hpq := by
  refine (e4BaseCover hD).hom_ext _ _ (fun w => ?_)
  show w.V.1.ι ≫ σ ≫ e4Top hD = _
  have hfac : w.V.1.ι ≫ σ =
      sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫
        (e4WitnessCover hD).f w := by
    rw [e4WitnessCover_f]
    unfold sectionLift
    rw [pullback.lift_fst]
  rw [← Category.assoc, hfac, Category.assoc, e4Top_piece]
  obtain ⟨hpq', hMeq⟩ := hmark w
  have hMeq' : sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom =
      w.V.2.isoSpec.hom ≫ projModelAffineSection w.Pr.W _ _ hpq' := by
    calc sectionLift X.curve.toEllipticCurveGeom hσ w.V ≫ w.Pr.e.hom
        = w.V.2.isoSpec.hom ≫ (w.V.2.isoSpec.inv ≫
            sectionLift X.curve.toEllipticCurveGeom hσ w.V) ≫ w.Pr.e.hom := by
          rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [hMeq]
  rw [e4Piece, ← Category.assoc, hMeq']
  rw [Category.assoc, ← Category.assoc (projModelAffineSection w.Pr.W _ _ hpq'),
    projModelAffineSection_congr
      (universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm]
  letI : Algebra (E4ModuliRing R) Γ(X.base, w.V.1) :=
    ((((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
      (e4ClassifyingRingHom X L hD))).toAlgebra
  have hbc := projModelAffineSection_baseChange (universalE4 R) p q hpq
    (WeierstrassCurve.Affine.Equation.map (algebraMap (E4ModuliRing R)
      Γ(X.base, w.V.1)) hpq)
  rw [show projModelAffineSection ((universalE4 R).map
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD)))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e4ClassifyingRingHom X L hD p))
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e4ClassifyingRingHom X L hD q))
      ((universalE4_map_classifying X L hD w.V w.Pr w.B w.u w.v
        w.hF w.hP w.hQ).symm ▸ hpq') ≫
      projModelBaseChange
        (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
          (e4ClassifyingRingHom X L hD))
        (universalE4 R) =
    Spec.map (CommRingCat.ofHom
      (((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X L hD))) ≫
      projModelAffineSection (universalE4 R) p q hpq from hbc]
  rw [← Category.assoc, ← restrict_e4ClassifyingMap hD w.V, Category.assoc]
  rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt1 ★★)** Pulling the universal marked `P` back recovers `P`. Mirror of
`pullSection_e3ClassifyingEllHom_P`. -/
theorem pullSection_e4ClassifyingEllHom_P {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    EllHom.pullSection R (e4ClassifyingEllHom hD h2) (universalE4P R) = L.1.1 := by
  have hdown : L.1.1.1 ≫ e4Top hD =
      e4ClassifyingMap X L hD ≫
        projModelAffineSection (universalE4 R) 0 0 (universalE4_equation_zero R) := by
    refine section_comp_e4Top hD L.1.1.2 0 0 (universalE4_equation_zero R)
      (fun w => ?_)
    have hz : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e4ClassifyingRingHom X L hD (0 : E4ModuliRing R)) =
      (0 : Γ(X.base, w.V.1)) := by rw [map_zero, map_zero]
    rw [hz]
    exact w.hP
  refine Subtype.ext ?_
  refine (e4ClassifyingEllHom hD h2).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (e4ClassifyingEllHom hD h2)
        (universalE4P R)).1 ≫ (e4ClassifyingEllHom hD h2).top =
      (e4ClassifyingEllHom hD h2).baseHom ≫ (universalE4P R).1
      from (e4ClassifyingEllHom hD h2).isPullback.lift_fst _ _ _]
    show _ = L.1.1.1 ≫ e4Top hD
    rw [hdown]
    rfl
  · rw [show (EllHom.pullSection R (e4ClassifyingEllHom hD h2)
        (universalE4P R)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (e4ClassifyingEllHom hD h2) (universalE4P R)).2]
    exact L.1.1.2.symm

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt1 ★★)** Pulling the universal marked `Q` back recovers `Q`. Mirror of
`pullSection_e3ClassifyingEllHom_Q`. -/
theorem pullSection_e4ClassifyingEllHom_Q {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L)
    (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    EllHom.pullSection R (e4ClassifyingEllHom hD h2) (universalE4Q R) = L.1.2 := by
  have hdown : L.1.2.1 ≫ e4Top hD =
      e4ClassifyingMap X L hD ≫
        projModelAffineSection (universalE4 R) (e4U R) (e4V R)
          (universalE4_equation_Q R) := by
    refine section_comp_e4Top hD L.1.2.2 (e4U R) (e4V R)
      (universalE4_equation_Q R) (fun w => ?_)
    have hg : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e4ClassifyingRingHom X L hD (e4U R)) = w.u := by
      rw [e4ClassifyingRingHom_U]
      exact (e4UGlued X L hD).2 w.V w.Pr w.B w.u w.v w.hF w.hP w.hQ
    have hb : ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom)
        (e4ClassifyingRingHom X L hD (e4V R)) = w.v := by
      rw [e4ClassifyingRingHom_V]
      exact (e4VGlued X L hD).2 w.V w.Pr w.B w.u w.v w.hF w.hP w.hQ
    rw [hg, hb]
    exact w.hQ
  refine Subtype.ext ?_
  refine (e4ClassifyingEllHom hD h2).isPullback.hom_ext ?_ ?_
  · rw [show (EllHom.pullSection R (e4ClassifyingEllHom hD h2)
        (universalE4Q R)).1 ≫ (e4ClassifyingEllHom hD h2).top =
      (e4ClassifyingEllHom hD h2).baseHom ≫ (universalE4Q R).1
      from (e4ClassifyingEllHom hD h2).isPullback.lift_fst _ _ _]
    show _ = L.1.2.1 ≫ e4Top hD
    rw [hdown]
    rfl
  · rw [show (EllHom.pullSection R (e4ClassifyingEllHom hD h2)
        (universalE4Q R)).1 ≫ X.curve.π = 𝟙 X.base from
      (EllHom.pullSection R (e4ClassifyingEllHom hD h2) (universalE4Q R)).2]
    exact L.1.2.2.symm

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13)** The tautological presentation marks the universal `P` at `(0, 0)`. -/
theorem tautPresentation_marksAt_e4P :
    (tautPresentation (universalE4 R)).MarksAt
      (universalE4P R).2
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom 0)
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom 0) :=
  tautPresentation_marksAt (universalE4 R) 0 0 (universalE4_equation_zero R)

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13)** The tautological presentation marks the universal `Q` at
`(e4U, e4V)`. -/
theorem tautPresentation_marksAt_e4Q :
    (tautPresentation (universalE4 R)).MarksAt
      (universalE4Q R).2
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4U R))
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4V R)) :=
  tautPresentation_marksAt (universalE4 R) (e4U R) (e4V R)
    (universalE4_equation_Q R)

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13)** The tautologically marked universal pair IS an `ℰ₄`-datum. Mirror of
`universalE3_isE3Datum`. -/
theorem universalE4_isE4Datum
    (hL : (universalE4Obj R).curve.IsNaiveFullLevel 4
      (universalE4P R) (universalE4Q R)) :
    IsE4Datum (universalE4Obj R) ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩ := by
  haveI : IsAffine (universalE4Obj R).base :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (E4ModuliRing R))))
  intro s
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, tautPresentation (universalE4 R),
    (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4B R),
    (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4U R),
    (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4V R),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact IsE4Form.map _ (universalE4_isE4Form R)
  · have h := tautPresentation_marksAt_e4P R
    rw [map_zero] at h
    exact h
  · exact tautPresentation_marksAt_e4Q R
  · exact (isUnit_e4B R).map _
  · have h := congrArg
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom) (e4_order_rel R)
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
    exact h

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13)** `ℰ₄`-datum functoriality: an `ℰ₄`-datum pulls back along a morphism of
`Ell/R`-objects. Mirror of `IsE3Datum.map` (the `e4Rel` clause transports because
`sectionsMapLE` is a ring hom). -/
theorem IsE4Datum.map {R : CommRingCat.{u}} {X' X : EllObj R} (φ : X' ⟶ X)
    {L : X.curve.FullLevelPt 4} (hD : IsE4Datum X L) (L' : X'.curve.FullLevelPt 4)
    (hL'P : L'.1.1.1 = (EllHom.pullSection R φ L.1.1).1)
    (hL'Q : L'.1.2.1 = (EllHom.pullSection R φ L.1.2).1) :
    IsE4Datum X' L' := by
  intro s'
  obtain ⟨V, hsV, Pr, B, u, v, hF, hP, hQ, hBu, hrel⟩ := hD (φ.baseHom.base s')
  obtain ⟨V'₀, hV'aff, hs'V', hV'sub⟩ := exists_isAffineOpen_mem_and_subset
    (show s' ∈ (φ.baseHom ⁻¹ᵁ V.1 : X'.base.Opens) from hsV)
  have hle : (⟨V'₀, hV'aff⟩ : X'.base.affineOpens).1 ≤ φ.baseHom ⁻¹ᵁ V.1 := hV'sub
  refine ⟨⟨V'₀, hV'aff⟩, hs'V',
    Pr.transport φ.baseHom φ.top φ.isPullback φ.zero_w hle,
    sectionsMapLE φ.baseHom hle B, sectionsMapLE φ.baseHom hle u,
    sectionsMapLE φ.baseHom hle v, ?_, ?_, ?_, ?_, ?_⟩
  · rw [transport_W]
    exact IsE4Form.map _ hF
  · have h0 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hP
      (EllHom.pullSection R φ L.1.1).2
      (φ.isPullback.lift_fst _ _ _) hle
    rw [map_zero] at h0
    exact MarksAt.congr_section hL'P.symm L'.1.1.2 h0
  · have h1 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hQ
      (EllHom.pullSection R φ L.1.2).2
      (φ.isPullback.lift_fst _ _ _) hle
    exact MarksAt.congr_section hL'Q.symm L'.1.2.2 h1
  · exact hBu.map _
  · have h := congrArg (sectionsMapLE φ.baseHom hle) hrel
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
    exact h

section Rt2

variable {R : CommRingCat.{u}} {X : EllObj R} (φ : X ⟶ universalE4Obj R)
  (hL : (universalE4Obj R).curve.IsNaiveFullLevel 4
    (universalE4P R) (universalE4Q R))

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt2 prerequisite ★)** The pulled-witness family: over each affine `V` of
`X.base`, the tautological universal `ℰ₄`-chart transported along `φ` is an
`E4Witness` for the pulled datum. Mirror of `e3PulledWitness` (three parameters
`B, u, v`; the `Q`-marking is at `(e4U, e4V)` — no `map_add` juggling needed). -/
noncomputable def e4PulledWitness (V : X.base.affineOpens) :
    E4Witness X ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
      ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) := by
  refine
    { V := V
      Pr := (tautPresentation (universalE4 R)).transport
        φ.baseHom φ.top φ.isPullback φ.zero_w
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
      B := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4B R))
      u := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4U R))
      v := sectionsMapLE φ.baseHom
        (show V.1 ≤ φ.baseHom ⁻¹ᵁ
          (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
            (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom (e4V R))
      hF := ?_
      hP := ?_
      hQ := ?_ }
  · rw [transport_W]
    exact IsE4Form.map _ (IsE4Form.map _ (universalE4_isE4Form R))
  · have hmark := tautPresentation_marksAt_e4P R
    rw [map_zero] at hmark
    have hcomm : (EllHom.pullSection R φ (universalE4P R)).1 ≫ φ.top =
        φ.baseHom ≫ (universalE4P R).1 := φ.isPullback.lift_fst _ _ _
    have htr := LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalE4P R)).2 hcomm
      (V' := V) (fun x _ => trivial)
    rw [map_zero] at htr
    exact htr
  · have hmark := tautPresentation_marksAt_e4Q R
    have hcomm : (EllHom.pullSection R φ (universalE4Q R)).1 ≫ φ.top =
        φ.baseHom ≫ (universalE4Q R).1 := φ.isPullback.lift_fst _ _ _
    exact LocalPresentation.MarksAt.transport φ.baseHom φ.top
      φ.isPullback φ.zero_w hmark
      (EllHom.pullSection R φ (universalE4Q R)).2 hcomm
      (V' := V) (fun x _ => trivial)

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation MvPolynomial in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt2a ★)** The classifying ring map of the pulled datum is the ring map
of `φ` itself. Mirror of `e3ClassifyingRingHom_pulled`: `R`-scalars via `base_w`, the
THREE generators `B, u, v` via the pulled-witness family + the glued specs, and the
ext peels the `Away` localization, then the `E4Quotient` layer, then closes by
`MvPolynomial.induction_on`. -/
theorem e4ClassifyingRingHom_pulled :
    e4ClassifyingRingHom X
      ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
        ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩)
      (IsE4Datum.map φ (universalE4_isE4Datum R hL)
        ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
          ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl) =
    ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
      φ.baseHom.appTop).hom := by
  set hD' := IsE4Datum.map φ (universalE4_isE4Datum R hL)
    ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
      ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl with hD'def
  have hψR : ∀ r : R,
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (algebraMap R (E4ModuliRing R) r) = X.baseRingHom r := by
    intro r
    have hb : CommRingCat.ofHom (algebraMap R (E4ModuliRing R)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫ φ.baseHom.appTop =
        CommRingCat.ofHom X.baseRingHom := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        show φ.baseHom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (E4ModuliRing R))) = X.structMap from φ.base_w]
      rfl
    exact congrArg (fun g => CommRingCat.Hom.hom g r) hb
  have hcover : (⊤ : X.base.Opens) ≤
      iSup (fun V : X.base.affineOpens => V.1) := by
    intro x _
    obtain ⟨V₀, hVaff, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.base.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₀, hVaff⟩, hxV⟩
  have hnat_B : (e4BGlued X _ hD').1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (e4B R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (e4BGlued X _ hD').1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4B R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4B R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom
            (e4B R)) := rfl
    rw [hres]
    exact (e4BGlued X _ hD').2
      (e4PulledWitness φ hL V).V (e4PulledWitness φ hL V).Pr
      (e4PulledWitness φ hL V).B (e4PulledWitness φ hL V).u
      (e4PulledWitness φ hL V).v
      (e4PulledWitness φ hL V).hF (e4PulledWitness φ hL V).hP
      (e4PulledWitness φ hL V).hQ
  have hnat_U : (e4UGlued X _ hD').1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (e4U R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (e4UGlued X _ hD').1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4U R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4U R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom
            (e4U R)) := rfl
    rw [hres]
    exact (e4UGlued X _ hD').2
      (e4PulledWitness φ hL V).V (e4PulledWitness φ hL V).Pr
      (e4PulledWitness φ hL V).B (e4PulledWitness φ hL V).u
      (e4PulledWitness φ hL V).v
      (e4PulledWitness φ hL V).hF (e4PulledWitness φ hL V).hP
      (e4PulledWitness φ hL V).hQ
  have hnat_V : (e4VGlued X _ hD').1 =
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
        φ.baseHom.appTop).hom (e4V R) := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.base.sheaf
      (fun V : X.base.affineOpens => V.1) ⊤
      (fun V => homOfLE le_top) hcover _ _ (fun V => ?_)
    show Scheme.resLE le_top (e4VGlued X _ hD').1 =
      Scheme.resLE le_top
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4V R))
    have hres : Scheme.resLE (le_top : V.1 ≤ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
          φ.baseHom.appTop).hom (e4V R)) =
        sectionsMapLE φ.baseHom
          (show V.1 ≤ φ.baseHom ⁻¹ᵁ
            (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
              (E4ModuliRing R))).affineOpens).1 from fun x _ => trivial)
          ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom
            (e4V R)) := rfl
    rw [hres]
    exact (e4VGlued X _ hD').2
      (e4PulledWitness φ hL V).V (e4PulledWitness φ hL V).Pr
      (e4PulledWitness φ hL V).B (e4PulledWitness φ hL V).u
      (e4PulledWitness φ hL V).v
      (e4PulledWitness φ hL V).hF (e4PulledWitness φ hL V).hP
      (e4PulledWitness φ hL V).hQ
  refine IsLocalization.ringHom_ext (Submonoid.powers (e4Delta R)) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply]
  induction a using MvPolynomial.induction_on with
  | C r =>
    have hcr : (algebraMap (E4Quotient R) (E4ModuliRing R))
        (Ideal.Quotient.mk _ (MvPolynomial.C r)) = algebraMap R (E4ModuliRing R) r := by
      rw [IsScalarTower.algebraMap_apply R (E4Quotient R) (E4ModuliRing R),
        IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 3) R) (E4Quotient R)]
      rfl
    rw [hcr, e4ClassifyingRingHom_algebraMap]
    exact (hψR r).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp]
    congr 1
    fin_cases j
    · show e4ClassifyingRingHom X _ hD' (e4B R) = _
      rw [e4ClassifyingRingHom_B]
      exact hnat_B
    · show e4ClassifyingRingHom X _ hD' (e4U R) = _
      rw [e4ClassifyingRingHom_U]
      exact hnat_U
    · show e4ClassifyingRingHom X _ hD' (e4V R) = _
      rw [e4ClassifyingRingHom_V]
      exact hnat_V

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-13, rt2b ★)** BaseHom determination: the classifying morphism of the pulled
datum IS `φ`'s base morphism. Mirror of `e3ClassifyingMap_pulled`. -/
theorem e4ClassifyingMap_pulled :
    e4ClassifyingMap X
      ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
        ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩)
      (IsE4Datum.map φ (universalE4_isE4Datum R hL)
        ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
          ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl) = φ.baseHom := by
  show X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (e4ClassifyingRingHom X _ _)) = φ.baseHom
  rw [show CommRingCat.ofHom
      (e4ClassifyingRingHom X
        ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
          ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩)
        (IsE4Datum.map φ (universalE4_isE4Datum R hL)
          ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
            ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl)) =
    (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv ≫
      φ.baseHom.appTop from by
    rw [e4ClassifyingRingHom_pulled φ hL]
    rfl]
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  show φ.baseHom ≫ (Spec (CommRingCat.of (E4ModuliRing R))).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv =
    φ.baseHom
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

open AlgebraicGeometry CategoryTheory Limits Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
-- RESIDUAL BUMP (2×, was 32×): elaboration of this transport-chain proof lands at
-- ~280k heartbeats and cannot reach the 200k default. The irreducible hotspot is the
-- `whnf` of `(tautPresentation (universalE4 R)).W` (the `from rfl` step folding the
-- taut presentation into a base change) together with the final `e4Piece` `rfl`: both
-- force evaluation of `universalE4 R`'s `E4ModuliRing`-valued (localized-quotient)
-- coefficients. This whnf is cheap over an abstract carrier (a `(tautPresentation W).W =
-- W.map _` lemma over a variable ring is `rfl` in ~440 hb) but every device that keeps it
-- abstract here — a barrier-lemma `rw`, a bare `rw`, or a positional `conv` — either makes
-- the motive ill-typed or leaves the goal unclosed. A genuine 200k fix needs the whole
-- `e4Piece`/classifying API generalised over
-- an abstract curve (the mouth-core nativeGlue/reduceSide pattern), a file-wide refactor
-- beyond golfing; the identical ℰ₃ mirror `e3Top_pulled` carries the same 32× bump.
-- Valid golf applied: `hle` factoring of the 8 repeated open-inclusion proofs +
-- `conv_lhs` scoping of the final `e4Piece` unfold (cut the need from >440k to ~280k).
set_option maxHeartbeats 400000 in
/-- **(E4A-13, rt2c ★★)** Top determination: the glued classifying comparison of the
pulled datum IS `φ`'s total-space morphism. Mirror of `e3Top_pulled`. -/
theorem e4Top_pulled :
    e4Top (IsE4Datum.map φ (universalE4_isE4Datum R hL)
      ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
        ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl) = φ.top := by
  set hD' := IsE4Datum.map φ
    (universalE4_isE4Datum R hL)
    ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
      ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩)
    rfl rfl with hD'def
  letI : Algebra (E4ModuliRing R)
      Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (E4ModuliRing R)
      Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤)))) := by
    have h : CommRingCat.ofHom (algebraMap (E4ModuliRing R)
        Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv := rfl
    rw [h]
    infer_instance
  have hfst : pullback.fst (projModelπ (universalE4 R))
      (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).ι =
      (tautPresentation (universalE4 R)).e.hom ≫
        (isPullback_projModelBaseChange (universalE4 R)).isoPullback.hom ≫
        pullback.fst (projModelπ (universalE4 R))
          (Spec.map (CommRingCat.ofHom (algebraMap (E4ModuliRing R)
            Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤)))) := by
    rw [show (tautPresentation (universalE4 R)).e.hom =
      (asIso (pullback.fst (projModelπ (universalE4 R))
        (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ (universalE4 R))
        (Spec.map (CommRingCat.ofHom (algebraMap (E4ModuliRing R)
          Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤)))))).symm ≪≫
      (isPullback_projModelBaseChange (universalE4 R)).isoPullback.symm).hom
      from rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (e4WitnessCover hD').hom_ext _ _ (fun w => ?_)
  have hle : w.V.1 ≤ φ.baseHom ⁻¹ᵁ
      (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of
        (E4ModuliRing R))).affineOpens).1 := fun x _ => trivial
  rw [e4Top_piece hD' w, e4WitnessCover_f]
  rw [e4Piece_congr hD' w (e4PulledWitness φ hL w.V) rfl, eqToHom_refl,
    Category.id_comp]
  -- now: chartPiece(pulled) = fst ≫ φ.top; unfold the φ-side through the transport
  rw [show pullback.fst X.curve.toEllipticCurveGeom.π w.V.1.ι ≫ φ.top =
    transportTheta φ.baseHom φ.top φ.isPullback
      hle ≫
      pullback.fst (projModelπ (universalE4 R))
        (⊤ : (Spec (CommRingCat.of (E4ModuliRing R))).Opens).ι from
    (transportTheta_fst φ.baseHom φ.top φ.isPullback _).symm]
  rw [hfst, ← Category.assoc,
    show transportTheta φ.baseHom φ.top φ.isPullback
        hle ≫
      (tautPresentation (universalE4 R)).e.hom =
    ((tautPresentation (universalE4 R)).transport
      φ.baseHom φ.top φ.isPullback φ.zero_w
      hle).e.hom ≫
      projModelBaseChange (sectionsMapLE φ.baseHom
        hle)
        (tautPresentation (universalE4 R)).W from
    (transport_e_baseChange φ.baseHom φ.top φ.isPullback φ.zero_w
      (tautPresentation (universalE4 R)) _).symm]
  -- collapse the universal-side chain into a single base change along the composite
  have hσ : (sectionsMapLE φ.baseHom
      hle).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom) =
      ((X.base.presheaf.map (homOfLE (le_top : w.V.1 ≤ ⊤)).op).hom).comp
        (e4ClassifyingRingHom X _ hD') := by
    rw [sectionsMapLE_congr_hom (e4ClassifyingMap_pulled φ hL).symm
      hle]
    exact sectionsMapLE_e4ClassifyingMap hD' w.V (fun x _ => trivial)
  rw [show projModelBaseChange (sectionsMapLE φ.baseHom
      hle)
      (tautPresentation (universalE4 R)).W =
    projModelBaseChange (sectionsMapLE φ.baseHom
      hle)
      ((universalE4 R).map
        ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom)) from rfl]
  rw [show (isPullback_projModelBaseChange (universalE4 R)).isoPullback.hom ≫
      pullback.fst (projModelπ (universalE4 R))
        (Spec.map (CommRingCat.ofHom (algebraMap (E4ModuliRing R)
          Γ(Spec (CommRingCat.of (E4ModuliRing R)), ⊤)))) =
    projModelBaseChange
      ((Scheme.ΓSpecIso (CommRingCat.of (E4ModuliRing R))).inv.hom)
      (universalE4 R) from
    (isPullback_projModelBaseChange (universalE4 R)).isoPullback_hom_fst]
  rw [Category.assoc, ← projModelBaseChange_comp',
    projModelBaseChange_congr_hom hσ (universalE4 R)]
  conv_lhs => rw [e4Piece]
  rfl

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option linter.unusedVariables false in
/-- **(E4A-13, rt2 ★★★, the uniqueness half of the universal property)** ANY
`Ell/R`-morphism to the universal `ℰ₄` object IS the classifying morphism of the datum
it pulls back. Mirror of `e3ClassifyingEllHom_pulled`. -/
theorem e4ClassifyingEllHom_pulled (h2 : IsUnit (2 : Γ(X.base, ⊤))) :
    e4ClassifyingEllHom
      (IsE4Datum.map φ (universalE4_isE4Datum R hL)
        ((gammaFullNaiveProblem R 4).map (Opposite.op φ)
          ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩) rfl rfl) h2 = φ :=
  EllHom.ext (e4ClassifyingMap_pulled φ hL) (e4Top_pulled φ hL)

end Rt2

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(E4A-14, the raw naive-functor `RepresentableBy`)** Given `hL` (the universal
marked pair is a level-4 structure) and `hArb` (every naive level-4 structure is an
`ℰ₄`-datum), the raw naive level-4 functor is representable by `universalE4Obj`. The
inverse classifies via `hArb`; `IsE4Datum` is a `Prop`, so `hArb X x` is defeq to the
pulled datum, making the roundtrips reduce to rt1
(`pullSection_e4ClassifyingEllHom_P/_Q`) and rt2 (`e4ClassifyingEllHom_pulled`).
Mirror of `naiveLevelThreeRepresentableBy`. -/
def naiveLevelFourRepresentableBy (R : CommRingCat.{u}) (hR : IsUnit (2 : R))
    (hL : (universalE4Obj R).curve.IsNaiveFullLevel 4
      (universalE4P R) (universalE4Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 4), IsE4Datum X L) :
    (gammaFullNaiveProblem R 4).RepresentableBy (universalE4Obj R) where
  homEquiv {X} :=
    { toFun := fun φ => (gammaFullNaiveProblem R 4).map (Opposite.op φ)
        ⟨⟨universalE4P R, universalE4Q R⟩, hL⟩
      invFun := fun x => e4ClassifyingEllHom (hArb X x) (X.isUnit_two hR)
      left_inv := fun φ => e4ClassifyingEllHom_pulled φ hL (X.isUnit_two hR)
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact pullSection_e4ClassifyingEllHom_P (hArb X x) (X.isUnit_two hR)
        · exact pullSection_e4ClassifyingEllHom_Q (hArb X x) (X.isUnit_two hR) }
  homEquiv_comp {X X'} f g :=
    (gammaFullNaiveProblem R 4).map_comp_apply
      (Opposite.op g) (Opposite.op f) _

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
      Nonempty ((gammaFullNaiveProblem R 4).RepresentableBy X) := by
  refine naiveLevelFour_representable_by_affine_of_conditions R hR
    ⟨⟨?_, ?_⟩, fun k _ _ t x hx => universalE4_generation R hR k t x hx⟩
    (fun X L => isE4Datum_of_bridges X hR L)
  · exact_mod_cast four_zsmul_universalE4P_of_isUnit R hR
  · exact_mod_cast four_zsmul_universalE4Q_of_isUnit R hR

end ModularCurves
