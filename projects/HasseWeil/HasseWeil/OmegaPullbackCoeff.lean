/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Polynomial.Derivation
import HasseWeil.Auxiliary.DiffQuotientRule
import HasseWeil.FormalGroupCorrespondence
import HasseWeil.WronskianAux

/-!
# The Omega-Based Pullback Coefficient

Following Silverman III.5, for an endomorphism α of an elliptic curve E,
the pullback coefficient `a_α` is defined by `α*(ω) = a_α · ω` where
`ω = dx/(2y + a₁x + a₃)` is the invariant differential.

The key property: `a_α ∈ F` (the base field), not just K(E). This follows
from ω having no zeros or poles (Silverman III.1.5), making `α*(ω)/ω`
a regular function on a complete curve, hence constant.

With `a_α ∈ F`:
- Chain rule: `a_{α∘β} = a_α · a_β` (from semilinearity of pullback on forms)
- Additivity: `a_{α+β} = a_α + a_β` (from Silverman III.5.2)
- `a_{[n]} = n` (from Silverman III.5.3)

## Implementation

The pullback `α*(ω)` in the Kähler differential module Ω[K(E)/F] is computed as:
  `α*(ω) = D(α*(x)) · α*(u)⁻¹`
where `u = 2y + a₁x + a₃` and `α*(u) = 2·α*(y) + a₁·α*(x) + a₃`.

Since Ω is 1-dimensional (kaehler_rank_one), `α*(ω) = c · ω` for unique `c ∈ K(E)`.
The pullback coefficient is this `c`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.1.5, III.5
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

/-- The element `u = 2y + a₁x + a₃` in K(E), the denominator of the
    invariant differential ω = u⁻¹ • D(x). -/
noncomputable def u_gen : KE :=
  2 * algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial) +
  algebraMap F KE W.a₁ * algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X) +
  algebraMap F KE W.a₃

theorem u_gen_ne_zero : u_gen W ≠ 0 := denom_ne_zero W.toAffine

/-- `α*(u)` where `u = 2y + a₁x + a₃`. Since α* is an F-algebra hom,
    `α*(u) = 2·α*(y) + a₁·α*(x) + a₃`. -/
noncomputable def alpha_star_u (α : Isogeny W.toAffine W.toAffine) : KE :=
  2 * α.pullback (algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)) +
  algebraMap F KE W.a₁ * α.pullback (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) +
  algebraMap F KE W.a₃

/-- `α*(u) = α.pullback(u_gen)`: the pullback of u is u evaluated at
    the image point. This follows from α* being an F-algebra hom. -/
theorem alpha_star_u_eq (α : Isogeny W.toAffine W.toAffine) :
    alpha_star_u W α = α.pullback (u_gen W) := by
  simp only [alpha_star_u, u_gen, map_add, map_mul, map_ofNat, AlgHom.commutes]

/-- The omega-based pullback coefficient: the unique `c ∈ K(E)` such that
    `c • ω = α*(u)⁻¹ • D(α*(x))` in `Ω[K(E)/F]`. -/
noncomputable def omegaPullbackCoeff (α : Isogeny W.toAffine W.toAffine) : KE :=
  (exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine)
    ((alpha_star_u W α)⁻¹ •
      KaehlerDifferential.D F KE
        (α.pullback
          (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))))).choose

/-- The defining property of `omegaPullbackCoeff`:
    `omegaPullbackCoeff W α • ω = α*(u)⁻¹ • D(α*(x))`. -/
theorem omegaPullbackCoeff_spec (α : Isogeny W.toAffine W.toAffine) :
    omegaPullbackCoeff W α • invariantDifferential W.toAffine =
      (alpha_star_u W α)⁻¹ •
        KaehlerDifferential.D F KE
          (α.pullback
            (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))) :=
  (exists_smul_eq_of_finrank_eq_one
    (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine)
    ((alpha_star_u W α)⁻¹ •
      KaehlerDifferential.D F KE
        (α.pullback
          (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))))).choose_spec

-- Chain rule for `omegaPullbackCoeff`. The chain rule `a_{α∘β} = a_α · a_β` holds when `a_α`
-- is in the base field `F` (so that `β*(a_α) = a_α`); for the Silverman convention `a_α ∈ F`
-- always holds (Silverman III.5.5). It is proved abstractly as `omegaPullbackCoeff_comp_of_base`
-- in `HasseWeil/InvariantDifferentialPullback.lean`; not restated here to avoid a naming clash.
-- For `α = [n]` we get `a_{[n]} = n ∈ F`, which is what the Hasse bound needs.

/-- Uniqueness of the omega-based pullback coefficient: in the 1-dimensional Kähler module,
    if `c₁ • ω = c₂ • ω` then `c₁ = c₂` (since `ω ≠ 0` and `KE` is a field). -/
theorem omegaPullbackCoeff_unique (c₁ c₂ : KE)
    (h : c₁ • invariantDifferential W.toAffine = c₂ • invariantDifferential W.toAffine) :
    c₁ = c₂ := by
  have hsub : (c₁ - c₂) • invariantDifferential W.toAffine = 0 := by
    rw [sub_smul, sub_eq_zero]; exact h
  rcases smul_eq_zero.mp hsub with hc | habs
  · exact sub_eq_zero.mp hc
  · exact absurd habs (invariantDifferential_ne_zero W.toAffine)

-- Pullback of `[n]` on generators: these lemmas compute what `[n]*` does on `x_gen` and `y_gen`,
-- connecting the abstract pullback `(mulByInt W.toAffine n).pullback` to the concrete division
-- polynomial expressions `mulByInt_x` and `mulByInt_y`.

/-- `[n]*(x_gen) = Φ_n / ΨSq_n` in K(E). -/
theorem mulByInt_pullback_x (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback
      (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) =
    mulByInt_x W n := by
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn := dif_neg hn
  rw [hpb]
  change mulByInt_pullbackRingHom W n hn
    (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) = _
  rw [mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  change mulByInt_coordHom W n hn (algebraMap (Polynomial F) R Polynomial.X) = _
  rw [show algebraMap (Polynomial F) R Polynomial.X =
    Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) from rfl,
    mulByInt_coordHom, AdjoinRoot.lift_mk]
  simp [Polynomial.eval₂_C, mulByInt_xHom, mulByInt_x]

/-- `[n]*(y_gen) = ω_n / ψ_n³` in K(E). -/
theorem mulByInt_pullback_y (n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback
      (algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)) =
    mulByInt_y W n := by
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn := dif_neg hn
  rw [hpb]
  change mulByInt_pullbackRingHom W n hn
    (algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)) = _
  rw [mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  change mulByInt_coordHom W n hn (AdjoinRoot.root W.toAffine.polynomial) = _
  rw [mulByInt_coordHom, AdjoinRoot.lift_root]

-- `alpha_star_u` for `[n]`. Using the ω_spec identity `2ω(n) + a₁φ(n)ψ(n) + a₃ψ(n)³ = ψc(n)`,
-- the pullback of `u` under `[n]` can be expressed as `ψc_n(x_gen) / ψ_n(x_gen)³`.

/-- `α*(u)` for `α = [n]` equals `2 · mulByInt_y + a₁ · mulByInt_x + a₃`. -/
theorem alpha_star_u_mulByInt (n : ℤ) (hn : n ≠ 0) :
    alpha_star_u W (mulByInt W.toAffine n) =
    2 * mulByInt_y W n +
    algebraMap F KE W.a₁ * mulByInt_x W n +
    algebraMap F KE W.a₃ := by
  simp only [alpha_star_u, mulByInt_pullback_x W n hn, mulByInt_pullback_y W n hn]

-- The Wronskian identity for division polynomials. The key algebraic identity: the "Wronskian"
-- of Φ_n and ΨSq_n evaluated at x_gen, combined with u_gen and the division polynomial
-- expressions, yields n. Concretely, after expanding `D([n]*(x)) = D(Φ_n/ΨSq_n)` using the
-- quotient rule and the chain rule `D(p(x_gen)) = p'(x_gen) · D(x_gen)`, we need
-- `(Φ_n' · ΨSq_n - Φ_n · ΨSq_n')(x_gen) · u_gen / (ΨSq_n(x_gen)² · alpha_star_u_n) = n`,
-- where `Φ_n' = Polynomial.derivative (W.Φ n)` and `ΨSq_n' = Polynomial.derivative (W.ΨSq n)`.
-- This reduces to the division polynomial relation
-- `Φ_n' · ΨSq_n - Φ_n · ΨSq_n' = n · (stuff involving y and Weierstrass coefficients)`
-- modulo the Weierstrass relation, combined with the ω_spec identity for alpha_star_u.
-- Reference: Silverman Exercise III.3.7, with the invariant differential computation from III.5.3.

/-- ψ_ff squared equals ΨSq_ff. -/
private lemma ψ_ff_sq_eq (n : ℤ) :
    (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))) ^ 2 =
      ΨSq_ff W n := by
  simp only [ΨSq_ff]; rw [← map_pow]; congr 1
  rw [Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]
  exact Affine.CoordinateRing.mk_Ψ_sq (W := W.toAffine) n

/-- ΨSq_ff is nonzero for n ≠ 0. -/
private lemma ΨSq_ff_ne_zero' {n : ℤ} (hn : n ≠ 0) : ΨSq_ff W n ≠ 0 := by
  rw [ΨSq_ff]; intro h
  exact ΨSq_poly_ne_zero W hn
    (((IsFractionRing.injective R KE).comp
      Affine.CoordinateRing.algebraMap_poly_injective)
    (by simp only [Function.comp, map_zero]; exact h))

/-- The image of φ in K(E) equals Φ_ff. -/
private lemma φ_ff_eq (n : ℤ) :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.φ n)) =
      Φ_ff W n := by
  simp only [Φ_ff]; congr 1
  exact Affine.CoordinateRing.mk_φ (W := W.toAffine) n

/-- CC a maps to algebraMap F KE a via the coordinate ring. -/
private lemma CC_eq_algebraMap (a : F) :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C (Polynomial.C a))) = algebraMap F KE a := by
  rw [show Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C a)) =
    algebraMap F R a from rfl]
  exact (IsScalarTower.algebraMap_apply F R KE a).symm

/-- The ω_spec identity in K(E):
    2 * ω_ff + a₁ * Φ_ff * ψ_ff + a₃ * ψ_ff ^ 3 = ψc_ff -/
private lemma ω_spec_ff (n : ℤ) :
    2 * (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ω n))) +
    algebraMap F KE W.a₁ * Φ_ff W n *
      (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))) +
    algebraMap F KE W.a₃ *
      (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))) ^ 3 =
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) := by
  have h := congr_arg (algebraMap R KE ∘ Affine.CoordinateRing.mk W.toAffine) (W.ω_spec n)
  simp only [Function.comp, map_add, map_mul, map_pow, map_ofNat] at h
  rwa [φ_ff_eq W n, CC_eq_algebraMap, CC_eq_algebraMap] at h

/-- The ψc_spec identity in K(E): ψ_ff * ψc_ff = ψ_ff(2n) -/
private lemma ψc_spec_ff (n : ℤ) :
    (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))) *
    (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n))) =
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ (2 * n))) := by
  have h := congr_arg (algebraMap R KE ∘ Affine.CoordinateRing.mk W.toAffine) (W.ψc_spec n)
  simpa only [Function.comp, map_mul] using h

/-- The image of `polynomialY` (= ψ₂) in K(E) equals `u_gen W = 2y + a₁x + a₃`. -/
private lemma mk_polynomialY_eq_u_gen :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomialY) =
      u_gen W := by
  rw [u_gen]
  change algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialY) =
    2 * algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial) +
    algebraMap F KE W.a₁ * algebraMap R KE
      (algebraMap (Polynomial F) R Polynomial.X) +
    algebraMap F KE W.a₃
  rw [Affine.polynomialY]
  simp only [map_add, map_mul, AdjoinRoot.mk_X]
  -- `mk (C (C c)) = algebraMap F R c`, then transport along the scalar tower `F → R → KE`.
  have h_C : ∀ c : F, (AdjoinRoot.mk W.toAffine.polynomial)
      (Polynomial.C (Polynomial.C c)) = algebraMap F R c := fun c ↦ rfl
  rw [h_C, h_C, h_C,
    show (AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C Polynomial.X) =
      algebraMap (Polynomial F) R Polynomial.X from rfl,
    show algebraMap R KE (algebraMap F R 2) = (2 : KE) from by
      rw [← IsScalarTower.algebraMap_apply F R KE]; simp [map_ofNat],
    show algebraMap R KE (algebraMap F R W.a₁) = algebraMap F KE W.a₁ from
      (IsScalarTower.algebraMap_apply F R KE W.a₁).symm,
    show algebraMap R KE (algebraMap F R W.a₃) = algebraMap F KE W.a₃ from
      (IsScalarTower.algebraMap_apply F R KE W.a₃).symm]
  ring

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Base case n=0 of the Wronskian identity. -/
private lemma wronskian_Φ_ΨSq_zero :
    Polynomial.derivative (W.Φ 0) * W.ΨSq 0 - W.Φ 0 * Polynomial.derivative (W.ΨSq 0) =
    Polynomial.C ((0 : ℤ) : F) * W.preΨ (2 * 0) := by
  simp [WeierstrassCurve.Φ_zero, WeierstrassCurve.ΨSq_zero,
    show (2 * 0 : ℤ) = 0 from by norm_num, WeierstrassCurve.preΨ_zero]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Base case n=1 of the Wronskian identity. -/
private lemma wronskian_Φ_ΨSq_one :
    Polynomial.derivative (W.Φ 1) * W.ΨSq 1 - W.Φ 1 * Polynomial.derivative (W.ΨSq 1) =
    Polynomial.C (1 : F) * W.preΨ (2 * 1) := by
  rw [WeierstrassCurve.Φ_one, WeierstrassCurve.ΨSq_one,
    show (2 * 1 : ℤ) = 2 from by norm_num, WeierstrassCurve.preΨ_two]
  simp [Polynomial.derivative_X, Polynomial.derivative_one]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Base case n=-1 of the Wronskian identity, follows from n=1 via Φ_neg, ΨSq_neg, preΨ_neg. -/
private lemma wronskian_Φ_ΨSq_neg_one :
    Polynomial.derivative (W.Φ (-1)) * W.ΨSq (-1) - W.Φ (-1) * Polynomial.derivative (W.ΨSq (-1)) =
    Polynomial.C ((-1 : ℤ) : F) * W.preΨ (2 * (-1)) := by
  have h1 := wronskian_Φ_ΨSq_one (F := F) W
  -- LHS using Φ_neg, ΨSq_neg
  rw [show (-1 : ℤ) = -(1 : ℤ) from rfl,
    WeierstrassCurve.Φ_neg (W := W) (1 : ℤ), WeierstrassCurve.ΨSq_neg (W := W) (1 : ℤ)]
  -- RHS using preΨ_neg
  rw [show ((2 : ℤ) * -1) = -((2 : ℤ) * 1) from by ring,
    WeierstrassCurve.preΨ_neg (W := W) ((2 : ℤ) * 1)]
  -- Now goal: LHS = C(-1) * (-preΨ(2*1)) = C(1) * preΨ(2*1)
  rw [mul_neg, ← neg_mul, ← Polynomial.C_neg,
    show -((-1 : ℤ) : F) = ((1 : ℤ) : F) from by push_cast; ring]
  exact_mod_cast h1

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Base case n=2 of the Wronskian identity.
    Verified mathematically: the Wronskian of Φ₂ and Ψ₂Sq equals 2 * preΨ₄.
    Direct computation using `Φ_two`, `ΨSq_two`, `preΨ_four`, plus `b₂`..`b₈` definitions
    in terms of `a₁`..`a₆`, then `ring`. -/
private lemma wronskian_Φ_ΨSq_two :
    Polynomial.derivative (W.Φ 2) * W.ΨSq 2 - W.Φ 2 * Polynomial.derivative (W.ΨSq 2) =
    Polynomial.C ((2 : ℤ) : F) * W.preΨ (2 * 2) := by
  rw [show (2 * 2 : ℤ) = 4 from by norm_num,
      WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two, WeierstrassCurve.preΨ_four]
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  simp only [Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.derivative_C]
  simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_ofNat, Nat.cast_ofNat]
  ring1

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The negation symmetry of the Wronskian identity: if it holds for `n`, it holds for `-n`. -/
private lemma wronskian_Φ_ΨSq_neg_of {n : ℤ}
    (h : Polynomial.derivative (W.Φ n) * W.ΨSq n - W.Φ n * Polynomial.derivative (W.ΨSq n) =
      Polynomial.C (n : F) * W.preΨ (2 * n)) :
    Polynomial.derivative (W.Φ (-n)) * W.ΨSq (-n) -
      W.Φ (-n) * Polynomial.derivative (W.ΨSq (-n)) =
    Polynomial.C ((-n : ℤ) : F) * W.preΨ (2 * (-n)) := by
  rw [WeierstrassCurve.Φ_neg, WeierstrassCurve.ΨSq_neg,
    show ((2 : ℤ) * -n) = -(2 * n) from by ring, WeierstrassCurve.preΨ_neg]
  rw [mul_neg, ← neg_mul, ← Polynomial.C_neg,
    show -(((-n : ℤ) : F)) = ((n : ℤ) : F) from by push_cast; ring]
  exact h

-- Helper: for any polynomials f q, the "Wronskian" of (X*f - q) and f simplifies.
omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma wronskian_X_mul_sub (f q : Polynomial F) :
    Polynomial.derivative (Polynomial.X * f - q) * f -
      (Polynomial.X * f - q) * Polynomial.derivative f =
    f ^ 2 - (Polynomial.derivative q * f - q * Polynomial.derivative f) := by
  simp [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X]
  ring

-- The auxiliary ring identity `wronskian_aux_three` has been moved to
-- `HasseWeil/WronskianAux.lean` (together with `wronskian_aux_four`) to isolate
-- its expensive elaboration. It is reused unchanged from there.

-- Case m=3: proved via `wronskian_aux_three` from `HasseWeil/WronskianAux.lean`.
-- The key insight: both LHS and RHS factor through Ψ₃, and after cancellation
-- the identity reduces to wronskian_aux_three (a tractable ring computation).
omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma wronskian_Φ_ΨSq_three :
    Polynomial.derivative (W.Φ 3) * W.ΨSq 3 -
      W.Φ 3 * Polynomial.derivative (W.ΨSq 3) =
    Polynomial.C ((3 : ℤ) : F) * W.preΨ (2 * 3) := by
  -- Expand all named division polynomials.
  rw [WeierstrassCurve.Φ_three, WeierstrassCurve.ΨSq_three,
    show (2 * 3 : ℤ) = 6 from by norm_num, show (6 : ℤ) = 2 * 3 from by norm_num,
    WeierstrassCurve.preΨ_even (W := W) (3 : ℤ),
    show (3 : ℤ) - 1 = 2 from by norm_num, show (3 : ℤ) + 2 = 5 from by norm_num,
    show (3 : ℤ) - 2 = 1 from by norm_num, show (3 : ℤ) + 1 = 4 from by norm_num,
    show (5 : ℤ) = 2 * 2 + 1 from by norm_num, WeierstrassCurve.preΨ_odd (W := W) (2 : ℤ),
    show (2 : ℤ) + 2 = 4 from by norm_num, show (2 : ℤ) - 1 = 1 from by norm_num,
    show (2 : ℤ) + 1 = 3 from by norm_num]
  simp only [show Even (2 : ℤ) from ⟨1, by ring⟩, ite_true]
  rw [WeierstrassCurve.preΨ_two, WeierstrassCurve.preΨ_one,
    WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_pow]
  simp only [Polynomial.C_ofNat, Nat.cast_ofNat]
  simp only [show ((3 : ℤ) : F) = (3 : F) from by push_cast; ring]
  -- Use wronskian_aux_three.
  have haux := wronskian_aux_three W
  -- Expand derivative(preΨ₄*Ψ₂Sq) in haux to match the goal.
  simp only [Polynomial.derivative_mul] at haux
  -- Normalize: Polynomial.C 3 and the literal 3 in F[X] are syntactically different.
  -- C_ofNat converts C (ofNat n) to ofNat n in the polynomial ring.
  simp only [Polynomial.C_ofNat] at haux ⊢
  -- Close with linear_combination.
  linear_combination W.Ψ₃ * haux

-- Silverman III.3.7 auxiliary: verified ring identity for m=4.
-- Only expands to b₂, b₄, b₆, b₈ (not a₁..a₆) keeping the ring computation tractable.
-- The auxiliary ring identity `wronskian_aux_four` has been moved to
-- `HasseWeil/WronskianAux.lean` to isolate its ~57 GB ring elaboration.

-- Case m=4: proved via `wronskian_aux_four` from `HasseWeil/WronskianAux.lean`.
-- After applying wronskian_X_mul_sub to restructure the Wronskian,
-- and expanding preΨ(8) via preΨ_even(4)/preΨ_odd(2)/preΨ_even(3),
-- the goal matches wronskian_aux_four exactly (up to 1-simplification).
omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma wronskian_Φ_ΨSq_four :
    Polynomial.derivative (W.Φ 4) * W.ΨSq 4 -
      W.Φ 4 * Polynomial.derivative (W.ΨSq 4) =
    Polynomial.C ((4 : ℤ) : F) * W.preΨ (2 * 4) := by
  -- Step 1: Expand Φ₄ and ΨSq₄.
  rw [WeierstrassCurve.Φ_four, WeierstrassCurve.ΨSq_four]
  -- Reassociate X * preΨ₄² * Ψ₂Sq = X * (preΨ₄² * Ψ₂Sq) for wronskian_X_mul_sub.
  rw [show Polynomial.X * W.preΨ₄ ^ 2 * W.Ψ₂Sq = Polynomial.X * (W.preΨ₄ ^ 2 * W.Ψ₂Sq) from by ring]
  -- Step 2: Apply wronskian_X_mul_sub with f = preΨ₄²*Ψ₂Sq, q = Ψ₃*(preΨ₄*Ψ₂Sq²-Ψ₃³).
  rw [wronskian_X_mul_sub]
  -- Step 3: Expand preΨ(8) on the RHS via preΨ_even(4).
  rw [show (2 * 4 : ℤ) = 8 from by norm_num, show (8 : ℤ) = 2 * 4 from by norm_num,
    WeierstrassCurve.preΨ_even (W := W) (4 : ℤ),
    show (4 : ℤ) - 1 = 3 from by norm_num, show (4 : ℤ) + 2 = 6 from by norm_num,
    show (4 : ℤ) - 2 = 2 from by norm_num, show (4 : ℤ) + 1 = 5 from by norm_num]
  -- Expand preΨ(5) = preΨ_odd(2).
  rw [show (5 : ℤ) = 2 * 2 + 1 from by norm_num, WeierstrassCurve.preΨ_odd (W := W) (2 : ℤ),
    show (2 : ℤ) + 2 = 4 from by norm_num, show (2 : ℤ) - 1 = 1 from by norm_num,
    show (2 : ℤ) + 1 = 3 from by norm_num]
  simp only [show Even (2 : ℤ) from ⟨1, by ring⟩, ite_true]
  -- Expand preΨ(6) = preΨ_even(3).
  rw [show (6 : ℤ) = 2 * 3 from by norm_num, WeierstrassCurve.preΨ_even (W := W) (3 : ℤ),
    show (3 : ℤ) - 1 = 2 from by norm_num, show (3 : ℤ) + 2 = 5 from by norm_num,
    show (3 : ℤ) - 2 = 1 from by norm_num, show (3 : ℤ) + 1 = 4 from by norm_num]
  -- preΨ(5) appears again inside preΨ(6); expand it.
  rw [show (5 : ℤ) = 2 * 2 + 1 from by norm_num, WeierstrassCurve.preΨ_odd (W := W) (2 : ℤ),
    show (2 : ℤ) + 2 = 4 from by norm_num, show (2 : ℤ) - 1 = 1 from by norm_num,
    show (2 : ℤ) + 1 = 3 from by norm_num]
  simp only [show Even (2 : ℤ) from ⟨1, by ring⟩, ite_true]
  -- Step 4: Simplify all base preΨ values to named polynomials.
  rw [WeierstrassCurve.preΨ_two, WeierstrassCurve.preΨ_one,
    WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four]
  -- Clean up 1^n, 1*, *1 residues from preΨ expansions.
  simp only [one_pow, mul_one, one_mul]
  -- Cast ℤ→F coercion in C ((4:ℤ):F).
  simp only [show ((4 : ℤ) : F) = (4 : F) from by push_cast; ring]
  -- Step 5: Use wronskian_aux_four.
  have haux := wronskian_aux_four W
  simp only [Polynomial.C_ofNat] at haux ⊢
  linear_combination haux

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The polynomial Wronskian identity for non-negative integers, by **strong induction**.

    Base cases `m = 0,1,2` use direct computation; `m = 3,4` use the factored ring identities
    (`wronskian_aux_three`, `wronskian_aux_four`). For `m = n+5` the proof is by strong induction:
    the induction hypothesis `ih` provides the identity at **all** smaller indices `k < m`.

    ## Status of the `m ≥ 5` inductive step

    The inductive step is the elliptic-divisibility-sequence (EDS) Wronskian recursion. Writing
    `p k := W.preΨ k` and `s := W.Ψ₂Sq`, and `W(k) := Φ_k' ΨSq_k − Φ_k ΨSq_k'`, the target is
    `W(k) = k · p(2k)`. The two halving recursions that drive the induction are (both verified by
    computer algebra against the actual division polynomials):

    * **Even step.** `W(2m) = 2 · complEDS₂(2m) · W(m)`, where
      `complEDS₂(2m) = p(2m-1)² p(2m+2) − p(2m-2) p(2m+1)²`. Combined with the induction hypothesis
      `W(m) = m · p(2m)` and `p(4m) = complEDS₂(2m) · p(2m)` (mathlib's `preNormEDS_mul_complEDS₂`)
      this collapses to `W(2m) = 2m · p(4m)`, i.e. the claim at `2m`. Both `m` and `m±1 < 2m`.
    * **Odd step.** The analogous reduction of `W(2m+1)` to `W(m)` and `W(m+1)`.

    The irreducible algebraic content of *each* halving step is the **EDS addition formula**
    (Ward's relation), verified by CAS in the exact form
    `p(i+j) p(i-j) = Aᵢ · p(i+1) p(i-1) p(j)² − Aⱼ · p(j+1) p(j-1) p(i)²`,
    with `Aᵢ = s²` iff (`i` odd and `j` even) else `1`, and `Aⱼ = s²` iff (`i` even and `j` odd)
    else `1`. Its `j = 2` specialisation is the Somos‑4 relation
    `p(m+2) p(m-2) = (Even m ? 1 : s²) · p(m+1) p(m-1) − Ψ₃ · p(m)²`.

    The even step `W(2m) = 2·complEDS₂(2m)·W(m)` is **not** a free-ring identity in the consecutive
    `preΨ` values alone — it is provably *false* without further relations, and is *not* closed by
    Somos‑4 together with the Weierstrass `b`-relation either: it genuinely requires the addition
    formula at general index `j`. Mathlib does not currently provide the EDS addition formula
    (only the duplication recursions `preΨ_even`/`preΨ_odd`), so closing this step needs that
    formula to be developed first. The `WronskianAux` `m = 3,4` proofs avoid it only because, at
    fixed small index, the difference factors through the single `b`-relation with an explicitly
    computed multiplier;
    that multiplier grows with the index, so the same device does not generalise.

    An **axiom-clean** alternative is available downstream of this file via the function field:
    the field-general Route-B chord induction `omegaCoeff_mulByInt`
    (`HasseWeil/RouteBGeneral.lean`) proves the differential statement `[n]*ω = n·ω`
    (Silverman III.5.3) over any field, with no EDS Wronskian; it cannot be imported here (it
    depends transitively on this file), but every former geometric consumer of the Wronskian
    (`Hasse/Separability.lean`, `PullbackCoeff.lean`) now routes through it, so this `sorry` is
    **consumer-free**. The polynomial identity itself also has an axiom-clean downstream proof:
    `wronskian_Φ_ΨSq_general` (`EC/WronskianGeneral.lean`). -/
private lemma wronskian_Φ_ΨSq_nat (m : ℕ) :
    Polynomial.derivative (W.Φ (m : ℤ)) * W.ΨSq (m : ℤ) -
      W.Φ (m : ℤ) * Polynomial.derivative (W.ΨSq (m : ℤ)) =
    Polynomial.C ((m : ℤ) : F) * W.preΨ (2 * (m : ℤ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- `ih : ∀ k < m, (the identity at k)` — the strong induction hypothesis.
    match m, ih with
    | 0, _ => exact wronskian_Φ_ΨSq_zero W
    | 1, _ => exact_mod_cast wronskian_Φ_ΨSq_one W
    | 2, _ => exact_mod_cast wronskian_Φ_ΨSq_two W
    | 3, _ => exact_mod_cast wronskian_Φ_ΨSq_three W
    | 4, _ => exact_mod_cast wronskian_Φ_ΨSq_four W
    | (n + 5), ih =>
      -- General case `m = n+5 ≥ 5`. The induction hypothesis `ih k hk` gives the identity at
      -- every `k < n+5`, in particular at the halves `⌊(n+5)/2⌋`, `⌈(n+5)/2⌉` needed by the EDS
      -- Wronskian recursion (even/odd halving step). The single missing ingredient is the EDS
      -- addition formula (see the docstring above); supplying it closes this step via
      -- `linear_combination` of the induction hypothesis at the halves with the
      -- addition-formula / Somos‑4 instances.
      sorry

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The division polynomial Wronskian identity:
    `Φ_n' · ΨSq_n - Φ_n · ΨSq_n' = n · preΨ(2n)` as polynomials in `F[X]`.

    Reference: Silverman Exercise III.3.7.

    Proved by reducing to the natural number case via `wronskian_Φ_ΨSq_neg_of`
    (negation symmetry) and `wronskian_Φ_ΨSq_nat` (positive case by induction). -/
theorem wronskian_Φ_ΨSq (n : ℤ) :
    Polynomial.derivative (W.Φ n) * W.ΨSq n - W.Φ n * Polynomial.derivative (W.ΨSq n) =
    Polynomial.C (n : F) * W.preΨ (2 * n) := by
  rcases lt_or_ge n 0 with hneg | hpos
  · -- n < 0: use negation symmetry on the positive case
    have hm : (0 : ℤ) ≤ -n := by omega
    obtain ⟨m, hm_eq⟩ := Int.eq_ofNat_of_zero_le hm
    have hn_eq : n = -(m : ℤ) := by omega
    rw [hn_eq]
    exact wronskian_Φ_ΨSq_neg_of W (wronskian_Φ_ΨSq_nat W m)
  · -- n ≥ 0: directly from wronskian_Φ_ΨSq_nat
    obtain ⟨m, hm_eq⟩ := Int.eq_ofNat_of_zero_le hpos
    subst hm_eq
    exact wronskian_Φ_ΨSq_nat W m

/-- `Φ_ff` and `ΨSq_ff` factor through `algebraMap (Polynomial F) KE`. -/
private lemma Φ_ff_eq_algebraMap_poly (n : ℤ) :
    Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n) :=
  (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm

private lemma ΨSq_ff_eq_algebraMap_poly (n : ℤ) :
    ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n) :=
  (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm

/-- **The `ω_n`/`preΨ` bridge in K(E)** (independent of the EDS Wronskian):
    `preΨ(2n) · u = ΨSq_n² · α*(u)` for `[n]`, where `α*(u) = 2·[n]*y + a₁·[n]*x + a₃`.

    This is the polynomial shadow of the third division polynomial `ω_n` and follows from the
    geometric facts `preΨ(2n)·u = ψ_n·ψc_n` (i.e. `ψ_{2n} = ψ_n·ψc_n`, `ψc_spec_ff`) and
    `α*(u) = ψc_n/ψ_n³` (`ω_spec_ff`), together with `ΨSq_ff = ψ_n²` (`ψ_ff_sq_eq`). It does **not**
    use the division-polynomial Wronskian, so it is axiom-clean and can be combined with the
    chord-recursion `omegaPullbackCoeff_mulByInt_routeB` downstream to recover the polynomial
    Wronskian. -/
theorem preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u (n : ℤ) (hn : n ≠ 0) :
    algebraMap (Polynomial F) KE (W.preΨ (2 * n)) * u_gen W =
      ΨSq_ff W n ^ 2 * alpha_star_u W (mulByInt W.toAffine n) := by
  set ψn := algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n)) with hψn_def
  set ψcn := algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) with hψcn_def
  have hψ_ne : ψn ≠ 0 := by
    rw [hψn_def]
    intro h
    exact ΨSq_ff_ne_zero' W hn ((ψ_ff_sq_eq W n).symm ▸
      show (ψ_ff W n) ^ 2 = 0 by unfold ψ_ff; rw [h]; ring)
  have h_preΨ_u : algebraMap (Polynomial F) KE (W.preΨ (2 * n)) * u_gen W = ψn * ψcn := by
    rw [hψn_def, hψcn_def, ψc_spec_ff W n, Affine.CoordinateRing.mk_ψ (W := W.toAffine) (2 * n)]
    have hΨ_eq : W.Ψ (2 * n) = Polynomial.C (W.preΨ (2 * n)) * W.ψ₂ := by
      rw [WeierstrassCurve.Ψ, if_pos (even_two_mul n)]
    rw [hΨ_eq, map_mul, map_mul,
      show W.ψ₂ = W.toAffine.polynomialY from rfl, mk_polynomialY_eq_u_gen W]
    rfl
  have h_alpha_u : alpha_star_u W (mulByInt W.toAffine n) = ψcn / ψn ^ 3 := by
    rw [alpha_star_u_mulByInt W n hn, mulByInt_y, mulByInt_x]
    have hω := ω_spec_ff W n
    rw [show (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ψ n)) = ψn from rfl] at hω
    rw [show (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) = ψcn from rfl] at hω
    rw [show ΨSq_ff W n = ψn ^ 2 from (ψ_ff_sq_eq W n).symm,
      show ψ_ff W n = ψn from rfl,
      show ω_ff W n =
        (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ω n)) from rfl]
    set ω_ff_n := (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ω n))
    have hψ3 : ψn ^ 3 ≠ 0 := pow_ne_zero 3 hψ_ne
    apply mul_right_cancel₀ hψ3
    rw [show (2 * (ω_ff_n / ψn ^ 3) + (algebraMap F KE) W.a₁ * (Φ_ff W n / ψn ^ 2) +
        (algebraMap F KE) W.a₃) * ψn ^ 3 =
        2 * ω_ff_n + (algebraMap F KE) W.a₁ * Φ_ff W n * ψn +
        (algebraMap F KE) W.a₃ * ψn ^ 3 from by field_simp,
      show ψcn / ψn ^ 3 * ψn ^ 3 = ψcn from div_mul_cancel₀ ψcn hψ3]
    exact hω
  rw [h_preΨ_u, h_alpha_u, show ΨSq_ff W n = ψn ^ 2 from (ψ_ff_sq_eq W n).symm]
  field_simp

/-- The division polynomial Wronskian identity in K(E), **parametrized** by the
    polynomial-level Wronskian identity `hpoly`.

    Reduces to `hpoly` via:
    - alpha_star_u for [n] = ψc_n/ψ_n^3 (from ω_spec)
    - ψ_n * ψc_n = ψ_{2n} (from ψc_spec)
    - ψ_{2n} = preΨ(2n) * polynomialY in R (since 2n is even)
    - mk(polynomialY) = u_gen in K(E)

    Taking `hpoly` as a hypothesis lets specific values of `n` (e.g. `n = 2`) be
    discharged from the axiom-clean per-value polynomial lemmas
    (`wronskian_Φ_ΨSq_two`, …), independently of the general `wronskian_Φ_ΨSq`.
    Reference: Silverman Exercise III.3.7, III.5.3 -/
theorem divPoly_wronskian_identity_of_poly (n : ℤ) (hn : n ≠ 0)
    (hpoly : Polynomial.derivative (W.Φ n) * W.ΨSq n -
        W.Φ n * Polynomial.derivative (W.ΨSq n) =
      Polynomial.C (n : F) * W.preΨ (2 * n)) :
    (algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) *
      ΨSq_ff W n -
    Φ_ff W n *
      algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n))) *
    u_gen W =
    algebraMap F KE n *
    ΨSq_ff W n ^ 2 *
    alpha_star_u W (mulByInt W.toAffine n) := by
  -- Lift the polynomial Wronskian identity `hpoly` to K(E), then reduce both sides to
  -- `n · ψ_n · ψc_n` via `preΨ(2n)·u = ψ_n·ψc_n` and `α*(u) = ψc_n/ψ_n³`.
  have hpoly_ff : (algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) *
        ΨSq_ff W n -
      Φ_ff W n *
        algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n))) =
      algebraMap (Polynomial F) KE (Polynomial.C (n : F) * W.preΨ (2 * n)) := by
    rw [Φ_ff_eq_algebraMap_poly, ΨSq_ff_eq_algebraMap_poly,
      ← map_mul, ← map_mul, ← map_sub, hpoly]
  rw [hpoly_ff, map_mul,
    show algebraMap (Polynomial F) KE (Polynomial.C (n : F)) =
      algebraMap F KE (n : F) from
      (IsScalarTower.algebraMap_apply F (Polynomial F) KE _).symm]
  set ψn := algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n)) with hψn_def
  set ψcn := algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) with hψcn_def
  have hψ_ne : ψn ≠ 0 := by
    rw [hψn_def]
    intro h
    exact ΨSq_ff_ne_zero' W hn ((ψ_ff_sq_eq W n).symm ▸
      show (ψ_ff W n) ^ 2 = 0 by
        unfold ψ_ff
        rw [h]; ring)
  have h_preΨ_u : algebraMap (Polynomial F) KE (W.preΨ (2 * n)) * u_gen W = ψn * ψcn := by
    rw [hψn_def, hψcn_def, ψc_spec_ff W n, Affine.CoordinateRing.mk_ψ (W := W.toAffine) (2 * n)]
    have hΨ_eq : W.Ψ (2 * n) = Polynomial.C (W.preΨ (2 * n)) * W.ψ₂ := by
      rw [WeierstrassCurve.Ψ, if_pos (even_two_mul n)]
    rw [hΨ_eq, map_mul, map_mul,
      show W.ψ₂ = W.toAffine.polynomialY from rfl, mk_polynomialY_eq_u_gen W]
    rfl
  have h_alpha_u : alpha_star_u W (mulByInt W.toAffine n) = ψcn / ψn ^ 3 := by
    rw [alpha_star_u_mulByInt W n hn, mulByInt_y, mulByInt_x]
    have hω := ω_spec_ff W n
    rw [show (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ψ n)) = ψn from rfl] at hω
    rw [show (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) = ψcn from rfl] at hω
    rw [show ΨSq_ff W n = ψn ^ 2 from (ψ_ff_sq_eq W n).symm,
      show ψ_ff W n = ψn from rfl,
      show ω_ff W n =
        (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ω n)) from rfl]
    set ω_ff_n := (algebraMap R KE) (Affine.CoordinateRing.mk W.toAffine (W.ω n))
    have hψ3 : ψn ^ 3 ≠ 0 := pow_ne_zero 3 hψ_ne
    apply mul_right_cancel₀ hψ3
    rw [show (2 * (ω_ff_n / ψn ^ 3) + (algebraMap F KE) W.a₁ * (Φ_ff W n / ψn ^ 2) +
        (algebraMap F KE) W.a₃) * ψn ^ 3 =
        2 * ω_ff_n + (algebraMap F KE) W.a₁ * Φ_ff W n * ψn +
        (algebraMap F KE) W.a₃ * ψn ^ 3 from by field_simp,
      show ψcn / ψn ^ 3 * ψn ^ 3 = ψcn from div_mul_cancel₀ ψcn hψ3]
    exact hω
  rw [show (algebraMap F KE ↑n) * (algebraMap (Polynomial F) KE (W.preΨ (2 * n))) * u_gen W =
      (algebraMap F KE ↑n) * ((algebraMap (Polynomial F) KE (W.preΨ (2 * n))) * u_gen W) from
      by ring,
    h_preΨ_u, h_alpha_u, show ΨSq_ff W n = ψn ^ 2 from (ψ_ff_sq_eq W n).symm]
  field_simp

/-- The division polynomial Wronskian identity in K(E) (general `n`), via the
    general polynomial-level identity `wronskian_Φ_ΨSq`.
    Reference: Silverman Exercise III.3.7, III.5.3 -/
theorem divPoly_wronskian_identity (n : ℤ) (hn : n ≠ 0) :
    (algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) *
      ΨSq_ff W n -
    Φ_ff W n *
      algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n))) *
    u_gen W =
    algebraMap F KE n *
    ΨSq_ff W n ^ 2 *
    alpha_star_u W (mulByInt W.toAffine n) :=
  divPoly_wronskian_identity_of_poly W n hn (wronskian_Φ_ΨSq (W := W) n)

-- Chain rule for `D` on polynomial images in K(E), using `Derivation.comp_aeval_eq`: for
-- `p : F[X]` and `a ∈ KE`, `D(aeval a p) = aeval a (derivative p) • D(a)`.

-- `DecidableEq F` is needed for the `K(E)` instance in the statement but not by the proof, so
-- the `unusedSectionVars` linter (a false positive here) is locally disabled.
set_option linter.unusedSectionVars false in
/-- `D(p(x_gen)) = p'(x_gen) • D(x_gen)` for any polynomial `p : F[X]`.
    This is the chain rule for the universal derivation applied to polynomial evaluation.
    Uses `Derivation.comp_aeval_eq` from mathlib. -/
theorem D_poly_eval (p : Polynomial F) :
    KaehlerDifferential.D F KE (algebraMap (Polynomial F) KE p) =
    algebraMap (Polynomial F) KE (Polynomial.derivative p) •
      KaehlerDifferential.D F KE (algebraMap (Polynomial F) KE Polynomial.X) := by
  set x_ff := algebraMap (Polynomial F) KE Polynomial.X
  -- algebraMap F[X] KE q = aeval x_ff q
  have haeval : ∀ q : Polynomial F,
      Polynomial.aeval x_ff q = algebraMap (Polynomial F) KE q := by
    intro q; induction q using Polynomial.induction_on' with
    | add _ _ hp hq => simp [hp, hq]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial]
      change algebraMap (Polynomial F) KE (Polynomial.C a) * x_ff ^ n =
        algebraMap (Polynomial F) KE (Polynomial.monomial n a)
      rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [← haeval, ← haeval]
  -- Apply the chain rule: D(aeval x p) = aeval x (derivative p) • D(x)
  exact @Derivation.comp_aeval_eq F KE (KaehlerDifferential F KE)
    _ _ _ _ _ _ _ x_ff (KaehlerDifferential.D F KE) p

-- (removed D_div_eq; we work directly with Leibniz + D_inv_smul in the main proof)

/-- For [n], the omega-based pullback coefficient is n, **parametrized** by the
    polynomial-level Wronskian identity `hpoly`.

    The proof reduces to the division polynomial Wronskian identity
    via the quotient rule and chain rule for the universal derivation.

    Taking `hpoly` as a hypothesis lets specific values of `n` be discharged from
    the axiom-clean per-value polynomial lemmas (`wronskian_Φ_ΨSq_two`, …),
    independently of the general `wronskian_Φ_ΨSq`. -/
theorem omegaPullbackCoeff_mulByInt_of_poly (n : ℤ) (hn : n ≠ 0)
    (hpoly : Polynomial.derivative (W.Φ n) * W.ΨSq n -
        W.Φ n * Polynomial.derivative (W.ΨSq n) =
      Polynomial.C (n : F) * W.preΨ (2 * n)) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n := by
  -- Use uniqueness in the 1-dimensional Kähler module: show `algebraMap F KE n` also satisfies
  -- the spec `c • ω = α*(u)⁻¹ • D(α*x)` that defines `omegaPullbackCoeff`.
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec]
  set D := KaehlerDifferential.D F KE
  set α := mulByInt W.toAffine n
  set u := u_gen W with hu_def
  set αu := alpha_star_u W α with hαu_def
  set Φ := Φ_ff W n with hΦ_def
  set Ψ := ΨSq_ff W n with hΨ_def
  set x_ff := algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X) with hxff_def
  have hu : u ≠ 0 := u_gen_ne_zero W
  have hΨ_ne : Ψ ≠ 0 := by
    rw [hΨ_def, ΨSq_ff]
    intro h
    have hinj : Function.Injective ((algebraMap R KE).comp (algebraMap (Polynomial F) R)) :=
      (IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective
    exact ΨSq_poly_ne_zero W hn (hinj (by
      rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero]; exact h))
  have hαu_ne : αu ≠ 0 := by
    rw [hαu_def, alpha_star_u_eq]
    exact fun h ↦ hu (α.pullback_injective (h.trans (map_zero _).symm))
  have hαx : α.pullback x_ff = Φ * Ψ⁻¹ := by
    rw [mulByInt_pullback_x W n hn, mulByInt_x, div_eq_mul_inv]
  -- Rewrite `Φ`, `Ψ`, `x_ff` as images of polynomials so the chain rule `D_poly_eval` applies.
  have hΦ_poly : Φ = algebraMap (Polynomial F) KE (W.Φ n) := by
    simp only [hΦ_def, Φ_ff,
      (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm]
  have hΨ_poly : Ψ = algebraMap (Polynomial F) KE (W.ΨSq n) := by
    simp only [hΨ_def, ΨSq_ff,
      (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm]
  have hx_poly : x_ff = algebraMap (Polynomial F) KE Polynomial.X :=
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE Polynomial.X).symm
  set Φ' := algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) with hΦ'_def
  set Ψ' := algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n)) with hΨ'_def
  have hDΦ : D Φ = Φ' • D x_ff := by rw [hΦ_poly, hx_poly]; exact D_poly_eval W _
  have hDΨ : D Ψ = Ψ' • D x_ff := by rw [hΨ_poly, hx_poly]; exact D_poly_eval W _
  have hDx : D x_ff ≠ 0 := D_x_ne_zero W.toAffine
  symm
  rw [show invariantDifferential W.toAffine = u⁻¹ • D x_ff from rfl, smul_smul, hαx]
  -- Expand `D(Φ · Ψ⁻¹)` by Leibniz (note the Lean summand order) and the chain rule, then
  -- flatten all `KE`-scalar actions on the Kähler module into a single scalar on `D x_ff`.
  rw [Derivation.leibniz, D_inv_smul W.toAffine Ψ hΨ_ne, hDΦ, hDΨ]
  simp only [smul_smul, smul_neg, smul_add]
  rw [show -((αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) • D x_ff) +
    (αu⁻¹ * (Ψ⁻¹ * Φ')) • D x_ff =
    (αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) • D x_ff from by
    rw [sub_smul, sub_eq_add_neg, add_comm]]
  congr 1
  -- `hW : (Φ' Ψ − Φ Ψ') · u = n · Ψ² · αu` (the Wronskian identity in local notation); clear
  -- denominators against `αu · Ψ² · u ≠ 0` to match the cancelled goal.
  have hW := divPoly_wronskian_identity_of_poly W n hn hpoly
  rw [← hΦ_def, ← hΨ_def, ← hΦ'_def, ← hΨ'_def, ← hu_def, ← hαu_def] at hW
  have hmul := mul_ne_zero (mul_ne_zero hαu_ne (pow_ne_zero 2 hΨ_ne)) hu
  apply mul_right_cancel₀ hmul
  have lhs_eq : algebraMap F KE ↑n * u⁻¹ * (αu * Ψ ^ 2 * u) =
    algebraMap F KE ↑n * Ψ ^ 2 * αu := by field_simp
  have rhs_eq : (αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) *
    (αu * Ψ ^ 2 * u) = (Φ' * Ψ - Φ * Ψ') * u := by field_simp
  rw [lhs_eq, rhs_eq, hW]

/-- **Reverse direction**: the K(E)-level division-polynomial Wronskian identity, derived from the
    ω-pullback coefficient `a_{[n]} = n` (rather than from the polynomial Wronskian).

    This is the converse of `omegaPullbackCoeff_mulByInt_of_poly`'s final algebra: the spec
    `a • ω = α*(u)⁻¹ • D(α*x)` together with `a = n` and the chain/quotient rule for `D` gives the
    scalar identity `(Φ' Ψ − Φ Ψ') · u = n · Ψ² · α*u` in K(E). Fed the axiom-clean
    `omegaPullbackCoeff_mulByInt_routeB` (downstream), it recovers the K(E) Wronskian — and then,
    via the bridge `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u` and injectivity of
    `algebraMap (Polynomial F) KE`, the **polynomial** Wronskian — without the EDS addition
    formula. -/
theorem divPoly_wronskian_identity_of_omega (n : ℤ) (hn : n ≠ 0)
    (homega : omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n) :
    (algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) *
      ΨSq_ff W n -
    Φ_ff W n *
      algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n))) *
    u_gen W =
    algebraMap F KE n *
    ΨSq_ff W n ^ 2 *
    alpha_star_u W (mulByInt W.toAffine n) := by
  have hspec := omegaPullbackCoeff_spec W (mulByInt W.toAffine n)
  rw [homega] at hspec
  set D := KaehlerDifferential.D F KE
  set α := mulByInt W.toAffine n
  set u := u_gen W with hu_def
  set αu := alpha_star_u W α with hαu_def
  set Φ := Φ_ff W n with hΦ_def
  set Ψ := ΨSq_ff W n with hΨ_def
  set x_ff := algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X) with hxff_def
  have hu : u ≠ 0 := u_gen_ne_zero W
  have hΨ_ne : Ψ ≠ 0 := by
    rw [hΨ_def, ΨSq_ff]
    intro h
    have hinj : Function.Injective ((algebraMap R KE).comp (algebraMap (Polynomial F) R)) :=
      (IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective
    exact ΨSq_poly_ne_zero W hn (hinj (by
      rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero]; exact h))
  have hαu_ne : αu ≠ 0 := by
    rw [hαu_def, alpha_star_u_eq]
    exact fun h ↦ hu (α.pullback_injective (h.trans (map_zero _).symm))
  have hαx : α.pullback x_ff = Φ * Ψ⁻¹ := by
    rw [mulByInt_pullback_x W n hn, mulByInt_x, div_eq_mul_inv]
  have hΦ_poly : Φ = algebraMap (Polynomial F) KE (W.Φ n) := by
    simp only [hΦ_def, Φ_ff, (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm]
  have hΨ_poly : Ψ = algebraMap (Polynomial F) KE (W.ΨSq n) := by
    simp only [hΨ_def, ΨSq_ff, (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm]
  have hx_poly : x_ff = algebraMap (Polynomial F) KE Polynomial.X :=
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE Polynomial.X).symm
  set Φ' := algebraMap (Polynomial F) KE (Polynomial.derivative (W.Φ n)) with hΦ'_def
  set Ψ' := algebraMap (Polynomial F) KE (Polynomial.derivative (W.ΨSq n)) with hΨ'_def
  have hDΦ : D Φ = Φ' • D x_ff := by rw [hΦ_poly, hx_poly]; exact D_poly_eval W _
  have hDΨ : D Ψ = Ψ' • D x_ff := by rw [hΨ_poly, hx_poly]; exact D_poly_eval W _
  have hDx : D x_ff ≠ 0 := D_x_ne_zero W.toAffine
  -- Transform hspec into the scalar identity, exactly as in `omegaPullbackCoeff_mulByInt_of_poly`.
  rw [show invariantDifferential W.toAffine = u⁻¹ • D x_ff from rfl, smul_smul, hαx,
    Derivation.leibniz, D_inv_smul W.toAffine Ψ hΨ_ne, hDΦ, hDΨ] at hspec
  simp only [smul_smul, smul_neg, smul_add] at hspec
  rw [show -((αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) • D x_ff) +
    (αu⁻¹ * (Ψ⁻¹ * Φ')) • D x_ff =
    (αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) • D x_ff from by
    rw [sub_smul, sub_eq_add_neg, add_comm]] at hspec
  -- hspec : (algebraMap F KE n * u⁻¹) • D x_ff = (αu⁻¹ * (Ψ⁻¹ * Φ') - ...) • D x_ff
  have hscalar : algebraMap F KE ↑n * u⁻¹ =
      αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ')) := by
    have hzero : (algebraMap F KE ↑n * u⁻¹ -
        (αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ')))) • D x_ff = 0 := by
      rw [sub_smul, hspec, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hDx
  -- Clear denominators to obtain the K(E) Wronskian.
  have lhs_eq : algebraMap F KE ↑n * u⁻¹ * (αu * Ψ ^ 2 * u) =
    algebraMap F KE ↑n * Ψ ^ 2 * αu := by field_simp
  have rhs_eq : (αu⁻¹ * (Ψ⁻¹ * Φ') - αu⁻¹ * (Φ * (Ψ⁻¹ ^ 2 * Ψ'))) *
    (αu * Ψ ^ 2 * u) = (Φ' * Ψ - Φ * Ψ') * u := by field_simp
  have hfin := congrArg (· * (αu * Ψ ^ 2 * u)) hscalar
  rw [lhs_eq, rhs_eq] at hfin
  -- Goal is already in the `set` names `Φ, Ψ, Φ', Ψ', u, αu`; `hfin` matches up to symmetry.
  linear_combination -hfin

/-- For [n], the omega-based pullback coefficient is n (general `n`, via the
    general polynomial-level Wronskian identity `wronskian_Φ_ΨSq`).
    Silverman III.5.3, IV.2.3.

    NOTE: this routing through `wronskian_Φ_ΨSq` inherits its `sorryAx` taint
    (the `m ≥ 5` branch of `wronskian_Φ_ΨSq_nat`). The **axiom-clean, field-general**
    proof of the same statement, via the Route-B chord recurrence (Silverman
    III.5.2/3 at the differential level), is `HasseWeil.omegaCoeff_mulByInt` in
    `HasseWeil/RouteBGeneral.lean`. That module cannot be imported here (its chord
    step lives downstream of this file), so the replacement cannot be applied in
    place — instead all former consumers (`Hasse/Separability.lean`,
    `PullbackCoeff.lean`) now route through `omegaCoeff_mulByInt`, leaving this
    theorem (and its Wronskian `sorry`) **consumer-free**. -/
theorem omegaPullbackCoeff_mulByInt (n : ℤ) (hn : n ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n :=
  omegaPullbackCoeff_mulByInt_of_poly W n hn (wronskian_Φ_ΨSq (W := W) n)

/-- **Axiom-clean base case `[2]`**: `omegaPullbackCoeff W (mulByInt 2) = 2`.

    Uses the per-value polynomial Wronskian lemma `wronskian_Φ_ΨSq_two` (a direct
    `ring` computation, axiom-clean) through `omegaPullbackCoeff_mulByInt_of_poly`,
    so it does NOT depend on the general `wronskian_Φ_ΨSq` (whose `m ≥ 5` branch
    is unproved). Seeds the Route-B chord induction (`m ≥ 3` follows from the
    chord step `omegaPullbackCoeff_mulByInt_succ`). -/
theorem omegaPullbackCoeff_mulByInt_two :
    omegaPullbackCoeff W (mulByInt W.toAffine 2) = algebraMap F KE (2 : ℤ) :=
  omegaPullbackCoeff_mulByInt_of_poly W 2 (by norm_num)
    (by simpa using wronskian_Φ_ΨSq_two W)

end HasseWeil
