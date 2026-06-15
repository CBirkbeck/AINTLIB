import HasseWeil.Curves.IntegralClosure
import HasseWeil.Curves.NormBezout
import HasseWeil.Curves.Valuation
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Localization.NormTrace

/-!
# The order at the point at infinity on a smooth plane curve

For a smooth plane curve `C` given by a Weierstrass equation over a field
`F`, the function field `F(C)` has a distinguished place "at infinity"
corresponding to the projective point `[0 : 1 : 0]`. The associated
additive valuation is the **order at infinity** `ordAtInfty : F(C) → WithTop ℤ`,
with the classical values

```
ordAtInfty(x) = -2,   ordAtInfty(y) = -3.
```

Rather than building a local ring at infinity and extracting the valuation
from its DVR structure (the approach outlined in the Phase-D ticket
`T-II-INFRA-D-001`), this file defines `ordAtInfty` algebraically via the
algebra norm `N : F(C) → F(x)`:

```
ordAtInfty(f) := - intDegree (N(f)) ∈ ℤ ∪ {∞}.
```

The rationale is that for a degree-2 extension of `F(x)`, ramified only at
the place at infinity of `ℙ¹_F` with ramification index 2 and residue
degree 1, the valuation at the unique place of `F(C)` above infinity is
related to the ℙ¹-valuation of the norm by the classical formula
`v_K(N(f)) = f_w · w(f)` with `f_w = 1`. Concretely,
`ordAtInfty(f) = ordAtInfty(N(f))` where the right-hand side is the order at
infinity on `F(x)`, computed by `- intDegree`.

This closes (partial form) ticket `T-II-INFRA-D-002`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.1 (for
  `ordAtInfty(x) = -2`, `ordAtInfty(y) = -3` on an elliptic curve);
* [Hartshorne, *Algebraic Geometry*], II.6.10 (norm approach to counting
  zeros and poles on a smooth curve).
-/

open scoped RatFunc Polynomial.Bivariate

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The algebra norm `N(f) ∈ F(x)` of `f ∈ F(C)`, packaged as a
`RatFunc F` for ease of access to `intDegree` and related API. -/
noncomputable def normAsRatFunc (f : C.FunctionField) : RatFunc F :=
  RatFunc.ofFractionRing (C.fieldNorm f)

@[simp] theorem normAsRatFunc_zero : C.normAsRatFunc 0 = 0 := by
  simp [normAsRatFunc, RatFunc.ofFractionRing_zero]

@[simp] theorem normAsRatFunc_one : C.normAsRatFunc 1 = 1 := by
  simp [normAsRatFunc, RatFunc.ofFractionRing_one]

theorem normAsRatFunc_mul (f g : C.FunctionField) :
    C.normAsRatFunc (f * g) = C.normAsRatFunc f * C.normAsRatFunc g := by
  simp [normAsRatFunc, RatFunc.ofFractionRing_mul]

theorem normAsRatFunc_eq_zero_iff (f : C.FunctionField) :
    C.normAsRatFunc f = 0 ↔ f = 0 := by
  rw [normAsRatFunc, show (0 : RatFunc F) = RatFunc.ofFractionRing 0 from
      RatFunc.ofFractionRing_zero.symm,
      Function.Injective.eq_iff (fun _ _ h => by cases h; rfl),
      C.fieldNorm_eq_zero_iff]

/-- The order of a function at the point at infinity on a Weierstrass
curve. Returns `⊤` for the zero function; otherwise returns
`- intDegree (N(f))` where `N : F(C) → F(x)` is the algebra norm.
Reference: Silverman IV.1. -/
noncomputable def ordAtInfty (f : C.FunctionField) : WithTop ℤ :=
  if f = 0 then ⊤
  else ((- RatFunc.intDegree (C.normAsRatFunc f) : ℤ) : WithTop ℤ)

@[simp] theorem ordAtInfty_zero : C.ordAtInfty 0 = ⊤ := if_pos rfl

theorem ordAtInfty_eq_top_iff (f : C.FunctionField) :
    C.ordAtInfty f = ⊤ ↔ f = 0 := by
  unfold ordAtInfty
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · simp [h]

theorem ordAtInfty_of_ne {f : C.FunctionField} (hf : f ≠ 0) :
    C.ordAtInfty f = (- RatFunc.intDegree (C.normAsRatFunc f) : ℤ) :=
  if_neg hf

/-- Multiplicativity of `ordAtInfty`: for nonzero `f, g`,
`ordAtInfty(f · g) = ordAtInfty(f) + ordAtInfty(g)`. -/
theorem ordAtInfty_mul {f g : C.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    C.ordAtInfty (f * g) = C.ordAtInfty f + C.ordAtInfty g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hNf : C.normAsRatFunc f ≠ 0 := (C.normAsRatFunc_eq_zero_iff f).not.mpr hf
  have hNg : C.normAsRatFunc g ≠ 0 := (C.normAsRatFunc_eq_zero_iff g).not.mpr hg
  rw [ordAtInfty_of_ne _ hfg, ordAtInfty_of_ne _ hf, ordAtInfty_of_ne _ hg,
    normAsRatFunc_mul, RatFunc.intDegree_mul hNf hNg, neg_add]
  exact_mod_cast rfl

/-- The order of `1` at infinity is `0`. -/
@[simp] theorem ordAtInfty_one : C.ordAtInfty (1 : C.FunctionField) = 0 := by
  rw [ordAtInfty_of_ne _ one_ne_zero, normAsRatFunc_one, RatFunc.intDegree_one]
  rfl

/-- The norm of `-1 ∈ F(C)` as a rational function: `N(-1) = (-1)^2 = 1`. -/
theorem normAsRatFunc_neg_one : C.normAsRatFunc (-1 : C.FunctionField) = 1 := by
  rw [normAsRatFunc, show (-1 : C.FunctionField) =
      algebraMap (FractionRing (Polynomial F)) C.FunctionField (-1) from by
    rw [map_neg, map_one], C.fieldNorm_algebraMap, neg_one_sq,
    RatFunc.ofFractionRing_one]

/-- The order at infinity of `-1 : F(C)` is `0`. -/
@[simp] theorem ordAtInfty_neg_one : C.ordAtInfty (-1 : C.FunctionField) = 0 := by
  have h_ne : (-1 : C.FunctionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [ordAtInfty_of_ne _ h_ne, normAsRatFunc_neg_one, RatFunc.intDegree_one]
  rfl

/-- Order is invariant under negation: `ord(-f) = ord(f)`. -/
@[simp] theorem ordAtInfty_neg (f : C.FunctionField) :
    C.ordAtInfty (-f) = C.ordAtInfty f := by
  by_cases hf : f = 0
  · simp [hf]
  · have h_neg1 : (-1 : C.FunctionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    rw [show -f = (-1 : C.FunctionField) * f from (neg_one_mul f).symm,
      C.ordAtInfty_mul h_neg1 hf, ordAtInfty_neg_one, zero_add]

/-- Powers: `ord(f^n) = n • ord f` for nonzero `f`. -/
theorem ordAtInfty_pow {f : C.FunctionField} (hf : f ≠ 0) (n : ℕ) :
    C.ordAtInfty (f ^ n) = n • C.ordAtInfty f := by
  induction n with
  | zero => rw [pow_zero, C.ordAtInfty_one, zero_smul]
  | succ k ih =>
    rw [pow_succ, C.ordAtInfty_mul (pow_ne_zero k hf) hf, ih, succ_nsmul]

/-- The norm of an inverse, on the rational-function side: for nonzero `f`,
`N(f⁻¹) = N(f)⁻¹`. Derived from multiplicativity of `fieldNorm` and that
`normAsRatFunc 1 = 1`. -/
theorem normAsRatFunc_inv {f : C.FunctionField} (hf : f ≠ 0) :
    C.normAsRatFunc (f⁻¹) = (C.normAsRatFunc f)⁻¹ := by
  have h_prod : C.normAsRatFunc (f⁻¹) * C.normAsRatFunc f = 1 := by
    rw [← C.normAsRatFunc_mul, inv_mul_cancel₀ hf, normAsRatFunc_one]
  exact eq_inv_of_mul_eq_one_left h_prod

/-- Inverse: `ord(f⁻¹) = -ord(f)`. -/
theorem ordAtInfty_inv (f : C.FunctionField) :
    C.ordAtInfty (f⁻¹) = -C.ordAtInfty f := by
  by_cases hf : f = 0
  · simp [hf]
  · have h_inv : f⁻¹ ≠ 0 := inv_ne_zero hf
    rw [ordAtInfty_of_ne _ h_inv, ordAtInfty_of_ne _ hf, C.normAsRatFunc_inv hf,
      RatFunc.intDegree_inv]
    push_cast
    rfl

/-- Division as `ord(f/g) = ord f + ord(g⁻¹)` for nonzero `g`. The `WithTop ℤ`
type lacks a direct `Sub` instance (because `ℤ` has no `Bot`), so we phrase
the formula additively. The user should combine `ordAtInfty_mul` and
`ordAtInfty_inv` for the two-line decomposition. -/
theorem ordAtInfty_div_eq_mul_inv (f : C.FunctionField) {g : C.FunctionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    C.ordAtInfty (f / g) = C.ordAtInfty f + C.ordAtInfty (g⁻¹) := by
  rw [div_eq_mul_inv, C.ordAtInfty_mul hf (inv_ne_zero hg)]

private theorem ofFractionRing_sq (r : FractionRing (Polynomial F)) :
    RatFunc.ofFractionRing (r ^ 2) = (RatFunc.ofFractionRing r : RatFunc F) ^ 2 := by
  rw [sq, RatFunc.ofFractionRing_mul, sq]

private theorem ofFractionRing_ne_zero {r : FractionRing (Polynomial F)} (hr : r ≠ 0) :
    (RatFunc.ofFractionRing r : RatFunc F) ≠ 0 :=
  fun h => hr (RatFunc.ofFractionRing_injective (h.trans RatFunc.ofFractionRing_zero.symm))

/-- For nonzero `r ∈ F(X)`, the order at infinity of its image in `F(C)` is
twice the order at infinity of `r` itself (where the latter is `-intDegree`).
This generalizes `ordAtInfty_algebraMap_F_nonzero` from constants to all of
`F(X)`. The factor of `2` comes from the fact that `F(C) → F(X)` has
ramification index `2` at infinity (the point at infinity on `E` is the
unique point above `∞ ∈ ℙ¹_F` in the `x`-projection). -/
theorem ordAtInfty_algebraMap_fracPolyX_of_ne_zero
    {r : FractionRing (Polynomial F)} (hr : r ≠ 0) :
    C.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C.FunctionField r) =
      ((- 2 * RatFunc.intDegree (RatFunc.ofFractionRing r) : ℤ) : WithTop ℤ) := by
  have h_alg_ne : algebraMap (FractionRing (Polynomial F)) C.FunctionField r ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (FractionRing (Polynomial F)) C.FunctionField)]
    exact fun h => hr <|
      FaithfulSMul.algebraMap_injective (FractionRing (Polynomial F))
        C.FunctionField h
  have hRat_ne : (RatFunc.ofFractionRing r : RatFunc F) ≠ 0 := ofFractionRing_ne_zero hr
  rw [ordAtInfty_of_ne _ h_alg_ne, normAsRatFunc, C.fieldNorm_algebraMap,
    ofFractionRing_sq, sq, RatFunc.intDegree_mul hRat_ne hRat_ne]
  congr 1
  ring

/-- For a nonzero polynomial `p ∈ F[X]`, the order at infinity of its image in
`F(C)` is `-2 · natDegree(p)`. Direct consequence of
`ordAtInfty_algebraMap_fracPolyX_of_ne_zero` + `RatFunc.intDegree_polynomial`. -/
theorem ordAtInfty_algebraMap_polynomial_of_ne_zero
    {p : Polynomial F} (hp : p ≠ 0) :
    C.ordAtInfty (algebraMap (Polynomial F) C.FunctionField p) =
      ((- 2 * p.natDegree : ℤ) : WithTop ℤ) := by
  have h_alg_eq :
      algebraMap (Polynomial F) C.FunctionField p =
      algebraMap (FractionRing (Polynomial F)) C.FunctionField
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) :=
    IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
      C.FunctionField p
  have hp_alg : algebraMap (Polynomial F) (FractionRing (Polynomial F)) p ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial F) (FractionRing (Polynomial F)))]
    exact fun h => hp <| FaithfulSMul.algebraMap_injective
      (Polynomial F) (FractionRing (Polynomial F)) h
  rw [h_alg_eq, C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hp_alg,
    RatFunc.ofFractionRing_algebraMap, RatFunc.intDegree_polynomial]

/-- **natDegree variant** of mathlib's `Affine.CoordinateRing.degree_norm_smul_basis`:
for `p, q ∈ F[X]` both nonzero, `(N(p · 1 + q · Y)).natDegree = max(2·natDeg p, 2·natDeg q + 3)`. -/
theorem natDegree_norm_smul_basis_of_both_ne_zero
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm (Polynomial F) (p • (1 : C.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)))).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h_deg := WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis
    (W' := C.toAffine) p q
  have hp_deg : p.degree = (p.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hp
  have hq_deg : q.degree = (q.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hq
  rw [hp_deg, hq_deg] at h_deg
  have h_lhs : (2 : ℕ) • (p.natDegree : WithBot ℕ) = ((2 * p.natDegree : ℕ) : WithBot ℕ) := by
    rw [nsmul_eq_mul]
    push_cast
    rfl
  have h_rhs : (2 : ℕ) • (q.natDegree : WithBot ℕ) + 3 =
      ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
    rw [nsmul_eq_mul]
    push_cast
    rfl
  rw [h_lhs, h_rhs] at h_deg
  have h_max : (max ((2 * p.natDegree : ℕ) : WithBot ℕ) ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ)) =
      ((max (2 * p.natDegree) (2 * q.natDegree + 3) : ℕ) : WithBot ℕ) :=
    (WithBot.coe_max (2 * p.natDegree) (2 * q.natDegree + 3)).symm
  rw [h_max] at h_deg
  exact Polynomial.natDegree_eq_of_degree_eq_some h_deg

/-- The coordinate ring `F[C]` is a free module over `F[X]`. -/
noncomputable instance coordinateRing_free_over_polynomialX :
    Module.Free (Polynomial F) C.CoordinateRing :=
  Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine)

/-- The coordinate function `x` has order `-2` at the point at infinity.
Reference: Silverman IV.1. -/
theorem ordAtInfty_coordX : C.ordAtInfty C.coordX = ((-2 : ℤ) : WithTop ℤ) := by
  have hne : C.coordX ≠ 0 := C.coordX_ne_zero
  have hXRat_ne : algebraMap (Polynomial F) (RatFunc F) Polynomial.X ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial F) (RatFunc F))]
    exact fun h => Polynomial.X_ne_zero <|
      FaithfulSMul.algebraMap_injective (Polynomial F) (RatFunc F) h
  have h_coordX :
      C.coordX = algebraMap (FractionRing (Polynomial F)) C.FunctionField
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) := by
    rw [coordX, IsScalarTower.algebraMap_apply (Polynomial F)
      (FractionRing (Polynomial F)) C.FunctionField]
  rw [ordAtInfty_of_ne _ hne, normAsRatFunc, h_coordX, C.fieldNorm_algebraMap,
    ofFractionRing_sq, RatFunc.ofFractionRing_algebraMap, sq,
    RatFunc.intDegree_mul hXRat_ne hXRat_ne,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_X]
  rfl

private noncomputable def weierstrassCubic : Polynomial F :=
  Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
    Polynomial.C C.toAffine.a₄ * Polynomial.X + Polynomial.C C.toAffine.a₆

private theorem weierstrassCubic_natDegree : C.weierstrassCubic.natDegree = 3 := by
  unfold weierstrassCubic
  compute_degree!

private theorem weierstrassCubic_ne_zero : C.weierstrassCubic ≠ 0 := by
  intro h
  have := C.weierstrassCubic_natDegree
  rw [h, Polynomial.natDegree_zero] at this
  exact absurd this (by decide)

private theorem algebraNorm_coordY_eq :
    Algebra.norm (Polynomial F)
      (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine 1) =
        - C.weierstrassCubic := by
  have h := WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis
    (W' := C.toAffine) (0 : Polynomial F) (1 : Polynomial F)
  rw [zero_smul, zero_add, one_smul,
    WeierstrassCurve.Affine.CoordinateRing.basis_one] at *
  rw [h]
  unfold weierstrassCubic
  ring

/-- The coordinate function `y` has order `-3` at the point at infinity.
Reference: Silverman IV.1. -/
theorem ordAtInfty_coordY : C.ordAtInfty C.coordY = ((-3 : ℤ) : WithTop ℤ) := by
  have hne : C.coordY ≠ 0 := C.coordY_ne_zero
  rw [ordAtInfty_of_ne _ hne, normAsRatFunc, coordY, fieldNorm,
    Algebra.norm_localization (Polynomial F) (nonZeroDivisors (Polynomial F)),
    algebraNorm_coordY_eq, map_neg, RatFunc.ofFractionRing_neg,
    RatFunc.intDegree_neg, RatFunc.ofFractionRing_algebraMap,
    RatFunc.intDegree_polynomial, weierstrassCubic_natDegree]
  rfl

/-- For `u ∈ C.CoordinateRing` viewed in `F(C)`, the order at infinity is
`-natDegree(Algebra.norm_{F[X]} u)` (returning `⊤` when `u = 0`). This is
the bridge between the `RatFunc.intDegree`-based `ordAtInfty` on the
function field and the explicit polynomial-degree formula at the
coordinate-ring level. -/
theorem ordAtInfty_algebraMap_coordinateRing (u : C.CoordinateRing)
    (hu : u ≠ 0) :
    C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u) =
      ((-(Algebra.norm (Polynomial F) u).natDegree : ℤ) : WithTop ℤ) := by
  have hne : algebraMap C.CoordinateRing C.FunctionField u ≠ 0 := fun h =>
    hu ((IsFractionRing.injective C.CoordinateRing C.FunctionField)
      (h.trans (map_zero _).symm))
  rw [ordAtInfty_of_ne _ hne, normAsRatFunc, fieldNorm,
    Algebra.norm_localization (Polynomial F) (nonZeroDivisors (Polynomial F)),
    RatFunc.ofFractionRing_algebraMap, RatFunc.intDegree_polynomial]

/-- **Constants have `ordAtInfty = 0`**: for `c : F` with `c ≠ 0`, the image
`algebraMap F C.FunctionField c` has order 0 at infinity. Chain:
lift `c` through the scalar tower `F → F[X] → F[C] → F(C)`, apply
`ordAtInfty_algebraMap_coordinateRing` with `u = algebraMap F C[C] c`, and
compute `Algebra.norm F[X] u = (C c)^2` via `Algebra.norm_algebraMap`;
`natDegree ((C c)^2) = 0`. -/
theorem ordAtInfty_algebraMap_F_nonzero {c : F} (hc : c ≠ 0) :
    C.ordAtInfty (algebraMap F C.FunctionField c) = 0 := by
  have h_lift : (algebraMap F C.FunctionField c) =
      algebraMap C.CoordinateRing C.FunctionField
        (algebraMap F C.CoordinateRing c) :=
    IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField c
  have hu_ne : (algebraMap F C.CoordinateRing c) ≠ 0 := fun h => hc <|
    FaithfulSMul.algebraMap_injective F C.CoordinateRing
      (h.trans (map_zero _).symm)
  rw [h_lift, C.ordAtInfty_algebraMap_coordinateRing _ hu_ne]
  have hnorm :
      Algebra.norm (Polynomial F) (algebraMap F C.CoordinateRing c) =
        Polynomial.C c ^ 2 := by
    rw [show (algebraMap F C.CoordinateRing c : C.CoordinateRing) =
        algebraMap (Polynomial F) C.CoordinateRing
          (Polynomial.C c) from by
      rw [IsScalarTower.algebraMap_apply F (Polynomial F) C.CoordinateRing c]
      rfl]
    have h_card : Fintype.card (Fin 2) = 2 := by decide
    rw [← h_card]
    exact Algebra.norm_algebraMap_of_basis
      (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine) (Polynomial.C c)
  rw [hnorm, show ((Polynomial.C c ^ 2 : Polynomial F)).natDegree = 0 from by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C, Nat.mul_zero]]
  rfl

/-- **Basis decomposition for `ordAtInfty` at the coordinate-ring level**:
for `p, q ∈ F[X]` both nonzero,
`ord(algebraMap (p • 1 + q • Y)) = -max(2·natDeg p, 2·natDeg q + 3)`.

This is the polynomial-level analog of the desired non-archimedean formula:
`ord(p · 1 + q · Y) = min(2 v_∞(p), 2 v_∞(q) - 3)`. The corresponding
`FractionRing F[X]`-level lemma `ordAtInfty_basis_fracPolyX` lifts this via
`Algebra.norm_localization`. -/
theorem ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField
      (p • (1 : C.CoordinateRing) +
       q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
         (Polynomial.X : Polynomial (Polynomial F)))) =
      ((-(max (2 * p.natDegree) (2 * q.natDegree + 3) : ℕ) : ℤ) : WithTop ℤ) := by
  have h_norm := C.natDegree_norm_smul_basis_of_both_ne_zero hp hq
  have h_max_pos : 0 < max (2 * p.natDegree) (2 * q.natDegree + 3) := by
    apply lt_max_of_lt_right; omega
  have h_norm_ne : (Algebra.norm (Polynomial F) (p • (1 : C.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)))) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at h_norm
    omega
  have h_smul_ne_zero : p • (1 : C.CoordinateRing) +
      q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)) ≠ 0 := fun h =>
    h_norm_ne (by rw [h, Algebra.norm_zero])
  rw [C.ordAtInfty_algebraMap_coordinateRing _ h_smul_ne_zero, h_norm]

/-- Helper: `algebraMap` of `(p • 1 + q • mk Y)` from `C.CoordinateRing` to
`C.FunctionField` equals `algebraMap p + algebraMap q * coordYInFunctionField`.
Used to bridge the smul-basis form (in `C.CoordinateRing`) with the additive
form (in `C.FunctionField`). -/
theorem algebraMap_smul_basis_eq
    (p q : Polynomial F) :
    algebraMap C.CoordinateRing C.FunctionField
      (p • (1 : C.CoordinateRing) +
       q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
         (Polynomial.X : Polynomial (Polynomial F))) =
      algebraMap (Polynomial F) C.FunctionField p +
      algebraMap (Polynomial F) C.FunctionField q * C.coordYInFunctionField := by
  rw [show p • (1 : C.CoordinateRing) =
        algebraMap (Polynomial F) C.CoordinateRing p * 1 from Algebra.smul_def p 1,
    show q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)) =
      algebraMap (Polynomial F) C.CoordinateRing q *
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)) from Algebra.smul_def q _,
    map_add, map_mul, map_mul, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) C.CoordinateRing C.FunctionField]
  rfl

/-- **Polynomial-coefficient basis decomposition for `ordAtInfty`**:
for `p, q ∈ F[X]` both nonzero,
`ord(algebraMap p + algebraMap q * coordYInFunctionField) =
  -max(2·natDeg p, 2·natDeg q + 3)`.

This is the additive form of `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`,
combining it with `algebraMap_smul_basis_eq`. -/
theorem ordAtInfty_basis_polynomial_of_both_ne_zero
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    C.ordAtInfty
      (algebraMap (Polynomial F) C.FunctionField p +
       algebraMap (Polynomial F) C.FunctionField q * C.coordYInFunctionField) =
      ((-(max (2 * p.natDegree) (2 * q.natDegree + 3) : ℕ) : ℤ) : WithTop ℤ) := by
  rw [← C.algebraMap_smul_basis_eq p q]
  exact C.ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero hp hq

private theorem intDegree_ofFractionRing_eq_of_surj
    {r : FractionRing (Polynomial F)} {p d : Polynomial F}
    (hp : p ≠ 0) (hd : d ≠ 0)
    (h : r * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d =
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) :
    (RatFunc.ofFractionRing r : RatFunc F).intDegree =
      (p.natDegree : ℤ) - (d.natDegree : ℤ) := by
  have hd_alg_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial F) (FractionRing (Polynomial F)))]
    exact fun heq => hd (FaithfulSMul.algebraMap_injective _ _ heq)
  have hr_eq : r = algebraMap (Polynomial F) (FractionRing (Polynomial F)) p *
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hd_alg_ne]; exact h
  have hofD_ne : (RatFunc.ofFractionRing (algebraMap (Polynomial F)
      (FractionRing (Polynomial F)) d) : RatFunc F) ≠ 0 := by
    rw [RatFunc.ofFractionRing_algebraMap]
    intro heq
    apply hd
    exact FaithfulSMul.algebraMap_injective (Polynomial F) (RatFunc F)
      (heq.trans (map_zero _).symm)
  have hofP_ne : (RatFunc.ofFractionRing (algebraMap (Polynomial F)
      (FractionRing (Polynomial F)) p) : RatFunc F) ≠ 0 := by
    rw [RatFunc.ofFractionRing_algebraMap]
    intro heq
    apply hp
    exact FaithfulSMul.algebraMap_injective (Polynomial F) (RatFunc F)
      (heq.trans (map_zero _).symm)
  have h_of_r : (RatFunc.ofFractionRing r : RatFunc F) =
      (RatFunc.ofFractionRing (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)) p) : RatFunc F) *
      (RatFunc.ofFractionRing (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)) d) : RatFunc F)⁻¹ := by
    rw [hr_eq, RatFunc.ofFractionRing_mul, RatFunc.ofFractionRing_inv]
  rw [h_of_r, RatFunc.intDegree_mul hofP_ne (inv_ne_zero hofD_ne),
    RatFunc.intDegree_inv, RatFunc.ofFractionRing_algebraMap,
    RatFunc.ofFractionRing_algebraMap, RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

/-- **FractionRing-coefficient basis decomposition for `ordAtInfty`**: for
`r₁, r₂ ∈ FractionRing F[X]` both nonzero, the order at infinity of
`r₁ + r₂ · coordY` equals `min(-2·intDeg r₁, -2·intDeg r₂ - 3)`.

This is the non-archimedean precursor at the K-coefficient level. The min
is uniquely achieved (parity: even vs odd), so the cross term in the
algebra norm vanishes. -/
theorem ordAtInfty_basis_fracPolyX_of_both_ne_zero
    {r₁ r₂ : FractionRing (Polynomial F)} (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    C.ordAtInfty
      (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₁ +
       algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂ *
         C.coordYInFunctionField) =
      ((min (- 2 * (RatFunc.ofFractionRing r₁ : RatFunc F).intDegree)
            (- 2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree - 3) : ℤ)
        : WithTop ℤ) := by
  obtain ⟨⟨p₁, ⟨d₁, hd₁_mem⟩⟩, h₁⟩ :=
    IsLocalization.surj (nonZeroDivisors (Polynomial F)) r₁
  obtain ⟨⟨p₂, ⟨d₂, hd₂_mem⟩⟩, h₂⟩ :=
    IsLocalization.surj (nonZeroDivisors (Polynomial F)) r₂
  have hd₁_ne : d₁ ≠ 0 := nonZeroDivisors.ne_zero hd₁_mem
  have hd₂_ne : d₂ ≠ 0 := nonZeroDivisors.ne_zero hd₂_mem
  have hd₁_alg_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d₁ ≠ 0 :=
    fun h => hd₁_ne (FaithfulSMul.algebraMap_injective _ _ (h.trans (map_zero _).symm))
  have hd₂_alg_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d₂ ≠ 0 :=
    fun h => hd₂_ne (FaithfulSMul.algebraMap_injective _ _ (h.trans (map_zero _).symm))
  have hp₁_ne : p₁ ≠ 0 := by
    intro hp; apply hr₁
    have h_zero : r₁ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d₁ = 0 := by
      rw [h₁, hp, map_zero]
    rcases mul_eq_zero.mp h_zero with h | h
    · exact h
    · exact absurd h hd₁_alg_ne
  have hp₂_ne : p₂ ≠ 0 := by
    intro hp; apply hr₂
    have h_zero : r₂ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d₂ = 0 := by
      rw [h₂, hp, map_zero]
    rcases mul_eq_zero.mp h_zero with h | h
    · exact h
    · exact absurd h hd₂_alg_ne
  set d : Polynomial F := d₁ * d₂ with hd_def
  set p₁' : Polynomial F := p₁ * d₂ with hp₁'_def
  set p₂' : Polynomial F := p₂ * d₁ with hp₂'_def
  have hd_ne : d ≠ 0 := mul_ne_zero hd₁_ne hd₂_ne
  have hp₁'_ne : p₁' ≠ 0 := mul_ne_zero hp₁_ne hd₂_ne
  have hp₂'_ne : p₂' ≠ 0 := mul_ne_zero hp₂_ne hd₁_ne
  have hd_alg_ne : algebraMap (Polynomial F) (FractionRing (Polynomial F)) d ≠ 0 :=
    fun h => hd_ne (FaithfulSMul.algebraMap_injective _ _ (h.trans (map_zero _).symm))
  have h₁' : r₁ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) p₁' := by
    rw [hd_def, hp₁'_def, map_mul, ← mul_assoc, h₁, ← map_mul]
  have h₂' : r₂ * algebraMap (Polynomial F) (FractionRing (Polynomial F)) d =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) p₂' := by
    rw [hd_def, hp₂'_def, map_mul, mul_comm (algebraMap _ _ d₁) (algebraMap _ _ d₂),
      ← mul_assoc, h₂, ← map_mul]
  have hd_KE_ne : algebraMap (Polynomial F) C.FunctionField d ≠ 0 := by
    rw [show (algebraMap (Polynomial F) C.FunctionField d) =
        algebraMap (FractionRing (Polynomial F)) C.FunctionField
          (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) from
      IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
        C.FunctionField d]
    intro hh
    apply hd_alg_ne
    exact FaithfulSMul.algebraMap_injective (FractionRing (Polynomial F)) C.FunctionField
      (hh.trans (map_zero _).symm)
  set f : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField r₁ +
    algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂ *
      C.coordYInFunctionField with hf_def
  have h_lift : algebraMap (Polynomial F) C.FunctionField d * f =
      algebraMap C.CoordinateRing C.FunctionField
        (p₁' • (1 : C.CoordinateRing) +
         p₂' • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
           (Polynomial.X : Polynomial (Polynomial F))) := by
    rw [C.algebraMap_smul_basis_eq p₁' p₂', hf_def, mul_add]
    have h_left : algebraMap (Polynomial F) C.FunctionField d *
        algebraMap (FractionRing (Polynomial F)) C.FunctionField r₁ =
        algebraMap (Polynomial F) C.FunctionField p₁' := by
      rw [show algebraMap (Polynomial F) C.FunctionField d =
          algebraMap (FractionRing (Polynomial F)) C.FunctionField
            (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) from
        IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField d,
        ← map_mul, mul_comm, h₁',
        ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField p₁']
    have h_right : algebraMap (Polynomial F) C.FunctionField d *
        (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂ *
         C.coordYInFunctionField) =
        algebraMap (Polynomial F) C.FunctionField p₂' * C.coordYInFunctionField := by
      rw [← mul_assoc,
        show algebraMap (Polynomial F) C.FunctionField d =
          algebraMap (FractionRing (Polynomial F)) C.FunctionField
            (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) from
        IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField d,
        ← map_mul,
        mul_comm (algebraMap (Polynomial F) (FractionRing (Polynomial F)) d) r₂,
        h₂', ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F))
          C.FunctionField p₂']
    rw [h_left, h_right]
  have hu_ne : p₁' • (1 : C.CoordinateRing) +
      p₂' • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.X : Polynomial (Polynomial F)) ≠ 0 := by
    intro h
    have h_norm := C.natDegree_norm_smul_basis_of_both_ne_zero hp₁'_ne hp₂'_ne
    rw [h, Algebra.norm_zero, Polynomial.natDegree_zero] at h_norm
    have h_max_pos : 0 < max (2 * p₁'.natDegree) (2 * p₂'.natDegree + 3) := by
      apply lt_max_of_lt_right; omega
    omega
  have hf_ne : f ≠ 0 := by
    intro h
    apply hu_ne
    have h_alg_zero : algebraMap C.CoordinateRing C.FunctionField (p₁' • (1 : C.CoordinateRing) +
        p₂' • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
          (Polynomial.X : Polynomial (Polynomial F))) = 0 := by
      rw [← h_lift, h, mul_zero]
    exact (IsFractionRing.injective C.CoordinateRing C.FunctionField)
      (h_alg_zero.trans (map_zero _).symm)
  have h_ord_lhs : C.ordAtInfty (algebraMap (Polynomial F) C.FunctionField d * f) =
      C.ordAtInfty (algebraMap (Polynomial F) C.FunctionField d) + C.ordAtInfty f :=
    C.ordAtInfty_mul hd_KE_ne hf_ne
  have h_ord_rhs := C.ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero hp₁'_ne hp₂'_ne
  have h_ord_d := C.ordAtInfty_algebraMap_polynomial_of_ne_zero hd_ne
  rw [h_lift, h_ord_rhs] at h_ord_lhs
  rw [h_ord_d] at h_ord_lhs
  have h_intDeg_r₁ := intDegree_ofFractionRing_eq_of_surj hp₁'_ne hd_ne h₁'
  have h_intDeg_r₂ := intDegree_ofFractionRing_eq_of_surj hp₂'_ne hd_ne h₂'
  have h_p₁'_natDeg : p₁'.natDegree = p₁.natDegree + d₂.natDegree := by
    rw [hp₁'_def, Polynomial.natDegree_mul hp₁_ne hd₂_ne]
  have h_p₂'_natDeg : p₂'.natDegree = p₂.natDegree + d₁.natDegree := by
    rw [hp₂'_def, Polynomial.natDegree_mul hp₂_ne hd₁_ne]
  have h_d_natDeg : d.natDegree = d₁.natDegree + d₂.natDegree := by
    rw [hd_def, Polynomial.natDegree_mul hd₁_ne hd₂_ne]
  have h_arith_int :
      (-(max (2 * p₁'.natDegree) (2 * p₂'.natDegree + 3) : ℕ) : ℤ) =
      -2 * (d.natDegree : ℤ) +
      min (- 2 * (RatFunc.ofFractionRing r₁ : RatFunc F).intDegree)
          (- 2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree - 3) := by
    rw [h_p₁'_natDeg, h_p₂'_natDeg, h_d_natDeg, h_intDeg_r₁, h_intDeg_r₂]
    push_cast
    omega
  have h_arith_lifted :
      ((-(max (2 * p₁'.natDegree) (2 * p₂'.natDegree + 3) : ℕ) : ℤ) : WithTop ℤ) =
      (((-2 * (d.natDegree : ℤ)) +
        min (- 2 * (RatFunc.ofFractionRing r₁ : RatFunc F).intDegree)
            (- 2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree - 3) : ℤ)
        : WithTop ℤ) := by exact_mod_cast h_arith_int
  rw [WithTop.coe_add] at h_arith_lifted
  have h_combined := h_ord_lhs.symm.trans h_arith_lifted
  rw [hf_def] at h_combined ⊢
  exact WithTop.add_left_cancel
    (show ((-2 * (d.natDegree : ℤ) : ℤ) : WithTop ℤ) ≠ ⊤ from WithTop.coe_ne_top)
    h_combined

/-- `coordY` and `coordYInFunctionField` are the same element of `K(C)`.
Both are the image of `AdjoinRoot.root W.polynomial = mk W' Y` (mathlib's
`basis_one`) under the algebraMap. -/
theorem coordY_eq_coordYInFunctionField : C.coordY = C.coordYInFunctionField := by
  unfold coordY coordYInFunctionField
  congr 1
  exact WeierstrassCurve.Affine.CoordinateRing.basis_one (W' := C.toAffine)

/-- `coordYInFunctionField` is nonzero (since `coordY` is). -/
theorem coordYInFunctionField_ne_zero : C.coordYInFunctionField ≠ 0 := by
  rw [← C.coordY_eq_coordYInFunctionField]; exact C.coordY_ne_zero

/-- `ord_∞(coordYInFunctionField) = -3`. -/
@[simp] theorem ordAtInfty_coordYInFunctionField :
    C.ordAtInfty C.coordYInFunctionField = ((-3 : ℤ) : WithTop ℤ) := by
  rw [← C.coordY_eq_coordYInFunctionField]; exact C.ordAtInfty_coordY

/-- **Unified basis decomposition for `ordAtInfty`** (handles zero coefficients):
for any `r₁, r₂ ∈ FractionRing F[X]`,
`ord(algebraMap r₁ + algebraMap r₂ · coordY) =
  min(ord(algebraMap r₁), ord(algebraMap r₂) + ord(coordY))`. -/
theorem ordAtInfty_basis_eq_min (r₁ r₂ : FractionRing (Polynomial F)) :
    C.ordAtInfty
      (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₁ +
       algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂ *
         C.coordYInFunctionField) =
      min (C.ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₁))
          (C.ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂) +
           C.ordAtInfty C.coordYInFunctionField) := by
  by_cases hr₁ : r₁ = 0
  · by_cases hr₂ : r₂ = 0
    · subst hr₁; subst hr₂
      simp [ordAtInfty_zero]
    · subst hr₁
      have ha₂_ne : algebraMap (FractionRing (Polynomial F)) C.FunctionField r₂ ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (FractionRing (Polynomial F)) C.FunctionField)]
        exact fun h => hr₂ (FaithfulSMul.algebraMap_injective _ _ h)
      rw [map_zero, zero_add, C.ordAtInfty_mul ha₂_ne C.coordYInFunctionField_ne_zero,
        show C.ordAtInfty 0 = (⊤ : WithTop ℤ) from C.ordAtInfty_zero]
      exact (min_eq_right le_top).symm
  · by_cases hr₂ : r₂ = 0
    · subst hr₂
      rw [map_zero, zero_mul, add_zero,
        show C.ordAtInfty (0 : C.FunctionField) = (⊤ : WithTop ℤ) from C.ordAtInfty_zero,
        ordAtInfty_coordYInFunctionField,
        show (⊤ : WithTop ℤ) + ((-3 : ℤ) : WithTop ℤ) = ⊤ from top_add _]
      exact (min_eq_left le_top).symm
    · rw [C.ordAtInfty_basis_fracPolyX_of_both_ne_zero hr₁ hr₂,
        C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr₁,
        C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr₂,
        ordAtInfty_coordYInFunctionField]
      rw [show ((-2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree : ℤ) : WithTop ℤ) +
            ((-3 : ℤ) : WithTop ℤ) =
          (((-2 * (RatFunc.ofFractionRing r₂ : RatFunc F).intDegree - 3) : ℤ) : WithTop ℤ) from by
        rw [← WithTop.coe_add]; push_cast; rfl]
      exact_mod_cast rfl

/-- Non-archimedean inequality for elements coming from `FractionRing F[X]`:
`min(ord(algebraMap p), ord(algebraMap q)) ≤ ord(algebraMap p + algebraMap q)`.

This is the F(X) non-archimedean inequality (`RatFunc.intDegree_add_le`)
lifted through the algebraMap to F(C). Key intermediate for the full
non-archimedean inequality on F(C). -/
theorem ordAtInfty_algebraMap_fracPolyX_add_ge_min (p q : FractionRing (Polynomial F)) :
    min (C.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C.FunctionField p))
        (C.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C.FunctionField q)) ≤
      C.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C.FunctionField p +
                    algebraMap (FractionRing (Polynomial F)) C.FunctionField q) := by
  rw [← map_add]
  by_cases hpq : p + q = 0
  · rw [hpq, map_zero, ordAtInfty_zero]; exact le_top
  · by_cases hp : p = 0
    · subst hp
      rw [zero_add, map_zero, ordAtInfty_zero]
      exact min_le_right _ _
    · by_cases hq : q = 0
      · subst hq
        rw [add_zero, map_zero, ordAtInfty_zero]
        exact min_le_left _ _
      · have hofR_ne_p : (RatFunc.ofFractionRing p : RatFunc F) ≠ 0 := ofFractionRing_ne_zero hp
        have hofR_ne_q : (RatFunc.ofFractionRing q : RatFunc F) ≠ 0 := ofFractionRing_ne_zero hq
        have hofR_ne_pq : (RatFunc.ofFractionRing (p + q) : RatFunc F) ≠ 0 :=
          ofFractionRing_ne_zero hpq
        rw [C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hp,
          C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hq,
          C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hpq]
        have h_add_le := RatFunc.intDegree_add_le (x := (RatFunc.ofFractionRing p : RatFunc F))
          (y := (RatFunc.ofFractionRing q : RatFunc F)) hofR_ne_q (by
            rw [← RatFunc.ofFractionRing_add]
            exact hofR_ne_pq)
        rw [← RatFunc.ofFractionRing_add] at h_add_le
        have h_int : min (- 2 * (RatFunc.ofFractionRing p : RatFunc F).intDegree)
                (- 2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree) ≤
            -2 * (RatFunc.ofFractionRing (p + q) : RatFunc F).intDegree := by
          rcases le_max_iff.mp h_add_le with h | h
          · calc min (- 2 * (RatFunc.ofFractionRing p : RatFunc F).intDegree)
                     (- 2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree)
                ≤ -2 * (RatFunc.ofFractionRing p : RatFunc F).intDegree :=
                  min_le_left _ _
              _ ≤ -2 * (RatFunc.ofFractionRing (p + q) : RatFunc F).intDegree := by
                  linarith
          · calc min (- 2 * (RatFunc.ofFractionRing p : RatFunc F).intDegree)
                     (- 2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree)
                ≤ -2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree :=
                  min_le_right _ _
              _ ≤ -2 * (RatFunc.ofFractionRing (p + q) : RatFunc F).intDegree := by
                  linarith
        exact_mod_cast h_int

/-- **Non-archimedean inequality for `ordAtInfty`** (T-ORD-ARITH-12):
for any `f, g ∈ F(C)`, `min(ord f, ord g) ≤ ord(f + g)`.

Proof: decompose via `exists_decomp`, apply `ordAtInfty_basis_eq_min` for ord
of f, g, f+g, and combine via the K-level non-archimedean
(`ordAtInfty_algebraMap_fracPolyX_add_ge_min`). -/
theorem ordAtInfty_add_ge_min (f g : C.FunctionField) :
    min (C.ordAtInfty f) (C.ordAtInfty g) ≤ C.ordAtInfty (f + g) := by
  obtain ⟨p₁, q₁, hf⟩ := C.exists_decomp f
  obtain ⟨p₂, q₂, hg⟩ := C.exists_decomp g
  set α₁ : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField p₁
  set α₂ : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField p₂
  set β₁ : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField q₁
  set β₂ : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField q₂
  have h_eq_f : f = α₁ + β₁ * C.coordYInFunctionField := by
    rw [hf, Algebra.smul_def, mul_one, Algebra.smul_def]
  have h_eq_g : g = α₂ + β₂ * C.coordYInFunctionField := by
    rw [hg, Algebra.smul_def, mul_one, Algebra.smul_def]
  have h_eq_sum : f + g = (α₁ + α₂) + (β₁ + β₂) * C.coordYInFunctionField := by
    rw [h_eq_f, h_eq_g]; ring
  have h_ord_f : C.ordAtInfty f = min (C.ordAtInfty α₁)
      (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField) := by
    rw [h_eq_f]; exact C.ordAtInfty_basis_eq_min p₁ q₁
  have h_ord_g : C.ordAtInfty g = min (C.ordAtInfty α₂)
      (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) := by
    rw [h_eq_g]; exact C.ordAtInfty_basis_eq_min p₂ q₂
  have h_ord_sum : C.ordAtInfty (f + g) = min (C.ordAtInfty (α₁ + α₂))
      (C.ordAtInfty (β₁ + β₂) + C.ordAtInfty C.coordYInFunctionField) := by
    rw [h_eq_sum, show α₁ + α₂ =
        algebraMap (FractionRing (Polynomial F)) C.FunctionField (p₁ + p₂) from
      (map_add _ _ _).symm,
      show β₁ + β₂ =
        algebraMap (FractionRing (Polynomial F)) C.FunctionField (q₁ + q₂) from
      (map_add _ _ _).symm]
    exact C.ordAtInfty_basis_eq_min (p₁ + p₂) (q₁ + q₂)
  rw [h_ord_f, h_ord_g, h_ord_sum]
  have h_α : min (C.ordAtInfty α₁) (C.ordAtInfty α₂) ≤ C.ordAtInfty (α₁ + α₂) :=
    C.ordAtInfty_algebraMap_fracPolyX_add_ge_min p₁ p₂
  have h_β : min (C.ordAtInfty β₁) (C.ordAtInfty β₂) ≤ C.ordAtInfty (β₁ + β₂) :=
    C.ordAtInfty_algebraMap_fracPolyX_add_ge_min q₁ q₂
  have h_β' : min (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField)
                  (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) ≤
      C.ordAtInfty (β₁ + β₂) + C.ordAtInfty C.coordYInFunctionField := by
    have h_min_add : min (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField)
                        (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) =
        min (C.ordAtInfty β₁) (C.ordAtInfty β₂) +
        C.ordAtInfty C.coordYInFunctionField := by
      rcases le_total (C.ordAtInfty β₁) (C.ordAtInfty β₂) with h | h
      · have h1 : min (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField)
            (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) =
            C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField :=
          min_eq_left (add_le_add_left h _)
        rw [h1, min_eq_left h]
      · have h2 : min (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField)
            (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) =
            C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField :=
          min_eq_right (add_le_add_left h _)
        rw [h2, min_eq_right h]
    rw [h_min_add]
    exact add_le_add_left h_β _
  refine le_min ?_ ?_
  · calc min (min (C.ordAtInfty α₁) _) (min (C.ordAtInfty α₂) _)
        ≤ min (C.ordAtInfty α₁) (C.ordAtInfty α₂) :=
          min_le_min (min_le_left _ _) (min_le_left _ _)
      _ ≤ C.ordAtInfty (α₁ + α₂) := h_α
  · calc min (min _ (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField))
             (min _ (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField))
        ≤ min (C.ordAtInfty β₁ + C.ordAtInfty C.coordYInFunctionField)
              (C.ordAtInfty β₂ + C.ordAtInfty C.coordYInFunctionField) :=
          min_le_min (min_le_right _ _) (min_le_right _ _)
      _ ≤ C.ordAtInfty (β₁ + β₂) + C.ordAtInfty C.coordYInFunctionField := h_β'

/-- **Non-archimedean for subtraction** (T-ORD-ARITH-13):
`min(ord f, ord g) ≤ ord(f - g)`. Direct corollary of `add_ge_min` + `neg`. -/
theorem ordAtInfty_sub_ge_min (f g : C.FunctionField) :
    min (C.ordAtInfty f) (C.ordAtInfty g) ≤ C.ordAtInfty (f - g) := by
  rw [sub_eq_add_neg, ← C.ordAtInfty_neg g]
  exact C.ordAtInfty_add_ge_min f (-g)

/-- **Strict non-archimedean for `ordAtInfty`**: when `ord f < ord g`,
the dominant term wins: `ord(f + g) = ord f`.

Standard derivation: from `ord(f + g) ≥ min(ord f, ord g) = ord f` and
`ord f = ord((f + g) - g) ≥ min(ord(f + g), ord g)`, the second gives
either `ord(f + g) ≤ ord f` (closing the equality) or `ord g ≤ ord f`
(contradicting `ord f < ord g`). -/
theorem ordAtInfty_add_eq_of_lt {f g : C.FunctionField}
    (h : C.ordAtInfty f < C.ordAtInfty g) :
    C.ordAtInfty (f + g) = C.ordAtInfty f := by
  have h_ge : C.ordAtInfty f ≤ C.ordAtInfty (f + g) := by
    have := C.ordAtInfty_add_ge_min f g
    rwa [min_eq_left h.le] at this
  have h_step : (f + g) + (-g) = f := by ring
  have h_le_step := C.ordAtInfty_add_ge_min (f + g) (-g)
  rw [h_step, C.ordAtInfty_neg g] at h_le_step
  rcases le_total (C.ordAtInfty (f + g)) (C.ordAtInfty g) with h_case | h_case
  · rw [min_eq_left h_case] at h_le_step
    exact le_antisymm h_le_step h_ge
  · rw [min_eq_right h_case] at h_le_step
    exact absurd (lt_of_lt_of_le h h_le_step) (lt_irrefl _)

/-- Subtraction variant: when `ord f < ord g`, `ord(f - g) = ord f`. -/
theorem ordAtInfty_sub_eq_of_lt {f g : C.FunctionField}
    (h : C.ordAtInfty f < C.ordAtInfty g) :
    C.ordAtInfty (f - g) = C.ordAtInfty f := by
  rw [sub_eq_add_neg]
  apply C.ordAtInfty_add_eq_of_lt
  rwa [C.ordAtInfty_neg]

private theorem intDegree_algebraMap_div_algebraMap
    {a b : Polynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (algebraMap (Polynomial F) (RatFunc F) a /
        algebraMap (Polynomial F) (RatFunc F) b).intDegree =
      (a.natDegree : ℤ) - (b.natDegree : ℤ) := by
  have ha' : algebraMap (Polynomial F) (RatFunc F) a ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr ha
  have hb' : algebraMap (Polynomial F) (RatFunc F) b ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hb
  rw [div_eq_mul_inv, RatFunc.intDegree_mul ha' (inv_ne_zero hb'),
    RatFunc.intDegree_inv, RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  ring

private theorem ratFunc_exists_C_sub_intDegree_neg {r : RatFunc F}
    (hr : r.intDegree ≤ 0) :
    ∃ lam : F, r - RatFunc.C lam = 0 ∨ (r - RatFunc.C lam).intDegree < 0 := by
  by_cases hr0 : r = 0
  · exact ⟨0, Or.inl (by rw [hr0, map_zero, sub_zero])⟩
  set n : Polynomial F := r.num with hn
  set d : Polynomial F := r.denom with hd
  have hn_ne : n ≠ 0 := RatFunc.num_ne_zero hr0
  have hd_ne : d ≠ 0 := RatFunc.denom_ne_zero r
  have h_intDeg : r.intDegree = (n.natDegree : ℤ) - (d.natDegree : ℤ) := by
    rw [RatFunc.intDegree, hn, hd]
  rw [h_intDeg] at hr
  have h_le : n.natDegree ≤ d.natDegree := by omega
  have hr_div : r = algebraMap (Polynomial F) (RatFunc F) n /
      algebraMap (Polynomial F) (RatFunc F) d := (RatFunc.num_div_denom r).symm
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · refine ⟨0, Or.inr ?_⟩
    rw [map_zero, sub_zero, h_intDeg]
    omega
  · set lam : F := n.leadingCoeff / d.leadingCoeff with hlam
    have hlc_d : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hd_ne
    have hlc_n : n.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hn_ne
    have hlam_ne : lam ≠ 0 := div_ne_zero hlc_n hlc_d
    have hd' : algebraMap (Polynomial F) (RatFunc F) d ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hd_ne
    have h_sub_eq : r - RatFunc.C lam =
        algebraMap (Polynomial F) (RatFunc F) (n - Polynomial.C lam * d) /
          algebraMap (Polynomial F) (RatFunc F) d := by
      rw [eq_div_iff hd', sub_mul, hr_div, div_mul_cancel₀ _ hd', map_sub, map_mul,
        ← RatFunc.algebraMap_C]
    have h_lc : n.leadingCoeff = (Polynomial.C lam * d).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlam,
        div_mul_cancel₀ _ hlc_d]
    have h_deg : n.degree = (Polynomial.C lam * d).degree := by
      rw [Polynomial.degree_C_mul hlam_ne, Polynomial.degree_eq_natDegree hn_ne,
        Polynomial.degree_eq_natDegree hd_ne, h_eq]
    have h_deg_lt : (n - Polynomial.C lam * d).degree < n.degree :=
      Polynomial.degree_sub_lt h_deg hn_ne h_lc
    by_cases h_num_zero : n - Polynomial.C lam * d = 0
    · exact ⟨lam, Or.inl (by rw [h_sub_eq, h_num_zero, map_zero, zero_div])⟩
    · refine ⟨lam, Or.inr ?_⟩
      have h_natDeg_lt : (n - Polynomial.C lam * d).natDegree < n.natDegree :=
        Polynomial.natDegree_lt_natDegree h_num_zero h_deg_lt
      rw [h_sub_eq, intDegree_algebraMap_div_algebraMap h_num_zero hd_ne]
      omega

/-- **Value at infinity of a `K(x)`-element, `ordAtInfty` form**: if
`r₀ ∈ FractionRing F[X]` has `0 ≤ ordAtInfty (algebraMap r₀)` (regular at `∞`),
then there is a constant `lam : F` with
`0 < ordAtInfty (algebraMap r₀ − algebraMap_F lam)`. This is the
`ordAtInfty`-flavored corollary of `ratFunc_exists_C_sub_intDegree_neg`,
transported through `RatFunc.ofFractionRing`. -/
theorem ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg
    {r₀ : FractionRing (Polynomial F)}
    (hr₀ : (0 : WithTop ℤ) ≤
      C.ordAtInfty (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₀)) :
    ∃ lam : F, (0 : WithTop ℤ) < C.ordAtInfty
      (algebraMap (FractionRing (Polynomial F)) C.FunctionField r₀ -
        algebraMap F C.FunctionField lam) := by
  have h_const : ∀ lam : F, algebraMap F C.FunctionField lam =
      algebraMap (FractionRing (Polynomial F)) C.FunctionField
        (algebraMap F (FractionRing (Polynomial F)) lam) :=
    fun lam => IsScalarTower.algebraMap_apply F (FractionRing (Polynomial F))
      C.FunctionField lam
  have h_ofC : ∀ lam : F, (RatFunc.ofFractionRing
        (algebraMap F (FractionRing (Polynomial F)) lam) : RatFunc F) = RatFunc.C lam := by
    intro lam
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)),
      RatFunc.ofFractionRing_algebraMap, Polynomial.algebraMap_eq, RatFunc.algebraMap_C]
  by_cases hr₀_zero : r₀ = 0
  · refine ⟨0, ?_⟩
    rw [hr₀_zero, map_zero, map_zero, sub_zero, ordAtInfty_zero]
    exact WithTop.coe_lt_top 0
  · rw [C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hr₀_zero] at hr₀
    have h_intDeg_le : (RatFunc.ofFractionRing r₀ : RatFunc F).intDegree ≤ 0 := by
      have : (0 : ℤ) ≤ -2 * (RatFunc.ofFractionRing r₀ : RatFunc F).intDegree := by
        exact_mod_cast hr₀
      omega
    obtain ⟨lam, hlam⟩ :=
      ratFunc_exists_C_sub_intDegree_neg (F := F) h_intDeg_le
    refine ⟨lam, ?_⟩
    rw [h_const lam, ← map_sub]
    have h_of_sub : (RatFunc.ofFractionRing
        (r₀ - algebraMap F (FractionRing (Polynomial F)) lam) : RatFunc F) =
        (RatFunc.ofFractionRing r₀ : RatFunc F) - RatFunc.C lam := by
      rw [RatFunc.ofFractionRing_sub, h_ofC]
    rcases hlam with h_zero | h_neg
    · have h_sub_zero : r₀ - algebraMap F (FractionRing (Polynomial F)) lam = 0 := by
        apply (RatFunc.ofFractionRing.injEq _ _).mp
        rw [h_of_sub, h_zero, RatFunc.ofFractionRing_zero]
      rw [h_sub_zero, map_zero, ordAtInfty_zero]
      exact WithTop.coe_lt_top 0
    · have h_sub_ne : r₀ - algebraMap F (FractionRing (Polynomial F)) lam ≠ 0 := by
        intro h
        rw [h, RatFunc.ofFractionRing_zero, eq_comm, sub_eq_zero] at h_of_sub
        rw [← h_of_sub, sub_self, RatFunc.intDegree_zero] at h_neg
        exact absurd h_neg (lt_irrefl 0)
      rw [C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero h_sub_ne, h_of_sub]
      have : (0 : ℤ) <
          -2 * ((RatFunc.ofFractionRing r₀ : RatFunc F) - RatFunc.C lam).intDegree := by
        omega
      exact_mod_cast this

/-- The multiplicative value at infinity of a function: `0 ↦ 0`, and for nonzero `x`,
`exp(-ordAtInfty x) = exp(intDegree (N x)) ∈ ℤᵐ⁰`. -/
noncomputable def ordAtInftyVal (f : C.FunctionField) : WithZero (Multiplicative ℤ) :=
  if f = 0 then 0 else WithZero.exp (RatFunc.intDegree (C.normAsRatFunc f))

theorem ordAtInftyVal_eq_exp_neg_ordAtInfty {f : C.FunctionField} (hf : f ≠ 0)
    {n : ℤ} (hn : C.ordAtInfty f = (n : WithTop ℤ)) :
    C.ordAtInftyVal f = WithZero.exp (-n) := by
  have hN : C.ordAtInfty f = (- RatFunc.intDegree (C.normAsRatFunc f) : ℤ) :=
    C.ordAtInfty_of_ne hf
  have : (n : WithTop ℤ) = ((- RatFunc.intDegree (C.normAsRatFunc f) : ℤ) : WithTop ℤ) :=
    hn.symm.trans hN
  have hni : n = - RatFunc.intDegree (C.normAsRatFunc f) := by exact_mod_cast this
  rw [ordAtInftyVal, if_neg hf, hni, neg_neg]

@[simp] theorem ordAtInftyVal_zero : C.ordAtInftyVal 0 = 0 := if_pos rfl

theorem ordAtInftyVal_ne_zero {f : C.FunctionField} (hf : f ≠ 0) :
    C.ordAtInftyVal f ≠ 0 := by
  rw [ordAtInftyVal, if_neg hf]; exact WithZero.exp_ne_zero

@[simp] theorem ordAtInftyVal_one : C.ordAtInftyVal (1 : C.FunctionField) = 1 := by
  rw [C.ordAtInftyVal_eq_exp_neg_ordAtInfty one_ne_zero C.ordAtInfty_one, neg_zero,
    WithZero.exp_zero]

theorem ordAtInftyVal_mul (f g : C.FunctionField) :
    C.ordAtInftyVal (f * g) = C.ordAtInftyVal f * C.ordAtInftyVal g := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨m, hm⟩ : ∃ m : ℤ, C.ordAtInfty f = (m : WithTop ℤ) :=
    ⟨_, C.ordAtInfty_of_ne hf⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, C.ordAtInfty g = (n : WithTop ℤ) :=
    ⟨_, C.ordAtInfty_of_ne hg⟩
  have hfg : C.ordAtInfty (f * g) = ((m + n : ℤ) : WithTop ℤ) := by
    rw [C.ordAtInfty_mul hf hg, hm, hn]; push_cast; rfl
  rw [C.ordAtInftyVal_eq_exp_neg_ordAtInfty hf hm,
    C.ordAtInftyVal_eq_exp_neg_ordAtInfty hg hn,
    C.ordAtInftyVal_eq_exp_neg_ordAtInfty (mul_ne_zero hf hg) hfg, neg_add,
    WithZero.exp_add]

theorem ordAtInftyVal_add_le_max (f g : C.FunctionField) :
    C.ordAtInftyVal (f + g) ≤ max (C.ordAtInftyVal f) (C.ordAtInftyVal g) := by
  rcases eq_or_ne (f + g) 0 with hfg | hfg
  · rw [hfg, ordAtInftyVal_zero]; exact zero_le'
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨m, hm⟩ : ∃ m : ℤ, C.ordAtInfty f = (m : WithTop ℤ) :=
    ⟨_, C.ordAtInfty_of_ne hf⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, C.ordAtInfty g = (n : WithTop ℤ) :=
    ⟨_, C.ordAtInfty_of_ne hg⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, C.ordAtInfty (f + g) = (k : WithTop ℤ) :=
    ⟨_, C.ordAtInfty_of_ne hfg⟩
  have h_min := C.ordAtInfty_add_ge_min f g
  rw [hm, hn, hk] at h_min
  rw [C.ordAtInftyVal_eq_exp_neg_ordAtInfty hf hm,
    C.ordAtInftyVal_eq_exp_neg_ordAtInfty hg hn,
    C.ordAtInftyVal_eq_exp_neg_ordAtInfty hfg hk]
  have h_min' : min m n ≤ k := by
    rcases le_total m n with h | h
    · rw [min_eq_left (WithTop.coe_le_coe.mpr h)] at h_min
      rw [min_eq_left h]; exact_mod_cast h_min
    · rw [min_eq_right (WithTop.coe_le_coe.mpr h)] at h_min
      rw [min_eq_right h]; exact_mod_cast h_min
  rw [le_max_iff, WithZero.exp_le_exp, WithZero.exp_le_exp]
  rcases le_total m n with h | h
  · left; rw [min_eq_left h] at h_min'; omega
  · right; rw [min_eq_right h] at h_min'; omega

/-- **`ordAtInfty` as a multiplicative `Valuation`** on `F(C)` with values in `ℤᵐ⁰`.
The reusable infinity-place valuation object, mirroring the affine `pointValuation`. -/
noncomputable def ordAtInftyValuation :
    Valuation C.FunctionField (WithZero (Multiplicative ℤ)) where
  toFun := C.ordAtInftyVal
  map_zero' := C.ordAtInftyVal_zero
  map_one' := C.ordAtInftyVal_one
  map_mul' := C.ordAtInftyVal_mul
  map_add_le_max' := C.ordAtInftyVal_add_le_max

@[simp] theorem ordAtInftyValuation_apply (f : C.FunctionField) :
    C.ordAtInftyValuation f = C.ordAtInftyVal f := rfl

/-- **Value bridge at infinity** (mirror of `pointValuation_eq_exp_neg_of_ord_P_eq`):
for nonzero `f` with `ordAtInfty f = n`, `ordAtInftyValuation f = exp(-n)`. -/
theorem ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq {f : C.FunctionField} {n : ℤ}
    (hf : f ≠ 0) (hn : C.ordAtInfty f = (n : WithTop ℤ)) :
    C.ordAtInftyValuation f = WithZero.exp (-n) := by
  rw [ordAtInftyValuation_apply]; exact C.ordAtInftyVal_eq_exp_neg_ordAtInfty hf hn

/-- **Surjectivity at infinity** (mirror of `pointValuation_surjective`): the
`ordAtInftyValuation` is surjective onto `ℤᵐ⁰`, using the pole of `coordX`
(`ordAtInfty coordX = -2`) as a value source and that the value group is `ℤ`. -/
theorem ordAtInftyValuation_surjective :
    Function.Surjective C.ordAtInftyValuation := by
  -- Uniformizer at infinity: `t := coordY / coordX` has `ord_∞ t = -3 - (-2) = -1`,
  -- so `w(t) = exp 1`; every value of `ℤᵐ⁰` is then a power of `w(t)`.
  have hx_ne : C.coordX ≠ 0 := C.coordX_ne_zero
  have hy_ne : C.coordY ≠ 0 := by
    intro h
    have := C.ordAtInfty_coordY
    rw [h, C.ordAtInfty_zero] at this
    exact (WithTop.coe_ne_top this.symm).elim
  set t : C.FunctionField := C.coordY / C.coordX with ht
  have ht_ne : t ≠ 0 := div_ne_zero hy_ne hx_ne
  have ht_ord : C.ordAtInfty t = ((-1 : ℤ) : WithTop ℤ) := by
    rw [ht, C.ordAtInfty_div_eq_mul_inv _ hy_ne hx_ne, C.ordAtInfty_inv, C.ordAtInfty_coordX,
      C.ordAtInfty_coordY,
      show -(((-2 : ℤ)) : WithTop ℤ) = (((2 : ℤ)) : WithTop ℤ) from rfl,
      ← WithTop.coe_add]
    norm_num
  have hvt : C.ordAtInftyValuation t = WithZero.exp (1 : ℤ) := by
    rw [C.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq ht_ne ht_ord]; norm_num
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  · refine ⟨t ^ (WithZero.log z), ?_⟩
    rw [map_zpow₀, hvt, ← WithZero.exp_zsmul, smul_eq_mul, mul_one, WithZero.exp_log hz]

theorem ordAtInftyValuation_ne_zero {f : C.FunctionField} (hf : f ≠ 0) :
    C.ordAtInftyValuation f ≠ 0 := C.ordAtInftyVal_ne_zero hf

/-- **Integrality bridge at infinity** (mirror of `pointValuation_le_one_of_ord_nonneg`):
for nonzero `f`, `ordAtInftyValuation f ≤ 1 ↔ 0 ≤ ordAtInfty f`. Both sides say the
function has no pole at infinity. -/
theorem ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg {f : C.FunctionField}
    (hf : f ≠ 0) :
    C.ordAtInftyValuation f ≤ 1 ↔ (0 : WithTop ℤ) ≤ C.ordAtInfty f := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, C.ordAtInfty f = (n : WithTop ℤ) := ⟨_, C.ordAtInfty_of_ne hf⟩
  rw [C.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hf hn, hn,
    show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      (WithZero.exp_zero).symm,
    WithZero.exp_le_exp,
    show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  omega

theorem ordAtInftyValuation_le_one_of_ordAtInfty_nonneg {f : C.FunctionField}
    (hf : f ≠ 0) (h : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
    C.ordAtInftyValuation f ≤ 1 :=
  (C.ordAtInftyValuation_le_one_iff_ordAtInfty_nonneg hf).mpr h

/-- **Closed-form ord of a quotient with known ord values**: when `ord(num) = m`
and `ord(den) = n` (as integers, with den ≠ 0), `ord(num / den) = m - n` (as
ℤ, then cast to `WithTop ℤ`). Avoids the `WithTop` arithmetic plumbing in
downstream proofs. -/
theorem ordAtInfty_div_of_ord_eq {a b : C.FunctionField}
    (hb : b ≠ 0) (m n : ℤ)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ))
    (h_b : C.ordAtInfty b = ((n : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a / b) = (((m - n : ℤ)) : WithTop ℤ) := by
  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, C.ordAtInfty_zero] at h_a
    exact WithTop.coe_ne_top h_a.symm
  rw [C.ordAtInfty_div_eq_mul_inv _ ha_ne hb, C.ordAtInfty_inv, h_a, h_b,
    show (-((n : ℤ) : WithTop ℤ)) = (((-n : ℤ) : WithTop ℤ)) from rfl, ← WithTop.coe_add]
  exact_mod_cast (sub_eq_add_neg m n).symm

/-- **Closed-form ord of a power**: `ord(f^n) = n * (ord f as ℤ)`, given that
`f ≠ 0` and the ord value as an integer. -/
theorem ordAtInfty_pow_of_ord_eq {f : C.FunctionField} (hf : f ≠ 0)
    (m : ℤ) (n : ℕ)
    (h_f : C.ordAtInfty f = ((m : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (f ^ n) = (((n : ℤ) * m : ℤ) : WithTop ℤ) := by
  rw [C.ordAtInfty_pow hf n, h_f]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ih,
      show ((((k + 1 : ℕ) : ℤ) * m : ℤ) : WithTop ℤ) =
        (((k : ℤ) * m + m : ℤ) : WithTop ℤ) from by congr 1; push_cast; ring]
    rw [WithTop.coe_add]

private theorem natDegree_zero_of_ordAtInfty_nonneg {u : C.CoordinateRing}
    (hu : (0 : WithTop ℤ) ≤
      C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u))
    (huz : u ≠ 0) : (Algebra.norm (Polynomial F) u).natDegree = 0 := by
  rw [C.ordAtInfty_algebraMap_coordinateRing u huz] at hu
  set n := (Algebra.norm (Polynomial F) u).natDegree
  have h_coe : ((0 : ℤ) : WithTop ℤ) ≤ ((-(n : ℤ) : ℤ) : WithTop ℤ) := hu
  have h_int : (0 : ℤ) ≤ -(n : ℤ) := WithTop.coe_le_coe.mp h_coe
  omega

private theorem q_eq_zero_of_norm_natDeg_zero {p q : Polynomial F}
    (hNu_ne : Algebra.norm (Polynomial F)
      (p • (1 : C.CoordinateRing) + q •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y) ≠ 0)
    (hN_natDeg : (Algebra.norm (Polynomial F)
      (p • (1 : C.CoordinateRing) + q •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y)).natDegree = 0) :
    q = 0 := by
  have hDeg :=
    WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis (W' := C.toAffine) p q
  have hNu_deg :
      (Algebra.norm (Polynomial F) (p • (1 : C.CoordinateRing) + q •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y)).degree = (0 : ℕ) := by
    rw [Polynomial.degree_eq_natDegree hNu_ne, hN_natDeg]
  rw [hNu_deg] at hDeg
  by_contra hq_ne
  have h_qdeg : q.degree = (q.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hq_ne
  have h_le : (2 • q.degree + 3 : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) :=
    le_trans (le_max_right _ _) hDeg.ge
  rw [h_qdeg] at h_le
  have h_eq : (2 : ℕ) • (q.natDegree : WithBot ℕ) + 3 =
      ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
    push_cast; ring
  rw [h_eq] at h_le
  have h_nat : 2 * q.natDegree + 3 ≤ 0 := WithBot.coe_le_coe.mp h_le
  omega

/-- **Algebraic Liouville, CoordinateRing form** (partial Silverman II.1.2):
if `u ∈ C.CoordinateRing` has nonnegative order at infinity (viewed in `F(C)`),
then `u` is the image of a constant from `F`. -/
theorem coordinateRing_const_of_ordAtInfty_nonneg (u : C.CoordinateRing)
    (hu : (0 : WithTop ℤ) ≤
      C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u)) :
    ∃ c : F, u = algebraMap F C.CoordinateRing c := by
  by_cases huz : u = 0
  · exact ⟨0, by rw [huz, map_zero]⟩
  have hN_natDeg := C.natDegree_zero_of_ordAtInfty_nonneg hu huz
  have hNu_ne : Algebra.norm (Polynomial F) u ≠ 0 := fun h =>
    huz ((Algebra.norm_eq_zero_iff (R := Polynomial F)).mp h)
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  rw [← hpq] at hNu_ne hN_natDeg
  have hq : q = 0 := C.q_eq_zero_of_norm_natDeg_zero hNu_ne hN_natDeg
  subst hq
  have hpq' : p • (1 : C.CoordinateRing) = u := by rw [← hpq, zero_smul, add_zero]
  have hp_ne : p ≠ 0 := fun hp => huz (by rw [← hpq', hp, zero_smul])
  have h_Nu_eq : Algebra.norm (Polynomial F) (p • (1 : C.CoordinateRing) +
      (0 : Polynomial F) •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y) = p ^ 2 := by
    rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
    ring
  rw [h_Nu_eq, Polynomial.natDegree_pow] at hN_natDeg
  have hp_natDeg : p.natDegree = 0 := by omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hp_natDeg
  refine ⟨c, ?_⟩
  rw [← hpq', ← hc, Algebra.smul_def, mul_one]
  change (algebraMap (Polynomial F) C.CoordinateRing)
    (algebraMap F (Polynomial F) c) = (algebraMap F C.CoordinateRing) c
  exact (IsScalarTower.algebraMap_apply F (Polynomial F) C.CoordinateRing c).symm

private noncomputable def fiberQuadratic (a : F) : Polynomial F :=
  Polynomial.X ^ 2 +
    Polynomial.C (C.toAffine.a₁ * a + C.toAffine.a₃) * Polynomial.X -
    Polynomial.C (a ^ 3 + C.toAffine.a₂ * a ^ 2 + C.toAffine.a₄ * a + C.toAffine.a₆)

private theorem fiberQuadratic_natDegree (a : F) : (C.fiberQuadratic a).natDegree = 2 := by
  unfold fiberQuadratic
  compute_degree!

private theorem fiberQuadratic_ne_zero (a : F) : C.fiberQuadratic a ≠ 0 := by
  intro h
  have := C.fiberQuadratic_natDegree a
  rw [h, Polynomial.natDegree_zero] at this
  exact absurd this (by decide)

private theorem fiberQuadratic_isRoot_of_smoothPoint {a : F} {P : C.SmoothPoint}
    (hP : P.x = a) : (C.fiberQuadratic a).IsRoot P.y := by
  have heq := P.nonsingular.1
  rw [hP, WeierstrassCurve.Affine.equation_iff'] at heq
  unfold fiberQuadratic
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
  linear_combination heq

/-- The x-projection `P ↦ P.x` from smooth points to `F` has finite fibers: for
any `a : F`, only finitely many `P : C.SmoothPoint` satisfy `P.x = a`. This is
because each such `P.y` is a root of the quadratic
`Y² + (a₁·a + a₃)·Y − (a³ + a₂·a² + a₄·a + a₆)`, which has at most two roots.
Reference: Silverman II.2 (behavior of fibers of `x : C → ℙ¹`). -/
theorem smoothPoint_x_preimage_finite (a : F) :
    {P : C.SmoothPoint | P.x = a}.Finite :=
  Set.Finite.of_injOn
    (s := {P : C.SmoothPoint | P.x = a})
    (t := {y : F | (C.fiberQuadratic a).IsRoot y})
    (fun _ hP => C.fiberQuadratic_isRoot_of_smoothPoint hP)
    (fun _ hP₁ _ hP₂ hy => SmoothPoint.ext (hP₁.trans hP₂.symm) hy)
    (Polynomial.finite_setOf_isRoot (C.fiberQuadratic_ne_zero a))

/-- The x-projection preimage of a finite set of `x`-values is finite. In
particular, `{P : C.SmoothPoint | P.x ∈ roots f}` is finite for any nonzero
`f ∈ F[X]`. This is the key step toward Bezout counting of zeros/poles on `C`
(Silverman II.1.2). -/
theorem smoothPoint_x_preimage_finite_of_set (s : Set F) (hs : s.Finite) :
    {P : C.SmoothPoint | P.x ∈ s}.Finite := by
  have h : {P : C.SmoothPoint | P.x ∈ s} = ⋃ a ∈ s, {P : C.SmoothPoint | P.x = a} := by
    ext P; simp
  rw [h]
  exact hs.biUnion (fun a _ => C.smoothPoint_x_preimage_finite a)

private noncomputable def coordEval (P : C.SmoothPoint) :
    C.CoordinateRing →+* F :=
  AdjoinRoot.lift (Polynomial.evalRingHom P.x) P.y <| by
    rw [Polynomial.eval₂_evalRingHom]
    exact P.nonsingular.1

private theorem coordEval_mk (P : C.SmoothPoint) (g : Polynomial (Polynomial F)) :
    C.coordEval P
        (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine g) =
      g.evalEval P.x P.y := by
  unfold coordEval
  rw [show (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine g :
      C.CoordinateRing) = AdjoinRoot.mk C.toAffine.polynomial g from rfl,
    AdjoinRoot.lift_mk, ← Polynomial.eval₂_evalRingHom]

private theorem coordEval_smul_basis (P : C.SmoothPoint) (p q : Polynomial F) :
    C.coordEval P (p • (1 : C.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y) =
      Polynomial.eval P.x p + Polynomial.eval P.x q * P.y := by
  have h1 : p • (1 : C.CoordinateRing) =
      WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine (Polynomial.C p) := by
    rw [Algebra.smul_def, mul_one]; rfl
  have h2 : q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y =
      WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
        (Polynomial.C q * Y) := by
    rw [Algebra.smul_def]; rfl
  rw [h1, h2, ← map_add, C.coordEval_mk]
  simp [Polynomial.evalEval_add, Polynomial.evalEval_mul,
    Polynomial.evalEval_C, Polynomial.evalEval_X]

private theorem XClass_mem_ker_coordEval (P : C.SmoothPoint) :
    WeierstrassCurve.Affine.CoordinateRing.XClass C.toAffine P.x ∈
      RingHom.ker (C.coordEval P) := by
  rw [RingHom.mem_ker, WeierstrassCurve.Affine.CoordinateRing.XClass,
    C.coordEval_mk]
  simp [Polynomial.evalEval_C]

private theorem YClass_mem_ker_coordEval (P : C.SmoothPoint) :
    WeierstrassCurve.Affine.CoordinateRing.YClass C.toAffine
        (Polynomial.C P.y) ∈ RingHom.ker (C.coordEval P) := by
  rw [RingHom.mem_ker, WeierstrassCurve.Affine.CoordinateRing.YClass,
    C.coordEval_mk]
  simp [Polynomial.evalEval_sub, Polynomial.evalEval_X, Polynomial.evalEval_C]

private theorem maximalIdealAt_le_ker_coordEval (P : C.SmoothPoint) :
    C.maximalIdealAt P ≤ RingHom.ker (C.coordEval P) := by
  rw [maximalIdealAt, WeierstrassCurve.Affine.CoordinateRing.XYIdeal,
    Ideal.span_le]
  intro u hu
  rcases hu with rfl | rfl
  · exact C.XClass_mem_ker_coordEval P
  · exact C.YClass_mem_ker_coordEval P

private theorem ker_coordEval_ne_top (P : C.SmoothPoint) :
    RingHom.ker (C.coordEval P) ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
  exact one_ne_zero

private theorem ker_coordEval_eq (P : C.SmoothPoint) :
    RingHom.ker (C.coordEval P) = C.maximalIdealAt P :=
  ((C.maximalIdealAt_isMaximal P).eq_of_le (C.ker_coordEval_ne_top P)
    (C.maximalIdealAt_le_ker_coordEval P)).symm

/-- **`u ∈ M_P ⟺ u evaluates to 0 at `P`**: the scheme-theoretic membership
characterisation. For `u = p · 1 + q · Y ∈ F[C]`, `u ∈ maximalIdealAt P`
iff `p(P.x) + q(P.x) · P.y = 0`. Closes the missing bridge of D-004.
Reference: Silverman II.1.2 (zeros-are-finite step). -/
theorem mem_maximalIdealAt_iff_eval_zero (P : C.SmoothPoint)
    (p q : Polynomial F) :
    (p • (1 : C.CoordinateRing) + q •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y) ∈
      C.maximalIdealAt P ↔
    Polynomial.eval P.x p + Polynomial.eval P.x q * P.y = 0 := by
  rw [← C.ker_coordEval_eq P, RingHom.mem_ker, C.coordEval_smul_basis]

/-- **Bezout counting, algebraic identity**: if `p.eval P.x + q.eval P.x · P.y = 0`
(i.e. `p·1 + q·Y` vanishes at `(P.x, P.y)` in the scheme-theoretic sense), then
`N(p·1 + q·Y)` has `P.x` as a root. This is the core computation behind
Silverman II.1.2's zeros-are-finite argument: it reduces the curve-level
vanishing to a polynomial root in `F[X]`.
Reference: Silverman II.1.2 proof sketch. -/
theorem norm_eval_at_x_of_zero_at_smoothPoint (P : C.SmoothPoint) (p q : Polynomial F)
    (hPu : p.eval P.x + q.eval P.x * P.y = 0) :
    (Algebra.norm (Polynomial F)
      (p • (1 : C.CoordinateRing) + q •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y)).eval P.x = 0 := by
  have hEq := P.nonsingular.1
  rw [WeierstrassCurve.Affine.equation_iff] at hEq
  rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  linear_combination
    (q.eval P.x) ^ 2 * hEq +
    (p.eval P.x - q.eval P.x * (P.y + C.toAffine.a₁ * P.x + C.toAffine.a₃)) * hPu

/-- For `u ∈ C.CoordinateRing`, the point valuation is strictly less than 1
iff `u` is in the maximal ideal at `P`. Combines
`HeightOneSpectrum.valuation_lt_one_iff_mem` with
`Localization.AtPrime.comap_maximalIdeal`. -/
theorem pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (u : C.CoordinateRing) (P : C.SmoothPoint) :
    C.pointValuation P (algebraMap C.CoordinateRing C.FunctionField u) < 1 ↔
    u ∈ C.maximalIdealAt P := by
  have h_comap : u ∈ C.maximalIdealAt P ↔
      algebraMap C.CoordinateRing (C.localRingAt P) u ∈
        IsLocalRing.maximalIdeal (C.localRingAt P) := by
    rw [← Ideal.mem_under, Localization.AtPrime.under_maximalIdeal]
  rw [h_comap, IsScalarTower.algebraMap_apply C.CoordinateRing
    (C.localRingAt P) C.FunctionField u, pointValuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  rfl

/-- For `u ∈ C.CoordinateRing`, the point valuation of its image in `F(C)` is
at most 1 (i.e. nonnegative `ord_P`). -/
theorem pointValuation_algebraMap_le_one (u : C.CoordinateRing)
    (P : C.SmoothPoint) :
    C.pointValuation P (algebraMap C.CoordinateRing C.FunctionField u) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt P)
    C.FunctionField u, pointValuation]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal (C.localRingAt P)) _

/-- **Step (B'') foundational structural lemma (one direction)**: every
element of `C.localRingAt P` (after embedding into `K(C)`) has valuation
≤ 1 at `P`. Direct from `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`
applied at the localRingAt level (the localRing is a DVR, hence a Dedekind
domain with the maximal ideal as a HeightOneSpectrum element). -/
theorem pointValuation_algebraMap_localRingAt_le_one
    (C : SmoothPlaneCurve F) (P : C.SmoothPoint) (x : C.localRingAt P) :
    C.pointValuation P (algebraMap (C.localRingAt P) C.FunctionField x) ≤ 1 := by
  unfold pointValuation
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal (C.localRingAt P)) x

/-- **Step (B'') foundational structural lemma (converse direction)**: every
element of `K(C)` with valuation ≤ 1 at `P` lifts to an element of
`C.localRingAt P`. Together with the easy direction, this characterises
the `algebraMap (localRingAt P) → KE` image as exactly
`(pointValuation P).integer.subring`. -/
theorem mem_localRingAt_image_of_pointValuation_le_one
    {C : SmoothPlaneCurve F} {P : C.SmoothPoint} (f : C.FunctionField)
    (hf : C.pointValuation P f ≤ 1) :
    ∃ x : C.localRingAt P,
      algebraMap (C.localRingAt P) C.FunctionField x = f := by
  obtain ⟨n, d, h_eq⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (IsDiscreteValuationRing.maximalIdeal (C.localRingAt P)) f hf
  have hd_unit : IsUnit (d : C.localRingAt P) :=
    IsLocalRing.notMem_maximalIdeal.mp d.prop
  refine ⟨n * (hd_unit.unit⁻¹ : (C.localRingAt P)ˣ), ?_⟩
  have h_alg_d_ne :
      algebraMap (C.localRingAt P) C.FunctionField (d : C.localRingAt P) ≠ 0 := by
    intro h
    have h_inj := IsFractionRing.injective (C.localRingAt P) C.FunctionField
    have h_d_zero : (d : C.localRingAt P) = 0 := h_inj (by rw [h, map_zero])
    exact hd_unit.ne_zero h_d_zero
  rw [map_mul]
  have h_inv :
      algebraMap (C.localRingAt P) C.FunctionField
          ((hd_unit.unit⁻¹ : (C.localRingAt P)ˣ) : C.localRingAt P) =
        (algebraMap (C.localRingAt P) C.FunctionField (d : C.localRingAt P))⁻¹ := by
    rw [map_units_inv (algebraMap (C.localRingAt P) C.FunctionField) hd_unit.unit,
      IsUnit.unit_spec hd_unit]
  rw [h_inv, ← h_eq, mul_assoc, mul_inv_cancel₀ h_alg_d_ne, mul_one]

/-- **Step (B'') foundational structural identification (biconditional)**:
combines `pointValuation_algebraMap_localRingAt_le_one` and
`mem_localRingAt_image_of_pointValuation_le_one` into the canonical iff form.
This characterises the `algebraMap (localRingAt P) → KE` image as exactly
the v-adic integer subring `(C.pointValuation P).integer.toSubring`. -/
theorem mem_localRingAt_image_iff_pointValuation_le_one
    {C : SmoothPlaneCurve F} {P : C.SmoothPoint} (f : C.FunctionField) :
    (∃ x : C.localRingAt P, algebraMap _ _ x = f) ↔
      C.pointValuation P f ≤ 1 := by
  refine ⟨?_, mem_localRingAt_image_of_pointValuation_le_one f⟩
  rintro ⟨x, rfl⟩
  exact pointValuation_algebraMap_localRingAt_le_one C P x

/-- `ord_P` is zero iff the point valuation equals 1. -/
theorem ord_P_eq_zero_iff_pointValuation_eq_one (C : SmoothPlaneCurve F)
    {P : C.SmoothPoint} {f : C.FunctionField} (hf : f ≠ 0) :
    C.ord_P P f = 0 ↔ C.pointValuation P f = 1 := by
  have hv : C.pointValuation P f ≠ 0 := (C.pointValuation P).ne_zero_iff.mpr hf
  unfold ord_P
  rw [dif_neg hv]
  constructor
  · intro h
    have h_nat : -((WithZero.unzero hv).toAdd : ℤ) = 0 := by exact_mod_cast h
    have h_toAdd : (WithZero.unzero hv).toAdd = 0 := by omega
    have : WithZero.unzero hv = (1 : Multiplicative ℤ) := by
      ext; exact h_toAdd
    rw [← WithZero.coe_unzero hv, this]; rfl
  · intro h
    have : WithZero.unzero hv = 1 := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, h]; rfl
    rw [this]; rfl

/-- The **main bridge** for Bezout counting: for `u ∈ C.CoordinateRing`
nonzero, `ord_P ≠ 0` iff `u ∈ maximalIdealAt P`. -/
theorem ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt
    {u : C.CoordinateRing} (hu : u ≠ 0) (P : C.SmoothPoint) :
    C.ord_P P (algebraMap C.CoordinateRing C.FunctionField u) ≠ 0 ↔
    u ∈ C.maximalIdealAt P := by
  have hne : algebraMap C.CoordinateRing C.FunctionField u ≠ 0 := fun h =>
    hu ((IsFractionRing.injective C.CoordinateRing C.FunctionField)
      (h.trans (map_zero _).symm))
  have hle : C.pointValuation P
      (algebraMap C.CoordinateRing C.FunctionField u) ≤ 1 :=
    C.pointValuation_algebraMap_le_one u P
  rw [← C.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt u P,
    lt_iff_le_and_ne, and_iff_right hle]
  constructor
  · intro h hpv
    exact h ((C.ord_P_eq_zero_iff_pointValuation_eq_one hne).mpr hpv)
  · intro h h0
    exact h ((C.ord_P_eq_zero_iff_pointValuation_eq_one hne).mp h0)

/-- **Bezout counting for `F[C]`** (Silverman II.1.2): a nonzero element
`u ∈ C.CoordinateRing` vanishes at only finitely many smooth points.
Combines the membership bridge (`mem_maximalIdealAt_iff_eval_zero`), the
norm-eval identity (`norm_eval_at_x_of_zero_at_smoothPoint`), finiteness of
roots of `Algebra.norm F[X] u` in `F`, and the fibre-finiteness of the
x-projection. -/
theorem finite_setOf_mem_maximalIdealAt {u : C.CoordinateRing} (hu : u ≠ 0) :
    {P : C.SmoothPoint | u ∈ C.maximalIdealAt P}.Finite := by
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  have hNu_ne : Algebra.norm (Polynomial F) u ≠ 0 := fun h =>
    hu ((Algebra.norm_eq_zero_iff (R := Polynomial F)).mp h)
  refine (C.smoothPoint_x_preimage_finite_of_set
    {a : F | (Algebra.norm (Polynomial F) u).IsRoot a}
    (Polynomial.finite_setOf_isRoot hNu_ne)).subset ?_
  intro P (hP : u ∈ C.maximalIdealAt P)
  rw [← hpq, C.mem_maximalIdealAt_iff_eval_zero P p q] at hP
  change (Algebra.norm (Polynomial F) u).IsRoot P.x
  rw [Polynomial.IsRoot, ← hpq]
  exact C.norm_eval_at_x_of_zero_at_smoothPoint P p q hP

/-- **D-004 for coordinate-ring elements**: for nonzero `u ∈ C.CoordinateRing`,
`{P : C.SmoothPoint | ord_P (algebraMap u) ≠ 0}` is finite. -/
theorem finite_setOf_ord_P_nonzero_of_coordinateRing
    {u : C.CoordinateRing} (hu : u ≠ 0) :
    {P : C.SmoothPoint | C.ord_P P
      (algebraMap C.CoordinateRing C.FunctionField u) ≠ 0}.Finite := by
  have h_eq : {P : C.SmoothPoint | C.ord_P P
        (algebraMap C.CoordinateRing C.FunctionField u) ≠ 0} =
      {P : C.SmoothPoint | u ∈ C.maximalIdealAt P} := by
    ext P
    exact C.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hu P
  rw [h_eq]
  exact C.finite_setOf_mem_maximalIdealAt hu

/-- **Silverman II.1.2, main form**: any nonzero function on `C` has zeros and
poles only at finitely many smooth points.

Proof: write `f = u/v` with `u, v ∈ C.CoordinateRing` nonzero (via
`IsFractionRing.div_surjective`), then
`ord_P (algebraMap u) = ord_P f + ord_P (algebraMap v)` (by `ord_P_mul` on
`algebraMap u = f * algebraMap v`), so `ord_P f ≠ 0` forces at least one of
`ord_P (algebraMap u) ≠ 0` or `ord_P (algebraMap v) ≠ 0`. The latter two
finite sets are given by `finite_setOf_ord_P_nonzero_of_coordinateRing`. -/
theorem finite_setOf_ord_P_nonzero {f : C.FunctionField} (hf : f ≠ 0) :
    {P : C.SmoothPoint | C.ord_P P f ≠ 0}.Finite := by
  obtain ⟨u, v, hv_nzd, heq⟩ :=
    IsFractionRing.div_surjective (A := C.CoordinateRing) f
  have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_nzd
  have hv_map_ne : algebraMap C.CoordinateRing C.FunctionField v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective
      C.CoordinateRing C.FunctionField)).mpr hv_ne
  have hu_ne : u ≠ 0 := by
    intro h
    exact hf (by rw [← heq, h, map_zero, zero_div])
  have h_mul : algebraMap C.CoordinateRing C.FunctionField u =
      f * algebraMap C.CoordinateRing C.FunctionField v := by
    rw [← heq, div_mul_cancel₀ _ hv_map_ne]
  refine ((C.finite_setOf_ord_P_nonzero_of_coordinateRing hu_ne).union
    (C.finite_setOf_ord_P_nonzero_of_coordinateRing hv_ne)).subset ?_
  intro P hP
  by_contra h_both
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h_both
  obtain ⟨hu0, hv0⟩ := h_both
  have hord : C.ord_P P
      (algebraMap C.CoordinateRing C.FunctionField u) =
      C.ord_P P f + C.ord_P P
        (algebraMap C.CoordinateRing C.FunctionField v) := by
    rw [h_mul, C.ord_P_mul]
  rw [hu0, hv0, add_zero] at hord
  exact hP hord.symm

/-- **Silverman II.1.2, Part 1**: a nonzero function on a smooth plane curve
has zeros and poles at only finitely many smooth points. This is an alias
for `finite_setOf_ord_P_nonzero` matching the ticket statement. -/
theorem finite_zeros_poles (f : C.FunctionField) (hf : f ≠ 0) :
    {P : C.SmoothPoint | C.ord_P P f ≠ 0}.Finite :=
  C.finite_setOf_ord_P_nonzero hf

/-- **Silverman II.1.2, Part 2 (algebraic Liouville)**, CoordinateRing form:
if `f ∈ F(C)` has nonnegative order at infinity AND lies in the coordinate
ring, then `f` is the image of a constant from `F`.

This is the best form provable with our current infrastructure. The full
"no-affine-poles ⟹ in CoordinateRing" step is the integral-closure
property of smooth curves: for a smooth Weierstrass curve `[C.toAffine.IsElliptic]`,
`C.CoordinateRing` is a Dedekind domain, hence integrally closed, and any
`f ∈ F(C)` with `ord_P f ≥ 0` at every closed point is automatically in
`C.CoordinateRing`. Without the `IsElliptic` hypothesis (or an equivalent
smoothness assumption), singular points can have local rings that don't
align with the global coordinate ring structure, and the integral-closure
step requires genuinely new algebra-of-curves infrastructure.

Reference: Silverman II.1.2, second part; Hartshorne I.6.12. -/
theorem const_of_no_poles_of_coordinateRing (f : C.FunctionField)
    (h_coord : ∃ u : C.CoordinateRing,
      algebraMap C.CoordinateRing C.FunctionField u = f)
    (h_inf : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
    ∃ c : F, f = algebraMap F C.FunctionField c := by
  obtain ⟨u, rfl⟩ := h_coord
  obtain ⟨c, hc⟩ := C.coordinateRing_const_of_ordAtInfty_nonneg u h_inf
  refine ⟨c, ?_⟩
  rw [hc]
  exact (IsScalarTower.algebraMap_apply F C.CoordinateRing
    C.FunctionField c).symm

/-- **IC-006 (Silverman II.1.2, Part 2, prime-indexed)**: if `f ∈ F(C)` has
nonnegative valuation at every nonzero prime of `C.CoordinateRing` **and** at
infinity, then `f` is constant. Combines IC-006's Dedekind-Liouville bridge
`mem_coordinateRing_of_valuation_le_one` with the CoordinateRing-form
algebraic Liouville `const_of_no_poles_of_coordinateRing`. -/
theorem const_of_no_poles_of_valuation_of_ordAtInfty
    [IsIntegrallyClosed C.CoordinateRing] (f : C.FunctionField)
    (h_primes : ∀ v : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing,
      v.valuation C.FunctionField f ≤ 1)
    (h_inf : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
    ∃ c : F, f = algebraMap F C.FunctionField c :=
  C.const_of_no_poles_of_coordinateRing f
    (C.mem_coordinateRing_of_valuation_le_one f h_primes) h_inf

/-- **IC-006 (integrality-based Liouville)**: if `f ∈ F(C)` is integral over
`F[X]` **and** has nonnegative order at infinity, then `f` is constant.
This is the cleanest consequence of `IsIntegrallyClosed C.CoordinateRing`:
integrality over `F[X]` lifts `f` into `C.CoordinateRing`, and then
`const_of_no_poles_of_coordinateRing` pins it to `F`. -/
theorem const_of_isIntegral_polynomialX_of_ordAtInfty
    [IsIntegrallyClosed C.CoordinateRing] {f : C.FunctionField}
    (h_int : IsIntegral (Polynomial F) f)
    (h_inf : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
    ∃ c : F, f = algebraMap F C.FunctionField c :=
  C.const_of_no_poles_of_coordinateRing f
    (C.mem_coordinateRing_of_isIntegral_polynomialX h_int) h_inf

end SmoothPlaneCurve

end HasseWeil.Curves
