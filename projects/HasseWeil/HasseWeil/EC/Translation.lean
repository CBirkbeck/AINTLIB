/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback

/-!
# Translation by a base-field point on K(E)

For an elliptic curve `W` over `F` and a point `(xk, yk) ∈ W(F)` (= a base-field
solution of the Weierstrass equation), translation by `k = (xk, yk)` lifts
to a K-algebra automorphism `τ_k : K(E) ≃ₐ[F] K(E)` defined by:

* `τ_k(x_gen) = (W_KE).addX(x_gen, xk, slope_k)` where
  `slope_k = (y_gen - yk) / (x_gen - xk)`.
* `τ_k(y_gen) = (W_KE).addY(x_gen, xk, y_gen, slope_k)`.

This is the substantive Galois-correspondence content for elliptic
isogenies (Silverman III.4.10(a)): for an isogeny `α : E → E`, the kernel
of `α` (as an additive subgroup of `E.Point`) acts on `K(E₁)/α*K(E₂)` as
the Galois group, and the bijection `α.kernel ≃ Aut(K(E)/α*K(E))` sends
each kernel element `k` to the translation automorphism `τ_k`.

This file constructs the translation algebra hom directly via the addition
formula on coordinates, paralleling
`HasseWeil/AdditionPullback.lean`'s `addPullbackAlgHom_negFrobenius`
construction.

## Foundational definitions

The translation construction is parallel to `addPullback_x` / `addPullback_y`
but with the second point a base-field constant rather than `α.pullback`.

* `translateSlope_xy xk yk` — slope from `(x_gen, y_gen)` to `(xk, yk)`.
* `translateX_xy xk yk` — x-coord of `P_gen + (xk, yk)`.
* `translateY_xy xk yk` — y-coord of `P_gen + (xk, yk)`.

These are foundational K(E)-elements; the algebra-hom construction (analog
of `addPullbackAlgHom`) requires the `AddNonInverse` and injectivity
witnesses.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10(a).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- The slope of the line through `(x_gen, y_gen)` and `(xk, yk)`. The
    base-field constants `xk, yk` are lifted to K(E) via `algebraMap`. -/
noncomputable def translateSlope_xy (xk yk : F) : KE :=
  (W_KE W).toAffine.slope (x_gen W) (algebraMap F KE xk)
    (y_gen W) (algebraMap F KE yk)

/-- The x-coordinate of `P_gen + (xk, yk)`. -/
noncomputable def translateX_xy (xk yk : F) : KE :=
  (W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk)
    (translateSlope_xy W xk yk)

/-- The y-coordinate of `P_gen + (xk, yk)`. -/
noncomputable def translateY_xy (xk yk : F) : KE :=
  (W_KE W).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W)
    (translateSlope_xy W xk yk)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `translateX_xy` equals the `(W_KE).addX` formula at `(x_gen, algebraMap xk)`
with slope `translateSlope_xy`. -/
@[simp]
theorem translateX_xy_eq_addX (xk yk : F) :
    translateX_xy W xk yk =
      (W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk)
        (translateSlope_xy W xk yk) := rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `translateY_xy` equals the `(W_KE).addY` formula at `(x_gen, algebraMap xk, y_gen)`
with slope `translateSlope_xy`. -/
@[simp]
theorem translateY_xy_eq_addY (xk yk : F) :
    translateY_xy W xk yk =
      (W_KE W).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W)
        (translateSlope_xy W xk yk) := rfl

/-- The non-inverse hypothesis for translation by `(xk, yk)`. -/
abbrev TranslateNonInverse (xk yk : F) : Prop :=
  ¬(x_gen W = algebraMap F KE xk ∧
    y_gen W = (W_KE W).toAffine.negY (algebraMap F KE xk) (algebraMap F KE yk))

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The constant point `(algebraMap F KE xk, algebraMap F KE yk)` satisfies the
    `K(E)`-base-changed Weierstrass equation, given `(xk, yk)` satisfies
    the original `F`-equation. -/
theorem translate_constant_equation (xk yk : F) (h_eq : W.toAffine.Equation xk yk) :
    (W_KE W).toAffine.Equation (algebraMap F KE xk) (algebraMap F KE yk) :=
  Affine.Equation.map (algebraMap F KE) h_eq

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The translation outputs satisfy the Weierstrass equation. Same as
    `addPullback_equation` but with `α.pullback` replaced by base-field
    constants `(xk, yk)`. -/
theorem translate_equation (xk yk : F) (h_eq : W.toAffine.Equation xk yk)
    (hxy : TranslateNonInverse W xk yk) :
    (W_KE W).toAffine.Equation (translateX_xy W xk yk) (translateY_xy W xk yk) :=
  Affine.equation_add (generic_equation W) (translate_constant_equation W xk yk h_eq) hxy

/-- The base ring hom `F[X] →+* K(E)` sending `X ↦ translateX_xy xk yk`. -/
noncomputable def translateBaseHom (xk yk : F) : Polynomial F →+* KE :=
  Polynomial.eval₂RingHom (algebraMap F KE) (translateX_xy W xk yk)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The Weierstrass polynomial evaluates to zero at the translated coordinates. -/
theorem translate_poly_eval₂_zero (xk yk : F) (h_eq : W.toAffine.Equation xk yk)
    (hxy : TranslateNonInverse W xk yk) :
    W.toAffine.polynomial.eval₂ (translateBaseHom W xk yk) (translateY_xy W xk yk) = 0 := by
  rw [translateBaseHom, Polynomial.eval₂_eval₂RingHom_apply, ← Affine.map_polynomial]
  exact translate_equation W xk yk h_eq hxy

/-- The ring homomorphism `CoordinateRing → K(E)` sending the coordinate generators
    to the translation outputs. Reference: Silverman III.3.6 + III.4.10(a). -/
noncomputable def translateCoordRingHom (xk yk : F) (h_eq : W.toAffine.Equation xk yk)
    (hxy : TranslateNonInverse W xk yk) :
    W.toAffine.CoordinateRing →+* KE :=
  AdjoinRoot.lift (translateBaseHom W xk yk) (translateY_xy W xk yk)
    (translate_poly_eval₂_zero W xk yk h_eq hxy)

/-- The translation coordinate ring hom as an F-algebra hom `R →ₐ[F] K(E)`. -/
noncomputable def translateCoordAlgHom (xk yk : F) (h_eq : W.toAffine.Equation xk yk)
    (hxy : TranslateNonInverse W xk yk) :
    W.toAffine.CoordinateRing →ₐ[F] KE where
  toRingHom := translateCoordRingHom W xk yk h_eq hxy
  commutes' r := by
    change translateCoordRingHom W xk yk h_eq hxy
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing
        (algebraMap F (Polynomial F) r)) = _
    change AdjoinRoot.lift (translateBaseHom W xk yk) (translateY_xy W xk yk) _
      (AdjoinRoot.mk _ (Polynomial.C (algebraMap F (Polynomial F) r))) = _
    rw [AdjoinRoot.lift_mk]
    simp [translateBaseHom, Polynomial.eval₂_C]

local notation "R" => W.toAffine.CoordinateRing

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Image of a power-basis element `p • 1 + q • Y` under `translateCoordRingHom`: it
splits as `translateBaseHom p + translateBaseHom q * translateY_xy`, since the
`AdjoinRoot.lift` sends the basis generators to the translation-formula outputs.
(Translation analogue of `addCoordRingHom_smulBasis`.) -/
private theorem translateCoordRingHom_smulBasis (xk yk : F)
    (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk)
    (p q : Polynomial F) :
    translateCoordRingHom W xk yk h_eq hxy
        (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      translateBaseHom W xk yk p +
        translateBaseHom W xk yk q * translateY_xy W xk yk := by
  simp only [translateCoordRingHom, map_add]
  congr 1
  · change AdjoinRoot.lift _ _ _ (p • 1) = _
    rw [Algebra.smul_def, mul_one]
    exact AdjoinRoot.lift_of _
  · change AdjoinRoot.lift _ _ _ (q • AdjoinRoot.root _) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    · exact AdjoinRoot.lift_of _
    · exact AdjoinRoot.lift_root _

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- On the image of the base ring `F[X]` (under `algebraMap _ R`), `translateCoordRingHom`
agrees with `translateBaseHom`, since the `AdjoinRoot.lift` is defined by lifting that
base hom along `AdjoinRoot.of`. -/
private theorem translateCoordRingHom_algebraMap (xk yk : F)
    (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk)
    (f : Polynomial F) :
    translateCoordRingHom W xk yk h_eq hxy (algebraMap (Polynomial F) R f) =
      translateBaseHom W xk yk f := by
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ f) = _
  exact AdjoinRoot.lift_of _

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The norm of the power-basis element `p • 1 + q • Y`, pushed into the coordinate ring,
factors as the element times its conjugate `C p + C q * (-Y - C (a₁X + a₃))`. This is a
purely coordinate-ring statement (independent of the translation data). -/
private theorem algebraMap_norm_smulBasis_eq_mul_conj (p q : Polynomial F) :
    algebraMap (Polynomial F) R
        (Algebra.norm (Polynomial F)
          (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X)) =
      (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) *
        Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C p + Polynomial.C q *
            (-Polynomial.X - Polynomial.C
              (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))) := by
  change AdjoinRoot.of _ _ = _
  rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
  congr 1
  rw [map_add, map_mul]
  simp [Algebra.smul_def]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The norm of the power-basis element `p • 1 + q • Y` is nonzero whenever `q ≠ 0`: its
degree is `max (2·deg p) (2·deg q + 3)`, and the second summand is finite (`≠ ⊥`). This is
a purely coordinate-ring statement (independent of the translation data). -/
private theorem norm_smulBasis_ne_zero_of_snd_ne_zero (p : Polynomial F) {q : Polynomial F}
    (hq : q ≠ 0) :
    Algebra.norm (Polynomial F)
        (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) ≠ 0 := by
  intro h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine) p q
  rw [h_norm_eq, Polynomial.degree_zero] at h_deg
  have hq_deg : q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hq
  have hqd : 2 • q.degree + 3 ≠ (⊥ : WithBot ℕ) := by
    intro h
    apply hq_deg
    cases hd : q.degree with
    | bot => rfl
    | coe n =>
        rw [hd] at h
        exact absurd h (by
          change ¬ (2 • (↑n : WithBot ℕ) + 3 = ⊥)
          simp [WithBot.mul_ne_bot])
  exact absurd (h_deg ▸ le_max_right _ _ : 2 • q.degree + 3 ≤ ⊥)
    (not_le.mpr (WithBot.bot_lt_iff_ne_bot.mpr hqd))

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The base hom `translateBaseHom` sends the norm of a kernel element `p • 1 + q • Y` to
`0`: the norm factors through the element via `algebraMap_norm_smulBasis_eq_mul_conj`, and
the ring hom kills the element (hypothesis `hr`). -/
private theorem translateBaseHom_norm_smulBasis_eq_zero (xk yk : F)
    (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk)
    {p q : Polynomial F}
    (hr : translateCoordRingHom W xk yk h_eq hxy
      (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) = 0) :
    translateBaseHom W xk yk
        (Algebra.norm (Polynomial F)
          (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X)) = 0 := by
  rw [← translateCoordRingHom_algebraMap W xk yk h_eq hxy,
    algebraMap_norm_smulBasis_eq_mul_conj, map_mul, hr, zero_mul]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **Witness-parametric `translateCoordAlgHom_injective`**: takes the
base-hom injectivity (`hxinj`) as an explicit hypothesis. Transposes
`addCoordAlgHom_injective_of_baseHom_inj` to the translation-by-(xk,yk)
case. The only α-specific parts of that proof were `addBaseHom W α` and
`addPullback_y W α`; here they become `translateBaseHom W xk yk` and
`translateY_xy W xk yk`.

Outline: decompose `r = p • 1 + q • Y` on the rank-2 basis; its image splits via
`translateCoordRingHom_smulBasis`. If `q = 0` the image vanishing is exactly `hxinj` on
`p`; if `q ≠ 0` the norm `N(r) ≠ 0` (`norm_smulBasis_ne_zero_of_snd_ne_zero`) yet
`translateBaseHom N(r) = 0` (`translateBaseHom_norm_smulBasis_eq_zero`), contradicting
`hxinj`. -/
theorem translateCoordAlgHom_injective_of_baseHom_inj (xk yk : F)
    (h_eq : W.toAffine.Equation xk yk) (hxy : TranslateNonInverse W xk yk)
    (hxinj : Function.Injective (translateBaseHom W xk yk)) :
    Function.Injective (translateCoordAlgHom W xk yk h_eq hxy) := by
  change Function.Injective (translateCoordRingHom W xk yk h_eq hxy)
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  rw [← hpq] at hr ⊢
  rw [translateCoordRingHom_smulBasis] at hr
  suffices hp : p = 0 ∧ q = 0 by
    obtain ⟨hp1, hp2⟩ := hp
    rw [hp1, hp2]
    change (0 : Polynomial F) • (1 : R) + (0 : Polynomial F) •
      Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0
    rw [Algebra.smul_def, Algebra.smul_def, map_zero, zero_mul, zero_mul, add_zero]
  by_cases hq : q = 0
  · rw [hq, map_zero, zero_mul, add_zero] at hr
    exact ⟨hxinj (hr.trans (map_zero _).symm), hq⟩
  · -- `q ≠ 0`: the norm of `p • 1 + q • Y` is nonzero, yet `translateBaseHom` sends it to
    -- `0` (the ring hom kills the element), contradicting `hxinj`.
    refine absurd ?_ (norm_smulBasis_ne_zero_of_snd_ne_zero (W := W) p hq)
    refine hxinj (Eq.trans ?_ (map_zero _).symm)
    exact translateBaseHom_norm_smulBasis_eq_zero W xk yk h_eq hxy
      ((translateCoordRingHom_smulBasis W xk yk h_eq hxy p q).trans hr)

/-- The translation algebra hom on `K(E)`, lifted from the coordinate-ring
hom via `IsFractionRing.liftAlgHom`. Witness-parametric on the base-hom
injectivity (which gives the `Function.Injective` for the lift).

This is the core algebra-hom packaging — analogous to
`HasseWeil.addPullbackAlgHom`. -/
noncomputable def translateAlgHom (xk yk : F) (h_eq : W.toAffine.Equation xk yk)
    (hxy : TranslateNonInverse W xk yk)
    (hxinj : Function.Injective (translateBaseHom W xk yk)) :
    KE →ₐ[F] KE :=
  IsFractionRing.liftAlgHom
    (translateCoordAlgHom_injective_of_baseHom_inj W xk yk h_eq hxy hxinj)

omit [DecidableEq F] in
/-- **`translateX_xy_ne_const_of_pole`**: a pole of `translateX_xy` at infinity
forces non-constancy: if `ordAtInfty (translateX_xy) < 0` then `translateX_xy`
is not `algebraMap F KE c` for any `c : F`. -/
theorem translateX_xy_ne_const_of_pole (xk yk : F) (c : F)
    (h_pole : (W_smooth W).ordAtInfty (translateX_xy W xk yk) < 0)
    (hc : translateX_xy W xk yk = algebraMap F KE c) : False := by
  classical
  by_cases hc_zero : c = 0
  · have h0 : translateX_xy W xk yk = 0 := by rw [hc, hc_zero, map_zero]
    have h_top : (W_smooth W).ordAtInfty (translateX_xy W xk yk) = ⊤ := by
      rw [h0]; exact (W_smooth W).ordAtInfty_zero
    rw [h_top] at h_pole
    exact absurd h_pole (not_lt_of_ge le_top)
  · have h_ord_c : (W_smooth W).ordAtInfty (translateX_xy W xk yk) = 0 := by
      rw [hc]; exact ordAtInfty_algebraMap_F_nonzero W hc_zero
    rw [h_ord_c] at h_pole
    exact absurd h_pole (lt_irrefl _)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **`translateBaseHom_injective_of_transcendental`**: if `translateX_xy W xk yk`
is transcendental over `F`, then `translateBaseHom W xk yk` is injective.  Direct
from `transcendental_iff_injective` and `translateBaseHom = aeval translateX_xy`. -/
theorem translateBaseHom_injective_of_transcendental (xk yk : F)
    (h_trans : Transcendental F (translateX_xy W xk yk)) :
    Function.Injective (translateBaseHom W xk yk) := by
  change Function.Injective (Polynomial.eval₂RingHom (algebraMap F KE)
    (translateX_xy W xk yk))
  have h_eq : (Polynomial.eval₂RingHom (algebraMap F KE)
      (translateX_xy W xk yk) : Polynomial F →+* KE) =
      (Polynomial.aeval (translateX_xy W xk yk) :
        Polynomial F →ₐ[F] KE).toRingHom := by
    ext <;> simp [Polynomial.aeval_def]
  rw [h_eq]
  exact transcendental_iff_injective.mp h_trans

omit [DecidableEq F] in
private theorem ordAtInfty_sub_const_of_neg_aux {g : KE} {n : ℤ} (hn : n < 0)
    (hg : (W_smooth W).ordAtInfty g = ((n : ℤ) : WithTop ℤ)) (c : F) :
    (W_smooth W).ordAtInfty (g - algebraMap F KE c) = ((n : ℤ) : WithTop ℤ) := by
  classical
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero]; exact hg
  · refine ((W_smooth W).ordAtInfty_sub_eq_of_lt ?_).trans hg
    rw [hg, ordAtInfty_algebraMap_F_nonzero W hc]
    exact_mod_cast hn

omit [DecidableEq F] in
/-- **`ord_x_gen_sub_const`**: for any `xk ∈ F`, `ord(x_gen - xk) = -2`, since the
constant `xk` has nonnegative order while `x_gen` has order `-2`. -/
theorem ord_x_gen_sub_const (xk : F) :
    (W_smooth W).ordAtInfty (x_gen W - algebraMap F KE xk) =
      ((-2 : ℤ) : WithTop ℤ) := by
  classical
  exact ordAtInfty_sub_const_of_neg_aux W (by norm_num) (ordAtInfty_x_gen W) xk

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `x_gen W - algebraMap F KE xk ≠ 0`: from `x_gen_transcendental`, `x_gen`
is not equal to any base-field constant. -/
theorem x_gen_sub_const_ne_zero (xk : F) :
    x_gen W - algebraMap F KE xk ≠ 0 := by
  intro h_eq
  have h_x_eq : x_gen W = algebraMap F KE xk := sub_eq_zero.mp h_eq
  have h_alg : IsAlgebraic F (x_gen W) :=
    ⟨Polynomial.X - Polynomial.C xk, Polynomial.X_sub_C_ne_zero xk, by
      simp [h_x_eq]⟩
  exact (x_gen_transcendental W) h_alg

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `translateSlope_xy` simplifies via `slope_of_X_ne` since `x_gen ≠ algebraMap xk`. -/
theorem translateSlope_xy_eq (xk yk : F) :
    translateSlope_xy W xk yk =
      (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk) := by
  unfold translateSlope_xy
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  intro h_eq
  exact x_gen_sub_const_ne_zero W xk (sub_eq_zero.mpr h_eq)

omit [DecidableEq F] in
/-- **`ord_y_gen_sub_const`**: `ord(y_gen - yk) = -3` for any `yk : F`. -/
theorem ord_y_gen_sub_const (yk : F) :
    (W_smooth W).ordAtInfty (y_gen W - algebraMap F KE yk) =
      ((-3 : ℤ) : WithTop ℤ) := by
  classical
  exact ordAtInfty_sub_const_of_neg_aux W (by norm_num) (ordAtInfty_y_gen W) yk

omit [DecidableEq F] in
/-- **`ord_translateSlope_xy`**: `ord(translateSlope_xy) = -1` for non-zero
`xk` (so the slope is in secant form). -/
theorem ord_translateSlope_xy (xk yk : F) :
    (W_smooth W).ordAtInfty (translateSlope_xy W xk yk) =
      ((-1 : ℤ) : WithTop ℤ) := by
  rw [translateSlope_xy_eq W xk yk]
  exact (W_smooth W).ordAtInfty_div_of_ord_eq (x_gen_sub_const_ne_zero W xk)
    (-3) (-2) (ord_y_gen_sub_const W yk) (ord_x_gen_sub_const W xk)

end HasseWeil
