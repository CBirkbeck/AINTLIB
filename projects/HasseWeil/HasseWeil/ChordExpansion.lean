/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.FormalGroupLawSpec
import HasseWeil.FormalIsogenySeries

/-!
# Chord expansion: the specialization layer (Silverman IV §1 at isogeny pullbacks)

This file specializes the pure power-series layer of
`HasseWeil.FormalGroupLawSpec` (the `(z,w)`-chart Weierstrass operator, the
bivariate slope `λ`, Hensel uniqueness) at the local expansions of isogeny
pullbacks (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., IV §1,
pp. 119–120). Strategy and ticket board: `.mathlib-quality/plan-iv1.md`
(decision D2: all substitution is routed through the one-variable `w`-series;
no Laurent-series substitution anywhere) and `.mathlib-quality/tickets-iv1.md`
(FG-B1/B2/B3).

## Main results

* **FG-B1 keystone** `localExpand_wPair`: for an *abstract* point-like pair
  `(ξ, η)` in `K(E)` satisfying the Weierstrass equation, with an `x`-pole at
  `O` and `z`-expansion `localExpand (−ξ/η) = ofPowerSeries f`, the
  `w`-expansion is the substituted `w`-series:
  `localExpand (−η⁻¹) = ofPowerSeries (w ∘ f)`. The abstract-pair form is
  deliberate: FG-B5 reuses it at the chord-sum point `(X₃, Y₃′)`, not just at
  isogeny pullbacks. The engine is `eq_subst_formalW_of_fixedPoint`
  (Silverman IV.1.1(b)).
* `localExpand_pullback_localParam` (the Laurent → PowerSeries descent for
  `α*t`) and the isogeny corollary `localExpand_pullback_wFunc`
  (`w_α = w ∘ f_α`).
* **FG-B2** `localExpand_x_pair`/`localExpand_y_pair` (+ isogeny corollaries
  `localExpand_pullback_x_gen`/`localExpand_pullback_y_gen`): the chart
  identities `x = z/w`, `y = −1/w` pushed through `localExpand`, and the
  nonvanishing brick `subst_formalW_pair_ne_zero`.
* **FG-B3** `zwSlope` (the `(z,w)`-chart chord slope — *not* the `(x,y)`-slope
  `addSlopePair`) with `localExpand_zwSlope_eq`: its expansion is the
  bivariate slope series substituted at `(f_α, f_β)`. The wiring lemma
  `pullback_localParam_ne_of_pullback_x_ne` converts the chord hypothesis
  `α*x ≠ β*x` into the denominator hypothesis `α*t ≠ β*t`.
* **FG-B4/B4a** the chart-Vieta identity: the `(x,y)`-line through the two
  images is `y = ℓx + c` (`ℓ = addSlopePair`, `c = addLineC`), whose
  `(z,w)`-chart data is `λ = zwSlopeLine = −ℓ/c`, `ν = zwNuLine = −1/c`.
  `addPullback_vieta_cleared` is the *cleared* third-root identity
  `(−X₃)·A(λ) = ((−t_α − t_β)·A(λ) − B(λ,ν))·Y₃′` covering both the chord and
  the tangent branch (the free-variable Vieta core is shared; only the root-
  multiset inputs `he₂/he₃` differ). The nonvanishing bricks are
  `addLineC_ne_zero_of_x_ne`/`addLineC_ne_zero_of_x_eq` (the latter via the
  monic-cubic combination `x_gen_cubic_ne_zero`). The expansion legs FG-B5
  consumes: `localExpand_zwSlopeLine_of_x_ne` (chord, via the bridge
  `zwSlopeLine_eq_zwSlope` to FG-B3) and `localExpand_zwSlopeLine_of_x_eq`
  (tangent, FG-B4a — by *substituting* the implicit-differentiation identity
  `w′·(1 − f_w) = f_z`, valid for inseparable summands where `f_α′ = 0`),
  plus the ν-legs `localExpand_zwNuLine_of_x_ne`/`_of_x_eq` (both through the
  parametric `localExpand_zwNuLine_eq` and the bridge `zwNuLine_eq_sub`).
* **FG-B5 / T-IV-BRIDGE-003, the milestone** `formalIsogenySeries_add`
  (Silverman IV.1.4, `F(z₁,z₂) = i(z₃)`): the `z = −x/y` expansion of the
  chord-tangent sum `α(P) + β(P)` is the formal group law substituted at
  `(f_α, f_β)`. Statement relocated from `FormalIsogenySeries.lean`. The
  reusable sub-steps are `subst_formalW_of_expansions` (Hensel identification
  of a *supplied* `w`-expansion — no pole hypotheses) and
  `localExpand_neg_div_negY_of_expansions` (the `i(z₃)` inversion move).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV §1.
-/

open WeierstrassCurve PowerSeries LaurentSeries

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-! ### Laurent → PowerSeries descent

A Laurent series with nonnegative `orderTop` is faithfully described by its
`ℕ`-indexed coefficients; this is the reconstruction brick that converts the
`localExpand` world into the `PowerSeries` world where the Hensel uniqueness
of `FormalGroupLawSpec` operates. -/

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- A Laurent series with nonnegative `orderTop` is the `ofPowerSeries` image
of the power series of its `ℕ`-indexed coefficients. -/
theorem ofPowerSeries_mk_coeff {S : LaurentSeries F} (h : 0 ≤ S.orderTop) :
    HahnSeries.ofPowerSeries ℤ F (PowerSeries.mk fun n ↦ S.coeff (n : ℤ)) = S := by
  ext j
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
  · have hnr : j ∉ Set.range ((↑) : ℕ → ℤ) := by rintro ⟨n, rfl⟩; omega
    have hL : (HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.mk fun n ↦ S.coeff (n : ℤ))).coeff j = 0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      exact HahnSeries.embDomain_notin_range hnr
    have hR : S.coeff j = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (by exact_mod_cast hj) h)
    rw [hL, hR]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- If the `ofPowerSeries` image of `f` has positive `orderTop`, then `f` has
zero constant coefficient. -/
theorem constantCoeff_eq_zero_of_ofPowerSeries_orderTop_pos {f : PowerSeries F}
    (h : 0 < (HahnSeries.ofPowerSeries ℤ F f).orderTop) :
    PowerSeries.constantCoeff f = 0 := by
  have h0 : (HahnSeries.ofPowerSeries ℤ F f).coeff ((0 : ℕ) : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by exact_mod_cast h)
  rwa [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- An element with a pole at `O` is nonzero. -/
theorem ne_zero_of_ordAtInfty_neg {ξ : KE} (h : (W_smooth W).ordAtInfty ξ < 0) :
    ξ ≠ 0 := by
  intro h0
  have htop : (W_smooth W).ordAtInfty ξ = ⊤ := ((W_smooth W).ordAtInfty_eq_top_iff ξ).mpr h0
  rw [htop] at h
  exact not_top_lt h

/-- The local-parameter pullback as the `z`-coordinate of the pullback pair:
`α*t = −(α*x)/(α*y)`. -/
theorem pullback_localParam_eq (α : Isogeny W.toAffine W.toAffine) :
    α.pullback (localParam W) =
      -(α.pullback (x_gen W)) / α.pullback (y_gen W) := by
  unfold localParam
  rw [map_div₀, map_neg]

/-- **The Laurent → PowerSeries descent for `α*t`**: for a summand that
reduces to `O` (`ord_∞(α*x) < 0`), the local expansion of `α*t` *is* the
`ofPowerSeries` image of the formal isogeny series. -/
theorem localExpand_pullback_localParam (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (α.pullback (localParam W)) =
      HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α) := by
  unfold formalIsogenySeries
  exact (ofPowerSeries_mk_coeff
    (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α).le).symm

/-! ### FG-B1: the keystone `w = w(z)` for an abstract equation-satisfying pair

Silverman IV §1, p. 120: the `(z,w)`-chart image of a point-like pair on the
curve satisfies `w = f(z, w)`; by IV.1.1(b)-uniqueness (Hensel), its
`w`-expansion is therefore the canonical `w`-series substituted at its
`z`-expansion. We state this for an *abstract* pair `(ξ, η) ∈ K(E)²`
satisfying the Weierstrass equation with an `x`-pole at `O` — the two
instantiations are isogeny pullbacks `(α*x, α*y)` (here) and the FG-B5
chord-sum pair `(addPullback_x_pair, negY-line-value)`. -/

/-- The `(z,w)`-chart identity in an abstract field: dividing the Weierstrass
equation by `−y³` exhibits `w = −1/y` as a value of the `(z,w)`-Weierstrass
operator at `z = −x/y`. Stated over a generic field and instantiated (the
shape matches `weierstrassZWAt` term-for-term). -/
private lemma zw_identity_of_weierstrass {K : Type*} [Field K] (a₁ a₂ a₃ a₄ a₆ x y : K)
    (hy : y ≠ 0)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) :
    (-y⁻¹ : K) = (-x / y) ^ 3 + a₁ * (-x / y) * (-y⁻¹) + a₂ * (-x / y) ^ 2 * (-y⁻¹)
      + a₃ * (-y⁻¹) ^ 2 + a₄ * (-x / y) * (-y⁻¹) ^ 2 + a₆ * (-y⁻¹) ^ 3 := by
  field_simp
  linear_combination -h

/-- **FG-B1, the abstract keystone** (`w_pair = w ∘ z_pair`): for a pair
`(ξ, η)` in `K(E)` satisfying the Weierstrass equation, with an `x`-pole at
`O` (`ord_∞ ξ < 0`) and `z`-expansion `localExpand (−ξ/η) = ofPowerSeries f`,
the `w = −1/η` expansion is the `w`-series substituted at `f`:

`localExpand (−η⁻¹) = ofPowerSeries (PowerSeries.subst f (formalW W))`.

Proof: push the `(z,w)`-Weierstrass identity (an identity in `K(E)`,
equivalent to the curve equation) through the ring hom `localExpand`, descend
along the injective `ofPowerSeries` to a fixed point of `weierstrassZWAt W f`
in `F⟦z⟧`, and conclude by the Hensel uniqueness engine
`eq_subst_formalW_of_fixedPoint` ([Sil] IV.1.1(b)). -/
theorem localExpand_wPair {ξ η : KE} {f : PowerSeries F}
    (h_weier : (W_KE W).toAffine.Equation ξ η)
    (hξ_neg : (W_smooth W).ordAtInfty ξ < 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f) :
    localExpand W (-η⁻¹) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) := by
  -- Nonvanishing of the pair.
  have hξ_ne : ξ ≠ 0 := ne_zero_of_ordAtInfty_neg W hξ_neg
  have hη_ne : η ≠ 0 :=
    ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg W hξ_ne h_weier hξ_neg
  -- The `z`-expansion has positive order, so `f` has positive order.
  have hz_pos : 0 < (localExpand W (-ξ / η)).orderTop := by
    rw [orderTop_localExpand_eq_ordAtInfty W]
    exact ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg W hξ_ne hη_ne h_weier hξ_neg
  have hf0 : PowerSeries.constantCoeff f = 0 :=
    constantCoeff_eq_zero_of_ofPowerSeries_orderTop_pos (hz ▸ hz_pos)
  have hf_ord : 1 ≤ PowerSeries.order f :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf0
  -- The `w`-expansion has positive order (`η` has a pole at `O`).
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W).ordAtInfty η = (n : WithTop ℤ) := by
    cases hh : (W_smooth W).ordAtInfty η with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hη_ne
    | coe k => exact ⟨k, rfl⟩
  have hn_neg : n < 0 := by
    have h1 : (W_smooth W).ordAtInfty η < 0 :=
      lt_trans (ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg W hξ_ne hη_ne
        h_weier hξ_neg) hξ_neg
    rw [hn] at h1
    exact_mod_cast h1
  have h_ord_w : (W_smooth W).ordAtInfty (-η⁻¹ : KE) = ((-n : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans
      (((W_smooth W).ordAtInfty_inv _).trans (by rw [hn]; rfl))
  have hw_pos : 0 < (localExpand W (-η⁻¹ : KE)).orderTop := by
    rw [orderTop_localExpand_eq_ordAtInfty W, h_ord_w,
      show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
    omega
  -- Reconstruct the `w`-expansion as a power series `s` of positive order
  -- (`s` is introduced as an opaque variable so that the `localExpand`-to-
  -- `ofPowerSeries` rewrite below terminates).
  obtain ⟨s, hs_def⟩ : ∃ s : PowerSeries F,
      s = PowerSeries.mk fun k ↦ (localExpand W (-η⁻¹ : KE)).coeff (k : ℤ) := ⟨_, rfl⟩
  have hwfact : localExpand W (-η⁻¹ : KE) = HahnSeries.ofPowerSeries ℤ F s := by
    rw [hs_def]
    exact (ofPowerSeries_mk_coeff hw_pos.le).symm
  have hs0 : PowerSeries.constantCoeff s = 0 :=
    constantCoeff_eq_zero_of_ofPowerSeries_orderTop_pos (hwfact ▸ hw_pos)
  have hs_ord : 1 ≤ PowerSeries.order s :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hs0
  -- The Weierstrass equation, with the base-changed coefficients spelled
  -- through `algebraMap` (definitionally equal).
  have h_weier' : η ^ 2 + algebraMap F KE W.a₁ * ξ * η + algebraMap F KE W.a₃ * η
      = ξ ^ 3 + algebraMap F KE W.a₂ * ξ ^ 2 + algebraMap F KE W.a₄ * ξ
        + algebraMap F KE W.a₆ := by
    have h := (Affine.equation_iff _ _).mp h_weier
    exact h
  -- The `(z,w)`-chart identity in `K(E)`.
  have hKE : (-η⁻¹ : KE) = (-ξ / η) ^ 3
      + algebraMap F KE W.a₁ * (-ξ / η) * (-η⁻¹)
      + algebraMap F KE W.a₂ * (-ξ / η) ^ 2 * (-η⁻¹)
      + algebraMap F KE W.a₃ * (-η⁻¹) ^ 2
      + algebraMap F KE W.a₄ * (-ξ / η) * (-η⁻¹) ^ 2
      + algebraMap F KE W.a₆ * (-η⁻¹) ^ 3 :=
    zw_identity_of_weierstrass _ _ _ _ _ ξ η hη_ne h_weier'
  -- Push through `localExpand` and rewrite both charts as `ofPowerSeries`.
  have hL := congrArg (localExpand W) hKE
  simp only [map_add, map_mul, map_pow, localExpand_algebraMap, hz, hwfact] at hL
  -- Descend along the injective `ofPowerSeries` to a fixed point in `F⟦z⟧`.
  have hfix : s = weierstrassZWAt W f s := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F)
    simp only [weierstrassZWAt, map_add, map_mul, map_pow]
    linear_combination hL
  -- Hensel uniqueness: the fixed point is `w ∘ f`.
  rw [hwfact]
  exact congrArg (HahnSeries.ofPowerSeries ℤ F)
    (eq_subst_formalW_of_fixedPoint W f hf_ord s hs_ord hfix)

/-- **FG-B1, the isogeny corollary** (`w_α = w ∘ f_α`): for an isogeny whose
`x`-pullback has a pole at `O`, the local expansion of `α*(−1/y)` is the
`w`-series substituted at the formal isogeny series. [Sil] IV §1 p. 120. -/
theorem localExpand_pullback_wFunc (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (α.pullback (-(y_gen W)⁻¹)) =
      HahnSeries.ofPowerSeries ℤ F
        (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) := by
  rw [show α.pullback (-(y_gen W)⁻¹) = -(α.pullback (y_gen W))⁻¹ by
    rw [map_neg, map_inv₀]]
  refine localExpand_wPair W (pullback_equation_inl W α) h_α ?_
  rw [← pullback_localParam_eq W α]
  exact localExpand_pullback_localParam W α h_α

/-! ### FG-B2: the coordinate expansions `x = z/w`, `y = −1/w`

[Sil] IV §1 p. 115: the chart inverse. Both the abstract-pair and the
isogeny-pullback forms are recorded; the nonvanishing brick
`subst_formalW_pair_ne_zero` makes the divisions lawful downstream. -/

/-- The chart identity `x = z/w` in an abstract field. -/
private lemma x_eq_z_div_w {K : Type*} [Field K] (x y : K) (hy : y ≠ 0) :
    x = (-x / y) / (-y⁻¹ : K) := by
  rw [neg_div, neg_div_neg_eq, div_div, mul_inv_cancel₀ hy, div_one]

/-- The chart identity `y = −1/w` in an abstract field. -/
private lemma y_eq_neg_inv_w {K : Type*} [Field K] (y : K) : y = -(-y⁻¹ : K)⁻¹ := by
  rw [inv_neg, inv_inv, neg_neg]

/-- **FG-B2, abstract pair, nonvanishing**: the substituted `w`-series of an
equation-satisfying pair with an `x`-pole is nonzero (it expands the nonzero
function `−η⁻¹`). -/
theorem subst_formalW_pair_ne_zero {ξ η : KE} {f : PowerSeries F}
    (h_weier : (W_KE W).toAffine.Equation ξ η)
    (hξ_neg : (W_smooth W).ordAtInfty ξ < 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f) :
    PowerSeries.subst f (formalW W) ≠ 0 := by
  have hξ_ne : ξ ≠ 0 := ne_zero_of_ordAtInfty_neg W hξ_neg
  have hη_ne : η ≠ 0 :=
    ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg W hξ_ne h_weier hξ_neg
  intro h0
  apply neg_ne_zero.mpr (inv_ne_zero hη_ne)
  apply RingHom.injective (localExpand W)
  rw [localExpand_wPair W h_weier hξ_neg hz, h0, map_zero, map_zero]

/-- **FG-B2, abstract pair, `x`-leg**: `localExpand ξ = ofPS f / ofPS (w∘f)`. -/
theorem localExpand_x_pair {ξ η : KE} {f : PowerSeries F}
    (h_weier : (W_KE W).toAffine.Equation ξ η)
    (hξ_neg : (W_smooth W).ordAtInfty ξ < 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f) :
    localExpand W ξ =
      HahnSeries.ofPowerSeries ℤ F f /
        HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) := by
  have hξ_ne : ξ ≠ 0 := ne_zero_of_ordAtInfty_neg W hξ_neg
  have hη_ne : η ≠ 0 :=
    ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg W hξ_ne h_weier hξ_neg
  calc localExpand W ξ = localExpand W ((-ξ / η) / (-η⁻¹ : KE)) :=
        congrArg _ (x_eq_z_div_w ξ η hη_ne)
    _ = _ := by rw [map_div₀, hz, localExpand_wPair W h_weier hξ_neg hz]

/-- **FG-B2, abstract pair, `y`-leg**: `localExpand η = −(ofPS (w∘f))⁻¹`. -/
theorem localExpand_y_pair {ξ η : KE} {f : PowerSeries F}
    (h_weier : (W_KE W).toAffine.Equation ξ η)
    (hξ_neg : (W_smooth W).ordAtInfty ξ < 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f) :
    localExpand W η =
      -(HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))⁻¹ := by
  calc localExpand W η = localExpand W (-(-η⁻¹ : KE)⁻¹) := congrArg _ (y_eq_neg_inv_w η)
    _ = _ := by rw [map_neg, map_inv₀, localExpand_wPair W h_weier hξ_neg hz]

/-- The `hz` input of the abstract-pair lemmas, at an isogeny pullback. -/
theorem localExpand_pullback_z_eq_ofPowerSeries (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (-(α.pullback (x_gen W)) / α.pullback (y_gen W)) =
      HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α) := by
  rw [← pullback_localParam_eq W α]
  exact localExpand_pullback_localParam W α h_α

/-- **FG-B2 nonvanishing brick (isogeny form)**: `w ∘ f_α ≠ 0`. -/
theorem subst_formalIsogenySeries_formalW_ne_zero (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    PowerSeries.subst (formalIsogenySeries W α) (formalW W) ≠ 0 :=
  subst_formalW_pair_ne_zero W (pullback_equation_inl W α) h_α
    (localExpand_pullback_z_eq_ofPowerSeries W α h_α)

/-- **FG-B2, `x`-leg (isogeny form)**: `localExpand (α*x) = ofPS f_α / ofPS (w∘f_α)`. -/
theorem localExpand_pullback_x_gen (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (α.pullback (x_gen W)) =
      HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W α) /
        HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.subst (formalIsogenySeries W α) (formalW W)) :=
  localExpand_x_pair W (pullback_equation_inl W α) h_α
    (localExpand_pullback_z_eq_ofPowerSeries W α h_α)

/-- **FG-B2, `y`-leg (isogeny form)**: `localExpand (α*y) = −(ofPS (w∘f_α))⁻¹`. -/
theorem localExpand_pullback_y_gen (α : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0) :
    localExpand W (α.pullback (y_gen W)) =
      -(HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.subst (formalIsogenySeries W α) (formalW W)))⁻¹ :=
  localExpand_y_pair W (pullback_equation_inl W α) h_α
    (localExpand_pullback_z_eq_ofPowerSeries W α h_α)

/-! ### FG-B3: the `(z,w)`-chart chord slope

[Sil] IV §1 p. 119: the slope of the line through the two formal points.
The slope is taken in the `(z,w)` chart (`z = −x/y`, `w = −1/y`), *not* the
`(x,y)` chart of `addSlopePair`; its expansion is the bivariate slope series
`formalSlopeBiv` substituted at the pair of formal isogeny series. -/

omit [DecidableEq F] in
/-- Substitution into a bivariate difference (the `substAlgHom` transport;
`MvPowerSeries.subst` has no bundled `map_sub`). -/
private lemma mv_subst_sub (b : Fin 2 → PowerSeries F) (hb : MvPowerSeries.HasSubst b)
    (u v : MvPowerSeries (Fin 2) F) :
    MvPowerSeries.subst b (u - v) =
      MvPowerSeries.subst b u - MvPowerSeries.subst b v := by
  have h := map_sub (MvPowerSeries.substAlgHom (R := F) hb) u v
  rwa [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.substAlgHom_apply] at h

omit [DecidableEq F] in
/-- Substituting a `Fin 2`-family into an embedded univariate series picks out
the component: `subst b (g ∘ X i) = g ∘ (b i)`. -/
private lemma subst_subst_X (b : Fin 2 → PowerSeries F) (hb : MvPowerSeries.HasSubst b)
    (i : Fin 2) (φ : PowerSeries F) :
    MvPowerSeries.subst b
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) F) φ) =
      PowerSeries.subst (b i) φ := by
  have hX : MvPowerSeries.HasSubst
      (fun _ : Unit ↦ (MvPowerSeries.X i : MvPowerSeries (Fin 2) F)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦
      MvPowerSeries.constantCoeff_X (R := F) i
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply hX hb]
  congr 1
  funext u
  exact MvPowerSeries.subst_X hb i

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The divided-difference spec of `formalSlopeBiv` substituted at a general
`Fin 2`-family: `(b₁ − b₀) · (λ ∘ b) = w∘b₁ − w∘b₀`. -/
private lemma subst_formalSlopeBiv_spec (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b) :
    (b 1 - b 0) * MvPowerSeries.subst b (formalSlopeBiv W) =
      PowerSeries.subst (b 1) (formalW W) - PowerSeries.subst (b 0) (formalW W) := by
  have h := congrArg (MvPowerSeries.subst b) (formalSlopeBiv_spec W)
  rwa [MvPowerSeries.subst_mul hb, mv_subst_sub b hb, mv_subst_sub b hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    subst_subst_X b hb, subst_subst_X b hb] at h

/-- Sign bookkeeping over a generic commutative ring (instantiated at
`PowerSeries F` by `exact`; `ring` does not normalise `PowerSeries` goals in
this toolchain). -/
private lemma sub_swap_mul {A : Type*} [CommRing A] {a b l u v : A}
    (h : (b - a) * l = v - u) : u - v = (a - b) * l := by
  linear_combination h

/-- The **`(z,w)`-chart slope** of the chord through the `α`- and `β`-images
of the generic point: `(w_α − w_β)/(z_α − z_β)`. NOT the `(x,y)`-slope
`addSlopePair`. [Sil] IV §1 p. 119 (the line through the two formal points). -/
noncomputable def zwSlope (α β : Isogeny W.toAffine W.toAffine) : KE :=
  (α.pullback (-(y_gen W)⁻¹) - β.pullback (-(y_gen W)⁻¹)) /
    (α.pullback (localParam W) - β.pullback (localParam W))

/-- Unfolding lemma for `zwSlope`. -/
theorem zwSlope_def (α β : Isogeny W.toAffine W.toAffine) :
    zwSlope W α β =
      (α.pullback (-(y_gen W)⁻¹) - β.pullback (-(y_gen W)⁻¹)) /
        (α.pullback (localParam W) - β.pullback (localParam W)) :=
  rfl

/-- `zwSlope` is antisymmetric in the pair. -/
theorem zwSlope_comm (α β : Isogeny W.toAffine W.toAffine) :
    zwSlope W α β = zwSlope W β α := by
  rw [zwSlope_def, zwSlope_def, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- The two formal isogeny series of a `t`-pullback-coincident pair agree. -/
theorem formalIsogenySeries_eq_of_pullback_localParam_eq
    {α β : Isogeny W.toAffine W.toAffine}
    (ht : α.pullback (localParam W) = β.pullback (localParam W)) :
    formalIsogenySeries W α = formalIsogenySeries W β := by
  unfold formalIsogenySeries
  rw [ht]

/-- **The chord-hypothesis converter** (FG-B3 wiring for FG-B4): distinct
`x`-pullbacks force distinct `t`-pullbacks. Contrapositive: `t` determines
`w` through FG-B1, hence `x = z/w` through FG-B2. -/
theorem pullback_localParam_ne_of_pullback_x_ne {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    α.pullback (localParam W) ≠ β.pullback (localParam W) := by
  intro ht
  apply h_x
  apply RingHom.injective (localExpand W)
  rw [localExpand_pullback_x_gen W α h_α, localExpand_pullback_x_gen W β h_β,
    formalIsogenySeries_eq_of_pullback_localParam_eq W ht]

/-- For an isogeny pair whose `x`-pullbacks have negative order at infinity, the
two formal isogeny series have vanishing constant term, so the `Fin 2` family
`![f_α, f_β]` is a lawful substitution family. This is the lawfulness side
condition for the `(z,w)`-slope expansion. -/
private lemma hasSubst_formalIsogenySeries_pair (α β : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0) :
    MvPowerSeries.HasSubst
      (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F) := by
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  have hg0 : PowerSeries.constantCoeff (formalIsogenySeries W β) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W β
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W β h_β)
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> simpa [hf0, hg0]

/-- The slope denominator is nonzero in the Laurent field: if the two `t`-pullbacks
differ, then `ofPowerSeries (f_α − f_β) ≠ 0`. The two formal series differ
because `localExpand` is injective and sends them to the two distinct
`t`-pullbacks, and `ofPowerSeries` is injective. -/
private lemma ofPowerSeries_sub_formalIsogenySeries_ne_zero
    {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_t_ne : α.pullback (localParam W) ≠ β.pullback (localParam W)) :
    HahnSeries.ofPowerSeries ℤ F
        (formalIsogenySeries W α - formalIsogenySeries W β) ≠ 0 := by
  have hfg : formalIsogenySeries W α - formalIsogenySeries W β ≠ 0 := by
    intro h0
    apply h_t_ne
    apply RingHom.injective (localExpand W)
    rw [localExpand_pullback_localParam W α h_α,
      localExpand_pullback_localParam W β h_β, sub_eq_zero.mp h0]
  exact fun h ↦ hfg (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

/-- **FG-B3, the `(z,w)`-slope expansion (chord case)**: the local expansion
of the `(z,w)`-chart chord slope is the bivariate slope series substituted at
the pair of formal isogeny series:

`localExpand (zwSlope α β) = ofPS (subst ![f_α, f_β] (formalSlopeBiv W))`.

[Sil] IV §1 p. 119 — Silverman's `z₁, z₂` play exactly the role of
`f_α, f_β`. -/
theorem localExpand_zwSlope_eq (α β : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_t_ne : α.pullback (localParam W) ≠ β.pullback (localParam W)) :
    localExpand W (zwSlope W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalSlopeBiv W)) := by
  -- Constant coefficients vanish, so the substitution is lawful.
  have hb := hasSubst_formalIsogenySeries_pair W α β h_α h_β
  -- The substituted divided-difference spec at `(f_α, f_β)`.
  have hspec := subst_formalSlopeBiv_spec W _ hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hspec
  -- The four expansions.
  have hzα := localExpand_pullback_localParam W α h_α
  have hzβ := localExpand_pullback_localParam W β h_β
  have hwα := localExpand_pullback_wFunc W α h_α
  have hwβ := localExpand_pullback_wFunc W β h_β
  -- The denominator is nonzero.
  have hofg_ne := ofPowerSeries_sub_formalIsogenySeries_ne_zero W h_α h_β h_t_ne
  -- Assemble in the Laurent field.
  rw [zwSlope_def, map_div₀, map_sub, map_sub, hwα, hwβ, hzα, hzβ, ← map_sub, ← map_sub,
    show PowerSeries.subst (formalIsogenySeries W α) (formalW W)
        - PowerSeries.subst (formalIsogenySeries W β) (formalW W)
      = (formalIsogenySeries W α - formalIsogenySeries W β) *
          MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalSlopeBiv W) from sub_swap_mul hspec,
    map_mul]
  exact mul_div_cancel_left₀ _ hofg_ne

/-! ### FG-B4: the free-variable chart-Vieta core

[Sil] IV §1 pp. 119–120, the substituted chord cubic and its Vieta sum, made
into pure field algebra. Over a generic field `K`, with the `(x,y)`-line
`y = ℓx + c` (slope `ℓ` a *free* variable — both the chord and the tangent
branch feed the same core) and a third abscissa `x₃`, the hypotheses
`he₁/he₂/he₃` say that `x₁, x₂, x₃` are the full root multiset of the
substituted `(x,y)`-cubic
`Φ(x) = x³ − Sx² + Px − Q`, `S = ℓ² + a₁ℓ − a₂`, `P = a₄ − 2ℓc − a₁c − a₃ℓ`,
`Q = c² + a₃c − a₆`. The chord case derives `he₂/he₃` from the two curve
equations and `x₁ ≠ x₂` (`chord_e₂/chord_e₃`); the tangent case from one curve
equation and the tangent-slope relation (`tangent_e₂/tangent_e₃`); the free-ℓ
identity *without* a branch hypothesis is false (the third-intersection
formula presumes the root multiset).

The `(z,w)`-chart line is `w = λz + ν` with `λ = −ℓ/c`, `ν = −1/c` (from
`x = z/w`, `y = −1/w`), and the two Vieta engines are
`vieta_Ac : c³A(λ) = y₁y₂y₃` and `vieta_Bc : c³B(λ,ν) = Σᵢ xᵢ ∏_{j≠i} yⱼ`
(with `yᵢ = ℓxᵢ + c` the line values), which together give the cleared
chart-Vieta identity `vieta_assembly`. -/

section VietaCore

variable {K : Type*} [Field K]

/-- The `A`-engine: the cleared leading coefficient `c³·A(λ)` of the `(z,w)`-chord
cubic is the product of the three line values `yᵢ = ℓxᵢ + c`. -/
private lemma vieta_Ac (a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ ℓ c : K)
    (he₁ : x₁ + x₂ + x₃ = ℓ ^ 2 + a₁ * ℓ - a₂)
    (he₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ)
    (he₃ : x₁ * x₂ * x₃ = c ^ 2 + a₃ * c - a₆) :
    c ^ 3 - a₂ * ℓ * c ^ 2 + a₄ * ℓ ^ 2 * c - a₆ * ℓ ^ 3
      = (ℓ * x₁ + c) * ((ℓ * x₂ + c) * (ℓ * x₃ + c)) := by
  linear_combination (-(ℓ * c ^ 2)) * he₁ + (-(ℓ ^ 2 * c)) * he₂ + (-ℓ ^ 3) * he₃

/-- The `B`-engine: the cleared `z²`-coefficient `c³·B(λ,ν)` of the `(z,w)`-chord
cubic is the second symmetric function `Σᵢ xᵢ ∏_{j≠i} yⱼ` of the roots against
the line values. -/
private lemma vieta_Bc (a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ ℓ c : K)
    (he₁ : x₁ + x₂ + x₃ = ℓ ^ 2 + a₁ * ℓ - a₂)
    (he₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ)
    (he₃ : x₁ * x₂ * x₃ = c ^ 2 + a₃ * c - a₆) :
    -(a₁ * ℓ * c ^ 2) - a₂ * c ^ 2 + a₃ * ℓ ^ 2 * c + 2 * (a₄ * ℓ * c) - 3 * (a₆ * ℓ ^ 2)
      = x₃ * ((ℓ * x₁ + c) * (ℓ * x₂ + c)) + x₂ * ((ℓ * x₁ + c) * (ℓ * x₃ + c))
        + x₁ * ((ℓ * x₂ + c) * (ℓ * x₃ + c)) := by
  linear_combination (-(c ^ 2)) * he₁ + (-(2 * (ℓ * c))) * he₂ + (-(3 * ℓ ^ 2)) * he₃

/-- Chord branch, `e₂`: the second Vieta coefficient at `x₃ = S − x₁ − x₂`, from
the two curve equations, the on-line hypothesis and `x₁ ≠ x₂` (divided
difference `(Φ(x₁) − Φ(x₂))/(x₁ − x₂) = 0`). -/
private lemma chord_e₂ (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ ℓ c : K) (hx : x₁ ≠ x₂)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hc : c = y₁ - ℓ * x₁) (hline : y₂ = ℓ * x₂ + c) :
    x₁ * x₂ + x₁ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₂) + x₂ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₂)
      = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hx)
  linear_combination h₁ - h₂ + (y₂ + ℓ * x₂ + c + a₁ * x₂ + a₃) * hline
    + (y₁ + ℓ * x₁ + c + a₁ * x₁ + a₃) * hc

/-- Chord branch, `e₃`: the third Vieta coefficient at `x₃ = S − x₁ − x₂`
(the combination `(x₂Φ(x₁) − x₁Φ(x₂))/(x₂ − x₁) = 0`). -/
private lemma chord_e₃ (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ ℓ c : K) (hx : x₁ ≠ x₂)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hc : c = y₁ - ℓ * x₁) (hline : y₂ = ℓ * x₂ + c) :
    x₁ * x₂ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₂) = c ^ 2 + a₃ * c - a₆ := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr hx)
  linear_combination x₂ * h₁ - x₁ * h₂ + x₁ * (y₂ + ℓ * x₂ + c + a₁ * x₂ + a₃) * hline
    + x₂ * (y₁ + ℓ * x₁ + c + a₁ * x₁ + a₃) * hc

/-- Tangent branch, `e₂`: at `x₂ = x₁` the double-root condition is the
vanishing of `Φ′(x₁)`, which is exactly the (cleared) tangent-slope relation
`htan`. -/
private lemma tangent_e₂ (a₁ a₂ a₃ a₄ x₁ y₁ ℓ c : K)
    (hc : c = y₁ - ℓ * x₁)
    (htan : ℓ * (2 * y₁ + a₁ * x₁ + a₃) = 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) :
    x₁ * x₁ + x₁ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₁) + x₁ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₁)
      = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ := by
  linear_combination htan + (2 * ℓ + a₁) * hc

/-- Tangent branch, `e₃`: from `Φ(x₁) = 0` (the curve equation) and `Φ′(x₁) = 0`
(the tangent-slope relation). -/
private lemma tangent_e₃ (a₁ a₂ a₃ a₄ a₆ x₁ y₁ ℓ c : K)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (hc : c = y₁ - ℓ * x₁)
    (htan : ℓ * (2 * y₁ + a₁ * x₁ + a₃) = 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) :
    x₁ * x₁ * (ℓ ^ 2 + a₁ * ℓ - a₂ - x₁ - x₁) = c ^ 2 + a₃ * c - a₆ := by
  linear_combination x₁ * htan + (x₁ * (2 * ℓ + a₁) - (y₁ + ℓ * x₁ + c + a₁ * x₁ + a₃)) * hc - h₁

/-- The fully cleared (polynomial) chart-Vieta identity: with `Ac = c³A(λ)` and
`Bc = c³B(λ,ν)` the two engines combine, denominator-free, into
`(−x₃·Ac)·y₁y₂ = ((x₁y₂ + x₂y₁)Ac − Bc·y₁y₂)·Y₃′` where `Y₃′ = ℓ(x₃−x₁)+y₁` is
the pre-negation line value at the third root. -/
private lemma vieta_cleared_poly (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ x₃ ℓ c : K)
    (hcdef : c = y₁ - ℓ * x₁) (hline : y₂ = ℓ * x₂ + c)
    (he₁ : x₁ + x₂ + x₃ = ℓ ^ 2 + a₁ * ℓ - a₂)
    (he₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ)
    (he₃ : x₁ * x₂ * x₃ = c ^ 2 + a₃ * c - a₆) :
    (-x₃ * (c ^ 3 - a₂ * ℓ * c ^ 2 + a₄ * ℓ ^ 2 * c - a₆ * ℓ ^ 3)) * (y₁ * y₂)
      = ((x₁ * y₂ + x₂ * y₁) * (c ^ 3 - a₂ * ℓ * c ^ 2 + a₄ * ℓ ^ 2 * c - a₆ * ℓ ^ 3)
          - (-(a₁ * ℓ * c ^ 2) - a₂ * c ^ 2 + a₃ * ℓ ^ 2 * c + 2 * (a₄ * ℓ * c)
              - 3 * (a₆ * ℓ ^ 2)) * (y₁ * y₂))
        * (ℓ * (x₃ - x₁) + y₁) := by
  have hy₁' : ℓ * x₁ + c = y₁ := by linear_combination hcdef
  have hy₂' : ℓ * x₂ + c = y₂ := by linear_combination -hline
  have hAc := vieta_Ac a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ ℓ c he₁ he₂ he₃
  have hBc := vieta_Bc a₁ a₂ a₃ a₄ a₆ x₁ x₂ x₃ ℓ c he₁ he₂ he₃
  rw [← hy₁', ← hy₂']
  linear_combination
    (-(x₃ * ((ℓ * x₁ + c) * (ℓ * x₂ + c)))
        - (x₁ * (ℓ * x₂ + c) + x₂ * (ℓ * x₁ + c)) * (ℓ * x₃ + c)) * hAc
      + ((ℓ * x₁ + c) * ((ℓ * x₂ + c) * (ℓ * x₃ + c))) * hBc

/-- The divided-form assembly: the cleared chart-Vieta identity with the
`(z,w)`-line data `λ = −ℓ/c`, `ν = −1/c` and the chart abscissae
`zᵢ = −xᵢ/yᵢ` written as honest quotients. This is the free-variable form of
`addPullback_vieta_cleared`. -/
private lemma vieta_assembly (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ x₃ ℓ c : K)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hc : c ≠ 0)
    (hcdef : c = y₁ - ℓ * x₁) (hline : y₂ = ℓ * x₂ + c)
    (he₁ : x₁ + x₂ + x₃ = ℓ ^ 2 + a₁ * ℓ - a₂)
    (he₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * (ℓ * c) - a₁ * c - a₃ * ℓ)
    (he₃ : x₁ * x₂ * x₃ = c ^ 2 + a₃ * c - a₆) :
    (-x₃) * (1 + a₂ * (-ℓ / c) + a₄ * (-ℓ / c) ^ 2 + a₆ * (-ℓ / c) ^ 3)
      = ((-(-x₁ / y₁) - -x₂ / y₂)
            * (1 + a₂ * (-ℓ / c) + a₄ * (-ℓ / c) ^ 2 + a₆ * (-ℓ / c) ^ 3)
          - (a₁ * (-ℓ / c) + a₂ * (-1 / c) + a₃ * (-ℓ / c) ^ 2
              + 2 * (a₄ * (-ℓ / c) * (-1 / c)) + 3 * (a₆ * (-ℓ / c) ^ 2 * (-1 / c))))
        * (ℓ * (x₃ - x₁) + y₁) := by
  have hpoly := vieta_cleared_poly a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ x₃ ℓ c hcdef hline he₁ he₂ he₃
  field_simp
  linear_combination hpoly

end VietaCore

/-! ### FG-B4: the `(z,w)`-line data of the chord/tangent line at the pullback pair

The `(x,y)`-line through the `α`- and `β`-images is `y = ℓx + c` with
`ℓ = addSlopePair α β` (mathlib's slope, covering both branches) and intercept
`c = addLineC α β`. In the `(z,w)`-chart (`z = −x/y`, `w = −1/y`) the same
line reads `w = λz + ν` with `λ = −ℓ/c`, `ν = −1/c` — division only by `c`.
The two nonvanishing bricks `addLineC_ne_zero_of_x_ne` (chord, via the
`t`-pullback separation) and `addLineC_ne_zero_of_x_eq` (tangent, via the
monic cubic `x³ − a₄x − 2a₆ + a₃y ≠ 0` in `K(E)`) make the chart data lawful. -/

/-- The `y`-intercept `c = y_α − ℓ·x_α` of the `(x,y)`-line through the `α`-
and `β`-images of the generic point (`ℓ = addSlopePair α β`). -/
noncomputable def addLineC (α β : Isogeny W.toAffine W.toAffine) : KE :=
  α.pullback (y_gen W) - addSlopePair α β * α.pullback (x_gen W)

/-- Unfolding lemma for `addLineC`. -/
theorem addLineC_def (α β : Isogeny W.toAffine W.toAffine) :
    addLineC W α β =
      α.pullback (y_gen W) - addSlopePair α β * α.pullback (x_gen W) :=
  rfl

/-- The `(z,w)`-chart slope `λ = −ℓ/c` of the line through the `α`- and
`β`-images. In the chord case this is `zwSlope α β`
(`zwSlopeLine_eq_zwSlope`); unlike the divided difference it also makes sense
in the tangent case. -/
noncomputable def zwSlopeLine (α β : Isogeny W.toAffine W.toAffine) : KE :=
  -addSlopePair α β / addLineC W α β

/-- Unfolding lemma for `zwSlopeLine`. -/
theorem zwSlopeLine_def (α β : Isogeny W.toAffine W.toAffine) :
    zwSlopeLine W α β = -addSlopePair α β / addLineC W α β :=
  rfl

/-- The `(z,w)`-chart intercept `ν = −1/c` of the line through the `α`- and
`β`-images. -/
noncomputable def zwNuLine (α β : Isogeny W.toAffine W.toAffine) : KE :=
  -1 / addLineC W α β

/-- Unfolding lemma for `zwNuLine`. -/
theorem zwNuLine_def (α β : Isogeny W.toAffine W.toAffine) :
    zwNuLine W α β = -1 / addLineC W α β :=
  rfl

/-- The `y`-pullback of an isogeny is nonzero (pullbacks are injective). -/
theorem pullback_y_gen_ne_zero (α : Isogeny W.toAffine W.toAffine) :
    α.pullback (y_gen W) ≠ 0 := fun h ↦
  y_gen_ne_zero W (α.pullback_injective (h.trans (map_zero _).symm))

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Constants travel through `F[X] → F[W] → K(E)` as constants. -/
private lemma coordRing_map_C (a : F) :
    algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing (Polynomial.C a))
        = algebraMap F KE a := by
  rw [show (Polynomial.C a : Polynomial F) = algebraMap F (Polynomial F) a from rfl,
    ← IsScalarTower.algebraMap_apply F (Polynomial F) W.toAffine.CoordinateRing,
    ← IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing KE]

omit [DecidableEq F] in
/-- The combination `x³ − a₄x − 2a₆ + a₃y` of the generic coordinates is
nonzero in `K(E)`: it is the image of the coordinate-ring element with
basis coordinates `(X³ − a₄X − 2a₆, a₃)` against the power basis `{1, Y}`,
and the first coordinate is a monic cubic. ([Sil] III.3: the coordinate ring
is free of rank 2 over `F[x]`.) -/
theorem x_gen_cubic_ne_zero :
    x_gen W ^ 3 - algebraMap F KE W.a₄ * x_gen W - 2 * algebraMap F KE W.a₆
      + algebraMap F KE W.a₃ * y_gen W ≠ 0 := by
  intro h
  -- The basis coordinates of the element.
  set p : Polynomial F :=
    Polynomial.X ^ 3 - Polynomial.C W.a₄ * Polynomial.X - Polynomial.C (2 * W.a₆) with hp_def
  -- The coordinate-ring element vanishes (the algebra map to `K(E)` is injective).
  have hG : p • (1 : W.toAffine.CoordinateRing)
      + Polynomial.C W.a₃ • Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0 := by
    apply IsFractionRing.injective W.toAffine.CoordinateRing KE
    have himg : algebraMap W.toAffine.CoordinateRing KE
        (p • (1 : W.toAffine.CoordinateRing)
          + Polynomial.C W.a₃ • Affine.CoordinateRing.mk W.toAffine Polynomial.X)
        = x_gen W ^ 3 - algebraMap F KE W.a₄ * x_gen W - 2 * algebraMap F KE W.a₆
          + algebraMap F KE W.a₃ * y_gen W := by
      rw [map_add, Algebra.smul_def, mul_one, Algebra.smul_def, map_mul, hp_def]
      simp only [map_sub, map_pow, map_mul, coordRing_map_C, map_ofNat]
      rfl
    rw [himg, map_zero]
    exact h
  -- Basis independence forces the monic cubic coordinate to vanish.
  have hp0 : p = 0 := (Affine.CoordinateRing.smul_basis_eq_zero hG).1
  have h3 := congrArg (fun r ↦ Polynomial.coeff r 3) hp0
  simp [hp_def, Polynomial.coeff_X_pow] at h3

/-- **Chord-branch nonvanishing of the line intercept**: if `α*x ≠ β*x`, then
`c = addLineC α β ≠ 0`. Otherwise the line would be `y = ℓx`, forcing
`t_α = −x_α/y_α = −x_β/y_β = t_β` and hence `α*x = β*x` through FG-B1/B2
(`pullback_localParam_ne_of_pullback_x_ne`). -/
theorem addLineC_ne_zero_of_x_ne {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    addLineC W α β ≠ 0 := by
  intro h0
  apply pullback_localParam_ne_of_pullback_x_ne W h_α h_β h_x
  have hy₁ : α.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W α
  have hy₂ : β.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W β
  have hxx : α.pullback (x_gen W) - β.pullback (x_gen W) ≠ 0 := sub_ne_zero.mpr h_x
  rw [addLineC_def, addSlopePair_eq_of_x_ne h_x] at h0
  rw [pullback_localParam_eq, pullback_localParam_eq, div_eq_div_iff hy₁ hy₂]
  field_simp at h0
  linear_combination -h0

/-- The pullback Weierstrass equation, `algebraMap`-spelled (the form
`linear_combination` certificates consume). -/
theorem pullback_weierstrass_eq (α : Isogeny W.toAffine W.toAffine) :
    α.pullback (y_gen W) ^ 2
      + algebraMap F KE W.a₁ * α.pullback (x_gen W) * α.pullback (y_gen W)
      + algebraMap F KE W.a₃ * α.pullback (y_gen W)
      = α.pullback (x_gen W) ^ 3 + algebraMap F KE W.a₂ * α.pullback (x_gen W) ^ 2
        + algebraMap F KE W.a₄ * α.pullback (x_gen W) + algebraMap F KE W.a₆ := by
  have h := (Affine.equation_iff _ _).mp (pullback_equation_inl W α)
  exact h

/-- At a tangent pair (`α*x = β*x`, non-inverse), the `y`-pullbacks agree
(mathlib's `Y_eq_of_Y_ne`). -/
theorem pullback_y_eq_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    α.pullback (y_gen W) = β.pullback (y_gen W) :=
  Affine.Y_eq_of_Y_ne (pullback_equation_inl W α) (pullback_equation_inl W β) h_x
    fun h ↦ h_ni ⟨h_x, h⟩

/-- At a tangent pair, the tangent denominator `u = 2y_α + a₁x_α + a₃` is
nonzero (the `α`-image is not 2-torsion-like, by non-inverseness). -/
theorem pullback_u_ne_zero_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    2 * α.pullback (y_gen W) + algebraMap F KE W.a₁ * α.pullback (x_gen W)
      + algebraMap F KE W.a₃ ≠ 0 := by
  have hy_ne : α.pullback (y_gen W)
      ≠ (W_KE W).toAffine.negY (β.pullback (x_gen W)) (β.pullback (y_gen W)) :=
    fun h ↦ h_ni ⟨h_x, h⟩
  have hy_ne' : α.pullback (y_gen W)
      ≠ (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W)) := by
    rw [show (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W))
        = (W_KE W).toAffine.negY (β.pullback (x_gen W)) (β.pullback (y_gen W)) by
      rw [h_x, pullback_y_eq_of_x_eq W h_x h_ni]]
    exact hy_ne
  have h := sub_ne_zero.mpr hy_ne'
  rw [show (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W))
      = -α.pullback (y_gen W) - algebraMap F KE W.a₁ * α.pullback (x_gen W)
        - algebraMap F KE W.a₃ from rfl] at h
  intro h0
  apply h
  linear_combination h0

/-- The tangent-branch slope, cleared of its denominator:
`ℓ·(2y_α + a₁x_α + a₃) = 3x_α² + 2a₂x_α + a₄ − a₁y_α`
(mathlib's `slope_of_Y_ne`, multiplied out). This is the hypothesis `htan` of
the tangent Vieta branch. -/
theorem addSlopePair_mul_u_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    addSlopePair α β
      * (2 * α.pullback (y_gen W) + algebraMap F KE W.a₁ * α.pullback (x_gen W)
          + algebraMap F KE W.a₃)
      = 3 * α.pullback (x_gen W) ^ 2 + 2 * algebraMap F KE W.a₂ * α.pullback (x_gen W)
        + algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * α.pullback (y_gen W) := by
  have hy_ne : α.pullback (y_gen W)
      ≠ (W_KE W).toAffine.negY (β.pullback (x_gen W)) (β.pullback (y_gen W)) :=
    fun h ↦ h_ni ⟨h_x, h⟩
  have h1 : addSlopePair α β
      = (3 * α.pullback (x_gen W) ^ 2
          + 2 * algebraMap F KE W.a₂ * α.pullback (x_gen W) + algebraMap F KE W.a₄
          - algebraMap F KE W.a₁ * α.pullback (y_gen W))
        / (α.pullback (y_gen W)
            - (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W))) :=
    Affine.slope_of_Y_ne h_x hy_ne
  have hden : α.pullback (y_gen W)
      - (-α.pullback (y_gen W) - algebraMap F KE W.a₁ * α.pullback (x_gen W)
          - algebraMap F KE W.a₃)
      = 2 * α.pullback (y_gen W) + algebraMap F KE W.a₁ * α.pullback (x_gen W)
        + algebraMap F KE W.a₃ := by ring
  rw [h1, show (W_KE W).toAffine.negY (α.pullback (x_gen W)) (α.pullback (y_gen W))
      = -α.pullback (y_gen W) - algebraMap F KE W.a₁ * α.pullback (x_gen W)
        - algebraMap F KE W.a₃ from rfl, hden,
    div_mul_cancel₀ _ (pullback_u_ne_zero_of_x_eq W h_x h_ni)]

/-- **Tangent-branch nonvanishing of the line intercept**: at a tangent pair
(`α*x = β*x`, non-inverse), `c = addLineC α β ≠ 0`. The cleared intercept is
`c·(2y_α + a₁x_α + a₃) = −(x_α³ − a₄x_α − 2a₆ + a₃y_α)`, the pullback of the
nonzero combination of `x_gen_cubic_ne_zero`. -/
theorem addLineC_ne_zero_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    addLineC W α β ≠ 0 := by
  -- The cleared intercept identity `c·u = −(x³ − a₄x − 2a₆ + a₃y)` at the pullback.
  have hcu : addLineC W α β
      * (2 * α.pullback (y_gen W) + algebraMap F KE W.a₁ * α.pullback (x_gen W)
          + algebraMap F KE W.a₃)
      = -(α.pullback (x_gen W) ^ 3 - algebraMap F KE W.a₄ * α.pullback (x_gen W)
          - 2 * algebraMap F KE W.a₆ + algebraMap F KE W.a₃ * α.pullback (y_gen W)) := by
    rw [addLineC_def]
    linear_combination 2 * pullback_weierstrass_eq W α
      + (-(α.pullback (x_gen W))) * addSlopePair_mul_u_of_x_eq W h_x h_ni
  intro h0
  rw [h0, zero_mul] at hcu
  have hg0 : α.pullback (x_gen W) ^ 3 - algebraMap F KE W.a₄ * α.pullback (x_gen W)
      - 2 * algebraMap F KE W.a₆ + algebraMap F KE W.a₃ * α.pullback (y_gen W) = 0 :=
    neg_eq_zero.mp hcu.symm
  apply x_gen_cubic_ne_zero W
  apply α.pullback_injective
  rw [map_zero]
  simp only [map_add, map_sub, map_pow, map_mul, map_ofNat, AlgHom.commutes]
  exact hg0

/-- **FG-B4/B4a, the chart-Vieta identity (cleared form, both branches)**:
for summands with `x`-poles at `O` and a non-inverse pair, the third
intersection point of the chord/tangent line satisfies, in `K(E)`,

`(−X₃)·A(λ) = ((−t_α − t_β)·A(λ) − B(λ,ν))·Y₃′`,

where `X₃ = addPullback_x_pair`, `Y₃′ = negY X₃ Y₃` is the *pre-negation*
line value at the third root, `λ = zwSlopeLine`, `ν = zwNuLine` are the
`(z,w)`-chart line data, and `A = 1 + a₂λ + a₄λ² + a₆λ³`,
`B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν` are the chord-cubic coefficients
(mirroring `chordA`/`chordB`). Dividing by `A` and `Y₃′` (which FG-B5 does on
the series side, where `A` expands to a unit) this is the corrected
`z₃ = −z₁ − z₂ − B/A` of [Sil] IV §1 p. 119 at the pullback pair. -/
theorem addPullback_vieta_cleared (α β : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_ni : AddNonInversePair α β) :
    (-addPullback_x_pair α β)
        * (1 + algebraMap F KE W.a₂ * zwSlopeLine W α β
            + algebraMap F KE W.a₄ * zwSlopeLine W α β ^ 2
            + algebraMap F KE W.a₆ * zwSlopeLine W α β ^ 3)
      = ((-α.pullback (localParam W) - β.pullback (localParam W))
              * (1 + algebraMap F KE W.a₂ * zwSlopeLine W α β
                  + algebraMap F KE W.a₄ * zwSlopeLine W α β ^ 2
                  + algebraMap F KE W.a₆ * zwSlopeLine W α β ^ 3)
            - (algebraMap F KE W.a₁ * zwSlopeLine W α β
                + algebraMap F KE W.a₂ * zwNuLine W α β
                + algebraMap F KE W.a₃ * zwSlopeLine W α β ^ 2
                + 2 • (algebraMap F KE W.a₄ * zwSlopeLine W α β * zwNuLine W α β)
                + 3 • (algebraMap F KE W.a₆ * zwSlopeLine W α β ^ 2 * zwNuLine W α β)))
          * (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β) := by
  have hy₁ : α.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W α
  have hy₂ : β.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W β
  -- The third abscissa, unfolded (`addX`).
  have hX₃ : addPullback_x_pair α β
      = addSlopePair α β ^ 2 + algebraMap F KE W.a₁ * addSlopePair α β
        - algebraMap F KE W.a₂ - α.pullback (x_gen W) - β.pullback (x_gen W) := rfl
  -- The pre-negation line value (`negY ∘ addY = negAddY`).
  have hY₃ : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      = addSlopePair α β * (addPullback_x_pair α β - α.pullback (x_gen W))
        + α.pullback (y_gen W) :=
    Affine.negY_negY (W' := (W_KE W).toAffine) _ _
  have he₁ : α.pullback (x_gen W) + β.pullback (x_gen W) + addPullback_x_pair α β
      = addSlopePair α β ^ 2 + algebraMap F KE W.a₁ * addSlopePair α β
        - algebraMap F KE W.a₂ := by
    linear_combination hX₃
  rw [zwSlopeLine_def, zwNuLine_def, pullback_localParam_eq W α, pullback_localParam_eq W β,
    hY₃]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h_x : α.pullback (x_gen W) = β.pullback (x_gen W)
  · -- Tangent branch: `ℓ` is the tangent slope, `Φ` has a double root at `x_α`.
    have hc : addLineC W α β ≠ 0 := addLineC_ne_zero_of_x_eq W h_x h_ni
    have htan := addSlopePair_mul_u_of_x_eq W h_x h_ni
    have hline : β.pullback (y_gen W)
        = addSlopePair α β * β.pullback (x_gen W) + addLineC W α β := by
      rw [addLineC_def, ← h_x]
      linear_combination -pullback_y_eq_of_x_eq W h_x h_ni
    have he₂ : α.pullback (x_gen W) * β.pullback (x_gen W)
        + α.pullback (x_gen W) * addPullback_x_pair α β
        + β.pullback (x_gen W) * addPullback_x_pair α β
        = algebraMap F KE W.a₄ - 2 * (addSlopePair α β * addLineC W α β)
          - algebraMap F KE W.a₁ * addLineC W α β
          - algebraMap F KE W.a₃ * addSlopePair α β := by
      rw [hX₃, ← h_x]
      exact tangent_e₂ _ _ _ _ _ _ _ _ (addLineC_def W α β) htan
    have he₃ : α.pullback (x_gen W) * β.pullback (x_gen W) * addPullback_x_pair α β
        = addLineC W α β ^ 2 + algebraMap F KE W.a₃ * addLineC W α β
          - algebraMap F KE W.a₆ := by
      rw [hX₃, ← h_x]
      exact tangent_e₃ _ _ _ _ _ _ _ _ _ (pullback_weierstrass_eq W α)
        (addLineC_def W α β) htan
    exact vieta_assembly _ _ _ _ _ _ _ _ _ _ _ _ hy₁ hy₂ hc (addLineC_def W α β) hline
      he₁ he₂ he₃
  · -- Chord branch: `x₁ ≠ x₂`, the divided-difference Vieta coefficients.
    have hc : addLineC W α β ≠ 0 := addLineC_ne_zero_of_x_ne W h_α h_β h_x
    have hline : β.pullback (y_gen W)
        = addSlopePair α β * β.pullback (x_gen W) + addLineC W α β := by
      have hxx : α.pullback (x_gen W) - β.pullback (x_gen W) ≠ 0 := sub_ne_zero.mpr h_x
      rw [addLineC_def, addSlopePair_eq_of_x_ne h_x]
      field_simp
      ring
    have he₂ : α.pullback (x_gen W) * β.pullback (x_gen W)
        + α.pullback (x_gen W) * addPullback_x_pair α β
        + β.pullback (x_gen W) * addPullback_x_pair α β
        = algebraMap F KE W.a₄ - 2 * (addSlopePair α β * addLineC W α β)
          - algebraMap F KE W.a₁ * addLineC W α β
          - algebraMap F KE W.a₃ * addSlopePair α β := by
      rw [hX₃]
      exact chord_e₂ _ _ _ _ _ _ _ _ _ _ _ h_x (pullback_weierstrass_eq W α)
        (pullback_weierstrass_eq W β) (addLineC_def W α β) hline
    have he₃ : α.pullback (x_gen W) * β.pullback (x_gen W) * addPullback_x_pair α β
        = addLineC W α β ^ 2 + algebraMap F KE W.a₃ * addLineC W α β
          - algebraMap F KE W.a₆ := by
      rw [hX₃]
      exact chord_e₃ _ _ _ _ _ _ _ _ _ _ _ h_x (pullback_weierstrass_eq W α)
        (pullback_weierstrass_eq W β) (addLineC_def W α β) hline
    exact vieta_assembly _ _ _ _ _ _ _ _ _ _ _ _ hy₁ hy₂ hc (addLineC_def W α β) hline
      he₁ he₂ he₃

/-! ### The λ- and ν-legs: expansions of the `(z,w)`-line data

FG-B5 consumes, per branch, the matches `localExpand λ = ofPS (λ_biv ∘ (f_α, f_β))`
and `localExpand ν = ofPS (ν_biv ∘ (f_α, f_β))`. The chord λ-leg routes through
FG-B3's divided difference (`zwSlopeLine_eq_zwSlope`); the tangent λ-leg
(FG-B4a) is below. The ν-leg is uniform in the branch, parametric in the λ-leg. -/

/-- **The chord bridge**: in the chord case, the line-data slope `−ℓ/c` *is*
the `(z,w)` divided-difference slope `zwSlope` of FG-B3 (both compute the
slope of the same line through two distinct `(z,w)`-points). -/
theorem zwSlopeLine_eq_zwSlope {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    zwSlopeLine W α β = zwSlope W α β := by
  have ht_ne := pullback_localParam_ne_of_pullback_x_ne W h_α h_β h_x
  have hc := addLineC_ne_zero_of_x_ne W h_α h_β h_x
  have hy₁ : α.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W α
  have hy₂ : β.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W β
  have hxx : α.pullback (x_gen W) - β.pullback (x_gen W) ≠ 0 := sub_ne_zero.mpr h_x
  -- The cleared two-point slope identity `(w_α − w_β)·c = −ℓ·(t_α − t_β)`.
  have hkey : (α.pullback (-(y_gen W)⁻¹) - β.pullback (-(y_gen W)⁻¹)) * addLineC W α β
      = -addSlopePair α β
          * (α.pullback (localParam W) - β.pullback (localParam W)) := by
    rw [addLineC_def, addSlopePair_eq_of_x_ne h_x, pullback_localParam_eq W α,
      pullback_localParam_eq W β,
      show α.pullback (-(y_gen W)⁻¹) = -(α.pullback (y_gen W))⁻¹ by rw [map_neg, map_inv₀],
      show β.pullback (-(y_gen W)⁻¹) = -(β.pullback (y_gen W))⁻¹ by rw [map_neg, map_inv₀]]
    field_simp
    ring
  rw [zwSlopeLine_def, zwSlope_def, div_eq_div_iff hc (sub_ne_zero.mpr ht_ne)]
  linear_combination -hkey

/-- **The ν-bridge** (FG-B4 item 4, ν-side): the line-data intercept is the
intercept of the `(z,w)`-line through the `α`-image with slope `zwSlopeLine`:
`ν = w_α − λ·t_α`. Branch-free (only `c ≠ 0` is needed). -/
theorem zwNuLine_eq_sub {α β : Isogeny W.toAffine W.toAffine}
    (hc : addLineC W α β ≠ 0) :
    zwNuLine W α β
      = α.pullback (-(y_gen W)⁻¹) - zwSlopeLine W α β * α.pullback (localParam W) := by
  have hy₁ : α.pullback (y_gen W) ≠ 0 := pullback_y_gen_ne_zero W α
  rw [zwNuLine_def, zwSlopeLine_def, pullback_localParam_eq W α,
    show α.pullback (-(y_gen W)⁻¹) = -(α.pullback (y_gen W))⁻¹ by rw [map_neg, map_inv₀]]
  field_simp
  linear_combination addLineC_def W α β

/-- **The chord λ-leg** (FG-B4 item 4): the expansion of the line-data slope is
the bivariate slope series substituted at `(f_α, f_β)` — via the bridge to
FG-B3's `localExpand_zwSlope_eq`. -/
theorem localExpand_zwSlopeLine_of_x_ne {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    localExpand W (zwSlopeLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalSlopeBiv W)) := by
  rw [zwSlopeLine_eq_zwSlope W h_α h_β h_x]
  exact localExpand_zwSlope_eq W α β h_α h_β
    (pullback_localParam_ne_of_pullback_x_ne W h_α h_β h_x)

/-- **The ν-leg, parametric in the λ-leg** (uniform over the two branches):
given the λ-expansion match, the line-data intercept `ν = −1/c` expands to the
intercept series `formalNuBiv` substituted at `(f_α, f_β)`. The `K(E)`-side
input is `ν = w_α − λ·t_α` (the line through the `α`-image). -/
theorem localExpand_zwNuLine_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (hc : addLineC W α β ≠ 0)
    (h_lam : localExpand W (zwSlopeLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalSlopeBiv W))) :
    localExpand W (zwNuLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalNuBiv W)) := by
  -- The substitution is lawful (FG-B3's block).
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  have hg0 : PowerSeries.constantCoeff (formalIsogenySeries W β) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W β
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W β h_β)
  have hb : MvPowerSeries.HasSubst
      (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    fin_cases s <;> simpa [hf0, hg0]
  -- The `K(E)`-side line identity `ν = w_α − λ·t_α`.
  have hKE := zwNuLine_eq_sub W (α := α) (β := β) hc
  -- The series-side intercept decomposition `ν∘b = w∘f_α − f_α·(λ∘b)`.
  have hser : MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
        (formalNuBiv W)
      = PowerSeries.subst (formalIsogenySeries W α) (formalW W)
        - formalIsogenySeries W α
          * MvPowerSeries.subst
              (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
              (formalSlopeBiv W) := by
    rw [show formalNuBiv W
        = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) F)
            (formalW W) - MvPowerSeries.X 0 * formalSlopeBiv W from rfl,
      mv_subst_sub _ hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb,
      subst_subst_X _ hb]
    simp only [Matrix.cons_val_zero]
  rw [hKE, map_sub, map_mul, localExpand_pullback_wFunc W α h_α, h_lam,
    localExpand_pullback_localParam W α h_α, hser, map_sub, map_mul]
  ring

/-! ### FG-B4a: the tangent λ-leg

The tangent slope's expansion is computed *without dividing by `f′`* (which can
vanish for inseparable summands): the univariate implicit-differentiation
identity `w′·(1 − f_w(X, w)) = f_z(X, w)` (from differentiating the
`w = f(z,w)` fixed point) is *substituted* at `f_α` — substitution is a ring
hom, so no chain rule and no `f′` appear — and the matching `K(E)`-side
identity `λ·(1 − f_w(t_α, w_α)) = f_z(t_α, w_α)` is pure field algebra modulo
the curve equation and the (cleared) tangent-slope relation. Cancelling the
common unit factor `1 − f_w∘` in the Laurent field identifies
`localExpand λ = ofPS (w′ ∘ f_α)`, and `formalSlopeBiv_diag` converts to the
bivariate form `λ_biv ∘ (f_α, f_α)`. -/

/-- Rearrangement of the differentiated fixed-point equation into the implicit
form `w′·(1 − f_w) = f_z` (abstract commutative-ring identity, because `ring`
cannot normalise `PowerSeries` goals in this toolchain). -/
private lemma implicit_diff_rearrange {A : Type*} [CommRing A] (a₁ a₂ a₃ a₄ a₆ z w w' : A)
    (h : w' = 3 * z ^ 2 + (a₁ * z * w' + w * a₁) + (a₂ * z ^ 2 * w' + w * (a₂ * (2 * z)))
        + a₃ * (2 * (w * w')) + (a₄ * z * (2 * (w * w')) + w ^ 2 * a₄)
        + a₆ * (3 * (w ^ 2 * w'))) :
    w' * (1 - (a₁ * z + a₂ * z ^ 2 + 2 * (a₃ * w) + 2 * (a₄ * (z * w)) + 3 * (a₆ * w ^ 2)))
      = 3 * z ^ 2 + a₁ * w + 2 * (a₂ * (z * w)) + a₄ * w ^ 2 := by
  linear_combination h

omit [DecidableEq F] [W.toAffine.IsElliptic] in
-- The transparency override is required for `Derivation.leibniz`-headed simp
-- rewrites to match on `PowerSeries` (the same override mathlib's
-- `PowerSeries.derivative_pow` needs).
set_option backward.isDefEq.respectTransparency false in
/-- **The univariate implicit-differentiation identity** (FG-B4a step (i)):
`w′·(1 − f_w(X, w)) = f_z(X, w)`, where `f_z, f_w` are the partials of the
`(z,w)`-Weierstrass operator `f(z,s) = z³ + a₁zs + a₂z²s + a₃s² + a₄zs² + a₆s³`.
Obtained by differentiating the fixed point `w = f(X, w)` ([Sil] IV.1.1). -/
private lemma derivative_formalW_key :
    d⁄dX F (formalW W)
        * (1 - (PowerSeries.C W.a₁ * PowerSeries.X + PowerSeries.C W.a₂ * PowerSeries.X ^ 2
            + 2 * (PowerSeries.C W.a₃ * formalW W)
            + 2 * (PowerSeries.C W.a₄ * (PowerSeries.X * formalW W))
            + 3 * (PowerSeries.C W.a₆ * formalW W ^ 2)))
      = 3 * PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * formalW W
        + 2 * (PowerSeries.C W.a₂ * (PowerSeries.X * formalW W))
        + PowerSeries.C W.a₄ * formalW W ^ 2 := by
  have hd := congrArg (d⁄dX F) (formalW_fixedPoint W)
  unfold weierstrassZWAt at hd
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
    PowerSeries.derivative_C, smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  exact implicit_diff_rearrange (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃)
    (PowerSeries.C W.a₄) (PowerSeries.C W.a₆) PowerSeries.X (formalW W)
    (d⁄dX F (formalW W)) hd

omit [DecidableEq F] [W.toAffine.IsElliptic] in
-- The transparency override is again required for the `map_*` rewrites to
-- match through the `substAlgHom` coercion.
set_option backward.isDefEq.respectTransparency false in
/-- **The substituted implicit-differentiation identity** (FG-B4a step (ii)):
substituting any lawful `f` into step (i) — substitution is a ring hom, so the
identity transports with *no* chain rule and *no* `f′` (this is what makes the
tangent case work for inseparable summands, where `f′ = 0`).

De-privatized 2026-06-11: the IV.4.3 chain-rule leaf (`pullback_invariantDiff_coeff_zero`,
`GapQfKernel.lean`, FG-C4) consumes this as its `hkey` input. -/
lemma subst_derivative_formalW_key (f : PowerSeries F) (hf : PowerSeries.HasSubst f) :
    PowerSeries.subst f (d⁄dX F (formalW W))
        * (1 - (PowerSeries.C W.a₁ * f + PowerSeries.C W.a₂ * f ^ 2
            + 2 * (PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
            + 2 * (PowerSeries.C W.a₄ * (f * PowerSeries.subst f (formalW W)))
            + 3 * (PowerSeries.C W.a₆ * PowerSeries.subst f (formalW W) ^ 2)))
      = 3 * f ^ 2 + PowerSeries.C W.a₁ * PowerSeries.subst f (formalW W)
        + 2 * (PowerSeries.C W.a₂ * (f * PowerSeries.subst f (formalW W)))
        + PowerSeries.C W.a₄ * PowerSeries.subst f (formalW W) ^ 2 := by
  have h := congrArg (PowerSeries.substAlgHom (R := F) hf) (derivative_formalW_key W)
  simp only [map_mul, map_sub, map_add, map_one, map_pow, map_ofNat] at h
  simpa only [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hf, subst_C' f hf] using h

/-- The `K(E)`-side tangent-slope identity `λ·(1 − f_w(z₁, w₁)) = f_z(z₁, w₁)`
(free-variable core): the chart-transformed tangent slope `−ℓ/c` satisfies the
implicit-differentiation relation of the `(z,w)`-curve at the point
`(z₁, w₁) = (−x₁/y₁, −1/y₁)`. Pure field algebra modulo the curve equation and
the cleared tangent-slope relation. -/
private lemma tangent_zwslope_core {K : Type*} [Field K] (a₁ a₂ a₃ a₄ a₆ x₁ y₁ ℓ c : K)
    (hy₁ : y₁ ≠ 0) (hc : c ≠ 0) (hcdef : c = y₁ - ℓ * x₁)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (htan : ℓ * (2 * y₁ + a₁ * x₁ + a₃) = 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) :
    -ℓ / c * (1 - (a₁ * (-x₁ / y₁) + a₂ * (-x₁ / y₁) ^ 2 + 2 * (a₃ * -y₁⁻¹)
        + 2 * (a₄ * (-x₁ / y₁ * -y₁⁻¹)) + 3 * (a₆ * (-y₁⁻¹) ^ 2)))
      = 3 * (-x₁ / y₁) ^ 2 + a₁ * -y₁⁻¹ + 2 * (a₂ * (-x₁ / y₁ * -y₁⁻¹))
        + a₄ * (-y₁⁻¹) ^ 2 := by
  subst hcdef
  field_simp
  linear_combination (-3 * ℓ) * h₁ + y₁ * htan

/-- The `K(E)`-side tangent-slope identity at the pullback pair (FG-B4a step
(iii)): `zwSlopeLine·(1 − f_w(t_α, w_α)) = f_z(t_α, w_α)`. -/
private lemma zwSlopeLine_mul_eq_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    zwSlopeLine W α β
        * (1 - (algebraMap F KE W.a₁ * α.pullback (localParam W)
            + algebraMap F KE W.a₂ * α.pullback (localParam W) ^ 2
            + 2 * (algebraMap F KE W.a₃ * α.pullback (-(y_gen W)⁻¹))
            + 2 * (algebraMap F KE W.a₄
                * (α.pullback (localParam W) * α.pullback (-(y_gen W)⁻¹)))
            + 3 * (algebraMap F KE W.a₆ * α.pullback (-(y_gen W)⁻¹) ^ 2)))
      = 3 * α.pullback (localParam W) ^ 2
        + algebraMap F KE W.a₁ * α.pullback (-(y_gen W)⁻¹)
        + 2 * (algebraMap F KE W.a₂
            * (α.pullback (localParam W) * α.pullback (-(y_gen W)⁻¹)))
        + algebraMap F KE W.a₄ * α.pullback (-(y_gen W)⁻¹) ^ 2 := by
  rw [zwSlopeLine_def, pullback_localParam_eq W α,
    show α.pullback (-(y_gen W)⁻¹) = -(α.pullback (y_gen W))⁻¹ by rw [map_neg, map_inv₀]]
  exact tangent_zwslope_core _ _ _ _ _ _ _ _ _ (pullback_y_gen_ne_zero W α)
    (addLineC_ne_zero_of_x_eq W h_x h_ni) (addLineC_def W α β)
    (pullback_weierstrass_eq W α) (addSlopePair_mul_u_of_x_eq W h_x h_ni)

/-- **The tangent λ-leg (FG-B4a)**: at a tangent pair, the expansion of the
line-data slope is the bivariate slope series substituted at `(f_α, f_β)`
(with `f_β = f_α`). Valid for *all* summands, including inseparable ones
(`f_α′ = 0`): the route is the substituted implicit-differentiation identity,
never the chain rule. -/
theorem localExpand_zwSlopeLine_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    localExpand W (zwSlopeLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalSlopeBiv W)) := by
  -- `f_β = f_α`, and the diagonal of the slope series is `w′ ∘ f_α`.
  have ht : α.pullback (localParam W) = β.pullback (localParam W) := by
    rw [pullback_localParam_eq W α, pullback_localParam_eq W β, h_x,
      pullback_y_eq_of_x_eq W h_x h_ni]
  have hfβ : formalIsogenySeries W β = formalIsogenySeries W α :=
    (formalIsogenySeries_eq_of_pullback_localParam_eq W ht).symm
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  have hford : 1 ≤ (formalIsogenySeries W α).order :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf0
  have hsub : PowerSeries.HasSubst (formalIsogenySeries W α) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  rw [hfβ, formalSlopeBiv_diag W (formalIsogenySeries W α) hford]
  -- The two factor-expansions: `f_w∘` and `f_z∘`.
  have hfw : localExpand W (algebraMap F KE W.a₁ * α.pullback (localParam W)
        + algebraMap F KE W.a₂ * α.pullback (localParam W) ^ 2
        + 2 * (algebraMap F KE W.a₃ * α.pullback (-(y_gen W)⁻¹))
        + 2 * (algebraMap F KE W.a₄
            * (α.pullback (localParam W) * α.pullback (-(y_gen W)⁻¹)))
        + 3 * (algebraMap F KE W.a₆ * α.pullback (-(y_gen W)⁻¹) ^ 2))
      = HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.C W.a₁ * formalIsogenySeries W α
            + PowerSeries.C W.a₂ * formalIsogenySeries W α ^ 2
            + 2 * (PowerSeries.C W.a₃
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W))
            + 2 * (PowerSeries.C W.a₄ * (formalIsogenySeries W α
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W)))
            + 3 * (PowerSeries.C W.a₆
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W) ^ 2)) := by
    simp only [map_add, map_mul, map_pow, map_ofNat, localExpand_algebraMap,
      localExpand_pullback_localParam W α h_α, localExpand_pullback_wFunc W α h_α,
      show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
      show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3]
  have hfz : localExpand W (3 * α.pullback (localParam W) ^ 2
        + algebraMap F KE W.a₁ * α.pullback (-(y_gen W)⁻¹)
        + 2 * (algebraMap F KE W.a₂
            * (α.pullback (localParam W) * α.pullback (-(y_gen W)⁻¹)))
        + algebraMap F KE W.a₄ * α.pullback (-(y_gen W)⁻¹) ^ 2)
      = HahnSeries.ofPowerSeries ℤ F
          (3 * formalIsogenySeries W α ^ 2
            + PowerSeries.C W.a₁ * PowerSeries.subst (formalIsogenySeries W α) (formalW W)
            + 2 * (PowerSeries.C W.a₂ * (formalIsogenySeries W α
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W)))
            + PowerSeries.C W.a₄
              * PowerSeries.subst (formalIsogenySeries W α) (formalW W) ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat, localExpand_algebraMap,
      localExpand_pullback_localParam W α h_α, localExpand_pullback_wFunc W α h_α,
      show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
      show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3]
  -- The `K(E)`-side identity, pushed to the Laurent field.
  have hL := congrArg (localExpand W) (zwSlopeLine_mul_eq_of_x_eq W h_x h_ni)
  rw [map_mul, map_sub, map_one, hfw, hfz] at hL
  -- The series-side identity, pushed to the Laurent field.
  have hser := congrArg (HahnSeries.ofPowerSeries ℤ F)
    (subst_derivative_formalW_key W (formalIsogenySeries W α) hsub)
  rw [map_mul, map_sub, map_one] at hser
  -- Cancel the common unit factor `1 − f_w∘`.
  have hD_ne : (1 : LaurentSeries F)
      - HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.C W.a₁ * formalIsogenySeries W α
            + PowerSeries.C W.a₂ * formalIsogenySeries W α ^ 2
            + 2 * (PowerSeries.C W.a₃
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W))
            + 2 * (PowerSeries.C W.a₄ * (formalIsogenySeries W α
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W)))
            + 3 * (PowerSeries.C W.a₆
                * PowerSeries.subst (formalIsogenySeries W α) (formalW W) ^ 2)) ≠ 0 := by
    rw [show (1 : LaurentSeries F) = HahnSeries.ofPowerSeries ℤ F 1 from (map_one _).symm,
      ← map_sub]
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp [hf0, constantCoeff_subst_formalW W _ hf0] at h2
  exact mul_right_cancel₀ hD_ne (hL.trans hser.symm)

/-- **The chord ν-leg**: the intercept expansion in the chord branch. -/
theorem localExpand_zwNuLine_of_x_ne {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) ≠ β.pullback (x_gen W)) :
    localExpand W (zwNuLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalNuBiv W)) :=
  localExpand_zwNuLine_eq W h_α h_β (addLineC_ne_zero_of_x_ne W h_α h_β h_x)
    (localExpand_zwSlopeLine_of_x_ne W h_α h_β h_x)

/-- **The tangent ν-leg**: the intercept expansion in the tangent branch. -/
theorem localExpand_zwNuLine_of_x_eq {α β : Isogeny W.toAffine W.toAffine}
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_x : α.pullback (x_gen W) = β.pullback (x_gen W))
    (h_ni : AddNonInversePair α β) :
    localExpand W (zwNuLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalNuBiv W)) :=
  localExpand_zwNuLine_eq W h_α h_β (addLineC_ne_zero_of_x_eq W h_x h_ni)
    (localExpand_zwSlopeLine_of_x_eq W h_α h_x h_ni)

/-! ### FG-B5 / T-IV-BRIDGE-003: the milestone — `formalIsogenySeries_add`

[Sil] IV §1 p. 120: `F(z₁, z₂) = i(z₃(z₁, z₂))` — the `z = −x/y` expansion of
the chord-tangent sum `α(P) + β(P)` is the formal group law substituted at the
two summand series. The assembly:

1. the cleared chart-Vieta identity (`addPullback_vieta_cleared`) pushed
   through `localExpand`, against its pure-series mirror (`formalZ3·A =
   (−z₁−z₂)·A − B` substituted at `(f_α, f_β)`), gives — after cancelling the
   unit `A∘` — the *z-leg* `localExpand (−X₃/Y₃′) = ofPS (z₃ ∘ (f_α, f_β))`
   at the pre-negation pair `(X₃, Y₃′) = (addX…, negY X₃ Y₃)`;
2. the *w-leg* comes from the line: `(X₃, Y₃′)` lies on `y = ℓx + c`, so its
   `(z,w)`-chart `w`-value satisfies `−1/Y₃′ = λ·z₃′ + ν`, whose expansion is
   `ofPS (λ∘·z₃∘ + ν∘)`; Hensel uniqueness (`subst_formalW_of_expansions`)
   identifies this with `w ∘ z₃∘`. *No pole bound on `X₃` is needed* — this
   is what breaks the Wall-A `−6`-tie without circularity;
3. the inversion spec (FG-A5) substituted at `z₃∘`
   (`localExpand_neg_div_negY_of_expansions`) converts the pre-negation data
   into the expansion of `−X₃/Y₃`, as `ofPS (i ∘ z₃∘)`;
4. the substitution composition law and the chord spec
   `formalGroupLaw_eq_chord` (FG-A6) rewrite `i ∘ z₃∘` as the formal group
   law at `(f_α, f_β)`. -/

/-- Pushing a cleared Vieta identity through a ring hom, with the composite
factors transported as single atoms (so that the expansion legs can be stated
for the *whole* `A`/`B`/`z`-sum expressions). -/
private lemma cleared_push {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    {X3 AK BK T Y3' : K} {A B Tser : L}
    (hA : φ AK = A) (hB : φ BK = B) (hT : φ T = Tser)
    (hcl : (-X3) * AK = (T * AK - BK) * Y3') :
    (-(φ X3)) * A = (Tser * A - B) * φ Y3' := by
  simp only [← hA, ← hB, ← hT, ← map_neg, ← map_mul, ← map_sub]
  exact congrArg φ hcl

/-- The final chart-negation computation, as abstract field algebra: with
`x = f/w` and `y′ = −w⁻¹` (the chart values of the pre-negation pair) and the
substituted inversion spec `i·(1 − a₁f − a₃w) = −f`, the negated chart
coordinate is `i`. -/
private lemma neg_div_negY_field {K : Type*} [Field K] (a1 a3 f w i : K)
    (hw_ne : w ≠ 0) (hU : 1 - a1 * f - a3 * w ≠ 0)
    (hspec : i * (1 - a1 * f - a3 * w) = -f) :
    -(f / w) / (-(-w⁻¹) - a1 * (f / w) - a3) = i := by
  have hD : -(-w⁻¹) - a1 * (f / w) - a3 = (1 - a1 * f - a3 * w) / w := by
    field_simp
  have h1 : -(f / w) * w = -f := by field_simp
  rw [hD, div_div_eq_mul_div, h1, div_eq_iff hU]
  exact hspec.symm

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Substitution fixes constants (bivariate source, univariate target); the
`ChordExpansion` copy of the `FormalGroupLawSpec` private helper. -/
private lemma mv_subst_C (b : Fin 2 → PowerSeries F) (r : F) :
    MvPowerSeries.subst b (MvPowerSeries.C r) = PowerSeries.C r := by
  rw [show (MvPowerSeries.C r : MvPowerSeries (Fin 2) F)
      = ((MvPolynomial.C r : MvPolynomial (Fin 2) F) : MvPowerSeries (Fin 2) F) from
        (MvPolynomial.coe_C r).symm,
    MvPowerSeries.subst_coe, MvPolynomial.aeval_C]
  rfl

omit [DecidableEq F] in
/-- The substitution composition law for a univariate series substituted with a
bivariate one: `(φ ∘ g) ∘ b = φ ∘ (g ∘ b)`. -/
private lemma mv_subst_powerSeries_subst (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b) {g : MvPowerSeries (Fin 2) F}
    (hg : MvPowerSeries.HasSubst (fun _ : Unit ↦ g)) (φ : PowerSeries F) :
    MvPowerSeries.subst b (PowerSeries.subst g φ) =
      PowerSeries.subst (MvPowerSeries.subst b g) φ := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply hg hb]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The series-level cleared Vieta: `z₃·A = (−z₁ − z₂)·A − B` (multiplying the
`formalZ3` definition through by the unit `A`). -/
private lemma formalZ3_mul_chordA :
    formalZ3 W * chordA W
      = (-MvPowerSeries.X 0 - MvPowerSeries.X 1) * chordA W - chordB W := by
  rw [formalZ3]
  linear_combination (-(chordB W)) * chordA_inv_mul W

omit [DecidableEq F] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
/-- `chordA` substituted at a lawful family, termwise. -/
private lemma subst_chordA_eq (b : Fin 2 → PowerSeries F) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (chordA W)
      = 1 + PowerSeries.C W.a₂ * MvPowerSeries.subst b (formalSlopeBiv W)
        + PowerSeries.C W.a₄ * MvPowerSeries.subst b (formalSlopeBiv W) ^ 2
        + PowerSeries.C W.a₆ * MvPowerSeries.subst b (formalSlopeBiv W) ^ 3 := by
  have h1 : chordA W
      = MvPowerSeries.C (1 : F) + MvPowerSeries.C W.a₂ * formalSlopeBiv W
        + MvPowerSeries.C W.a₄ * formalSlopeBiv W ^ 2
        + MvPowerSeries.C W.a₆ * formalSlopeBiv W ^ 3 := by
    rw [chordA, map_one]
  have h := congrArg (MvPowerSeries.substAlgHom (R := F) hb) h1
  simp only [map_add, map_mul, map_pow] at h
  simpa only [MvPowerSeries.substAlgHom_apply, mv_subst_C, map_one] using h

omit [DecidableEq F] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
/-- `chordB` substituted at a lawful family, termwise (numeral form, matching
the `nsmul`-normalised Vieta identity). -/
private lemma subst_chordB_eq (b : Fin 2 → PowerSeries F) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (chordB W)
      = PowerSeries.C W.a₁ * MvPowerSeries.subst b (formalSlopeBiv W)
        + PowerSeries.C W.a₂ * MvPowerSeries.subst b (formalNuBiv W)
        + PowerSeries.C W.a₃ * MvPowerSeries.subst b (formalSlopeBiv W) ^ 2
        + 2 * (PowerSeries.C W.a₄ * MvPowerSeries.subst b (formalSlopeBiv W)
            * MvPowerSeries.subst b (formalNuBiv W))
        + 3 * (PowerSeries.C W.a₆ * MvPowerSeries.subst b (formalSlopeBiv W) ^ 2
            * MvPowerSeries.subst b (formalNuBiv W)) := by
  have h1 : chordB W
      = MvPowerSeries.C W.a₁ * formalSlopeBiv W + MvPowerSeries.C W.a₂ * formalNuBiv W
        + MvPowerSeries.C W.a₃ * formalSlopeBiv W ^ 2
        + 2 * (MvPowerSeries.C W.a₄ * formalSlopeBiv W * formalNuBiv W)
        + 3 * (MvPowerSeries.C W.a₆ * formalSlopeBiv W ^ 2 * formalNuBiv W) := by
    rw [chordB]
    ring
  have h := congrArg (MvPowerSeries.substAlgHom (R := F) hb) h1
  simp only [map_add, map_mul, map_pow, map_ofNat] at h
  simpa only [MvPowerSeries.substAlgHom_apply, mv_subst_C] using h

omit [DecidableEq F] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
/-- The substituted series-level cleared Vieta: `z₃∘·A∘ = (−b₀ − b₁)·A∘ − B∘`. -/
private lemma subst_formalZ3_mul_chordA (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (formalZ3 W) * MvPowerSeries.subst b (chordA W)
      = (-(b 0) - b 1) * MvPowerSeries.subst b (chordA W)
        - MvPowerSeries.subst b (chordB W) := by
  have h := congrArg (MvPowerSeries.substAlgHom (R := F) hb) (formalZ3_mul_chordA W)
  simp only [map_mul, map_sub, map_neg] at h
  simpa only [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X hb] using h

/-- **Hensel identification of a known `w`-expansion**: if an
equation-satisfying pair `(ξ, η)` has `z`-expansion `ofPS f` and `w`-expansion
`ofPS s`, both series with zero constant term, then `s` *is* `w ∘ f`. This is
`localExpand_wPair` with the reconstruction step replaced by a supplied
expansion — in particular **no pole hypothesis on `ξ`**, which is what lets
FG-B5 break the Wall-A order tie without circularity. -/
theorem subst_formalW_of_expansions {ξ η : KE} {f s : PowerSeries F}
    (h_weier : (W_KE W).toAffine.Equation ξ η)
    (hη_ne : η ≠ 0)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hs0 : PowerSeries.constantCoeff s = 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f)
    (hw : localExpand W (-η⁻¹) = HahnSeries.ofPowerSeries ℤ F s) :
    s = PowerSeries.subst f (formalW W) := by
  have hf_ord : 1 ≤ PowerSeries.order f :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hf0
  have hs_ord : 1 ≤ PowerSeries.order s :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hs0
  have h_weier' : η ^ 2 + algebraMap F KE W.a₁ * ξ * η + algebraMap F KE W.a₃ * η
      = ξ ^ 3 + algebraMap F KE W.a₂ * ξ ^ 2 + algebraMap F KE W.a₄ * ξ
        + algebraMap F KE W.a₆ := by
    have h := (Affine.equation_iff _ _).mp h_weier
    exact h
  have hKE : (-η⁻¹ : KE) = (-ξ / η) ^ 3
      + algebraMap F KE W.a₁ * (-ξ / η) * (-η⁻¹)
      + algebraMap F KE W.a₂ * (-ξ / η) ^ 2 * (-η⁻¹)
      + algebraMap F KE W.a₃ * (-η⁻¹) ^ 2
      + algebraMap F KE W.a₄ * (-ξ / η) * (-η⁻¹) ^ 2
      + algebraMap F KE W.a₆ * (-η⁻¹) ^ 3 :=
    zw_identity_of_weierstrass _ _ _ _ _ ξ η hη_ne h_weier'
  have hL := congrArg (localExpand W) hKE
  simp only [map_add, map_mul, map_pow, localExpand_algebraMap, hz, hw] at hL
  have hfix : s = weierstrassZWAt W f s := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F)
    simp only [weierstrassZWAt, map_add, map_mul, map_pow]
    linear_combination hL
  exact eq_subst_formalW_of_fixedPoint W f hf_ord s hs_ord hfix

set_option backward.isDefEq.respectTransparency false in
/-- **The inversion step at a chart-expanded pair** ([Sil] IV §1 p. 120, the
`i(z₃)` move): given the `z`- and `w`-expansions of `(ξ, η)`, the expansion of
the *negated* chart coordinate `−ξ/negY(ξ, η)` is the inversion series
substituted at the `z`-series. Pure chart algebra plus the FG-A5 spec — no
curve equation and no pole hypotheses. -/
theorem localExpand_neg_div_negY_of_expansions {ξ η : KE} {f : PowerSeries F}
    (hη_ne : η ≠ 0)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hz : localExpand W (-ξ / η) = HahnSeries.ofPowerSeries ℤ F f)
    (hw : localExpand W (-η⁻¹) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W))) :
    localExpand W (-ξ / (W_KE W).toAffine.negY ξ η) =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalInverse W)) := by
  have hsub : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  -- The substituted inversion spec `i∘f · (1 − a₁f − a₃(w∘f)) = −f`.
  have hspec : PowerSeries.subst f (formalInverse W)
      * (1 - PowerSeries.C W.a₁ * f
          - PowerSeries.C W.a₃ * PowerSeries.subst f (formalW W))
      = -f := by
    have h := congrArg (PowerSeries.substAlgHom (R := F) hsub) (formalInverse_spec W)
    rw [show (PowerSeries.substAlgHom (R := F) hsub) (-PowerSeries.X)
        = -((PowerSeries.substAlgHom (R := F) hsub) PowerSeries.X) from map_neg _ _] at h
    simp only [map_mul, map_sub, map_one] at h
    simpa only [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hsub, subst_C' f hsub] using h
  -- The coordinate expansions of the pair.
  have hξ : localExpand W ξ =
      HahnSeries.ofPowerSeries ℤ F f /
        HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) := by
    calc localExpand W ξ = localExpand W ((-ξ / η) / (-η⁻¹ : KE)) :=
          congrArg _ (x_eq_z_div_w ξ η hη_ne)
      _ = _ := by rw [map_div₀, hz, hw]
  have hη : localExpand W η =
      -(HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))⁻¹ := by
    calc localExpand W η = localExpand W (-(-η⁻¹ : KE)⁻¹) := congrArg _ (y_eq_neg_inv_w η)
      _ = _ := by rw [map_neg, map_inv₀, hw]
  -- Nonvanishing of the expanded `w`-series and of the unit factor.
  have hWb_ne : HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ≠ 0 := by
    intro h0
    apply neg_ne_zero.mpr (inv_ne_zero hη_ne)
    apply RingHom.injective (localExpand W)
    rw [hw, h0, map_zero]
  have hU_ne : (1 : LaurentSeries F)
      - HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
      - HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
          * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)) ≠ 0 := by
    rw [show (1 : LaurentSeries F) = HahnSeries.ofPowerSeries ℤ F 1 from (map_one _).symm,
      ← map_mul, ← map_mul, ← map_sub, ← map_sub]
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp [hf0, constantCoeff_subst_formalW W f hf0] at h2
  -- The spec, pushed to the Laurent field.
  have hspecL : HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalInverse W))
      * ((1 : LaurentSeries F)
          - HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₁) * HahnSeries.ofPowerSeries ℤ F f
          - HahnSeries.ofPowerSeries ℤ F (PowerSeries.C W.a₃)
              * HahnSeries.ofPowerSeries ℤ F (PowerSeries.subst f (formalW W)))
      = -(HahnSeries.ofPowerSeries ℤ F f) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ F) hspec
    rw [show (HahnSeries.ofPowerSeries ℤ F) (-f)
        = -(HahnSeries.ofPowerSeries ℤ F f) from map_neg _ f] at h
    simp only [map_mul, map_sub, map_one] at h
    exact h
  -- The negation, as chart algebra in the Laurent field.
  have hnegY : (W_KE W).toAffine.negY ξ η
      = -η - algebraMap F KE W.a₁ * ξ - algebraMap F KE W.a₃ := rfl
  rw [hnegY, map_div₀, map_neg, map_sub, map_sub, map_neg, map_mul,
    localExpand_algebraMap, localExpand_algebraMap, hξ, hη]
  exact neg_div_negY_field _ _ _ _ _ hWb_ne hU_ne hspecL

/-- The pair family `![f, g]` of two series with vanishing constant term is a
lawful substitution family, and each of its two entries has vanishing constant
term. The series-side bookkeeping packaged for the chord-addition assembly. -/
private lemma hasSubst_cons_pair {f g : PowerSeries F}
    (hf0 : PowerSeries.constantCoeff f = 0) (hg0 : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (![f, g] : Fin 2 → PowerSeries F) ∧
      ∀ i, MvPowerSeries.constantCoeff ((![f, g] : Fin 2 → PowerSeries F) i) = 0 := by
  refine ⟨?_, ?_⟩
  · apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    fin_cases s <;> simpa [hf0, hg0]
  · intro i
    fin_cases i
    · simpa [PowerSeries.constantCoeff_eq] using hf0
    · simpa [PowerSeries.constantCoeff_eq] using hg0

/-- The `chordA` expansion leg: substituting the explicit `1 + a₂Λ + a₄Λ² +
a₆Λ³` Weierstrass denominator at a field element `Λ` whose `localExpand` is the
substituted formal slope returns the substituted `chordA`. -/
private lemma localExpand_chordA_substituted (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b) {Λ : KE}
    (hΛ : localExpand W Λ =
      HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (formalSlopeBiv W))) :
    localExpand W (1 + algebraMap F KE W.a₂ * Λ + algebraMap F KE W.a₄ * Λ ^ 2
        + algebraMap F KE W.a₆ * Λ ^ 3)
      = HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (chordA W)) := by
  rw [subst_chordA_eq W _ hb]
  simp only [map_add, map_one, map_mul, map_pow, localExpand_algebraMap, hΛ]

/-- The `chordB` expansion leg: substituting the explicit `nsmul`-normalised
Weierstrass numerator at field elements `Λ`, `N` whose `localExpand`s are the
substituted formal slope and intercept returns the substituted `chordB`. -/
private lemma localExpand_chordB_substituted (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b) {Λ N : KE}
    (hΛ : localExpand W Λ =
      HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (formalSlopeBiv W)))
    (hN : localExpand W N =
      HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (formalNuBiv W))) :
    localExpand W (algebraMap F KE W.a₁ * Λ + algebraMap F KE W.a₂ * N
        + algebraMap F KE W.a₃ * Λ ^ 2
        + 2 * (algebraMap F KE W.a₄ * Λ * N)
        + 3 * (algebraMap F KE W.a₆ * Λ ^ 2 * N))
      = HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (chordB W)) := by
  rw [subst_chordB_eq W _ hb]
  simp only [map_add, map_mul, map_pow, localExpand_algebraMap, hΛ, hN,
    show (localExpand W) (2 : KE) = 2 from map_ofNat _ 2,
    show (localExpand W) (3 : KE) = 3 from map_ofNat _ 3,
    show (HahnSeries.ofPowerSeries ℤ F) (2 : PowerSeries F) = 2 from map_ofNat _ 2,
    show (HahnSeries.ofPowerSeries ℤ F) (3 : PowerSeries F) = 3 from map_ofNat _ 3]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The `w`-leg chart identity from the line `y′ = ℓx + c`: the chart `w`-value
`−1/(ℓx+c)` equals `λ·z + ν` for the chart slope `λ = −ℓ/c`, intercept
`ν = −1/c`, and chart `z`-value `z = −x/(ℓx+c)`. Pure field algebra. -/
private lemma neg_inv_eq_zwLine_field {K : Type*} [Field K] (ℓ x c : K)
    (hc : c ≠ 0) (hY' : ℓ * x + c ≠ 0) :
    -(ℓ * x + c)⁻¹ = (-ℓ / c) * (-x / (ℓ * x + c)) + (-1 / c) := by
  field_simp
  ring

/-- The substituted Weierstrass denominator `A∘` is nonzero in the Laurent
field: its constant term is `1`, since the substituted slope has zero constant
term. -/
private lemma ofPowerSeries_subst_chordA_ne_zero (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b)
    (hΛ0 : PowerSeries.constantCoeff (MvPowerSeries.subst b (formalSlopeBiv W)) = 0) :
    HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst b (chordA W)) ≠ 0 := by
  have hA0 : PowerSeries.constantCoeff (MvPowerSeries.subst b (chordA W)) = 1 := by
    rw [subst_chordA_eq W _ hb]
    simp [hΛ0]
  intro h0
  have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  rw [h1] at hA0
  simp at hA0

/-- Cancelling the unit `A∘` against the pure-series Vieta mirror. From the
cleared, Laurent-pushed chart identity `(−X₃)·A∘ = (T·A∘ − B∘)·Y₃′` (here
`T = −f_α − f_β`), the substituted series identity `z₃∘·A∘ = T·A∘ − B∘`
(`subst_formalZ3_mul_chordA`) and nonvanishing of `A∘` give the *z-leg*
`−localExpand X₃ = z₃∘ · localExpand Y₃′`. -/
private lemma localExpand_negX_eq_subst_formalZ3_mul
    {α β : Isogeny W.toAffine W.toAffine} (hb : MvPowerSeries.HasSubst
      (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F))
    (hΛ0 : PowerSeries.constantCoeff
      (MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
        (formalSlopeBiv W)) = 0)
    (hclL : -(localExpand W (addPullback_x_pair α β))
        * HahnSeries.ofPowerSeries ℤ F
            (MvPowerSeries.subst
              (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
              (chordA W))
      = ((HahnSeries.ofPowerSeries ℤ F (-(formalIsogenySeries W α))
            - HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W β))
          * HahnSeries.ofPowerSeries ℤ F
              (MvPowerSeries.subst
                (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
                (chordA W))
        - HahnSeries.ofPowerSeries ℤ F
            (MvPowerSeries.subst
              (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
              (chordB W)))
        * localExpand W
            ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))) :
    -(localExpand W (addPullback_x_pair α β))
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalZ3 W))
        * localExpand W
            ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)) := by
  have hserPS := subst_formalZ3_mul_chordA W _ hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hserPS
  have hserL := congrArg (HahnSeries.ofPowerSeries ℤ F) hserPS
  simp only [map_mul, map_sub] at hserL
  apply mul_right_cancel₀ (ofPowerSeries_subst_chordA_ne_zero W _ hb hΛ0)
  rw [hclL, ← hserL]
  ring

/-- The pre-negation `y`-coordinate `Y₃′ = negY(X₃, Y₃)` is nonzero: were it
zero, the cleared `z`-leg identity `hXY` would force `X₃ = 0`, and then the line
relation `hY₃line` would collapse the intercept `addLineC` to zero — excluded by
`hc`. This is the order-tie-breaking nonvanishing of FG-B5. -/
private lemma negY_addPullback_pair_ne_zero {α β : Isogeny W.toAffine W.toAffine}
    (hc : addLineC W α β ≠ 0)
    (hY₃line : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      = addSlopePair α β * (addPullback_x_pair α β - α.pullback (x_gen W))
        + α.pullback (y_gen W))
    (hXY : -(localExpand W (addPullback_x_pair α β))
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalZ3 W))
        * localExpand W
            ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))) :
    (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β) ≠ 0 := by
  intro h0
  have hX₃0 : addPullback_x_pair α β = 0 := by
    have h1 : -(localExpand W (addPullback_x_pair α β)) = 0 := by
      rw [hXY, h0, map_zero, mul_zero]
    apply RingHom.injective (localExpand W)
    rw [map_zero, ← neg_eq_zero]
    exact h1
  apply hc
  have h3 := hY₃line
  rw [h0, hX₃0] at h3
  rw [addLineC_def]
  linear_combination -h3

/-- The substituted slope, intercept and `z₃` series all have vanishing
constant term, given a lawful substitution family. The remaining series-side
bookkeeping, packaged. -/
private lemma constantCoeff_subst_slope_nu_z3_eq_zero (b : Fin 2 → PowerSeries F)
    (hb : MvPowerSeries.HasSubst b)
    (hb' : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    PowerSeries.constantCoeff (MvPowerSeries.subst b (formalSlopeBiv W)) = 0 ∧
      PowerSeries.constantCoeff (MvPowerSeries.subst b (formalNuBiv W)) = 0 ∧
      PowerSeries.constantCoeff (MvPowerSeries.subst b (formalZ3 W)) = 0 :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero hb hb' (constantCoeff_formalSlopeBiv W),
    MvPowerSeries.constantCoeff_subst_eq_zero hb hb' (constantCoeff_formalNuBiv W),
    MvPowerSeries.constantCoeff_subst_eq_zero hb hb' (constantCoeff_formalZ3 W)⟩

/-- The `(z,w)`-line data of the pair sum: `addLineC ≠ 0` and the chart slope /
intercept expand to the substituted formal slope / intercept. Both the chord
branch (`x_α = x_β`) and the tangent branch (`x_α ≠ x_β`) are handled. -/
private lemma zwLine_data_expansions (α β : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_ni : AddNonInversePair α β) :
    addLineC W α β ≠ 0 ∧
      localExpand W (zwSlopeLine W α β) =
        HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalSlopeBiv W)) ∧
      localExpand W (zwNuLine W α β) =
        HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalNuBiv W)) := by
  by_cases h_x : α.pullback (x_gen W) = β.pullback (x_gen W)
  · exact ⟨addLineC_ne_zero_of_x_eq W h_x h_ni,
      localExpand_zwSlopeLine_of_x_eq W h_α h_x h_ni,
      localExpand_zwNuLine_of_x_eq W h_α h_β h_x h_ni⟩
  · exact ⟨addLineC_ne_zero_of_x_ne W h_α h_β h_x,
      localExpand_zwSlopeLine_of_x_ne W h_α h_β h_x,
      localExpand_zwNuLine_of_x_ne W h_α h_β h_x⟩

/-- The *w-leg* at the pre-negation pair. Since `(X₃, Y₃′)` lies on the line
`y = ℓx + c`, the chart `w`-value `−1/Y₃′` is `λ·z₃′ + ν` (`neg_inv_eq_zwLine_field`);
pushing through `localExpand` with the slope/intercept expansions (`h_lam`,
`h_nu`) and the `z`-leg `hz₃` yields the `w`-expansion `λ∘·z₃∘ + ν∘`. No pole
bound on `X₃` enters. -/
private lemma localExpand_neg_inv_negY_eq_subst {α β : Isogeny W.toAffine W.toAffine}
    (hc : addLineC W α β ≠ 0)
    (hY₃'_ne : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β) ≠ 0)
    (hY₃line : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      = addSlopePair α β * (addPullback_x_pair α β - α.pullback (x_gen W))
        + α.pullback (y_gen W))
    (h_lam : localExpand W (zwSlopeLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalSlopeBiv W)))
    (h_nu : localExpand W (zwNuLine W α β) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
          (formalNuBiv W)))
    (hz₃ : localExpand W (-(addPullback_x_pair α β)
        / (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalZ3 W))) :
    localExpand W (-((W_KE W).toAffine.negY (addPullback_x_pair α β)
        (addPullback_y_pair α β))⁻¹)
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalSlopeBiv W)
          * MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalZ3 W)
          + MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalNuBiv W)) := by
  have hline : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      = addSlopePair α β * addPullback_x_pair α β + addLineC W α β := by
    rw [hY₃line, addLineC_def]
    ring
  have hwKE : -((W_KE W).toAffine.negY (addPullback_x_pair α β)
        (addPullback_y_pair α β))⁻¹
      = zwSlopeLine W α β
          * (-(addPullback_x_pair α β)
              / (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))
        + zwNuLine W α β := by
    have hY'ne2 : addSlopePair α β * addPullback_x_pair α β + addLineC W α β ≠ 0 := by
      rw [← hline]; exact hY₃'_ne
    rw [zwSlopeLine_def, zwNuLine_def, hline]
    exact neg_inv_eq_zwLine_field _ _ _ hc hY'ne2
  have h := congrArg (localExpand W) hwKE
  rw [map_add, map_mul, h_lam, hz₃, h_nu, ← map_mul, ← map_add] at h
  exact h

/-- **T-IV-BRIDGE-003** (Silverman IV.1.4, FG-B5): the local `z = −x/y`
expansion of the genuine pair sum `α(P) + β(P)` — the chord-tangent addition
`addPullback_x_pair`/`addPullback_y_pair` on the generic point — equals the
bivariate formal group law `(formalGroupLaw W).toMvPowerSeries` substituted
with the two formal isogeny series, for summands that reduce to `O`
(`h_α`/`h_β`) and are not mutual inverses (`h_ni`).

Statement relocated verbatim from `FormalIsogenySeries.lean` (where it was the
long-standing `sorry`); the hypothesis-shape discussion and the B2-restatement
history live in the module docstring there. The conclusion is verbatim the
`h_iv14` hypothesis of `addPullback_x_pair_sum_reduces_of_iv14_witness`
(`Verschiebung/Genuine.lean`). -/
theorem formalIsogenySeries_add (α β : Isogeny W.toAffine W.toAffine)
    (h_α : (W_smooth W).ordAtInfty (α.pullback (x_gen W)) < 0)
    (h_β : (W_smooth W).ordAtInfty (β.pullback (x_gen W)) < 0)
    (h_ni : AddNonInversePair α β) :
    localExpand W
        (-(addPullback_x_pair α β) / (addPullback_y_pair α β) : KE) =
      HahnSeries.ofPowerSeries ℤ F
        (MvPowerSeries.subst
          (![formalIsogenySeries W α, formalIsogenySeries W β] :
            Fin 2 → PowerSeries F)
          (formalGroupLaw W).toMvPowerSeries) := by
  -- ## Series-side bookkeeping: the substitution family is lawful.
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α h_α)
  have hg0 : PowerSeries.constantCoeff (formalIsogenySeries W β) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W β
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W β h_β)
  obtain ⟨hb, hb'⟩ := hasSubst_cons_pair (f := formalIsogenySeries W α)
    (g := formalIsogenySeries W β) hf0 hg0
  obtain ⟨hΛ0, hN0, hf₃0⟩ := constantCoeff_subst_slope_nu_z3_eq_zero W _ hb hb'
  -- ## The expansion legs of the `(z,w)`-line data, per branch.
  obtain ⟨hc, h_lam, h_nu⟩ := zwLine_data_expansions W α β h_α h_β h_ni
  -- ## The cleared Vieta identity, `nsmul`-normalised and pushed to Laurent.
  have hcl := addPullback_vieta_cleared W α β h_α h_β h_ni
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hcl
  have hA := localExpand_chordA_substituted W _ hb h_lam
  have hB := localExpand_chordB_substituted W _ hb h_lam h_nu
  have hT : localExpand W (-α.pullback (localParam W) - β.pullback (localParam W))
      = HahnSeries.ofPowerSeries ℤ F (-(formalIsogenySeries W α))
        - HahnSeries.ofPowerSeries ℤ F (formalIsogenySeries W β) := by
    rw [map_sub, map_neg, localExpand_pullback_localParam W α h_α,
      localExpand_pullback_localParam W β h_β, ← map_neg]
  have hclL := cleared_push (localExpand W) hA hB hT hcl
  -- ## Cancel the unit `A∘` against the pure-series mirror: the `z`-leg.
  have hXY := localExpand_negX_eq_subst_formalZ3_mul W hb hΛ0 hclL
  -- ## `Y₃′ ≠ 0` (else `X₃ = 0` and the line intercept would vanish).
  have hY₃line : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      = addSlopePair α β * (addPullback_x_pair α β - α.pullback (x_gen W))
        + α.pullback (y_gen W) :=
    Affine.negY_negY (W' := (W_KE W).toAffine) _ _
  have hY₃'_ne : (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)
      ≠ 0 := negY_addPullback_pair_ne_zero W hc hY₃line hXY
  have hLY'ne : localExpand W
      ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)) ≠ 0 := by
    intro h0
    exact hY₃'_ne (RingHom.injective (localExpand W) (h0.trans (map_zero _).symm))
  -- ## The `z`-leg at `(X₃, Y₃′)`.
  have hz₃ : localExpand W (-(addPullback_x_pair α β)
        / (W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))
      = HahnSeries.ofPowerSeries ℤ F
          (MvPowerSeries.subst
            (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
            (formalZ3 W)) := by
    rw [map_div₀, map_neg, hXY]
    exact mul_div_cancel_right₀ _ hLY'ne
  -- ## The `w`-leg from the line: `−1/Y₃′ = λ·z₃′ + ν`, expanded.
  have hw₃' := localExpand_neg_inv_negY_eq_subst W hc hY₃'_ne hY₃line h_lam h_nu hz₃
  -- ## Hensel: the `w`-leg series is `w ∘ z₃∘`.
  have h_weier₃ : (W_KE W).toAffine.Equation (addPullback_x_pair α β)
      ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β)) :=
    (Affine.equation_neg _ _).mpr (addPullback_pair_equation h_ni)
  have hs0 : PowerSeries.constantCoeff
      (MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
        (formalSlopeBiv W)
      * MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
        (formalZ3 W)
      + MvPowerSeries.subst
        (![formalIsogenySeries W α, formalIsogenySeries W β] : Fin 2 → PowerSeries F)
        (formalNuBiv W)) = 0 := by
    simp [hf₃0, hN0]
  have hw_id := subst_formalW_of_expansions W h_weier₃ hY₃'_ne hf₃0 hs0 hz₃ hw₃'
  -- ## The inversion step, and the chord spec of the formal group law.
  have hfinal := localExpand_neg_div_negY_of_expansions W hY₃'_ne hf₃0 hz₃
    (hw₃'.trans (congrArg _ hw_id))
  have hYY : (W_KE W).toAffine.negY (addPullback_x_pair α β)
      ((W_KE W).toAffine.negY (addPullback_x_pair α β) (addPullback_y_pair α β))
      = addPullback_y_pair α β := Affine.negY_negY (W' := (W_KE W).toAffine) _ _
  rw [hYY] at hfinal
  have hgz₃ : MvPowerSeries.HasSubst (fun _ : Unit ↦ formalZ3 W) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_formalZ3 W
  rw [formalGroupLaw_eq_chord W,
    mv_subst_powerSeries_subst _ hb hgz₃ (formalInverse W)]
  exact hfinal

end HasseWeil
