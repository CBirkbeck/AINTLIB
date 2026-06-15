/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Verschiebung.IsDual
import HasseWeil.Verschiebung.QthRoots
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.ChordExpansion
import HasseWeil.FormalIsogenySeries

/-!
# V-side genuine `r·V − s·id` isogeny family

Mirrors Worker B's π-side D-track for the Verschiebung. Universal in q;
witness-parametric on the Session-3 inclusion `Im([q]*) ⊆ Im(π*)`.

## Strategy

Same template as π-side:

1. **σ-action on `V.pb(x_gen)` and `V.pb(y_gen)`** — use the just-shipped
   `verschiebung_pullback_commute_mulByInt_neg_one` (σ.pb commutes with V.pb)
   plus the existing σ-action on `x_gen` and `y_gen`.
2. **σ-action on `(V.zsmul r).pb`** — compose with `(mulByInt r).pb` and
   use the σ-action on `(mulByInt r)` (`sigma_mulByInt_pullback_x_eq` /
   `_y_eq` from `AdditionPullback/Frobenius.lean`).
3. **σ-invariance + K(x_gen) image** for
   `addPullback_x_pair (V.zsmul r) (mulByInt -s)`, via the generic
   `addPullback_x_pair_sigma_invariant`.
4. **Witness-parametric genuine V isogeny** taking AddNonInversePair +
   addCoordAlgHomPair-injectivity as hypotheses (curve-specific
   discharges per use; not all curves admit uniform discharge).

Worker D consumes the genuine V isogeny in
`degree_quadratic_genuine_addIsog` for the `α = V` instance, completing
the polarisation chain alongside the π-side.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.2(b)
  (bilinearity / Verschiebung dual).
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### σ-action on `V.pb` of generators -/

/-- **σ.pb fixes `V.pb x_gen`**. From σ-V commute + σ fixes `x_gen`
(`mulByInt_pullback_x_neg_one`). -/
theorem sigma_verschiebung_pullback_x_eq
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (mulByInt W.toAffine (-1)).pullback
        ((verschiebungPullback_of_witness W h_subset) (x_gen W)) =
      (verschiebungPullback_of_witness W h_subset) (x_gen W) := by
  have h := verschiebung_pullback_commute_mulByInt_neg_one W h_subset
  have h_app := DFunLike.congr_fun h.symm (x_gen W)
  -- h_app: σ.pb (V.pb x) = V.pb (σ.pb x)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h_app
  rw [h_app, mulByInt_pullback_x_neg_one]

/-- **σ.pb on `V.pb y_gen`**: equals `-V.pb(y_gen) - a₁·V.pb(x_gen) - a₃`. From
σ-V commute + σ-action on y_gen + V.pb being a K-alg hom. -/
theorem sigma_verschiebung_pullback_y_eq
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (mulByInt W.toAffine (-1)).pullback
        ((verschiebungPullback_of_witness W h_subset) (y_gen W)) =
      -(verschiebungPullback_of_witness W h_subset) (y_gen W) -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
        (verschiebungPullback_of_witness W h_subset) (x_gen W) -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₃ := by
  have h := verschiebung_pullback_commute_mulByInt_neg_one W h_subset
  have h_app := DFunLike.congr_fun h.symm (y_gen W)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h_app
  -- h_app: σ.pb (V.pb y_gen) = V.pb (σ.pb y_gen)
  rw [h_app, mulByInt_pullback_y_neg_one]
  -- Goal: V.pb(-y_gen - a₁·x_gen - a₃) = -V.pb(y_gen) - a₁·V.pb(x_gen) - a₃.
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (verschiebungPullback_of_witness W h_subset)]

/-! ### σ-action on `(V.zsmul r).pb` of generators -/

/-- **σ.pb fixes `((V.zsmul r).pb x_gen)`** for `r ≠ 0`. Reduces via
`(V.zsmul r).pb x_gen = V.pb (mulByInt_x W r)`, then σ-V commute, then
σ-action on `mulByInt_x W r`. -/
theorem sigma_zsmul_verschiebung_pullback_x_eq
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r : ℤ) (hr : r ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback
        (((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W)) =
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) := by
  show (mulByInt W.toAffine (-1)).pullback
      ((verschiebungPullback_of_witness W h_subset)
        ((mulByInt W.toAffine r).pullback (x_gen W))) = _
  have h_comm := verschiebung_pullback_commute_mulByInt_neg_one W h_subset
  have h_app := DFunLike.congr_fun h_comm.symm
    ((mulByInt W.toAffine r).pullback (x_gen W))
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h_app
  rw [h_app, sigma_mulByInt_pullback_x_eq W r hr]
  rfl

/-- **σ.pb on `((V.zsmul r).pb y_gen)`** for `r ≠ 0`. Same path as the
x-version, then push V.pb over the linear combination (V.pb is a
`K`-AlgHom). -/
theorem sigma_zsmul_verschiebung_pullback_y_eq
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r : ℤ) (hr : r ≠ 0) :
    (mulByInt W.toAffine (-1)).pullback
        (((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (y_gen W)) =
      -((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (y_gen W) -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
        ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) -
      algebraMap K W.toAffine.FunctionField W.toAffine.a₃ := by
  show (mulByInt W.toAffine (-1)).pullback
      ((verschiebungPullback_of_witness W h_subset)
        ((mulByInt W.toAffine r).pullback (y_gen W))) =
    -(verschiebungPullback_of_witness W h_subset)
      ((mulByInt W.toAffine r).pullback (y_gen W)) -
    algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
      (verschiebungPullback_of_witness W h_subset)
        ((mulByInt W.toAffine r).pullback (x_gen W)) -
    algebraMap K W.toAffine.FunctionField W.toAffine.a₃
  have h_comm := verschiebung_pullback_commute_mulByInt_neg_one W h_subset
  have h_app := DFunLike.congr_fun h_comm.symm
    ((mulByInt W.toAffine r).pullback (y_gen W))
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h_app
  rw [h_app, sigma_mulByInt_pullback_y_eq W r hr]
  -- Goal: V.pb(-(mulByInt r).pb y_gen - a₁·(mulByInt r).pb x_gen - a₃) = ...
  simp only [map_sub, map_neg, map_mul,
    AlgHom.commutes (verschiebungPullback_of_witness W h_subset)]

/-! ### V-side `addPullback_x_pair` σ-invariance + K(x_gen) image

Specialises the generic `addPullback_x_pair_sigma_invariant`
(AdditionPullback.lean) to `α₁ = V.zsmul r`, `α₂ = mulByInt -s`. The four
σ-symmetry hypotheses follow from `sigma_zsmul_verschiebung_pullback_x/y_eq`
(just shipped) and `sigma_mulByInt_pullback_x/y_eq` (specialised to
`n = -s`). The `h_x_ne` hypothesis is curve-specific and remains
witness-parametric. -/

/-- **σ-invariance of `addPullback_x_pair (V.zsmul r) (mulByInt -s)`**,
witness-parametric on the inclusion + the x-coord mismatch. Universal
in q. -/
theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) :
    (mulByInt W.toAffine (-1)).pullback
        (addPullback_x_pair
          ((verschiebungIsog_of_witness W h_subset).zsmul r)
          (mulByInt W.toAffine (-s))) =
      addPullback_x_pair ((verschiebungIsog_of_witness W h_subset).zsmul r)
        (mulByInt W.toAffine (-s)) :=
  addPullback_x_pair_sigma_invariant h_x_ne
    (sigma_zsmul_verschiebung_pullback_x_eq W h_subset r hr)
    (sigma_mulByInt_pullback_x_eq W (-s) (neg_ne_zero.mpr hs))
    (sigma_zsmul_verschiebung_pullback_y_eq W h_subset r hr)
    (sigma_mulByInt_pullback_y_eq W (-s) (neg_ne_zero.mpr hs))

/-- **K(x_gen) image of `addPullback_x_pair (V.zsmul r) (mulByInt -s)`**:
σ-fixed expressions lie in the image of `Frac(K[X]) → K(E)`. One-line
consequence of `sigma_fixed_implies_in_KX_image` applied to the
σ-invariance above. -/
theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W)) :
    ∃ a : FractionRing (Polynomial K),
      addPullback_x_pair ((verschiebungIsog_of_witness W h_subset).zsmul r)
        (mulByInt W.toAffine (-s)) =
        algebraMap (FractionRing (Polynomial K)) W.toAffine.FunctionField a :=
  sigma_fixed_implies_in_KX_image W _
    (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_sigma_invariant
      W h_subset r s hr hs h_x_ne)

/-! ### V-side genuine isogeny constructor (pole-bound-parametric)

Mirrors Worker B's π-side `genuineIsogSmulSub_of_pole`. The pole bound
discharges base-hom injectivity → addCoordAlgHomPair injectivity →
genuine V isogeny via the same chain as the π-side. Universal in q;
witness-parametric on the inclusion + AddNonInversePair (curve-specific)
+ pole bound. -/

local notation "KE" => W.toAffine.FunctionField

/-- **Witness-parametric base-hom injectivity for V-side**: given the
pole bound `ord_∞ < 0`, discharge base-hom injectivity for the
`(V.zsmul r, mulByInt -s)` family. Mirrors
`addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
(Frobenius.lean). -/
theorem addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Function.Injective
      (addBaseHomPair
        ((verschiebungIsog_of_witness W h_subset).zsmul r)
        (mulByInt W.toAffine (-s))) := by
  rw [addBaseHomPair_eq_aeval]
  apply transcendental_iff_injective.mp
  intro h_alg
  obtain ⟨a, ha⟩ :=
    addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
      W h_subset r s hr hs h_x_ne
  have h_inj : Function.Injective (algebraMap (FractionRing (Polynomial K)) KE) :=
    (algebraMap (FractionRing (Polynomial K)) KE).injective
  have ha_alg : IsAlgebraic K a := by
    by_contra h_trans
    have h_px_trans : Transcendental K
        (addPullback_x_pair
          ((verschiebungIsog_of_witness W h_subset).zsmul r)
          (mulByInt W.toAffine (-s))) := by
      rw [ha]
      exact (transcendental_algebraMap_iff h_inj).mpr h_trans
    exact h_px_trans h_alg
  obtain ⟨c, hc⟩ := algebraic_in_fracRing_eq_const a ha_alg
  have hc' : addPullback_x_pair
      ((verschiebungIsog_of_witness W h_subset).zsmul r)
      (mulByInt W.toAffine (-s)) = algebraMap K KE c := by
    rw [ha, hc, ← IsScalarTower.algebraMap_apply K (FractionRing (Polynomial K)) KE]
  by_cases hc_zero : c = 0
  · have h0 : addPullback_x_pair
        ((verschiebungIsog_of_witness W h_subset).zsmul r)
        (mulByInt W.toAffine (-s)) = 0 := by rw [hc', hc_zero, map_zero]
    have h_top : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) = ⊤ := by
      rw [h0]; exact (W_smooth W).ordAtInfty_zero
    rw [h_top] at h_pole
    exact absurd h_pole (not_lt_of_ge le_top)
  · have h_ord_c : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) = 0 := by
      rw [hc']; exact ordAtInfty_algebraMap_F_nonzero W hc_zero
    rw [h_ord_c] at h_pole
    exact absurd h_pole (lt_irrefl _)

/-- **Witness-parametric `addCoordAlgHomPair` injectivity for V-side**:
takes AddNonInversePair + x-mismatch + pole bound, gives injectivity. -/
theorem addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Function.Injective
      (addCoordAlgHomPair
        (AddNonInversePair_of_x_ne (α₁ :=
          (verschiebungIsog_of_witness W h_subset).zsmul r)
          (α₂ := mulByInt W.toAffine (-s)) h_x_ne)) :=
  addCoordAlgHomPair_injective_of_baseHom_inj _
    (addBaseHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole
      W h_subset r s hr hs h_x_ne h_pole)

/-- **V-side genuine `r·V − s·id` isogeny (pole-bound-parametric)**.

Mirrors Worker B's π-side `genuineIsogSmulSub_of_pole`. Witness-parametric
on:
- the Session-3 inclusion `h_subset` (Worker C universal Φ_q discharges
  this for general q);
- the x-coord mismatch `h_x_ne` (curve-specific; needed because V-side
  AddNonInversePair doesn't transpose uniformly from π-side);
- the pole bound (analogous to π-side, gated on Worker C/D's V-side ord
  computation in future).

`toAddMonoidHom = (V.zsmul r).toAddMonoidHom + (mulByInt -s).toAddMonoidHom
= [r·q + (-s)] = [r·q - s]` — since V over `F_q` has hom `[q]`. Worker D's
`degree_quadratic_genuine_addIsog` consumes this for the `α = V` instance,
completing the bilinear pairing argument alongside the π-side. -/
noncomputable def genuineIsogSmulSubV_of_pole_witness
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Isogeny W.toAffine W.toAffine :=
  addIsog (AddNonInversePair_of_x_ne h_x_ne)
    (addCoordAlgHomPair_injective_zsmul_verschiebung_mulByInt_neg_of_pole
      W h_subset r s hr hs h_x_ne h_pole)

@[simp] theorem genuineIsogSmulSubV_of_pole_witness_toAddMonoidHom
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_x_ne :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
        (mulByInt W.toAffine (-s)).pullback (x_gen W))
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Isogeny.toAddMonoidHom
        (genuineIsogSmulSubV_of_pole_witness W h_subset r s hr hs h_x_ne h_pole) =
      ((verschiebungIsog_of_witness W h_subset).zsmul r).toAddMonoidHom +
        (mulByInt W.toAffine (-s)).toAddMonoidHom :=
  rfl

/-! ### T26-B (R29 §2) — V-side x-coordinate mismatch (substantive)

The R29 §2 T26-B sub-ticket: discharge `h_x_ne` for the V-side
`(V.zsmul r, mulByInt (-s))` pair.

**Statement** (the conclusion the genuine V-side family consumes):
`((V.zsmul r).pullback x_gen) ≠ ((mulByInt -s).pullback x_gen)` for
`r, s ≠ 0` with `(r : K), (s : K) ≠ 0`.

**Substantive proof** (Worker D 2026-05-20). The ord-∞ comparison from
the π-side does **not** transpose uniformly (`V.pullback x_gen` has
ord-∞ = -2 for ordinary curves but -2q for supersingular curves, so a
single ord-formula can't fire). We use the curve-uniform
*polynomial-divisibility* argument instead:

1. Assume the equality. After simplifying both sides
   (`(V.zsmul r).pb x_gen = V.pb (mulByInt_x W r)` and
   `(mulByInt -s).pb x_gen = mulByInt_x W (-s) = mulByInt_x W s`),
   the assumption becomes `V.pb (mulByInt_x W r) = mulByInt_x W s` in K(E).
2. Apply π.pullback:  `π.pb (V.pb z) = (V.comp π).pb z = (mulByInt q).pb z`
   (via the `IsDualOf` first composition, with `(frobeniusIsog W).degree = q`).
   With `z = mulByInt_x W r`, this is `(mulByInt q).pb (mulByInt_x W r) =
   mulByInt_x W (r * q)`
   (`mulByInt_pullback_mulByInt_x_eq_mul`).
3. On the right: `π.pb (mulByInt_x W s) = (mulByInt_x W s) ^ q`
   (`frobeniusIsog_pullback_apply`).
4. The K(E) equality
   `mulByInt_x W (r * q) = (mulByInt_x W s) ^ q`
   lifts to the K[X] polynomial equality
   `W.Φ (r * q) * (W.ΨSq s) ^ q = (W.Φ s) ^ q * W.ΨSq (r * q)`
   (via algebra-map injectivity and clearing `ΨSq_ff` denominators).
5. With `isCoprime_Φ_ΨSq` for both `n = r * q` and `n = s` (Δ ≠ 0 from
   IsElliptic; both `r*q ≠ 0` and `s ≠ 0`), the divisibility flows give
   `W.Φ (r * q)` and `(W.Φ s) ^ q` are mutual divisors in `K[X]` (a UFD),
   hence equal as monic polynomials. Their `natDegree`s coincide:
   `r² * q² = q * s²`, i.e., `s² = r² * q` as integers.
6. By `FiniteField.card`, `q = p ^ n` for some prime `p` and `n ≥ 1`.
   So `p | q | r² * q = s²`. Since `p` is prime, `p | s`, hence
   `(s : K) = 0` (`CharP K p`). Contradicts `hsK`.

Mathematically this is the "x-coord mismatch at infinity" Silverman III.6
III.6.2(b) is implicitly using when stating the polarization is
non-degenerate; the cleanest formalisation goes via the polynomial
divisibility ⟹ degree match ⟹ `p`-adic valuation contradiction. -/

/-- **T26-B core** (R29 §2): from the assumed K(E) equation
`mulByInt_x W (r * q) = (mulByInt_x W s) ^ q`, derive the polynomial
equation in `K[X]` via algebra-map injectivity. -/
private theorem polyEq_of_mulByInt_x_eq_pow
    (n m : ℤ) (hn : n ≠ 0) (hm : m ≠ 0) (k : ℕ)
    (h_eq : mulByInt_x W n = (mulByInt_x W m) ^ k) :
    W.Φ n * (W.ΨSq m) ^ k = (W.Φ m) ^ k * W.ΨSq n := by
  -- Unfold mulByInt_x = Φ_ff / ΨSq_ff in K(E), clear denominators.
  have hΨn : ΨSq_ff W n ≠ 0 := ΨSq_ff_ne_zero W hn
  have hΨm : ΨSq_ff W m ≠ 0 := ΨSq_ff_ne_zero W hm
  have hΨm_pow : (ΨSq_ff W m) ^ k ≠ 0 := pow_ne_zero k hΨm
  -- mulByInt_x W n = Φ_ff(n) / ΨSq_ff(n).
  -- mulByInt_x W m = Φ_ff(m) / ΨSq_ff(m).
  -- (mulByInt_x W m) ^ k = (Φ_ff(m) / ΨSq_ff(m)) ^ k = Φ_ff(m)^k / ΨSq_ff(m)^k.
  -- Equation: Φ_ff(n) / ΨSq_ff(n) = Φ_ff(m)^k / ΨSq_ff(m)^k.
  -- Cross-multiply: Φ_ff(n) * ΨSq_ff(m)^k = Φ_ff(m)^k * ΨSq_ff(n).
  have h_cross :
      Φ_ff W n * (ΨSq_ff W m) ^ k = (Φ_ff W m) ^ k * ΨSq_ff W n := by
    have h := h_eq
    unfold mulByInt_x at h
    rw [div_pow] at h
    -- h : Φ_ff(n) / ΨSq_ff(n) = Φ_ff(m)^k / ΨSq_ff(m)^k
    field_simp at h
    linear_combination h
  -- Lift back through `algebraMap` from `K[X]` to `K(E)`.
  have h_alg :
      algebraMap (Polynomial K) W.toAffine.FunctionField
          (W.Φ n * (W.ΨSq m) ^ k) =
        algebraMap (Polynomial K) W.toAffine.FunctionField
          ((W.Φ m) ^ k * W.ΨSq n) := by
    rw [map_mul, map_mul, map_pow, map_pow,
      ← Φ_ff_eq_algebraMap_polynomial, ← Φ_ff_eq_algebraMap_polynomial,
      ← ΨSq_ff_eq_algebraMap_polynomial, ← ΨSq_ff_eq_algebraMap_polynomial]
    exact h_cross
  -- algebraMap (Polynomial K) → FunctionField is injective.
  have h_inj : Function.Injective
      (algebraMap (Polynomial K) W.toAffine.FunctionField) := by
    show Function.Injective
      ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing))
    exact (IsFractionRing.injective W.toAffine.CoordinateRing
        W.toAffine.FunctionField).comp
      Affine.CoordinateRing.algebraMap_poly_injective
  exact h_inj h_alg

/-- **T26-B (R29 §2 T26-B substantive ship)** — V-side x-coordinate
mismatch at infinity for the genuine `(V.zsmul r, mulByInt (-s))` pair.

Closes `h_x_ne` substantively (no witness wrappers; no `K = F_p`
restriction; no `[Fact (#K = p)]`). Used immediately downstream by
`genuineIsogSmulSubV_of_pole_witness` (and by Worker C's T11 to discharge
its own h_x_ne side-hypothesis). -/
theorem h_x_ne_zsmul_verschiebung_mulByInt_neg
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) ≠
      (mulByInt W.toAffine (-s)).pullback (x_gen W) := by
  intro h_eq
  -- Step 1: simplify LHS and RHS to mulByInt_x form.
  have h_lhs_x :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) =
        (verschiebungIsog_of_witness W h_subset).pullback (mulByInt_x W r) := by
    show ((mulByInt W.toAffine r).comp
        (verschiebungIsog_of_witness W h_subset)).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    congr 1
    show (mulByInt W.toAffine r).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact mulByInt_pullback_x W r hr
  have h_rhs_x : (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W s := by
    have h : (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W (-s) := by
      show (mulByInt W.toAffine (-s)).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W (-s) (neg_ne_zero.mpr hs)
    rw [h, mulByInt_x_neg]
  rw [h_lhs_x, h_rhs_x] at h_eq
  -- h_eq : V.pullback (mulByInt_x W r) = mulByInt_x W s
  -- Step 2: apply π.pullback to both sides.
  have h_pi := congrArg (frobeniusIsog W).pullback h_eq
  -- Step 3: simplify LHS via mulByInt_q_factor_via_witness + mulByInt_pullback_mulByInt_x_eq_mul.
  have h_rq_ne_int : r * ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    refine mul_ne_zero hr ?_
    exact_mod_cast Fintype.card_pos.ne'
  have h_q_ne_int : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have h_lhs_pi : (frobeniusIsog W).pullback
      ((verschiebungIsog_of_witness W h_subset).pullback (mulByInt_x W r)) =
        mulByInt_x W (r * ((Fintype.card K : ℕ) : ℤ)) := by
    show (frobeniusIsog W).pullback
        (verschiebungPullback_of_witness W h_subset (mulByInt_x W r)) = _
    have h_factor :
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
        (frobeniusIsog W).pullback.comp
          (verschiebungPullback_of_witness W h_subset) :=
      mulByInt_q_factor_via_witness W h_subset
    have h_app := DFunLike.congr_fun h_factor (mulByInt_x W r)
    rw [AlgHom.comp_apply] at h_app
    -- h_app : (mulByInt q).pb (mulByInt_x W r) = π.pb (V.pb (mulByInt_x W r))
    rw [← h_app]
    -- Goal: (mulByInt q).pb (mulByInt_x W r) = mulByInt_x W (r * q)
    exact mulByInt_pullback_mulByInt_x_eq_mul W r
      ((Fintype.card K : ℕ) : ℤ) hr h_q_ne_int h_rq_ne_int
  -- Step 4: simplify RHS via frobeniusIsog_pullback_apply.
  have h_rhs_pi : (frobeniusIsog W).pullback (mulByInt_x W s) =
      (mulByInt_x W s) ^ Fintype.card K :=
    frobeniusIsog_pullback_apply W (mulByInt_x W s)
  rw [h_lhs_pi, h_rhs_pi] at h_pi
  -- h_pi : mulByInt_x W (r * q) = (mulByInt_x W s) ^ q
  -- Step 5: lift to polynomial equation in K[X].
  have h_poly := polyEq_of_mulByInt_x_eq_pow W
    (r * ((Fintype.card K : ℕ) : ℤ)) s h_rq_ne_int hs (Fintype.card K) h_pi
  -- h_poly : W.Φ (r * q) * (W.ΨSq s) ^ q = (W.Φ s) ^ q * W.ΨSq (r * q)
  -- Step 6: use isCoprime_Φ_ΨSq to derive natDegree match.
  have hΔ : W.toAffine.Δ ≠ 0 := by
    rw [← W.toAffine.coe_Δ']
    exact_mod_cast W.toAffine.Δ'.ne_zero
  have h_cop_rq : IsCoprime (W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)))
      (W.toAffine.ΨSq (r * ((Fintype.card K : ℕ) : ℤ))) :=
    isCoprime_Φ_ΨSq W.toAffine hΔ h_rq_ne_int
  have h_cop_s : IsCoprime (W.toAffine.Φ s) (W.toAffine.ΨSq s) :=
    isCoprime_Φ_ΨSq W.toAffine hΔ hs
  have hΦs_ne : W.toAffine.Φ s ≠ 0 := W.toAffine.Φ_ne_zero s
  have hΦrq_ne : W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)) ≠ 0 :=
    W.toAffine.Φ_ne_zero _
  have hΨs_ne : W.toAffine.ΨSq s ≠ 0 := W.toAffine.ΨSq_ne_zero hsK
  have hΨs_pow_ne : (W.toAffine.ΨSq s) ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ hΨs_ne
  have hΦs_pow_ne : (W.toAffine.Φ s) ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ hΦs_ne
  -- Divisibility chain: W.Φ (r * q) divides (W.Φ s) ^ q.
  have h_div_LHS : W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)) ∣
      (W.toAffine.Φ s) ^ Fintype.card K := by
    have h_dvd_RHS :
        W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)) ∣
          (W.toAffine.Φ s) ^ Fintype.card K *
            W.toAffine.ΨSq (r * ((Fintype.card K : ℕ) : ℤ)) :=
      ⟨(W.toAffine.ΨSq s) ^ Fintype.card K, h_poly.symm⟩
    exact (IsCoprime.dvd_of_dvd_mul_right h_cop_rq h_dvd_RHS)
  -- Divisibility chain: (W.Φ s) ^ q divides W.Φ (r * q).
  have h_div_RHS : (W.toAffine.Φ s) ^ Fintype.card K ∣
      W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)) := by
    have h_cop_s_pow : IsCoprime ((W.toAffine.Φ s) ^ Fintype.card K)
        ((W.toAffine.ΨSq s) ^ Fintype.card K) :=
      h_cop_s.pow
    have h_dvd_LHS :
        (W.toAffine.Φ s) ^ Fintype.card K ∣
          W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ)) *
            (W.toAffine.ΨSq s) ^ Fintype.card K :=
      ⟨W.toAffine.ΨSq (r * ((Fintype.card K : ℕ) : ℤ)), h_poly⟩
    exact (IsCoprime.dvd_of_dvd_mul_right h_cop_s_pow h_dvd_LHS)
  -- Mutual divisibility ⟹ same natDegree (both nonzero, K[X] integral).
  have h_natDeg_le_1 :
      (W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ))).natDegree ≤
        ((W.toAffine.Φ s) ^ Fintype.card K).natDegree :=
    Polynomial.natDegree_le_of_dvd h_div_LHS hΦs_pow_ne
  have h_natDeg_le_2 :
      ((W.toAffine.Φ s) ^ Fintype.card K).natDegree ≤
        (W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ))).natDegree :=
    Polynomial.natDegree_le_of_dvd h_div_RHS hΦrq_ne
  have h_natDeg_eq :
      (W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ))).natDegree =
        ((W.toAffine.Φ s) ^ Fintype.card K).natDegree :=
    le_antisymm h_natDeg_le_1 h_natDeg_le_2
  -- Step 7: compute the natDegrees explicitly.
  -- natDegree(Φ (r * q)) = (r * q).natAbs² = r.natAbs² * q²
  -- natDegree(Φ s ^ q) = q * natDegree(Φ s) = q * s²
  -- Equation: r² * q² = q * s², i.e., s² = r² * q.
  have h_natDeg_Φrq : (W.toAffine.Φ (r * ((Fintype.card K : ℕ) : ℤ))).natDegree =
      (r * ((Fintype.card K : ℕ) : ℤ)).natAbs ^ 2 :=
    W.toAffine.natDegree_Φ _
  have h_natDeg_Φs_pow :
      ((W.toAffine.Φ s) ^ Fintype.card K).natDegree =
        Fintype.card K * s.natAbs ^ 2 := by
    rw [Polynomial.natDegree_pow, W.toAffine.natDegree_Φ]
  rw [h_natDeg_Φrq, h_natDeg_Φs_pow] at h_natDeg_eq
  -- h_natDeg_eq : (r * q).natAbs² = q * s.natAbs²
  have h_natAbs_rq : (r * ((Fintype.card K : ℕ) : ℤ)).natAbs =
      r.natAbs * Fintype.card K := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [h_natAbs_rq] at h_natDeg_eq
  -- h_natDeg_eq : (r.natAbs * q)² = q * s.natAbs², where q = Fintype.card K.
  -- i.e. r.natAbs² * q² = q * s.natAbs². Hence s.natAbs² = r.natAbs² * q.
  have hs_sq_eq : s.natAbs ^ 2 = r.natAbs ^ 2 * Fintype.card K := by
    have h_card_pos : 0 < Fintype.card K := Fintype.card_pos
    have h_expand : (r.natAbs * Fintype.card K) ^ 2 =
        r.natAbs ^ 2 * Fintype.card K * Fintype.card K := by ring
    rw [h_expand] at h_natDeg_eq
    -- h_natDeg_eq : r.natAbs² * q * q = q * s.natAbs²
    have h_rw_RHS : Fintype.card K * s.natAbs ^ 2 = s.natAbs ^ 2 * Fintype.card K := by ring
    rw [h_rw_RHS] at h_natDeg_eq
    -- h_natDeg_eq : r.natAbs² * q * q = s.natAbs² * q
    -- Cancel the rightmost q to get r.natAbs² * q = s.natAbs².
    exact (Nat.eq_of_mul_eq_mul_right h_card_pos h_natDeg_eq).symm
  -- Step 8: v_p contradiction.
  -- s² = r² * q with q = #K = p^n, n ≥ 1. p prime ⟹ p ∣ q ∣ s². p prime ⟹ p ∣ s.
  -- But (s : K) ≠ 0 ⟹ p ∤ s in CharP K p. Contradiction.
  obtain ⟨p, hCharP, ⟨n, n_pos⟩, hp_prime, hcard⟩ := FiniteField.card' K
  have hp_dvd_q : p ∣ Fintype.card K := by
    rw [hcard]; exact dvd_pow_self _ n_pos.ne'
  -- p ∣ q ∣ r² * q = s². So p ∣ s². p prime ⟹ p ∣ s.
  have hp_dvd_ssq : p ∣ s.natAbs ^ 2 := by
    rw [hs_sq_eq]; exact Dvd.dvd.mul_left hp_dvd_q _
  have hp_dvd_s_natAbs : p ∣ s.natAbs :=
    Nat.Prime.dvd_of_dvd_pow hp_prime hp_dvd_ssq
  -- (s : K) = 0 since p ∣ s in ℤ and CharP K p.
  have hp_dvd_s_int : (p : ℤ) ∣ s := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact hp_dvd_s_natAbs
  have hs_cast_zero : (s : K) = 0 := by
    haveI := hCharP
    exact (CharP.intCast_eq_zero_iff K p s).mpr hp_dvd_s_int
  exact hsK hs_cast_zero

/-! ### Universal-in-k inclusion: `Im([q^k]*) ⊆ Im(π*)`

For any k ≥ 0, the `[q^k]`-pullback image lies in the Frobenius range,
witness-parametric on the Session-3 inclusion (the `k = 1` base case).
Combines my x-side and y-side `[q^k].pb gen = (V^k.pb gen)^(q^k)`
identities (universal in k, shipped axiom-clean) with
`functionField_eq_intermediateField_adjoin_xy` (K(E) generated by
`{x_gen, y_gen}`) and `frobeniusIsog_pullback_range_inv_mem` (Frobenius
range closed under inverses).

For each k ≥ 1, this generalises Worker B's prior q=2 char=2 axiom-clean
inclusion (`mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`)
to all k ≥ 1, conditional only on the `k = 1` base inclusion. Combined
with Worker C's char-p generic base case (q = p shipped for p = 2, 3),
this gives `Im([p^k]*) ⊆ Im(π*)` axiom-clean for char 2 and char 3 over
any cardinality `F_{p^k}`. -/

/-- **Pow-of-q range membership** for `(mulByInt q^k).pb x_gen`: it's a
`q^k`-th power, hence a q-th power, hence in `Im(π*)`. Direct from
`mulByInt_pow_pullback_x_gen_eq_pow_qpow` + `pow_mem_iff_pow_mem`-style
reasoning. -/
theorem mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (x_gen W) ∈
      (frobeniusIsog W).pullback.fieldRange := by
  rw [mulByInt_pow_pullback_x_gen_eq_pow_qpow W h_subset k]
  -- The element is a q^k-th power of (V^k.pb x_gen). Write q^k = q · q^(k-1).
  -- Then the q-th-power factor places it in Im(π*).
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- q^(k'+1) = q · q^k'.
  have h_pow : Fintype.card K ^ (k' + 1) = Fintype.card K * Fintype.card K ^ k' := by
    ring
  rw [h_pow, pow_mul]
  rw [show ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) (k' + 1)).pullback
        (x_gen W) ^ Fintype.card K) ^ (Fintype.card K ^ k') =
      (((isogenyIterate W (verschiebungIsog_of_witness W h_subset) (k' + 1)).pullback
        (x_gen W)) ^ Fintype.card K) ^ (Fintype.card K ^ k') from rfl]
  -- Use the q-th-power → Im(π*) characterisation.
  refine pow_mem ?_ _
  rw [(frobeniusIsog_pullback_mem_iff W _)]
  exact ⟨_, rfl⟩

/-- **Pow-of-q range membership** for `(mulByInt q^k).pb y_gen`: y-side analog. -/
theorem mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (y_gen W) ∈
      (frobeniusIsog W).pullback.fieldRange := by
  rw [mulByInt_pow_pullback_y_gen_eq_pow_qpow W h_subset k]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h_pow : Fintype.card K ^ (k' + 1) = Fintype.card K * Fintype.card K ^ k' := by
    ring
  rw [h_pow, pow_mul]
  rw [show ((isogenyIterate W (verschiebungIsog_of_witness W h_subset) (k' + 1)).pullback
        (y_gen W) ^ Fintype.card K) ^ (Fintype.card K ^ k') =
      (((isogenyIterate W (verschiebungIsog_of_witness W h_subset) (k' + 1)).pullback
        (y_gen W)) ^ Fintype.card K) ^ (Fintype.card K ^ k') from rfl]
  refine pow_mem ?_ _
  rw [(frobeniusIsog_pullback_mem_iff W _)]
  exact ⟨_, rfl⟩

/-- **Universal-in-k inclusion theorem**: for every `k ≥ 1`, every
`[q^k]`-pullback image lies in the Frobenius range. Witness-parametric on
the Session-3 `k = 1` base inclusion.

Universal in k. For char p where the base case is shipped axiom-clean,
this gives `Im([p^k]*) ⊆ Im(π*)` for all k ≥ 1, completing the structural
side of Silverman III.6.2. -/
theorem mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ z : W.toAffine.FunctionField,
      (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback z ∈
        (frobeniusIsog W).pullback.fieldRange := by
  intro z
  -- Every z ∈ K(E) = adjoin K {x_gen, y_gen} (functionField_eq_intermediateField_adjoin_xy).
  -- The pullback is a K-alg hom; image of adjoin is in adjoin of images.
  -- Both [q^k]*x_gen and [q^k]*y_gen are in Im(π*) (just shipped).
  -- Im(π*) is a subfield (closed under +, *, inverse).
  -- Hence [q^k]*z ∈ Im(π*).
  have h_z_mem : z ∈ IntermediateField.adjoin K {x_gen W, y_gen W} := by
    rw [← functionField_eq_intermediateField_adjoin_xy W]; trivial
  have h_subfield : (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback z ∈
      IntermediateField.adjoin K
        {(mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (x_gen W),
         (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (y_gen W)} := by
    have h_map : ((mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback z) ∈
        ((IntermediateField.adjoin K {x_gen W, y_gen W}).map
          (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback) :=
      ⟨z, h_z_mem, rfl⟩
    rw [IntermediateField.adjoin_map] at h_map
    convert h_map using 2
    simp [Set.image_pair]
  refine IntermediateField.adjoin_le_iff.mpr ?_ h_subfield
  intro f hf
  rcases hf with rfl | rfl
  · exact mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange W h_subset k hk
  · exact mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange W h_subset k hk

/-- **Subalgebra-form universal-in-k inclusion** for Worker C / Verschiebung
chain consumers expecting `Subalgebra` (= `AlgHom.range`) typed witnesses
rather than `IntermediateField`. The two carriers coincide; we re-export
in the Subalgebra form via the `frobeniusIsog_intermediateField_eq_fieldRange`
bridge (PurelyInsep.lean). -/
theorem mulByInt_pow_pullback_range_subset_frobenius_universal_in_k
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback.range ≤
      (frobeniusIsog W).pullback.range := by
  rintro z ⟨w, rfl⟩
  -- z = [q^k]*(w); need [q^k]*(w) ∈ (frobeniusIsog).pullback.range.
  have h_field := mulByInt_pullback_fieldRange_subset_frobenius_universal_in_k
    W h_subset k hk w
  -- h_field gives membership in fieldRange; carrier is the same as range.
  -- AlgHom.fieldRange.toSubalgebra = AlgHom.range (canonical inclusion).
  exact h_field

/-- **Subalgebra-level generator membership: x_gen**. Direct from
`mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange` via the
fieldRange-to-Subalgebra carrier identification. Useful for consumers in
`PurelyInsep.lean` and `QthRoots.lean` that take `Subalgebra` arguments. -/
theorem mulByInt_pow_pullback_x_gen_mem_frobenius_subalgebra
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (x_gen W) ∈
      (frobeniusIsog W).pullback.range :=
  mulByInt_pow_pullback_x_gen_mem_frobenius_fieldRange W h_subset k hk

/-- **Subalgebra-level generator membership: y_gen**. Subalgebra form of
the y-side analog. -/
theorem mulByInt_pow_pullback_y_gen_mem_frobenius_subalgebra
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (k : ℕ) (hk : 1 ≤ k) :
    (mulByInt W.toAffine ((Fintype.card K ^ k : ℕ) : ℤ)).pullback (y_gen W) ∈
      (frobeniusIsog W).pullback.range :=
  mulByInt_pow_pullback_y_gen_mem_frobenius_fieldRange W h_subset k hk

/-! ### T26-A — Discharge `h_subset` from an `IsDualOf` witness

Given any `V` with `IsDualOf V (frobeniusIsog W)` (which is what T10's L9
universal V delivers), the `h_subset` inclusion
`Im([q]*) ⊆ Im(π*)` follows directly from the first composition
`V ∘ π = [q]`.

Mathematics (R29 §2 T26-A): `V.comp π = mulByInt q` ⟹
`(mulByInt q).pullback = π.pullback ∘ V.pullback` (functorial reversal) ⟹
`Im((mulByInt q).pullback) ⊆ Im(π.pullback)`.

This is the **R29 §2 T26-A** sub-ticket — the gateway by which T10's
universal V unlocks the V-side genuine isogeny family of T26-MAIN. -/

/-- **R29 §2 T26-A (discharge `h_subset` from `IsDualOf` witness)**.

Given any isogeny `V` satisfying `IsDualOf W.toAffine V (frobeniusIsog W)`
— i.e., `V.comp π = π.comp V = mulByInt q` (where `q = #K`) — the
function-field inclusion `Im([q]*) ⊆ Im(π*)` holds.

This converts T10's deliverable (a universal Verschiebung `V` and its
`IsDualOf` witness) into the `h_subset` shape consumed by the rest of
the V-side genuine isogeny pipeline (`verschiebungIsog_of_witness`,
`genuineIsogSmulSubV_of_pole_witness`, …). -/
theorem h_subset_of_isDualOf
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W)) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
      (frobeniusIsog W).pullback.range := by
  -- Extract V.comp π = mulByInt q from hV (using frobeniusIsog_degree = #K).
  have h_comp :
      V.comp (frobeniusIsog W) =
        mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) := by
    have h := hV.1
    rw [frobeniusIsog_degree] at h
    exact h
  -- Pullback identity: (mulByInt q).pullback = π.pullback ∘ V.pullback.
  -- For any z with [q].pullback z = w, we have w = π.pullback (V.pullback z).
  rintro w ⟨z, rfl⟩
  refine ⟨V.pullback z, ?_⟩
  -- Goal: π.pullback (V.pullback z) = (mulByInt q).pullback z.
  -- π.pullback (V.pullback z) = (V.comp π).pullback z (by `Isogeny.comp` defn)
  --                          = (mulByInt q).pullback z (by h_comp).
  have h := DFunLike.congr_fun (congrArg Isogeny.pullback h_comp) z
  exact h

/-! ### T11-DISCHARGE-X-NE (Worker C reusable) — `V.pullback x_gen ≠ x_gen`

The polynomial-divisibility template from T26-B (above) generalises directly
to Worker C's T11 (`isogOneSub_V`, `Hasse/OpenLemmaPrimitives.lean:1130`).
T11 takes `h_x_ne : id.pb x_gen ≠ (V.zsmul -1).pb x_gen` as a hypothesis;
unfolding `id.pb x_gen = x_gen` and
`(V.zsmul -1).pb x_gen = V.pb (mulByInt_x W (-1)) = V.pb (mulByInt_x W 1) = V.pb x_gen`,
the hypothesis becomes `x_gen ≠ V.pb x_gen` — easier than T26-B (no `r, s`
parameters).

**Argument** (cleaner than T26-B; ~50 LOC):
1. Assume `V.pb x_gen = x_gen`.
2. Raise to `q`: `(V.pb x_gen)^q = x_gen^q`. The LHS = `π.pb (V.pb x_gen)`
   (by `frobeniusIsog_pullback_apply`) = `(mulByInt q).pb x_gen` (by `hV.1`
   composition pullback) = `mulByInt_x W q`.
3. Thus `mulByInt_x W q = x_gen^q` in K(E).
4. Multiply by `ΨSq_ff(q)` and lift to K[X] via `algebraMap` injectivity:
   `W.Φ q = X^q * W.ΨSq q` in K[X].
5. `isCoprime_Φ_ΨSq` for `n = q` (Δ ≠ 0 + q ≠ 0) gives `W.Φ q` coprime to
   `W.ΨSq q`. From the equation, `W.ΨSq q ∣ W.Φ q`; coprime + divides ⟹
   `W.ΨSq q` is a unit in K[X], hence a nonzero constant.
6. So `natDegree(W.ΨSq q in K[X]) = 0`. Then
   `natDegree(W.Φ q) = natDegree(X^q * W.ΨSq q) = q + 0 = q`.
7. But `natDegree_Φ` gives `natDegree(W.Φ q) = q²` unconditionally.
8. So `q = q²`, i.e., `q ∈ {0, 1}`. But `q = #K ≥ 2` (Field+Fintype ⟹
   nontrivial ⟹ ≥ 2). Contradiction.

This generalises T26-B's template to the (1, V·(-1)) pair without requiring
any V-side ord-∞ infrastructure (which is genuinely curve-dependent). -/

/-- **T11-DISCHARGE-X-NE** — Worker C reusable: `V.pullback (x_gen W) ≠ x_gen W`
for any `V` satisfying `IsDualOf V (frobeniusIsog W)`.

Substantive proof via the T26-B polynomial-divisibility template: raise to
q-th power, lift to K[X], use `isCoprime_Φ_ΨSq` + `natDegree_Φ`, derive
`q = q²` (impossible for `q ≥ 2`).

Used immediately by Worker C's T11 to discharge `h_x_ne` (after the
`id.pb x_gen = x_gen` and `(V.zsmul -1).pb x_gen = V.pb x_gen`
simplifications). -/
theorem V_pullback_x_gen_ne_x_gen
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W)) :
    V.pullback (x_gen W) ≠ x_gen W := by
  intro h_eq
  -- (V.pb x_gen)^q = π.pb (V.pb x_gen) = (V.comp π).pb x_gen = (mulByInt q).pb x_gen.
  have h_comp_isog :
      V.comp (frobeniusIsog W) =
        mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) := by
    have h := hV.1
    rw [frobeniusIsog_degree] at h
    exact h
  have h_q_ne_int : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  -- π.pb (V.pb x_gen) = (V.comp π).pb x_gen by Isogeny.comp_algebraMap_eq.
  have h_pi : (frobeniusIsog W).pullback (V.pullback (x_gen W)) =
      mulByInt_x W ((Fintype.card K : ℕ) : ℤ) := by
    have h_app := DFunLike.congr_fun (congrArg Isogeny.pullback h_comp_isog) (x_gen W)
    -- h_app : (V.comp π).pb x_gen = (mulByInt q).pb x_gen
    -- LHS = π.pb (V.pb x_gen) (by comp_algebraMap_eq, definitionally).
    -- RHS = mulByInt_x W q (by mulByInt_pullback_x).
    have h_rhs : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
        (x_gen W) = mulByInt_x W ((Fintype.card K : ℕ) : ℤ) := by
      show (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W ((Fintype.card K : ℕ) : ℤ) h_q_ne_int
    rw [← h_rhs]
    exact h_app
  -- π.pb is z ↦ z^q.
  rw [frobeniusIsog_pullback_apply, h_eq] at h_pi
  -- h_pi : (x_gen W) ^ Fintype.card K = mulByInt_x W q
  -- Lift to K[X]: X^q * W.ΨSq q = W.Φ q in K[X].
  -- First: cross-multiply mulByInt_x = Φ_ff/ΨSq_ff equation by ΨSq_ff(q).
  have hΨq_ne : ΨSq_ff W ((Fintype.card K : ℕ) : ℤ) ≠ 0 :=
    ΨSq_ff_ne_zero W h_q_ne_int
  have h_cross : (x_gen W) ^ Fintype.card K *
      ΨSq_ff W ((Fintype.card K : ℕ) : ℤ) =
      Φ_ff W ((Fintype.card K : ℕ) : ℤ) := by
    have := h_pi
    unfold mulByInt_x at this
    field_simp at this
    linear_combination this
  -- Lift via algebraMap injectivity.
  have h_xgen_pow : (x_gen W) ^ Fintype.card K =
      algebraMap (Polynomial K) W.toAffine.FunctionField
        (Polynomial.X ^ Fintype.card K) := by
    rw [map_pow]
    rfl
  have h_alg :
      algebraMap (Polynomial K) W.toAffine.FunctionField
          (Polynomial.X ^ Fintype.card K *
            W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ)) =
        algebraMap (Polynomial K) W.toAffine.FunctionField
          (W.toAffine.Φ ((Fintype.card K : ℕ) : ℤ)) := by
    rw [map_mul, ← h_xgen_pow,
      ← ΨSq_ff_eq_algebraMap_polynomial,
      ← Φ_ff_eq_algebraMap_polynomial]
    exact h_cross
  have h_inj : Function.Injective
      (algebraMap (Polynomial K) W.toAffine.FunctionField) := by
    show Function.Injective
      ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing))
    exact (IsFractionRing.injective W.toAffine.CoordinateRing
        W.toAffine.FunctionField).comp
      Affine.CoordinateRing.algebraMap_poly_injective
  have h_poly :
      Polynomial.X ^ Fintype.card K *
          W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ) =
        W.toAffine.Φ ((Fintype.card K : ℕ) : ℤ) :=
    h_inj h_alg
  -- isCoprime_Φ_ΨSq + divides ⟹ W.ΨSq q is a unit in K[X].
  have hΔ : W.toAffine.Δ ≠ 0 := by
    rw [← W.toAffine.coe_Δ']
    exact_mod_cast W.toAffine.Δ'.ne_zero
  have h_cop : IsCoprime (W.toAffine.Φ ((Fintype.card K : ℕ) : ℤ))
      (W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ)) :=
    isCoprime_Φ_ΨSq W.toAffine hΔ h_q_ne_int
  have hΨq_dvd_Φq :
      W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ) ∣
        W.toAffine.Φ ((Fintype.card K : ℕ) : ℤ) :=
    ⟨Polynomial.X ^ Fintype.card K, by linear_combination -h_poly⟩
  have hΨq_unit : IsUnit (W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ)) :=
    h_cop.symm.isUnit_of_dvd hΨq_dvd_Φq
  -- Units in K[X] are nonzero constants ⟹ natDegree = 0.
  have hΨq_natDeg :
      (W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ)).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hΨq_unit
  -- natDegree(W.Φ q) = q from natDegree_Φ. natDegree(X^q * W.ΨSq q) = q + 0 = q.
  have hΨq_ne_K : W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    have h := IsUnit.ne_zero hΨq_unit
    exact h
  have h_X_pow_ne : (Polynomial.X : Polynomial K) ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have h_LHS_natDeg :
      (Polynomial.X ^ Fintype.card K *
          W.toAffine.ΨSq ((Fintype.card K : ℕ) : ℤ)).natDegree =
        Fintype.card K := by
    rw [Polynomial.natDegree_mul h_X_pow_ne hΨq_ne_K,
      Polynomial.natDegree_X_pow, hΨq_natDeg, Nat.add_zero]
  have h_RHS_natDeg :
      (W.toAffine.Φ ((Fintype.card K : ℕ) : ℤ)).natDegree =
        ((Fintype.card K : ℕ) : ℤ).natAbs ^ 2 :=
    W.toAffine.natDegree_Φ _
  -- From h_poly: LHS.natDegree = RHS.natDegree, i.e., q = q².
  have h_natDeg_eq :
      Fintype.card K = ((Fintype.card K : ℕ) : ℤ).natAbs ^ 2 := by
    have h := congrArg Polynomial.natDegree h_poly
    rw [h_LHS_natDeg, h_RHS_natDeg] at h
    exact h
  have h_natAbs : ((Fintype.card K : ℕ) : ℤ).natAbs = Fintype.card K :=
    Int.natAbs_natCast _
  rw [h_natAbs] at h_natDeg_eq
  -- h_natDeg_eq : Fintype.card K = Fintype.card K ^ 2.
  -- Contradicts q ≥ 2.
  have h_q_ge_two : 2 ≤ Fintype.card K :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  -- q = q² ⟹ q*(q-1) = 0 ⟹ q = 0 or q = 1.
  nlinarith [h_q_ge_two, h_natDeg_eq]

/-- **T11-DISCHARGE-X-NE (T11 hypothesis form)** — discharge T11's
`h_x_ne : (Isogeny.id W.toAffine).pullback (x_gen W) ≠
            (V.zsmul (-1)).pullback (x_gen W)`
substantively from `IsDualOf V (frobeniusIsog W)`. Worker C's T11
(`Hasse/OpenLemmaPrimitives.lean:1130`) can drop this in.

The proof unfolds `id.pb x_gen = x_gen` and
`(V.zsmul -1).pb x_gen = V.pb (mulByInt_x W (-1)) = V.pb (mulByInt_x W 1) = V.pb x_gen`,
reducing to `V_pullback_x_gen_ne_x_gen`. -/
theorem h_x_ne_id_V_zsmul_neg_one
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W)) :
    (Isogeny.id W.toAffine).pullback (x_gen W) ≠
      (V.zsmul (-1)).pullback (x_gen W) := by
  intro h_eq
  apply V_pullback_x_gen_ne_x_gen W V hV
  -- (Isogeny.id W.toAffine).pullback (x_gen W) = x_gen W (by `id.pb` = `AlgHom.id`).
  -- (V.zsmul -1).pb x_gen = V.pb (mulByInt_x W (-1)) = V.pb (mulByInt_x W 1) = V.pb x_gen.
  have h_lhs : (Isogeny.id W.toAffine).pullback (x_gen W) = x_gen W := rfl
  have h_rhs : (V.zsmul (-1)).pullback (x_gen W) = V.pullback (x_gen W) := by
    show ((mulByInt W.toAffine (-1)).comp V).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    congr 1
    have h : (mulByInt W.toAffine (-1)).pullback (x_gen W) = mulByInt_x W (-1) := by
      show (mulByInt W.toAffine (-1)).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W (-1) (by norm_num)
    rw [h, mulByInt_x_neg, mulByInt_x_one]
  rw [h_lhs, h_rhs] at h_eq
  exact h_eq.symm

/-! ### T26-MAIN (R29 §2) — assembly of the V-side genuine isogeny family

R29 §2's T26-MAIN ticket: assemble the V-side `r · V − s · id` genuine
isogeny family from T10's universal V (delivered as an `IsDualOf`
witness), with T26-A's `h_subset` extraction and T26-B's `h_x_ne`
discharge folded in.

The construction is universal in `(r, s)` with the standard `r, s ≠ 0`
and `(r : K), (s : K) ≠ 0` hypotheses (so the genuine isogeny is
non-degenerate). The pole-bound witness `h_pole` is taken as a
hypothesis (T26-C's domain). Worker D's substantive ord chain for
T26-C (mirror of `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`)
discharges `h_pole` curve-uniformly; until that ships, T26-MAIN is
witness-parametric on `h_pole`.

This unconditionally consumes T10's universal V output (no
`verschiebungIsog_of_witness`-vs-`V` translation needed; T26-A bridges
them). -/

/-- **T26-MAIN (R29 §2)** — V-side genuine `r · V − s · id` isogeny,
parameterised by T10's universal V (via `IsDualOf`) and a pole-bound
witness `h_pole` (T26-C's substantive deliverable).

The construction:
1. T26-A (`h_subset_of_isDualOf`): derives `h_subset` from `IsDualOf`.
2. T26-B (`h_x_ne_zsmul_verschiebung_mulByInt_neg`): closes `h_x_ne`
   substantively (no witness wrapper).
3. T26-C (h_pole): taken as hypothesis — witness-parametric until the
   V-side ord chain ships.

Worker D consumes this in `degree_quadratic_genuine_addIsog` for the
`α = V` polarisation instance. -/
noncomputable def genuineIsogSmulSubV_universal
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W
              (h_subset_of_isDualOf W V hV)).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Isogeny W.toAffine W.toAffine :=
  genuineIsogSmulSubV_of_pole_witness W
    (h_subset_of_isDualOf W V hV) r s hr hs
    (h_x_ne_zsmul_verschiebung_mulByInt_neg W
      (h_subset_of_isDualOf W V hV) r s hr hs hrK hsK)
    h_pole

@[simp] theorem genuineIsogSmulSubV_universal_toAddMonoidHom
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_pole : (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W
              (h_subset_of_isDualOf W V hV)).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0) :
    Isogeny.toAddMonoidHom
        (genuineIsogSmulSubV_universal W V hV r s hr hs hrK hsK h_pole) =
      ((verschiebungIsog_of_witness W
          (h_subset_of_isDualOf W V hV)).zsmul r).toAddMonoidHom +
        (mulByInt W.toAffine (-s)).toAddMonoidHom :=
  rfl

/-! ### T-PFA-4-WEAK substrate (reviewer Round 8, 2026-05-25)

The original Wall A claim `ord_∞(addPullback_x_pair (V.zsmul r) (-s)) = -2` was
**false**: counter-example `α = 1-V` over `F_q` with `p ∣ #E(F_q)` is inseparable
(via `(1-V)(1-π) = [#E(F_q)]` carrying inseparability through the dual factor).

The reviewer's repair (option (i)) is the **weak form** `ord_∞ < 0`, which suffices
for the consumer chain (base-hom injectivity → addCoordAlgHomPair injectivity →
genuine V isogeny).

**OBSTRUCTION (deep pass 2026-05-26).** The weak bound is NOT genuinely easier
than the (false) exact bound for the purpose of *deciding the sign*, because the
shipped bridge `Curves/Infinity.ordAtInfty_algebraMap_fracPolyX_of_ne_zero` is an
**exact equivalence**: for the K(x)-image witness `a`,
`ord_∞(algebraMap a) = -2 · intDegree(ofFractionRing a)`, hence
`ord_∞ < 0 ⟺ intDegree > 0`. Establishing either still requires pinning the *sign*
of the dominant order of the addition-formula output, which is exactly the step the
3-way ord tie blocks (`X₁²X₂`, `X₁X₂²`, `−2Y₁Y₂` all at order `−6`; see
`.mathlib-quality/v-side-pole-bound-obstruction.md`). Concretely:

* **Transcendence/pole route** (`γ*x` has a pole because `γ(O)=O`): circular — `γ
  = rV − s` is constructed *via* `addIsog`, whose injectivity is precisely what
  this pole bound feeds (`addBaseHomPair_injective_..._of_pole`). `γ` does not
  exist as an isogeny until *after* this bound.
* **Mirror the π-side**: the π-side `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
  has a *unique* strict dominant term (`α₁(x)²·α₂(x)` at `−4q−2`); the strict
  non-arch chain `ordAtInfty_add_eq_of_lt` fires only because all other terms are
  strictly above it. The V-side has a 3-way tie (V does not scale orders: both
  x-pullbacks have order `−2`), so `ordAtInfty_add_eq_of_lt` cannot fire.
* **intDegree-via-valuation**: this *is* the equivalence above; gives nothing new.

The honest discharge is the formal-group / kernel-of-reduction statement isolated
below (`addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`): both summand
points `(rV)(P_gen)` and `(−s)(P_gen)` reduce to `O` at the place over `∞`, the
kernel of reduction is a subgroup (the formal group), so their sum reduces to `O`
unless it *is* `O` — and `h_x_ne` rules out the latter. This is genuine Silverman
IV.1–IV.3 / VII.2 formal-group theory: mathlib's `Reduction.lean` only reduces
curve *coefficients*, not *points*. **(2026-06-11: discharged.)** The chord-expansion
layer (`ChordExpansion.lean`, FG-B1..B5) now supplies the formal-group subgroup
property, and the Wall-A pole bound `addPullback_x_pair_x_ord_neg` below is proven
from it — see its docstring for the route. -/

/-! ### Wall-A bricks: both summands reduce to `O` (axiom-clean)

The two points `Q₁ = (rV)(P_gen)`, `Q₂ = (−s)(P_gen)` summed by the addition formula
each lie in the **kernel of reduction at `O`** — equivalently their x-coordinate
pullbacks have a pole at `O` (`ord_∞ < 0`).  These two facts are proved
unconditionally below; they are the well-defined hypotheses the formal-group
subgroup closure consumes.  Note both are **universal in `q`** and require no
separability hypothesis — the `−s` summand directly, the `rV` summand via the
Frobenius `q`-power relation `(V.pb(mulByInt_x r))^q = mulByInt_x (r·q)` together
with the *unconditional* `ordAtInfty_mulByInt_x_neg` (so the inseparable factor
`r·q`, where `(r·q : K) = 0`, is handled). -/

/-- **The `(−s)` summand reduces to `O`**: `ord_∞((mulByInt −s).pb x_gen) < 0`.
Direct: `(mulByInt −s).pb x_gen = mulByInt_x W s`, with `ord < 0` by
`ordAtInfty_mulByInt_x_neg` (only needs `s ≠ 0`). -/
theorem ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg
    (s : ℤ) (hs : s ≠ 0) :
    (W_smooth W).ordAtInfty ((mulByInt W.toAffine (-s)).pullback (x_gen W)) < 0 := by
  have h_rhs_x : (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W s := by
    have h : (mulByInt W.toAffine (-s)).pullback (x_gen W) = mulByInt_x W (-s) := by
      show (mulByInt W.toAffine (-s)).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W (-s) (neg_ne_zero.mpr hs)
    rw [h, mulByInt_x_neg]
  rw [h_rhs_x]
  exact ordAtInfty_mulByInt_x_neg W s hs

/-- **The `rV` summand reduces to `O`**: `ord_∞((V.zsmul r).pb x_gen) < 0`.

Proof.  `(V.zsmul r).pb x_gen = V.pb (mulByInt_x W r)`.  Applying Frobenius `π.pb`
(which is the `q`-th power map) and using `[q] = π · V` (the witness factorisation)
gives `(V.pb (mulByInt_x W r))^q = mulByInt_x W (r·q)`.  Taking `ord_∞`:
`q · ord_∞(X₁) = ord_∞(mulByInt_x W (r·q))`, and the RHS is `< 0` by the
unconditional `ordAtInfty_mulByInt_x_neg` (here `(r·q : K) = 0`, so the exact
`-2` form is unavailable, but the *negative* bound still holds).  Dividing by
`q > 0` yields `ord_∞(X₁) < 0`. -/
theorem ordAtInfty_zsmul_verschiebung_pullback_x_neg
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r : ℤ) (hr : r ≠ 0) :
    (W_smooth W).ordAtInfty
        (((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W)) < 0 := by
  -- Step 1: `(V.zsmul r).pb x_gen = V.pb (mulByInt_x W r)`.
  have h_lhs_x :
      ((verschiebungIsog_of_witness W h_subset).zsmul r).pullback (x_gen W) =
        (verschiebungIsog_of_witness W h_subset).pullback (mulByInt_x W r) := by
    show ((mulByInt W.toAffine r).comp
        (verschiebungIsog_of_witness W h_subset)).pullback (x_gen W) = _
    rw [Isogeny.comp_algebraMap_eq]
    congr 1
    show (mulByInt W.toAffine r).pullback
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = _
    exact mulByInt_pullback_x W r hr
  set X₁ := (verschiebungIsog_of_witness W h_subset).pullback (mulByInt_x W r) with hX₁_def
  -- Step 2: `X₁^q = mulByInt_x W (r·q)` via `π.pb (V.pb z) = (mulByInt q).pb z = mulByInt_x (r·q)`
  --   and `π.pb f = f^q`.
  have h_q_ne_int : ((Fintype.card K : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have h_rq_ne_int : r * ((Fintype.card K : ℕ) : ℤ) ≠ 0 := mul_ne_zero hr h_q_ne_int
  have h_pow_eq : X₁ ^ Fintype.card K = mulByInt_x W (r * ((Fintype.card K : ℕ) : ℤ)) := by
    -- `π.pb X₁ = (mulByInt q).pb (mulByInt_x r) = mulByInt_x (r·q)`, and `π.pb X₁ = X₁^q`.
    have h_factor :
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
        (frobeniusIsog W).pullback.comp
          (verschiebungPullback_of_witness W h_subset) :=
      mulByInt_q_factor_via_witness W h_subset
    have h_app := DFunLike.congr_fun h_factor (mulByInt_x W r)
    rw [AlgHom.comp_apply] at h_app
    -- h_app : (mulByInt q).pb (mulByInt_x r) = π.pb (V.pb (mulByInt_x r)) = π.pb X₁  (defeq:
    --   `(verschiebungIsog_of_witness ...).pullback = verschiebungPullback_of_witness`).
    have h_lhs_pi : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback
        (mulByInt_x W r) = mulByInt_x W (r * ((Fintype.card K : ℕ) : ℤ)) :=
      mulByInt_pullback_mulByInt_x_eq_mul W r ((Fintype.card K : ℕ) : ℤ) hr
        h_q_ne_int h_rq_ne_int
    have h_pi_X₁ : (frobeniusIsog W).pullback X₁ = X₁ ^ Fintype.card K :=
      frobeniusIsog_pullback_apply W X₁
    -- Chain: X₁^q = π.pb X₁ = (mulByInt q).pb (mulByInt_x r) = mulByInt_x (r·q).
    have h_app' : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (mulByInt_x W r) =
        (frobeniusIsog W).pullback X₁ := by rw [hX₁_def]; exact h_app
    calc X₁ ^ Fintype.card K = (frobeniusIsog W).pullback X₁ := h_pi_X₁.symm
      _ = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (mulByInt_x W r) := h_app'.symm
      _ = mulByInt_x W (r * ((Fintype.card K : ℕ) : ℤ)) := h_lhs_pi
  -- Step 3: `q · ord(X₁) = ord(mulByInt_x (r·q)) < 0`, and `q > 0`, so `ord(X₁) < 0`.
  have hX₁_ne : X₁ ≠ 0 := by
    rw [hX₁_def]
    exact fun h => mulByInt_x_ne_zero W r hr
      ((verschiebungIsog_of_witness W h_subset).pullback_injective
        (h.trans (map_zero _).symm))
  have h_ord_pow : (W_smooth W).ordAtInfty (X₁ ^ Fintype.card K) =
      Fintype.card K • (W_smooth W).ordAtInfty X₁ :=
    (W_smooth W).ordAtInfty_pow hX₁_ne (Fintype.card K)
  have h_rhs_neg : (W_smooth W).ordAtInfty (mulByInt_x W (r * ((Fintype.card K : ℕ) : ℤ))) < 0 :=
    ordAtInfty_mulByInt_x_neg W (r * ((Fintype.card K : ℕ) : ℤ)) h_rq_ne_int
  rw [h_pow_eq] at h_ord_pow
  -- `q • ord(X₁) < 0` ⟹ `ord(X₁) < 0` since `q > 0`.
  rw [h_lhs_x]
  -- Goal now: ord X₁ < 0.  From `q • ord X₁ = ord(mulByInt_x (rq)) < 0`.
  have h_smul_neg : Fintype.card K • (W_smooth W).ordAtInfty X₁ < 0 := h_ord_pow ▸ h_rhs_neg
  -- If `ord X₁ ≥ 0` then `q • ord X₁ ≥ 0` (nsmul of nonneg in `WithTop ℤ`), contradiction.
  by_contra h_not
  push_neg at h_not
  -- h_not : 0 ≤ ord X₁.  Then 0 = q • 0 ≤ q • ord X₁, contradicting h_smul_neg.
  have h_nonneg : (0 : WithTop ℤ) ≤ Fintype.card K • (W_smooth W).ordAtInfty X₁ := by
    calc (0 : WithTop ℤ) = Fintype.card K • (0 : WithTop ℤ) := by rw [smul_zero]
      _ ≤ Fintype.card K • (W_smooth W).ordAtInfty X₁ := by
          gcongr
  exact absurd h_smul_neg (not_lt.mpr h_nonneg)

/-! ### Wall-A assembly: reduction to the single formal-group fact

The Wall-A lemma `addPullback_x_pair_ord_neg_of_summands_reduce` (below) is the
**generic** kernel-of-reduction subgroup closure: both summands reduce to `O`
(their x-pullbacks have a pole), they are not mutual inverses, ⟹ the sum reduces.

The honest decomposition (after this session's analysis) isolates the *single*
genuine Silverman IV.1.4 fact still missing — **"the sum point reduces to `O`"** —
from the surrounding discrete-valuation bookkeeping, which is now discharged
axiom-clean. Concretely, write `X_sum = addPullback_x_pair α₁ α₂`,
`Y_sum = addPullback_y_pair α₁ α₂`. The pair `(X_sum, Y_sum)` satisfies the
Weierstrass equation (`addPullback_pair_equation`, via `AddNonInversePair_of_x_ne`
from `h_x_ne`). The generic valuation brick
`ordAtInfty_x_neg_of_equation_of_neg_div_pos` (FormalIsogenySeries.lean,
axiom-clean) then converts:

  `Y_sum ≠ 0` + `ord_∞ X_sum ≤ 0` (basepoint) + `0 < ord_∞(−X_sum / Y_sum)`
  (the sum reduces to `O`, in the local parameter `z = −x/y`) ⟹ `ord_∞ X_sum < 0`.

The first witness is geometric (sum not 2-torsion); the basepoint is "the sum is
not regular-finite at `O`"; the third — **`0 < ord_∞(−X_sum / Y_sum)`** — is the
substantive IV.1.4 content. By the `z = −x/y` correspondence and R5b
(`orderTop_localExpand_eq_ordAtInfty`) it equals `0 < orderTop (localExpand z_sum)`,
and the formal-group subgroup property (sub-piece **(a)**,
`order_formalGroupLaw_subst_pos`, FormalIsogenySeries.lean) gives positive order
of `F̂(z₁, z₂)` — **once** the pair-level IV.1.4 identity
`localExpand z_sum = F̂(localExpand z₁, localExpand z₂)` (sub-piece **(b)**) is
available. Sub-piece (b) is the genuine remaining gap (see below). -/

/-- **Wall-A witness form (axiom-clean): the discrete-valuation assembly.**
Given the geometric/basepoint data and the IV.1.4 "sum reduces to `O`" fact
(`h_reduces`), the Wall-A conclusion `ord_∞(addPullback_x_pair α₁ α₂) < 0` follows
from the generic valuation brick `ordAtInfty_x_neg_of_equation_of_neg_div_pos`.

This isolates the **single** substantive hypothesis `h_reduces`
(`0 < ord_∞(−X_sum / Y_sum)`, the IV.1.4 formal-group content) from all the
discrete-valuation bookkeeping, which is fully discharged here. No `sorry`, no
axioms. -/
theorem addPullback_x_pair_ord_neg_of_sum_reduces_witness
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_y_sum_ne : (addPullback_y_pair α₁ α₂ : KE) ≠ 0)
    (h_base : (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) ≤ 0)
    (h_reduces : 0 < (W_smooth W).ordAtInfty
      (-(addPullback_x_pair α₁ α₂) / (addPullback_y_pair α₁ α₂) : KE)) :
    (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) < 0 := by
  -- The pair `(X_sum, Y_sum)` is on the curve (non-inverse from `h_x_ne`).
  have h_equation : (W_KE W).toAffine.Equation
      (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂) :=
    addPullback_pair_equation (AddNonInversePair_of_x_ne h_x_ne)
  -- `X_sum ≠ 0`: the basepoint hypothesis excludes `ord = ⊤` (which `X_sum = 0` would force).
  have h_x_sum_ne : (addPullback_x_pair α₁ α₂ : KE) ≠ 0 := by
    intro h
    have h_top : (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) = ⊤ :=
      ((W_smooth W).ordAtInfty_eq_top_iff _).mpr h
    rw [h_top] at h_base
    exact absurd h_base (by simp)
  exact ordAtInfty_x_neg_of_equation_of_neg_div_pos W h_x_sum_ne h_y_sum_ne
    h_equation h_base h_reduces

/-- **Wall-A target via the IV.1.4 identity (witness-parametric, axiom-clean).**

This is the *consumer* of Silverman IV.1.4 for the pair `(α₁, α₂)`: it reduces the
full target `addPullback_x_pair_sum_reduces_to_O` to exactly three named residual
witnesses, of which only the third (`h_iv14`) carries genuine IV.1.4 content:

1. `h_y_sum_ne : Y_sum ≠ 0` — the sum's `y`-coordinate is genuinely nonzero
   (the sum is an affine point, not a 2-torsion flip). *Not* derivable from the
   formal-group order alone (a cancellation `F̂(f₁, f₂) = 0` is a priori
   possible), so this is a genuine geometric residual.
2. `h_base : ord_∞ X_sum ≤ 0` — the basepoint bound (`X_sum` is not a
   high-order vanishing). Genuine residual (the 3-way `−6` tie obstruction).
3. `h_iv14 : localExpand z_sum = ofPowerSeries (F̂(f₁, f₂))` — the **IV.1.4
   identity**: the chord-tangent addition formula in the `z = −x/y` coordinate,
   local-expanded, equals the explicit formal group law `formalGroupLaw W`
   substituted with the two summand series `fᵢ = formalIsogenySeries W αᵢ`. This
   is the single irreducible chord-addition-match residual.

Given these, item 3 of the target (`0 < ord_∞ z_sum`) is produced *axiom-clean*
by composing the IV.1.4 order-output brick
`orderTop_localExpand_z_sum_pos_of_iv14_identity` (which chains sub-piece (a)
`order_formalGroupLaw_subst_pos`, the Phase-1 summand reductions, and the
`ofPowerSeries` order bridge) with R5b (`orderTop_localExpand_eq_ordAtInfty`).
Items 1, 2 pass through. No `sorry`, no axioms here — the entire substantive gap
is concentrated in the `h_iv14` hypothesis. -/
theorem addPullback_x_pair_sum_reduces_of_iv14_witness
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_α₁ : (W_smooth W).ordAtInfty (α₁.pullback (x_gen W)) < 0)
    (h_α₂ : (W_smooth W).ordAtInfty (α₂.pullback (x_gen W)) < 0)
    (h_y_sum_ne : (addPullback_y_pair α₁ α₂ : KE) ≠ 0)
    (h_base : (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) ≤ 0)
    (h_iv14 : localExpand W
        (-(addPullback_x_pair α₁ α₂) / (addPullback_y_pair α₁ α₂) : KE) =
      HahnSeries.ofPowerSeries ℤ K
        (MvPowerSeries.subst
          (![formalIsogenySeries W α₁, formalIsogenySeries W α₂] :
            Fin 2 → PowerSeries K)
          (formalGroupLaw W).toMvPowerSeries)) :
    (addPullback_y_pair α₁ α₂ : KE) ≠ 0 ∧
    (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) ≤ 0 ∧
    0 < (W_smooth W).ordAtInfty
      (-(addPullback_x_pair α₁ α₂) / (addPullback_y_pair α₁ α₂) : KE) := by
  refine ⟨h_y_sum_ne, h_base, ?_⟩
  -- Item 3: the IV.1.4 order output, transported through R5b.
  rw [← orderTop_localExpand_eq_ordAtInfty W]
  exact orderTop_localExpand_z_sum_pos_of_iv14_identity W α₁ α₂ _ h_α₁ h_α₂ h_iv14

/-- **The single Wall-A gap, sharpened to the kernel-of-reduction pole bound
(Silverman VII.2.2 / IV.1.4 — `X_sum` has a pole at `O`).**

`State (2026-05-29, deep-pass consolidation).`  This is the *single irreducible
residual* of the whole V-side pole bound, isolated as the bare statement
`ord_∞(addPullback_x_pair α₁ α₂) < 0`: if two points `Q₁ = α₁(P_gen)`,
`Q₂ = α₂(P_gen)` reduce to `O` (their `x`-pullbacks have poles, `h_α₁`/`h_α₂`) and
are not mutual inverses (`h_x_ne`, so `Q₁ + Q₂ ≠ O`), then the sum reduces to `O`
too — its `x`-coordinate `addPullback_x_pair α₁ α₂` has a pole at `O`.

**Why this is the precise BRIDGE-003 residual (and what is now derived from it
axiom-clean).**  The naive `ord_∞` analysis of `addX X₁ X₂ ℓ = ℓ² + a₁ℓ − a₂ − X₁ −
X₂` hits a **3-way tie** at the dominant order `−6` (`X₁²X₂`, `X₁X₂²`, `−2Y₁Y₂`; see
`.mathlib-quality/v-side-pole-bound-obstruction.md`).  Breaking the tie requires the
*formal group law* `z(Q₁+Q₂) = F̂(z(Q₁), z(Q₂))` on the `z = −x/y` coordinate
(Silverman IV.1.4) — the long-deferred **BRIDGE-003** (`formalIsogenySeries_add`):
no pure-`ord` substitute exists (the cancellation lives in the series coefficients,
invisible to `ord` arithmetic), and the `addIsog` route cannot supply it (the genuine
`α₁ + α₂` does not exist until *after* this pole bound feeds its injectivity —
circular).  The route that *consumes* the IV.1.4 identity to deliver this conclusion
is the axiom-clean `addPullback_x_pair_sum_reduces_of_iv14_witness` ⟶
`ordAtInfty_x_neg_of_equation_of_neg_div_pos`.

Everything *downstream* of this single fact is now axiom-clean: the bundled
"reduces to `O`" form `addPullback_x_pair_sum_reduces_to_O` (the `Y_sum ≠ 0`,
`ord X_sum ≤ 0`, `0 < ord(−X_sum/Y_sum)` triple) is *derived* from this pole bound
via the shipped curve-equation valuation bricks
(`ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`,
`ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`).

**PROVEN (FG-C1, post-BRIDGE-003).**  The proof runs on the `(z,w)`-chart line
data of `ChordExpansion` (FG-B3/B4) and pure `ord` arithmetic — by
contradiction, assume `0 ≤ ord X₃`:

1. The expansion legs `localExpand_zwSlopeLine_of_x_ne` /
   `localExpand_zwNuLine_of_x_ne` exhibit `λ = −ℓ/c` and `ν = −1/c` as
   `ofPowerSeries` images of series with *zero constant coefficient*
   (`constantCoeff_formalSlopeBiv`/`_formalNuBiv` substituted), so both have
   `ord > 0` at `O` (via R5b `orderTop_localExpand_eq_ordAtInfty`).  This is
   where the chord-expansion depth enters: the positive order of the chart
   slope/intercept is invisible to naive `(x,y)`-`ord` arithmetic (the `−6`
   tie), but is manifest on the series side.
2. `ord ν > 0` gives the intercept a pole: `ord c = mc ≤ −1`; `ord λ > 0`
   gives `ord ℓ ≥ mc + 1`, hence `ord (ℓ·X₃) ≥ mc + 1` (using `0 ≤ ord X₃`).
3. The pre-negation pair `(X₃, Y₃′ = negY X₃ Y₃)` satisfies the curve equation
   (`equation_neg` + `addPullback_pair_equation`); with `0 ≤ ord X₃` the monic
   quadratic in `Y₃′` (coefficients of `ord ≥ 0`) forces `0 ≤ ord Y₃′` by the
   ultrametric domination of `Y₃′²`.
4. But the line gives `c = Y₃′ − ℓ·X₃`, so
   `mc = ord c ≥ min(ord Y₃′, ord (ℓX₃)) ≥ min(0, mc + 1) = mc + 1` —
   contradiction. -/
theorem addPullback_x_pair_x_ord_neg
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_α₁ : (W_smooth W).ordAtInfty (α₁.pullback (x_gen W)) < 0)
    (h_α₂ : (W_smooth W).ordAtInfty (α₂.pullback (x_gen W)) < 0) :
    (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) < 0 := by
  by_contra h_not
  push_neg at h_not
  -- `h_not : 0 ≤ ord_∞ X₃`; derive a contradiction from the chart-line data.
  have h_ni : AddNonInversePair α₁ α₂ := AddNonInversePair_of_x_ne h_x_ne
  have hc : addLineC W α₁ α₂ ≠ 0 := addLineC_ne_zero_of_x_ne W h_α₁ h_α₂ h_x_ne
  -- Elementary `ord` helpers.
  have h_int : ∀ {f : KE}, f ≠ 0 →
      ∃ m : ℤ, (W_smooth W).ordAtInfty f = (m : WithTop ℤ) := by
    intro f hf
    cases hh : (W_smooth W).ordAtInfty f with
    | top => exact absurd ((W_smooth W).ordAtInfty_eq_top_iff _ |>.mp hh) hf
    | coe k => exact ⟨k, rfl⟩
  have h_mul_nonneg : ∀ {f g : KE}, 0 ≤ (W_smooth W).ordAtInfty f →
      0 ≤ (W_smooth W).ordAtInfty g → 0 ≤ (W_smooth W).ordAtInfty (f * g) := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hf0
    · simp only [zero_mul]
      exact le_of_le_of_eq le_top ((W_smooth W).ordAtInfty_zero).symm
    rcases eq_or_ne g 0 with rfl | hg0
    · simp only [mul_zero]
      exact le_of_le_of_eq le_top ((W_smooth W).ordAtInfty_zero).symm
    exact le_of_le_of_eq (add_nonneg hf hg) ((W_smooth W).ordAtInfty_mul hf0 hg0).symm
  -- The chord-branch expansion legs (FG-B3/B4): `λ = −ℓ/c` and `ν = −1/c`
  -- expand to the substituted bivariate series, whose constant coefficients
  -- vanish; hence both have positive `ord` at `O` (via R5b).
  have hf0 : PowerSeries.constantCoeff (formalIsogenySeries W α₁) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α₁
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α₁ h_α₁)
  have hg0 : PowerSeries.constantCoeff (formalIsogenySeries W α₂) = 0 :=
    constantCoeff_formalIsogenySeries_of_orderTop_pos W α₂
      (orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg W α₂ h_α₂)
  have h_lam_pos : 0 < (W_smooth W).ordAtInfty (zwSlopeLine W α₁ α₂) := by
    rw [← orderTop_localExpand_eq_ordAtInfty W,
      localExpand_zwSlopeLine_of_x_ne W h_α₁ h_α₂ h_x_ne]
    exact orderTop_ofPowerSeries_pos_of_order_pos
      (Order.one_le_iff_pos.mp (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
        (constantCoeff_subst_bivariate_eq_zero (formalSlopeBiv W)
          (constantCoeff_formalSlopeBiv W) _ _ hf0 hg0)))
  have h_nu_pos : 0 < (W_smooth W).ordAtInfty (zwNuLine W α₁ α₂) := by
    rw [← orderTop_localExpand_eq_ordAtInfty W,
      localExpand_zwNuLine_of_x_ne W h_α₁ h_α₂ h_x_ne]
    exact orderTop_ofPowerSeries_pos_of_order_pos
      (Order.one_le_iff_pos.mp (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
        (constantCoeff_subst_bivariate_eq_zero (formalNuBiv W)
          (constantCoeff_formalNuBiv W) _ _ hf0 hg0)))
  -- (1) The line intercept `c` has a pole at `O`: `ord c = mc ≤ −1`.
  obtain ⟨mc, hmc⟩ := h_int hc
  have hmc_neg : mc < 0 := by
    have h_nu_ord : (W_smooth W).ordAtInfty (zwNuLine W α₁ α₂)
        = (((0 - mc : ℤ)) : WithTop ℤ) := by
      rw [zwNuLine_def]
      exact (W_smooth W).ord_div_concrete hc 0 mc ((W_smooth W).ordAtInfty_neg_one) hmc
    rw [h_nu_ord] at h_nu_pos
    have h0 : (0 : ℤ) < 0 - mc := by exact_mod_cast h_nu_pos
    omega
  -- (2) `ord (ℓ·X₃) ≥ mc + 1` (the slope leg + `0 ≤ ord X₃`).
  have h_lX_ge : (((mc + 1 : ℤ)) : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty (addSlopePair α₁ α₂ * addPullback_x_pair α₁ α₂) := by
    rcases eq_or_ne (addSlopePair α₁ α₂) 0 with hl0 | hl_ne
    · rw [hl0, zero_mul]
      exact le_of_le_of_eq le_top ((W_smooth W).ordAtInfty_zero).symm
    rcases eq_or_ne (addPullback_x_pair α₁ α₂) 0 with hX0 | hX_ne
    · rw [hX0, mul_zero]
      exact le_of_le_of_eq le_top ((W_smooth W).ordAtInfty_zero).symm
    obtain ⟨ml, hml⟩ := h_int hl_ne
    obtain ⟨mx, hmx⟩ := h_int hX_ne
    have hmx_nonneg : 0 ≤ mx := by
      rw [hmx] at h_not
      exact_mod_cast h_not
    have hml_ge : mc + 1 ≤ ml := by
      have h_lam_ord : (W_smooth W).ordAtInfty (zwSlopeLine W α₁ α₂)
          = (((ml - mc : ℤ)) : WithTop ℤ) := by
        rw [zwSlopeLine_def]
        exact (W_smooth W).ord_div_concrete hc ml mc
          (((W_smooth W).ordAtInfty_neg _).trans hml) hmc
      rw [h_lam_ord] at h_lam_pos
      have h0 : (0 : ℤ) < ml - mc := by exact_mod_cast h_lam_pos
      omega
    have h_mul_eq := (W_smooth W).ordAtInfty_mul hl_ne hX_ne
    rw [hml, hmx] at h_mul_eq
    exact le_trans
      (by exact_mod_cast (show mc + 1 ≤ ml + mx by omega) :
        (((mc + 1 : ℤ)) : WithTop ℤ) ≤ (ml : WithTop ℤ) + (mx : WithTop ℤ))
      (le_of_eq h_mul_eq.symm)
  -- The pre-negation pair `(X₃, Y₃′)` lies on the curve.
  have h_weier₃ : (W_KE W).toAffine.Equation (addPullback_x_pair α₁ α₂)
      ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)) :=
    (Affine.equation_neg _ _).mpr (addPullback_pair_equation h_ni)
  have h_eq : ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
        (addPullback_y_pair α₁ α₂)) ^ 2
      + algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂))
      + algebraMap K KE W.a₃
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂))
      = addPullback_x_pair α₁ α₂ ^ 3
        + algebraMap K KE W.a₂ * addPullback_x_pair α₁ α₂ ^ 2
        + algebraMap K KE W.a₄ * addPullback_x_pair α₁ α₂ + algebraMap K KE W.a₆ := by
    have h := (Affine.equation_iff _ _).mp h_weier₃
    exact h
  -- (3) With `0 ≤ ord X₃`, the monic quadratic forces `0 ≤ ord Y₃′`.
  have h_Y'_nonneg : 0 ≤ (W_smooth W).ordAtInfty
      ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)) := by
    by_contra h_neg
    push_neg at h_neg
    have hY'_ne : (W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
        (addPullback_y_pair α₁ α₂) ≠ 0 := ne_zero_of_ordAtInfty_neg W h_neg
    obtain ⟨m', hm'⟩ := h_int hY'_ne
    have hm'_neg : m' < 0 := by
      rw [hm'] at h_neg
      exact_mod_cast h_neg
    -- Rearrange the curve equation: `Y₃′·Y₃′ = (X-terms) − a₁X₃Y₃′ − a₃Y₃′`
    -- (product spelling, so the `ord` bounds avoid `pow` rewrites).
    have h_sq : ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
            (addPullback_y_pair α₁ α₂))
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
            (addPullback_y_pair α₁ α₂))
        = addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂
          + algebraMap K KE W.a₂ * (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂)
          + algebraMap K KE W.a₄ * addPullback_x_pair α₁ α₂ + algebraMap K KE W.a₆
          - algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
              * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
                  (addPullback_y_pair α₁ α₂))
          - algebraMap K KE W.a₃
              * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
                  (addPullback_y_pair α₁ α₂)) := by
      linear_combination h_eq
    -- `ord` bounds: every right-hand-side term has `ord ≥ m'`.
    have hX2 : 0 ≤ (W_smooth W).ordAtInfty
        (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂) :=
      h_mul_nonneg h_not h_not
    have hX3 : 0 ≤ (W_smooth W).ordAtInfty
        (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂) :=
      h_mul_nonneg hX2 h_not
    have hm'_le : ((m' : ℤ) : WithTop ℤ) ≤ 0 := by
      exact_mod_cast hm'_neg.le
    have ht1 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂) :=
      le_trans hm'_le hX3
    have ht2 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.a₂
          * (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂)) :=
      le_trans hm'_le (h_mul_nonneg (ord_algebraMap_F_nonneg W W.a₂) hX2)
    have ht3 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.a₄ * addPullback_x_pair α₁ α₂) :=
      le_trans hm'_le (h_mul_nonneg (ord_algebraMap_F_nonneg W W.a₄) h_not)
    have ht4 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.a₆) :=
      le_trans hm'_le (ord_algebraMap_F_nonneg W W.a₆)
    have ht5 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
              (addPullback_y_pair α₁ α₂))) :=
      hm'.symm.le.trans (ord_coeff_mul_ge W _ _
        (h_mul_nonneg (ord_algebraMap_F_nonneg W W.a₁) h_not))
    have ht6 : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap K KE W.a₃
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
              (addPullback_y_pair α₁ α₂))) :=
      hm'.symm.le.trans (ord_coeff_mul_ge W _ _ (ord_algebraMap_F_nonneg W W.a₃))
    have h_rhs_ge : ((m' : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂
          + algebraMap K KE W.a₂ * (addPullback_x_pair α₁ α₂ * addPullback_x_pair α₁ α₂)
          + algebraMap K KE W.a₄ * addPullback_x_pair α₁ α₂ + algebraMap K KE W.a₆
          - algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
              * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
                  (addPullback_y_pair α₁ α₂))
          - algebraMap K KE W.a₃
              * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
                  (addPullback_y_pair α₁ α₂))) := by
      refine le_trans ?_ ((W_smooth W).ordAtInfty_sub_ge_min _ _)
      refine le_min ?_ ht6
      refine le_trans ?_ ((W_smooth W).ordAtInfty_sub_ge_min _ _)
      refine le_min ?_ ht5
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ ht4
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      refine le_min ?_ ht3
      refine le_trans ?_ ((W_smooth W).ordAtInfty_add_ge_min _ _)
      exact le_min ht1 ht2
    have h_prod : (W_smooth W).ordAtInfty
        (((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂))
          * ((W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
            (addPullback_y_pair α₁ α₂)))
        = ((m' + m' : ℤ) : WithTop ℤ) :=
      ((W_smooth W).ordAtInfty_mul hY'_ne hY'_ne).trans (by rw [hm']; norm_cast)
    rw [h_sq] at h_prod
    rw [h_prod] at h_rhs_ge
    have hfin : m' ≤ m' + m' := by exact_mod_cast h_rhs_ge
    omega
  -- (4) The line `c = Y₃′ − ℓ·X₃` forces `mc ≥ mc + 1` — contradiction.
  have hY₃line : (W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)
      = addSlopePair α₁ α₂ * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
        + α₁.pullback (y_gen W) :=
    Affine.negY_negY (W' := (W_KE W).toAffine) _ _
  have hc_eq : addLineC W α₁ α₂
      = (W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)
        - addSlopePair α₁ α₂ * addPullback_x_pair α₁ α₂ := by
    rw [hY₃line, addLineC_def]
    ring
  have h_min : ((mc + 1 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (addLineC W α₁ α₂) := by
    rw [hc_eq]
    refine le_trans (le_min (le_trans ?_ h_Y'_nonneg) h_lX_ge)
      ((W_smooth W).ordAtInfty_sub_ge_min _ _)
    exact_mod_cast (show (mc + 1 : ℤ) ≤ 0 by omega)
  rw [hmc] at h_min
  have hcontra : (mc + 1 : ℤ) ≤ mc := by exact_mod_cast h_min
  omega

/-- **The bundled "sum reduces to `O`" triple — now DERIVED axiom-clean from the
single pole bound `addPullback_x_pair_x_ord_neg`.**

Given the kernel-of-reduction pole bound `ord_∞ X_sum < 0`
(`addPullback_x_pair_x_ord_neg`, the lone BRIDGE-003 residual), the three facets of
"`Q₁ + Q₂` reduces to `O`" all follow from the curve equation
(`addPullback_pair_equation`) via the shipped, axiom-clean valuation bricks:

1. `Y_sum ≠ 0` — `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg` (a pole of `X` on the
   curve forces `Y ≠ 0`, since otherwise `X` would be a root of a base-field cubic and
   hence regular at `O`).
2. `ord_∞ X_sum ≤ 0` — immediate (`le_of_lt`) from the pole bound.
3. `0 < ord_∞(−X_sum/Y_sum)` — `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg` (a pole
   of `X` forces a strictly deeper pole of `Y`, so the local parameter `z = −X/Y`
   vanishes at `O`).

No fresh `sorry`, no axioms here — the entire deep content is concentrated in
`addPullback_x_pair_x_ord_neg`. -/
theorem addPullback_x_pair_sum_reduces_to_O
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_α₁ : (W_smooth W).ordAtInfty (α₁.pullback (x_gen W)) < 0)
    (h_α₂ : (W_smooth W).ordAtInfty (α₂.pullback (x_gen W)) < 0) :
    (addPullback_y_pair α₁ α₂ : KE) ≠ 0 ∧
    (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) ≤ 0 ∧
    0 < (W_smooth W).ordAtInfty
      (-(addPullback_x_pair α₁ α₂) / (addPullback_y_pair α₁ α₂) : KE) := by
  -- The single deep residual: `X_sum` has a pole at `O` (Silverman VII.2.2 / BRIDGE-003).
  have hX_neg : (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) < 0 :=
    addPullback_x_pair_x_ord_neg W h_x_ne h_α₁ h_α₂
  -- `X_sum ≠ 0` (a pole is not zero): otherwise `ord = ⊤`, contradicting `ord < 0`.
  have hX_ne : (addPullback_x_pair α₁ α₂ : KE) ≠ 0 := by
    intro h0
    have h_top : (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) = ⊤ :=
      ((W_smooth W).ordAtInfty_eq_top_iff _).mpr h0
    rw [h_top] at hX_neg
    exact absurd hX_neg (not_lt_of_ge le_top)
  -- The sum lies on the curve `W_KE` (addition formula output satisfies the equation).
  have h_weier : (W_KE W).toAffine.Equation
      (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂) :=
    addPullback_pair_equation (AddNonInversePair_of_x_ne h_x_ne)
  -- Conjunct 1: `Y_sum ≠ 0` from the pole of `X_sum` + the curve equation (axiom-clean).
  have hY_ne : (addPullback_y_pair α₁ α₂ : KE) ≠ 0 :=
    ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg W hX_ne h_weier hX_neg
  refine ⟨hY_ne, le_of_lt hX_neg, ?_⟩
  -- Conjunct 3: `0 < ord(−X_sum/Y_sum)` from the pole of `X_sum` + the curve equation.
  exact ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg W hX_ne hY_ne h_weier hX_neg

/-- **The formal-group / kernel-of-reduction subgroup closure (the single Wall-A gap).**

The content of Silverman VII.2.2: the **kernel of reduction at `O`** in the
`K(E)`-points of `E` — the set of points whose `x`-coordinate has a pole at the
place over `∞` — is a **subgroup** (it is the formal group / formal neighbourhood
of `O`).  Concretely: if two points `Q₁ = (α₁(P_gen))`, `Q₂ = (α₂(P_gen))` reduce
to `O` (their `x`-pullbacks have `ord_∞ < 0`) and are not mutual inverses
(`α₁(x) ≠ α₂(x)`, so `Q₁ + Q₂ ≠ O` is not forced by the doubling/inverse case),
then their sum `Q₁ + Q₂` — whose `x`-coordinate is `addPullback_x_pair α₁ α₂` by
the curve addition formula — also reduces to `O`: `ord_∞(addPullback_x_pair) < 0`.

**Why this is the genuine remaining content.**  Stated as the addition-formula
output `addX X₁ X₂ ℓ = ℓ² + a₁ℓ − a₂ − X₁ − X₂` with `ℓ = (Y₁−Y₂)/(X₁−X₂)`, the
naive `ord_∞` analysis hits a **3-way tie**: `X₁²X₂`, `X₁X₂²`, `−2 Y₁Y₂` all sit
at the dominant order `−6` of the reduced numerator (see the module note above and
`.mathlib-quality/v-side-pole-bound-obstruction.md`).  Breaking the tie requires
the *formal group law* `z(Q₁+Q₂) = F̂(z(Q₁), z(Q₂))` on the `z = −x/y` coordinate
(`F̂ ∈ Ẑ[[z₁,z₂]]`, `F̂(z₁,z₂) = z₁ + z₂ + O(2)`), Silverman IV.1 — equivalently
`formalGroup_preserves_positive_order` transported through the addition-formula
local expansion (`localExpand`).  That pair-level IV.1.4 bridge
(`localExpand(z(Q₁+Q₂)) = F̂(localExpand z₁, localExpand z₂)`) is now **proven** for
general pairs (`formalIsogenySeries_add`, `ChordExpansion.lean`, 2026-06-11); the
`addIsog` route could not have supplied it (the genuine isogeny `α₁ + α₂` does not
exist until *after* this pole bound feeds its injectivity — that dependency was
circular).

This is exactly the reviewer's **B-narrow / Pic⁰ comorphism** input.  Stated
generically (so it discharges *both* the V-side and π-side uniformly).

**State of this session's analysis (2026-05-29).**  Everything *except* the
IV.1.4 formal-group identity is now discharged axiom-clean and the gap is reduced
to a single, precisely-characterised fact:

* The discrete-valuation assembly is the proved, axiom-clean witness
  `addPullback_x_pair_ord_neg_of_sum_reduces_witness` (above), built on the three
  generic Weierstrass-point valuation bricks in `FormalIsogenySeries.lean`
  (`ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`,
  `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`,
  `ordAtInfty_x_neg_of_equation_of_neg_div_pos`).
* The **single remaining gap** is the IV.1.4 statement "the sum reduces to `O`",
  packaged below as `addPullback_x_pair_sum_reduces` — equivalently
  `0 < ord_∞(−X_sum / Y_sum)` with `Y_sum ≠ 0` (these come together: reduction to
  `O` means *both* coordinates have poles).  This is **sub-piece (b)**: by
  R5b + the `z = −x/y` correspondence it equals `0 < orderTop (localExpand z_sum)`,
  and sub-piece (a) (`order_formalGroupLaw_subst_pos`) closes it the moment the
  pair-level identity `localExpand z_sum = F̂(localExpand z₁, localExpand z₂)` is
  available.  A pure-order substitute for (b) does **not** exist: the order of
  `z_sum` is determined by the F̂ cancellation, which is invisible to the
  non-archimedean `ord` arithmetic (this is the 3-way −6 tie).  So (b) genuinely
  requires the IV.1.4 equality (full or its order-coefficient consequence), the
  one piece the project never proved. -/
theorem addPullback_x_pair_ord_neg_of_summands_reduce
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (h_x_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W))
    (h_α₁ : (W_smooth W).ordAtInfty (α₁.pullback (x_gen W)) < 0)
    (h_α₂ : (W_smooth W).ordAtInfty (α₂.pullback (x_gen W)) < 0) :
    (W_smooth W).ordAtInfty ((addPullback_x_pair α₁ α₂) : KE) < 0 :=
  -- This is *exactly* the single isolated deep residual `addPullback_x_pair_x_ord_neg`
  -- (Silverman VII.2.2 / BRIDGE-003): the kernel of reduction at `O` is a subgroup.  The
  -- bundled triple `addPullback_x_pair_sum_reduces_to_O` is now *derived* from this fact
  -- (axiom-clean), rather than the other way around.
  addPullback_x_pair_x_ord_neg W h_x_ne h_α₁ h_α₂

/-- **Residual (Pic⁰ / formal-group content) — the V-side pair pullback has a pole
at `O`.** Now reduced to the single formal-group subgroup statement
`addPullback_x_pair_ord_neg_of_summands_reduce`, with **both** "summand reduces to
`O`" hypotheses discharged axiom-clean by `ordAtInfty_zsmul_verschiebung_pullback_x_neg`
and `ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg`, and the non-inverse hypothesis by
`h_x_ne_zsmul_verschiebung_mulByInt_neg`.

Mathematically: `addPullback_x_pair (V.zsmul r) (mulByInt −s)` is the x-coordinate
of `Q₁ + Q₂` where `Q₁ = (rV)(P_gen)`, `Q₂ = (−s)(P_gen)` are points on `W_KE`.
Both `Q₁, Q₂` lie in the kernel of reduction at `O` (their x-coordinates have a pole
there — the two bricks), and the kernel of reduction is a subgroup (Silverman VII.2 /
the formal group), so `Q₁ + Q₂` lies in it too — i.e. its x-coordinate has order
`< 0` — *unless* `Q₁ + Q₂ = O`, which `h_x_ne` excludes (`Q₁ = −Q₂` forces equal
x-coordinates). -/
theorem addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0 :=
  addPullback_x_pair_ord_neg_of_summands_reduce W
    (h_x_ne_zsmul_verschiebung_mulByInt_neg W h_subset r s hr hs hrK hsK)
    (ordAtInfty_zsmul_verschiebung_pullback_x_neg W h_subset r hr)
    (ordAtInfty_zsmul_mulByInt_neg_pullback_x_neg W s hs)

/-- **Sub-leaf — intDegree of K(x)-preimage of the V-side pair pullback is positive**.

Per the K(x)-image lemma `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image`
(line 179), there exists `a ∈ FractionRing (Polynomial K)` with
`addPullback_x_pair = algebraMap a`. This sub-leaf asserts that the
canonical `a` chosen by that lemma has strictly positive `intDegree`.

Discharge: `intDegree(a) > 0 ⟺ ord_∞(algebraMap a) < 0` exactly (via the bridge
`ordAtInfty_algebraMap_fracPolyX_of_ne_zero`, `ord = -2·intDegree`); reduces to the
named formal-group / Pic⁰ residual `addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`.
No fresh `sorry` here — the gap lives entirely in that single named residual. -/
theorem intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    0 < RatFunc.intDegree (RatFunc.ofFractionRing
      (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image W h_subset
        r s hr hs
        (h_x_ne_zsmul_verschiebung_mulByInt_neg W h_subset r s hr hs hrK hsK)).choose) := by
  -- The K(x)-image witness `a` (the `.choose`) and its defining equation.
  have h_x_ne := h_x_ne_zsmul_verschiebung_mulByInt_neg W h_subset r s hr hs hrK hsK
  set a := (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
    W h_subset r s hr hs h_x_ne).choose with ha_def
  have ha : addPullback_x_pair ((verschiebungIsog_of_witness W h_subset).zsmul r)
      (mulByInt W.toAffine (-s)) =
      algebraMap (FractionRing (Polynomial K)) KE a :=
    (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
      W h_subset r s hr hs h_x_ne).choose_spec
  -- The named formal-group / Pic⁰ residual: the pair pullback has `ord_∞ < 0`.
  have h_pole := addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole
    W h_subset r s hr hs hrK hsK
  -- Rewrite the pole via the K(x)-image: `h_pole : ordAtInfty (algebraMap a) < 0`.
  rw [show ((addPullback_x_pair
      ((verschiebungIsog_of_witness W h_subset).zsmul r)
      (mulByInt W.toAffine (-s))) : KE) = _ from ha] at h_pole
  -- `a ≠ 0`: otherwise `algebraMap a = 0`, with `ord_∞ = ⊤`, contradicting the pole.
  have h_a_ne : a ≠ 0 := by
    intro h_a_zero
    have h_top : (W_smooth W).ordAtInfty
        ((algebraMap (FractionRing (Polynomial K)) KE) a) = ⊤ := by
      rw [h_a_zero, map_zero]; exact (W_smooth W).ordAtInfty_zero
    rw [h_top] at h_pole
    exact absurd h_pole (not_lt_of_ge le_top)
  -- Apply the exact `ord = -2·intDegree` bridge (align `KE` ≡ `(W_smooth W).FunctionField`).
  have h_ord_eq := (W_smooth W).ordAtInfty_algebraMap_fracPolyX_of_ne_zero h_a_ne
  rw [show (W_smooth W).ordAtInfty
      ((algebraMap (FractionRing (Polynomial K)) (W_smooth W).FunctionField) a) =
      (W_smooth W).ordAtInfty
        ((algebraMap (FractionRing (Polynomial K)) KE) a) from rfl] at h_ord_eq
  rw [h_ord_eq] at h_pole
  -- `h_pole : ((-2 * intDegree (ofFractionRing a) : ℤ) : WithTop ℤ) < 0`; hence `intDegree > 0`.
  have h_cast : (-2 * RatFunc.intDegree (RatFunc.ofFractionRing a) : ℤ) < 0 := by
    rwa [← WithTop.coe_zero, WithTop.coe_lt_coe] at h_pole
  linarith [h_cast]

/-- **T-PFA-4-WEAK substrate** (Round 8 reviewer repair): the V-side pair pullback
has strictly negative ord at infinity. This is the weak-form Wall A that suffices
for the existing `_of_pole`-parametric consumer chain (`addBaseHomPair_injective_..._of_pole`
→ `addCoordAlgHomPair_injective_..._of_pole` → `genuineIsogSmulSubV_of_pole_witness`).

Discharge: composes the K(x)-image lemma (line 179) with the curve-level
`ordAtInfty_algebraMap_fracPolyX_of_ne_zero` (gives `ord = -2·intDegree`)
plus the positive-intDegree sub-leaf above.

Note: the original `_hr, _hs, _hrK, _hsK` hypotheses are now USED to feed
the sub-leaves (h_x_ne discharge + intDegree positivity). -/
theorem ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_x_pair
            ((verschiebungIsog_of_witness W h_subset).zsmul r)
            (mulByInt W.toAffine (-s))) : KE) < 0 := by
  -- Step 1: extract the K(x)-image witness.
  have h_x_ne := h_x_ne_zsmul_verschiebung_mulByInt_neg W h_subset r s hr hs hrK hsK
  obtain ⟨a, ha⟩ := addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
    W h_subset r s hr hs h_x_ne
  -- Step 2: rewrite ord_∞ via the K(x)-image.
  rw [show ((addPullback_x_pair
      ((verschiebungIsog_of_witness W h_subset).zsmul r)
      (mulByInt W.toAffine (-s))) : KE) = _ from ha]
  -- Step 3: positive intDegree ⟹ a ≠ 0 (a constant zero has intDegree 0).
  have h_intDeg_pos :=
    intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos
      W h_subset r s hr hs hrK hsK
  have h_a_ne : a ≠ 0 := by
    intro h_a_zero
    -- a = 0 ⟹ intDegree = 0 (intDegree_zero), contradicting positivity.
    have h_a_choose_eq : a = (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
        W h_subset r s hr hs h_x_ne).choose := by
      -- ha says addPullback = algebraMap a; choose_spec also says
      -- addPullback = algebraMap (choose). So algebraMap a = algebraMap choose,
      -- and algebraMap is injective.
      have h_spec := (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
        W h_subset r s hr hs h_x_ne).choose_spec
      have h_eq : algebraMap (FractionRing (Polynomial K)) KE a =
          algebraMap (FractionRing (Polynomial K)) KE _ := ha.symm.trans h_spec
      exact (FaithfulSMul.algebraMap_injective (FractionRing (Polynomial K)) KE) h_eq
    rw [h_a_choose_eq] at h_a_zero
    rw [h_a_zero] at h_intDeg_pos
    simp [RatFunc.ofFractionRing_zero, RatFunc.intDegree_zero] at h_intDeg_pos
  -- Step 4: apply ordAtInfty_algebraMap_fracPolyX_of_ne_zero, going via W_smooth.
  have h_ord_eq := (W_smooth W).ordAtInfty_algebraMap_fracPolyX_of_ne_zero h_a_ne
  -- Step 5: connect intDegree of a to intDegree of choose.
  have h_eq_choose : a = (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
      W h_subset r s hr hs h_x_ne).choose := by
    have h_spec := (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image
      W h_subset r s hr hs h_x_ne).choose_spec
    have h_eq : algebraMap (FractionRing (Polynomial K)) KE a =
        algebraMap (FractionRing (Polynomial K)) KE _ := ha.symm.trans h_spec
    exact (FaithfulSMul.algebraMap_injective (FractionRing (Polynomial K)) KE) h_eq
  -- Step 6: h_intDeg_pos talks about choose's intDegree; transfer via h_eq_choose.
  have h_intDeg_a : 0 < RatFunc.intDegree (RatFunc.ofFractionRing a) := by
    rw [h_eq_choose]; exact h_intDeg_pos
  -- Step 7: combine — h_ord_eq gives ord = -2·intDegree, intDegree > 0 ⟹ -2·intDegree < 0.
  -- Goal is ord at W.toAffine.FunctionField; h_ord_eq talks about W_smooth.FunctionField.
  -- These are definitionally equal; use change to align.
  change (W_smooth W).ordAtInfty ((algebraMap (FractionRing (Polynomial K))
    (W_smooth W).FunctionField) a) < 0
  rw [h_ord_eq]
  have h_neg : -2 * RatFunc.intDegree (RatFunc.ofFractionRing a) < (0 : ℤ) := by linarith
  exact_mod_cast h_neg

/-- **`genuineIsogSmulSubV_universal_unconditional`** — universal V-side genuine
isogeny without the `h_pole` hypothesis. Wires the WEAK-form substrate sub-leaf
`ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero` into the existing
`genuineIsogSmulSubV_universal` to discharge the pole hypothesis internally.

Once the substrate sub-leaf ships axiom-clean, this constructor becomes axiom-clean
end-to-end, completing the V-side polarisation chain. -/
noncomputable def genuineIsogSmulSubV_universal_unconditional
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    Isogeny W.toAffine W.toAffine :=
  genuineIsogSmulSubV_universal W V hV r s hr hs hrK hsK
    (ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero W
      (h_subset_of_isDualOf W V hV) r s hr hs hrK hsK)

@[simp] theorem genuineIsogSmulSubV_universal_unconditional_toAddMonoidHom
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    Isogeny.toAddMonoidHom
        (genuineIsogSmulSubV_universal_unconditional W V hV r s hr hs hrK hsK) =
      ((verschiebungIsog_of_witness W
          (h_subset_of_isDualOf W V hV)).zsmul r).toAddMonoidHom +
        (mulByInt W.toAffine (-s)).toAddMonoidHom :=
  rfl

end HasseWeil
