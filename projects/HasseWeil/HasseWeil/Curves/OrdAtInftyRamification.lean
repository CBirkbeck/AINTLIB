/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Infinity
import HasseWeil.Curves.Transcendence
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The ramification-pullback formula at the place at infinity (Silverman II.2.6)

For a finite field extension `ψ : F(C₂) → F(C₁)` of curve function fields that
maps functions *regular at the basepoint* `O₂` to functions *regular at the
basepoint* `O₁` (i.e. the morphism `C₁ → C₂` whose pullback is `ψ` is defined at
`O₁` and sends it to `O₂`), the order at infinity transforms by the local
**ramification index** `e` at `O`:

  `ord_∞^{C₁}(ψ g) = e · ord_∞^{C₂}(g)`   (for `g ≠ 0`),

where `e = ord_∞^{C₁}(ψ t)` for any uniformizer `t` at `O₂` (`ord_∞^{C₂}(t) = 1`).

This is the standard valuation-pullback law `v_P ∘ ψ = e · v_{φP}` (Silverman
II.2, def. of the ramification index `e_φ(P) = ord_P(φ* t_{φP})`), specialised to
the place at infinity.  The proof is *purely formal* from:

* `ord_∞` is an additive valuation (`ordAtInfty_mul`);
* `ψ` is a field homomorphism (so `ψ(g⁻¹) = ψ(g)⁻¹`, `map_inv₀`);
* the geometric input `hreg : ord_∞ g ≥ 0 ⟹ ord_∞ (ψ g) ≥ 0` (regularity at `O`
  is preserved — this is the basepoint condition of an isogeny, carried by
  `EC.Isogeny.pullback_ordAtInfty_nonneg`).

Given `hreg`, `ψ` kills `O₂`-units (`ord_∞^{C₂} u = 0 ⟹ ord_∞^{C₁}(ψ u) = 0`,
applying `hreg` to `u` and `u⁻¹`).  Writing `g = (g · t^{-n}) · t^n` with
`n = ord_∞^{C₂} g`, the unit `g · t^{-n}` contributes `0` and `t^n` contributes
`n · e`, giving the formula.

The companion file `HasseWeil/EC/IsogenyAG/RamificationInfty.lean` instantiates
this for `EC.Isogeny`, discharging the `hramO` residual of the dual-isogeny
construction.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2 (ramification index),
  II.2.6 (`Σ e = deg`, `e` multiplicative), III.4.10a (`e = deg_i` ⟹ separable
  ⟹ `e = 1`), IV.1 (`ord_∞`).
-/

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}

/-! ### Integer powers of `ordAtInfty` -/

/-- `nsmul` commutes with the coercion `ℤ → WithTop ℤ`: `k • (a : WithTop ℤ) =
((k : ℤ) * a : WithTop ℤ)`.  (The additive monoid hom property of the coercion.) -/
private theorem coe_nsmul_int (k : ℕ) (a : ℤ) :
    (k • ((a : ℤ) : WithTop ℤ)) = ((((k : ℤ) * a : ℤ)) : WithTop ℤ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

/-- **`ordAtInfty` of an integer power** (value form): for nonzero `f` with
`ord_∞ f = a`, `ord_∞ (f ^ m) = m · a` for `m : ℤ`.  Stated with the order
extracted as an integer to avoid `WithTop ℤ` `zsmul`; proved by splitting `m` into
nonnegative and negative parts (`ordAtInfty_pow`, `ordAtInfty_inv`). -/
theorem ordAtInfty_zpow {C : SmoothPlaneCurve F} {f : C.FunctionField} (hf : f ≠ 0)
    {a : ℤ} (ha : C.ordAtInfty f = ((a : ℤ) : WithTop ℤ)) (m : ℤ) :
    C.ordAtInfty (f ^ m) = (((m * a : ℤ)) : WithTop ℤ) := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast, C.ordAtInfty_pow hf k, ha, coe_nsmul_int]
  · rw [zpow_neg, zpow_natCast, C.ordAtInfty_inv, C.ordAtInfty_pow hf k, ha,
      coe_nsmul_int,
      show -(((((k : ℤ) * a : ℤ)) : WithTop ℤ)) = ((((-(k : ℤ)) * a : ℤ)) : WithTop ℤ)
        from by rw [neg_mul]; rfl]

/-! ### A canonical uniformizer at infinity -/

/-- **`x/y` is a uniformizer at `O`**: `ord_∞ (coordX / coordY) = 1`.  From
`ord_∞ coordX = -2`, `ord_∞ coordY = -3` (Silverman IV.1):
`(-2) - (-3) = 1`.  (The reciprocal `coordY / coordX` of the more familiar
`t = -x/y` of `LocalExpansion`; both have `|ord| = 1`.) -/
theorem ordAtInfty_coordX_div_coordY (C : SmoothPlaneCurve F) :
    C.ordAtInfty (C.coordX / C.coordY) = ((1 : ℤ) : WithTop ℤ) := by
  rw [C.ordAtInfty_div_eq_mul_inv _ C.coordX_ne_zero C.coordY_ne_zero,
    C.ordAtInfty_inv, C.ordAtInfty_coordX, C.ordAtInfty_coordY]
  rfl

/-- `coordX / coordY ≠ 0` (both coordinates are nonzero in the function field). -/
theorem coordX_div_coordY_ne_zero (C : SmoothPlaneCurve F) :
    C.coordX / C.coordY ≠ 0 :=
  div_ne_zero C.coordX_ne_zero C.coordY_ne_zero

/-! ### The abstract valuation-pullback law at infinity -/

/-- **`ψ` kills `O`-units.** If `ψ : F(C₂) → F(C₁)` is a field homomorphism that
preserves regularity at infinity (`hreg`), then it sends a function with order `0`
at `O₂` (a unit at `O₂`) to a function with order `0` at `O₁`.  Applying `hreg` to
both `u` and `u⁻¹` pins `ord_∞^{C₁}(ψ u)` between `0` and `0`. -/
theorem ordAtInfty_ringHom_eq_zero_of_ordAtInfty_eq_zero
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    {u : C₂.FunctionField} (hu : u ≠ 0)
    (hu0 : C₂.ordAtInfty u = ((0 : ℤ) : WithTop ℤ)) :
    C₁.ordAtInfty (ψ u) = ((0 : ℤ) : WithTop ℤ) := by
  -- `ψ` is a field homomorphism, hence injective; so `ψ u ≠ 0`.
  have hψu : ψ u ≠ 0 := (map_ne_zero ψ).mpr hu
  -- Work with the integer value `k = ord_∞(ψ u)`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, C₁.ordAtInfty (ψ u) = ((k : ℤ) : WithTop ℤ) :=
    ⟨_, C₁.ordAtInfty_of_ne hψu⟩
  rw [hk]
  -- Lower bound: `u` is regular at `O₂` (order `0 ≥ 0`), so `ψ u` is regular at `O₁`: `0 ≤ k`.
  have h_lower : (0 : ℤ) ≤ k := by
    have := hreg u (by rw [hu0]; norm_cast)
    rw [hk] at this
    exact_mod_cast this
  -- Upper bound: `u⁻¹` is also regular at `O₂` (order `0`), so `ψ (u⁻¹) = (ψ u)⁻¹` is
  -- regular at `O₁`: `0 ≤ -k`, i.e. `k ≤ 0`.
  have hinv0 : C₂.ordAtInfty u⁻¹ = ((0 : ℤ) : WithTop ℤ) := by
    rw [C₂.ordAtInfty_inv, hu0]; rfl
  have h_upper : (0 : ℤ) ≤ -k := by
    have := hreg u⁻¹ (by rw [hinv0]; norm_cast)
    rw [map_inv₀, C₁.ordAtInfty_inv, hk] at this
    rw [show -((k : ℤ) : WithTop ℤ) = (((-k : ℤ)) : WithTop ℤ) from rfl] at this
    exact_mod_cast this
  -- `0 ≤ k` and `0 ≤ -k` force `k = 0`.
  norm_cast
  omega

/-- **Order of `ψ` on an integer power of `t`.** If `ψ t ≠ 0` and `ord_∞(ψ t) = e`,
then `ord_∞(ψ (t ^ k)) = k · e` for every `k : ℤ`.  Just `map_zpow₀` (`ψ` is a
field hom, so `ψ (t ^ k) = (ψ t) ^ k`) followed by `ordAtInfty_zpow`. -/
private theorem ordAtInfty_ringHom_zpow_uniformizer
    (ψ : C₂.FunctionField →+* C₁.FunctionField) {t : C₂.FunctionField}
    (hψt_ne : ψ t ≠ 0) {e : ℕ} (he : C₁.ordAtInfty (ψ t) = ((e : ℤ) : WithTop ℤ))
    (k : ℤ) :
    C₁.ordAtInfty (ψ (t ^ k)) = (((k * e : ℤ)) : WithTop ℤ) := by
  rw [map_zpow₀, C₁.ordAtInfty_zpow hψt_ne he k]

/-- **The unit-factorization core of the pullback law** (value form).  With `ψ`
preserving regularity (`hreg`), `t` a uniformizer at `O₂` (`ord_∞ t = 1`), `e` the
order of `ψ t`, and `g ≠ 0` of integer order `ord_∞ g = n`, the image `ψ g` has
order exactly `n · e` at `O₁`.

Write `g = u · t ^ n` with `u := g · t ^ (-n)` a unit at `O₂` (`ord_∞ u = 0`).
Then `ψ u` is a unit at `O₁` (`ord_∞(ψ u) = 0`, via
`ordAtInfty_ringHom_eq_zero_of_ordAtInfty_eq_zero`), and `ψ (t ^ n)` has order
`n · e` (`ordAtInfty_ringHom_zpow_uniformizer`), so additivity of `ord_∞` gives
`ord_∞(ψ g) = 0 + n · e`. -/
private theorem ordAtInfty_ringHom_eq_mul_of_ordAtInfty_eq
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    {t : C₂.FunctionField} (ht : C₂.ordAtInfty t = ((1 : ℤ) : WithTop ℤ))
    {e : ℕ} (he : C₁.ordAtInfty (ψ t) = ((e : ℤ) : WithTop ℤ))
    {g : C₂.FunctionField} (hg : g ≠ 0) {n : ℤ}
    (hn : C₂.ordAtInfty g = ((n : ℤ) : WithTop ℤ)) :
    C₁.ordAtInfty (ψ g) = (((n * e : ℤ)) : WithTop ℤ) := by
  -- `t ≠ 0` (its order is `1`, not `⊤`); `ψ` injective so `ψ t ≠ 0`.
  have ht_ne : t ≠ 0 := fun h ↦ by simp [h] at ht
  have hψt_ne : ψ t ≠ 0 := (map_ne_zero ψ).mpr ht_ne
  -- `u := g · t^(-n)` is a unit at `O₂`: `ord_∞ u = n + (-n)·1 = 0`.
  set u : C₂.FunctionField := g * t ^ (-n) with hu_def
  have htzpow_ne : t ^ (-n) ≠ 0 := zpow_ne_zero _ ht_ne
  have hu_ne : u ≠ 0 := mul_ne_zero hg htzpow_ne
  have hu0 : C₂.ordAtInfty u = ((0 : ℤ) : WithTop ℤ) := by
    rw [hu_def, C₂.ordAtInfty_mul hg htzpow_ne, hn,
      C₂.ordAtInfty_zpow ht_ne ht (-n), ← WithTop.coe_add]
    congr 1
    ring
  -- `ψ u` (= `ψ g · (ψ t)^(-n)`) has order `0` at `O₁` (Lemma 1).
  have hψu0 : C₁.ordAtInfty (ψ u) = ((0 : ℤ) : WithTop ℤ) :=
    ordAtInfty_ringHom_eq_zero_of_ordAtInfty_eq_zero ψ hreg hu_ne hu0
  -- `ψ u ≠ 0`, `ψ (t ^ n) ≠ 0`.
  have hψu_ne : ψ u ≠ 0 := (map_ne_zero ψ).mpr hu_ne
  have hψtn_ne : ψ (t ^ n) ≠ 0 := by
    rw [map_zpow₀]; exact zpow_ne_zero _ hψt_ne
  -- Now `g = u · t^n`, so `ψ g = ψ u · ψ(t^n)`, giving `ord_∞(ψ g) = 0 + n·e`.
  have hg_eq : g = u * t ^ n := by
    rw [hu_def, mul_assoc, ← zpow_add₀ ht_ne, neg_add_cancel, zpow_zero, mul_one]
  have hsplit : C₁.ordAtInfty (ψ g) =
      C₁.ordAtInfty (ψ u) + C₁.ordAtInfty (ψ (t ^ n)) := by
    conv_lhs => rw [hg_eq, map_mul]
    exact C₁.ordAtInfty_mul hψu_ne hψtn_ne
  rw [hsplit, ordAtInfty_ringHom_zpow_uniformizer ψ hψt_ne he n, hψu0]
  norm_num

/-- **The ramification-pullback law at infinity (abstract form).** Let
`ψ : F(C₂) → F(C₁)` be a field homomorphism preserving regularity at `O`
(`hreg`), `t` a uniformizer at `O₂` (`ord_∞^{C₂} t = 1`), and `e` the order of
`ψ t` at `O₁`.  Then for every nonzero `g`,

  `ord_∞^{C₁}(ψ g) = e · ord_∞^{C₂}(g)`.

This is Silverman's valuation-pullback formula `ord_P(φ* g) = e_φ(P)·ord_{φP}(g)`
at `P = O`. -/
theorem ordAtInfty_ringHom_eq_nsmul
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    {t : C₂.FunctionField} (ht : C₂.ordAtInfty t = ((1 : ℤ) : WithTop ℤ))
    {e : ℕ} (he : C₁.ordAtInfty (ψ t) = ((e : ℤ) : WithTop ℤ))
    {g : C₂.FunctionField} (hg : g ≠ 0) :
    C₁.ordAtInfty (ψ g) = e • C₂.ordAtInfty g := by
  -- Extract the integer order `n` of `g` at `O₂`.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, C₂.ordAtInfty g = ((n : ℤ) : WithTop ℤ) :=
    ⟨_, C₂.ordAtInfty_of_ne hg⟩
  -- Unit-factorization core: `ord_∞(ψ g) = n · e` (value form).
  have hψg_ord : C₁.ordAtInfty (ψ g) = (((n * e : ℤ)) : WithTop ℤ) :=
    ordAtInfty_ringHom_eq_mul_of_ordAtInfty_eq ψ hreg ht he hg hn
  -- `n·e = e • (n : WithTop ℤ)`, both equal to `(e*n : ℤ)`.
  rw [hψg_ord, hn, coe_nsmul_int e n]
  congr 1
  ring

/-! ### The ramification index and the pullback formula, packaged -/

/-- **The ramification index at infinity exists, and the pullback formula holds.**
For any field homomorphism `ψ : F(C₂) → F(C₁)` preserving regularity at the
basepoint (`hreg`) — e.g. the pullback of an isogeny — there is a natural number
`e` (the ramification index `e_ψ(O) = ord_∞(ψ t)` for the uniformizer `t = x/y`)
such that for every nonzero `g`,

  `ord_∞^{C₁}(ψ g) = e · ord_∞^{C₂}(g)`.

This is the ramification-pullback formula at infinity (Silverman II.2.6, the
`P = O` case of `ord_P(φ* g) = e_φ(P)·ord_{φP}(g)`), with the index produced
explicitly as `e = (ord_∞(ψ (x/y))).toNat`. -/
theorem exists_ramificationIdx_ordAtInfty_ringHom
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f)) :
    ∃ e : ℕ, ∀ g : C₂.FunctionField, g ≠ 0 →
      C₁.ordAtInfty (ψ g) = e • C₂.ordAtInfty g := by
  -- Uniformizer `t = x/y` at `O₂`, `ord_∞ t = 1`.
  set t : C₂.FunctionField := C₂.coordX / C₂.coordY with ht_def
  have ht : C₂.ordAtInfty t = ((1 : ℤ) : WithTop ℤ) := C₂.ordAtInfty_coordX_div_coordY
  have ht_ne : t ≠ 0 := C₂.coordX_div_coordY_ne_zero
  -- `ψ t ≠ 0` (ψ injective), and `ψ t` is regular at `O₁` (`hreg` at `t`).
  have hψt_ne : ψ t ≠ 0 := (map_ne_zero ψ).mpr ht_ne
  have hψt_nonneg : 0 ≤ C₁.ordAtInfty (ψ t) := hreg t (by rw [ht]; norm_cast)
  -- The ramification index `e := (ord_∞(ψ t)).toNat`, with `ord_∞(ψ t) = (e : WithTop ℤ)`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, C₁.ordAtInfty (ψ t) = ((m : ℤ) : WithTop ℤ) :=
    ⟨_, C₁.ordAtInfty_of_ne hψt_ne⟩
  have hm_nonneg : 0 ≤ m := by rw [hm] at hψt_nonneg; exact_mod_cast hψt_nonneg
  refine ⟨m.toNat, fun g hg ↦ ?_⟩
  have he : C₁.ordAtInfty (ψ t) = ((m.toNat : ℤ) : WithTop ℤ) := by
    rw [hm, Int.toNat_of_nonneg hm_nonneg]
  exact ordAtInfty_ringHom_eq_nsmul ψ hreg ht he hg

/-- **The ramification index at infinity is `≥ 1`, with the pullback formula**, when
the place above `O` is *non-trivial*: i.e. when `ψ` sends the uniformizer `t = x/y`
to a function that actually *vanishes at `O₁`* (`0 < ord_∞(ψ t)`).  This
non-triviality is the genuine "the `∞`-place of `C₁` lies over the `∞`-place of
`C₂`" / "morphism is non-constant" input — for a finite extension `F(C₁)/ψ(F(C₂))`
it holds automatically (a non-trivial discrete valuation restricts non-trivially
to a subfield over which the field is algebraic — that derivation is
`pos_ordAtInfty_ringHom_coordX_div_coordY_of_isAlgebraic` below, and
`CurveMap.exists_pos_ramificationIdx_ordAtInfty` packages the unconditional
`CurveMap` form), but is not a *formal* consequence of regularity-preservation
alone.  Given it, `e_ψ(O) = ord_∞(ψ t) ≥ 1`.

This is the `∞`-place analogue of the project's finite-point
`one_le_ramificationIndex_of_pullback_pointValuation_lt_one`. -/
theorem exists_pos_ramificationIdx_ordAtInfty_ringHom
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    (hnt : 0 < C₁.ordAtInfty (ψ (C₂.coordX / C₂.coordY))) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ g : C₂.FunctionField, g ≠ 0 →
      C₁.ordAtInfty (ψ g) = e • C₂.ordAtInfty g := by
  set t : C₂.FunctionField := C₂.coordX / C₂.coordY with ht_def
  have ht : C₂.ordAtInfty t = ((1 : ℤ) : WithTop ℤ) := C₂.ordAtInfty_coordX_div_coordY
  have ht_ne : t ≠ 0 := C₂.coordX_div_coordY_ne_zero
  have hψt_ne : ψ t ≠ 0 := (map_ne_zero ψ).mpr ht_ne
  obtain ⟨m, hm⟩ : ∃ m : ℤ, C₁.ordAtInfty (ψ t) = ((m : ℤ) : WithTop ℤ) :=
    ⟨_, C₁.ordAtInfty_of_ne hψt_ne⟩
  -- `0 < ord_∞(ψ t) = m`, so `1 ≤ m`, hence `1 ≤ m.toNat`.
  have hm_pos : 0 < m := by rw [hm] at hnt; exact_mod_cast hnt
  refine ⟨m.toNat, by omega, fun g hg ↦ ?_⟩
  have he : C₁.ordAtInfty (ψ t) = ((m.toNat : ℤ) : WithTop ℤ) := by
    rw [hm, Int.toNat_of_nonneg (le_of_lt hm_pos)]
  exact ordAtInfty_ringHom_eq_nsmul ψ hreg ht he hg

/-! ### Non-triviality of the place at infinity over the image: `e ≥ 1`

The remaining input of `exists_pos_ramificationIdx_ordAtInfty_ringHom` is the
non-triviality `0 < ord_∞(ψ (x/y))`.  We derive it from **algebraicity** of
`F(C₁)` over the image of `ψ`: a discrete valuation that vanishes identically on
a subfield also vanishes on every element *algebraic* over that subfield (write
down the minimal polynomial and compare the order of the constant term with the
orders of the higher terms via the ultrametric inequality), and `ord_∞` does
*not* vanish on `coordX` (`ord_∞ x = -2`).  Mathlib has no
"a nontrivial valuation restricts nontrivially along an algebraic extension"
for our additive `WithTop ℤ`-valued `ordAtInfty`, so we prove it directly. -/

/-- **Ultrametric bound for finite sums**: if every summand has `ord_∞ ≥ c`,
so does the sum.  Finset-sum form of `ordAtInfty_add_ge_min`. -/
theorem le_ordAtInfty_sum {ι : Type*} {C : SmoothPlaneCurve F} {c : WithTop ℤ}
    (s : Finset ι) (f : ι → C.FunctionField)
    (h : ∀ i ∈ s, c ≤ C.ordAtInfty (f i)) :
    c ≤ C.ordAtInfty (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x ↦ c ≤ C.ordAtInfty x)
    (fun a b ha hb ↦ le_trans (le_min ha hb) (C.ordAtInfty_add_ge_min a b))
    (by simp) h

/-- If `ord_∞ ∘ ψ` vanishes on all of `F(C₂)×`, then no element of `F(C₁)` that
is algebraic over the image of `ψ` can have *strictly positive* order at `O₁`.

Take the minimal polynomial `z^n + a_{n-1}z^{n-1} + ⋯ + a₀` of `z` over `F(C₂)`
(acting through `ψ`): its constant term `a₀` is nonzero, so `ord_∞(ψ a₀) = 0`;
but `ψ a₀ = -(z^n + ⋯ + a₁ z)` and every term on the right has order
`ord_∞(ψ aᵢ) + i·ord_∞ z = i·ord_∞ z ≥ ord_∞ z > 0`, so the ultrametric bound
forces `0 = ord_∞(ψ a₀) ≥ ord_∞ z > 0`, a contradiction. -/
private theorem not_ordAtInfty_pos_of_isAlgebraic
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (htriv : ∀ k : C₂.FunctionField, k ≠ 0 →
      C₁.ordAtInfty (ψ k) = ((0 : ℤ) : WithTop ℤ))
    {z : C₁.FunctionField} (hz : z ≠ 0)
    (halg : letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
      IsAlgebraic C₂.FunctionField z)
    (hpos : 0 < C₁.ordAtInfty z) : False := by
  letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
  have halg' : IsAlgebraic C₂.FunctionField z := halg
  have hint : IsIntegral C₂.FunctionField z := halg'.isIntegral
  -- the (positive, integer) order of `z` at `O₁`
  obtain ⟨a, ha⟩ : ∃ a : ℤ, C₁.ordAtInfty z = ((a : ℤ) : WithTop ℤ) :=
    ⟨_, C₁.ordAtInfty_of_ne hz⟩
  have ha_pos : 0 < a := by
    rw [ha] at hpos
    exact_mod_cast hpos
  -- the minimal polynomial of `z` over `F(C₂)`, with nonzero constant term
  set m : Polynomial C₂.FunctionField := minpoly C₂.FunctionField z with hm_def
  have hc0 : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hz
  have haev : (Polynomial.aeval z) m = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at haev
  -- isolate the constant term: `ψ a₀ = -(higher terms)`
  have hconst : m.coeff 0 • (z ^ 0 : C₁.FunctionField) = ψ (m.coeff 0) := by
    rw [pow_zero, Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
  have hkey : ψ (m.coeff 0) =
      -∑ i ∈ Finset.range m.natDegree, m.coeff (i + 1) • z ^ (i + 1) := by
    rw [← hconst]
    exact eq_neg_of_add_eq_zero_right haev
  -- every higher term has order at least `a` (`= 0 + (i+1)·a`)
  have hterm : ∀ i ∈ Finset.range m.natDegree,
      ((a : ℤ) : WithTop ℤ) ≤ C₁.ordAtInfty (m.coeff (i + 1) • z ^ (i + 1)) := by
    intro i _
    rcases eq_or_ne (m.coeff (i + 1)) 0 with hci | hci
    · rw [hci, zero_smul]
      simp
    · have hψci : ψ (m.coeff (i + 1)) ≠ 0 := (map_ne_zero ψ).mpr hci
      have hzpow : z ^ (i + 1) ≠ 0 := pow_ne_zero _ hz
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        C₁.ordAtInfty_mul hψci hzpow, htriv _ hci, C₁.ordAtInfty_pow hz, ha,
        coe_nsmul_int, ← WithTop.coe_add, WithTop.coe_le_coe]
      have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
      push_cast
      nlinarith
  -- ultrametric: the sum of the higher terms has order ≥ a > 0 — but it is
  -- `-ψ a₀`, of order 0
  have hsum : ((a : ℤ) : WithTop ℤ) ≤
      C₁.ordAtInfty (∑ i ∈ Finset.range m.natDegree, m.coeff (i + 1) • z ^ (i + 1)) :=
    le_ordAtInfty_sum _ _ hterm
  have h0 := htriv _ hc0
  rw [hkey, C₁.ordAtInfty_neg] at h0
  rw [h0, WithTop.coe_le_coe] at hsum
  omega

/-- **Valuation triviality ascends to algebraic elements** (key lemma).  If the
field homomorphism `ψ : F(C₂) → F(C₁)` satisfies `ord_∞(ψ k) = 0` for every
`k ≠ 0`, then every nonzero `z ∈ F(C₁)` *algebraic over the image of `ψ`* also
has `ord_∞ z = 0`.

WLOG `ord_∞ z > 0` (replace `z` by `z⁻¹`, also algebraic, if `ord_∞ z < 0`), and
apply the minimal-polynomial contradiction `not_ordAtInfty_pos_of_isAlgebraic`. -/
theorem ordAtInfty_eq_zero_of_isAlgebraic
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (htriv : ∀ k : C₂.FunctionField, k ≠ 0 →
      C₁.ordAtInfty (ψ k) = ((0 : ℤ) : WithTop ℤ))
    {z : C₁.FunctionField} (hz : z ≠ 0)
    (halg : letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
      IsAlgebraic C₂.FunctionField z) :
    C₁.ordAtInfty z = ((0 : ℤ) : WithTop ℤ) := by
  letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
  have halg' : IsAlgebraic C₂.FunctionField z := halg
  obtain ⟨a, ha⟩ : ∃ a : ℤ, C₁.ordAtInfty z = ((a : ℤ) : WithTop ℤ) :=
    ⟨_, C₁.ordAtInfty_of_ne hz⟩
  rcases lt_trichotomy a 0 with hlt | heq | hgt
  · -- a pole of `z` is a zero of `z⁻¹`
    exfalso
    refine not_ordAtInfty_pos_of_isAlgebraic ψ htriv (inv_ne_zero hz) halg'.inv ?_
    rw [C₁.ordAtInfty_inv, ha,
      show -((a : ℤ) : WithTop ℤ) = (((-a : ℤ)) : WithTop ℤ) from rfl]
    exact_mod_cast Int.neg_pos.mpr hlt
  · rw [ha, heq]
  · exact (not_ordAtInfty_pos_of_isAlgebraic ψ htriv hz halg'
      (by rw [ha]; exact_mod_cast hgt)).elim

/-- **Non-triviality of the place at infinity over the image** (the `e ≥ 1`
input).  If `F(C₁)` is algebraic over the image of `ψ` — it suffices that the
coordinate function `x₁` be algebraic — and `ψ` preserves regularity at `O`,
then the pullback of the uniformizer `t = x/y` genuinely *vanishes* at `O₁`:

  `0 < ord_∞(ψ (x₂/y₂))`.

Otherwise `ord_∞(ψ t) = 0`, so the (already proven) pullback formula
`ord_∞(ψ g) = e • ord_∞ g` holds with `e = 0`, i.e. `ord_∞ ∘ ψ ≡ 0` — and then
the key lemma forces `ord_∞ x₁ = 0`, contradicting `ord_∞ x₁ = -2`. -/
theorem pos_ordAtInfty_ringHom_coordX_div_coordY_of_isAlgebraic
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    (halg : letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
      IsAlgebraic C₂.FunctionField C₁.coordX) :
    0 < C₁.ordAtInfty (ψ (C₂.coordX / C₂.coordY)) := by
  set t : C₂.FunctionField := C₂.coordX / C₂.coordY with ht_def
  have ht : C₂.ordAtInfty t = ((1 : ℤ) : WithTop ℤ) := C₂.ordAtInfty_coordX_div_coordY
  have hψt_nonneg : 0 ≤ C₁.ordAtInfty (ψ t) := hreg t (by rw [ht]; norm_cast)
  rcases hψt_nonneg.lt_or_eq with hlt | heq
  · exact hlt
  · -- `ord_∞(ψ t) = 0` would make the pullback formula hold with `e = 0`
    exfalso
    have he : C₁.ordAtInfty (ψ t) = (((0 : ℕ) : ℤ) : WithTop ℤ) := by
      rw [← heq]; norm_num
    have htriv : ∀ k : C₂.FunctionField, k ≠ 0 →
        C₁.ordAtInfty (ψ k) = ((0 : ℤ) : WithTop ℤ) := by
      intro k hk
      rw [ordAtInfty_ringHom_eq_nsmul ψ hreg ht he hk, zero_nsmul]
      norm_num
    have h0 := ordAtInfty_eq_zero_of_isAlgebraic ψ htriv C₁.coordX_ne_zero halg
    rw [C₁.ordAtInfty_coordX] at h0
    have : (-2 : ℤ) = 0 := by exact_mod_cast h0
    omega

/-- **The ramification index at infinity is `≥ 1`** under the algebraicity
hypothesis: combines `exists_pos_ramificationIdx_ordAtInfty_ringHom` with the
non-triviality `pos_ordAtInfty_ringHom_coordX_div_coordY_of_isAlgebraic`. -/
theorem exists_pos_ramificationIdx_ordAtInfty_ringHom_of_isAlgebraic
    (ψ : C₂.FunctionField →+* C₁.FunctionField)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (ψ f))
    (halg : letI : Algebra C₂.FunctionField C₁.FunctionField := ψ.toAlgebra
      IsAlgebraic C₂.FunctionField C₁.coordX) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ g : C₂.FunctionField, g ≠ 0 →
      C₁.ordAtInfty (ψ g) = e • C₂.ordAtInfty g :=
  exists_pos_ramificationIdx_ordAtInfty_ringHom ψ hreg
    (pos_ordAtInfty_ringHom_coordX_div_coordY_of_isAlgebraic ψ hreg halg)

end HasseWeil.Curves.SmoothPlaneCurve

/-! ### The algebraicity witness for a `CurveMap`, and the unconditional `e ≥ 1`

For the pullback of an honest `CurveMap φ : C₁ → C₂` the algebraicity hypothesis
holds *unconditionally* (no coordinate-ring witness needed): `trdeg_F F(C₁) = 1`
(`functionField_trdeg_eq_one`) and the image of `ψ = φ*` contains the
transcendental element `φ* x₂` (`transcendental_coordX` + injectivity), so
`{φ* x₂}` is a transcendence basis of `F(C₁)/F` and `F(C₁)` is algebraic over the
image subfield.  (The same one-element-transcendence-basis argument as
`AdditionPullback/Differential.lean`'s `isogOneSub_negFrobenius` witness, here
for an arbitrary curve map.) -/

namespace HasseWeil.Curves.CurveMap

variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}

/-- **`F(C₁)` is algebraic over `φ* F(C₂)`** (element-wise, CoordHom-free): with
`F(C₁)` viewed as an `F(C₂)`-algebra via the pullback (`φ.toAlgebra`), every
element is algebraic.  Transcendence-degree argument: `φ* x₂` is transcendental
over `F` and `trdeg_F F(C₁) = 1`, so `{φ* x₂}` is a transcendence basis and
`F(C₁)` is algebraic over `F⟨φ* x₂⟩ ⊆ φ* F(C₂)`. -/
theorem isAlgebraic_toAlgebra (φ : CurveMap C₁ C₂) (z : C₁.FunctionField) :
    letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
    IsAlgebraic C₂.FunctionField z := by
  letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  -- `φ* x₂` is transcendental over `F` (pullbacks are injective `F`-algebra homs)
  have hu : Transcendental F (φ.pullback C₂.coordX) := fun hAlg ↦
    C₂.transcendental_coordX
      ((isAlgebraic_algHom_iff φ.pullback φ.pullback_injective).mp hAlg)
  -- the singleton `{φ* x₂}` is a transcendence basis of `F(C₁)/F`
  have hindep : AlgebraicIndependent F
      (![φ.pullback C₂.coordX] : Fin 1 → C₁.FunctionField) := by
    rw [algebraicIndependent_unique_type_iff]
    exact hu
  have hbasis : IsTranscendenceBasis F
      (![φ.pullback C₂.coordX] : Fin 1 → C₁.FunctionField) := by
    apply hindep.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    rw [C₁.functionField_trdeg_eq_one]
    simp
  -- hence `F(C₁)` is algebraic over the adjoin, which sits inside the range
  have hle : Algebra.adjoin F
      (Set.range (![φ.pullback C₂.coordX] : Fin 1 → C₁.FunctionField)) ≤
      φ.pullback.range := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    fin_cases i
    exact ⟨C₂.coordX, rfl⟩
  have hrange := ((hbasis.isAlgebraic).isAlgebraic z).tower_top_of_subalgebra_le hle
  -- transfer along the isomorphism `F(C₂) ≃ₐ[F] φ* F(C₂)`: map the coefficients
  -- of a witness polynomial back through `(AlgEquiv.ofInjective φ*).symm`
  obtain ⟨p, hp_ne, hp_eval⟩ := hrange
  let e : C₂.FunctionField ≃ₐ[F] φ.pullback.range :=
    AlgEquiv.ofInjective φ.pullback φ.pullback_injective
  let f : (↥φ.pullback.range) →+* C₂.FunctionField := e.symm
  have hf_inj : Function.Injective f := e.symm.injective
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf_inj).mpr hp_ne, ?_⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_map] at hp_eval ⊢
  have hcomp : (algebraMap C₂.FunctionField C₁.FunctionField).comp f =
      algebraMap (↥φ.pullback.range) C₁.FunctionField := by
    apply RingHom.ext
    intro w
    change φ.pullback (e.symm w) = (w : C₁.FunctionField)
    exact congrArg Subtype.val (e.apply_symm_apply w)
  rw [hcomp]
  exact hp_eval

/-- **Non-triviality of the place at infinity, unconditional for a `CurveMap`**:
if the pullback of `φ : C₁ → C₂` preserves regularity at `O` (`hreg`), it sends
the uniformizer `x₂/y₂` to a function *vanishing* at `O₁`.  This is the `hnt`
input of `exists_pos_ramificationIdx_ordAtInfty_ringHom`, now a theorem. -/
theorem pos_ordAtInfty_pullback_coordX_div_coordY (φ : CurveMap C₁ C₂)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (φ.pullback f)) :
    0 < C₁.ordAtInfty (φ.pullback (C₂.coordX / C₂.coordY)) :=
  SmoothPlaneCurve.pos_ordAtInfty_ringHom_coordX_div_coordY_of_isAlgebraic
    φ.pullback.toRingHom hreg (φ.isAlgebraic_toAlgebra C₁.coordX)

/-- **The ramification index at infinity of a `CurveMap` is `≥ 1`, with the
pullback formula** (Silverman II.2.6 at `P = O`, with `e ≥ 1`): for a curve map
whose pullback preserves regularity at the basepoint, there is `e ≥ 1` with
`ord_∞(φ* g) = e • ord_∞ g` for all `g ≠ 0`.  Fully unconditional in `φ`. -/
theorem exists_pos_ramificationIdx_ordAtInfty (φ : CurveMap C₁ C₂)
    (hreg : ∀ f : C₂.FunctionField, 0 ≤ C₂.ordAtInfty f →
      0 ≤ C₁.ordAtInfty (φ.pullback f)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ g : C₂.FunctionField, g ≠ 0 →
      C₁.ordAtInfty (φ.pullback g) = e • C₂.ordAtInfty g :=
  SmoothPlaneCurve.exists_pos_ramificationIdx_ordAtInfty_ringHom
    φ.pullback.toRingHom hreg (φ.pos_ordAtInfty_pullback_coordX_div_coordY hreg)

end HasseWeil.Curves.CurveMap
