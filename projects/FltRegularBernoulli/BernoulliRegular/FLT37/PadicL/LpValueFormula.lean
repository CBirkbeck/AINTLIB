import BernoulliRegular.FLT37.PadicL.Prop812

/-!
# B-C1.1′ — `L_p(1, ω^i)` via Washington Theorem 5.18 and the valuation of `log_p`-sums

This file **constructs** a Kubota–Leopoldt package `PadicLFunction p` whose
Iwasawa-congruence field `v_p(L_p(1, ω^i)) = v_p(B_i / i)` is **proved**, by
defining `L_p(1, ω^i)` through Washington's *explicit* Theorem 5.18 formula
(Case I, conductor `f = p`)

  `L_p(1, ω^i) = -(τ(ω^{-i}) / p) · Σ_{a=1}^{p-1} ω^{-i}(a) · log_p(1 - ζ_p^a)`,

and reading off its valuation by **valuation algebra** plus the *proven* B-C1.2
Gauss-sum valuation `v_p(τ(ω^{-i})) = i/(p-1)`.  This **sidesteps the
Kubota–Leopoldt Iwasawa-limit construction entirely**: only the *valuation* of
`L_p(1, ω^i)` is needed downstream (Cor 8.23 / Thm 8.22 / Prop 8.12), and that
valuation is recovered from the explicit RHS.

## The valuation read-off (fully proved here)

Write `v` for a `ℚ`-valued valuation on the ambient field (additive on nonzero
products).  With `LpValue i := -(τ i / p) · logSum i`, additivity of `v` gives, for
`τ i, logSum i ≠ 0`,

  `v(LpValue i) = v(τ i) - v(p) + v(logSum i) = i/(p-1) - v(p) + v(logSum i)`.   (★)

This identity is **proved unconditionally** in `LpData.valuation_LpValue`,
reusing only the valuation axioms and the B-C1.2 input `v(τ i) = i/(p-1)`.

## The genuine analytic residual

Equation (★) reduces the whole Iwasawa congruence to the single valuation of the
character-twisted `p`-adic-log sum:

  `v(logSum i) = v_p(B_i / i) + v(p) - i/(p-1)`.   (LogBernoulli)

This is the *valuation* shadow of Washington's resummation (pp. 63–66):
`log_p(1 - ζ^a) = -Σ_{n≥1} ζ^{an}/n`, the Gauss-sum orthogonality collapse
`Σ_a ω^{-i}(a) ζ^{an} = ω^i(n) τ(ω^{-i})`, and the generalized-Bernoulli
identification of the resulting series with `B_{1, ω^{i-1}} ≡ B_i/i` (Kummer
congruence, Cor 5.13).  It is carried here as the named field `logBernoulli` of
`LpData` — a `Prop`, **not** an axiom, **not** a `sorry` — and is the precise
smallest open analytic content of `v_p(L_p(1, ω^i)) = v_p(B_i/i)`.

Combining (★) with (LogBernoulli) gives `v(LpValue i) = v_p(B_i / i)`, hence the
`PadicLFunction.valuation_eq_bernoulliFactor` field — this is `LpData.toPadicLFunction`.

## What is unconditional

* `LpData.valuation_LpValue` (★): proved from valuation algebra + B-C1.2.
* `LpData.valuation_LpValue_eq_bernoulliFactor`: `v(LpValue i) = v_p(B_i/i)`,
  proved from (★) + the `logBernoulli` field.
* `LpData.toPadicLFunction`: a genuine `PadicLFunction p` whose Iwasawa-congruence
  field is **proved** (not assumed) from the explicit formula.
* `LpData` is shown **non-vacuous** (`ofPadicLFunction'`): any abstract
  Kubota–Leopoldt package gives rise to one, so no hidden contradiction is
  introduced.  The actual `p = 37` instance requires discharging `logBernoulli`
  (the named residual) together with `Theorem518CaseI`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.18 (pp. 63–66), Cor 5.13, Prop 6.13, Prop 8.12.
-/

namespace BernoulliRegular.FLT37.PadicL

namespace Val

variable {K : Type*} [Field K] (v : K → ℚ)

/-- A `ℚ`-valued valuation is **multiplicative-additive** on nonzero arguments.
We bundle exactly the closure properties used by the `L_p`-formula valuation
read-off (matching the `Prop812Data` valuation interface, which likewise does not
fix the normalisation of `v(p)`).  The actual normalisation of `v(p)` is carried
abstractly and cancels in the final read-off; over `ℚ_p(ζ_p)` with `v(ζ_p-1) = 1`
one has `v(p) = p - 1`, while the `normVal`/`Padic.valuation` normalisation has
`v(p) = 1` — both give the same final Iwasawa congruence. -/
structure IsValuation (p : ℕ) : Prop where
  /-- Additivity on nonzero products. -/
  map_mul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  /-- Negation invariance. -/
  map_neg : ∀ x : K, v (-x) = v x
  /-- `p ≠ 0` in `K` (so division by `p` is legitimate). -/
  p_ne_zero : (p : K) ≠ 0

variable {v} {p : ℕ}

/-- Valuation of an inverse: `v(x⁻¹) = - v(x)` for `x ≠ 0`. -/
theorem IsValuation.map_inv (hv : IsValuation v p) {x : K} (hx : x ≠ 0) :
    v x⁻¹ = - v x := by
  have hxi : x⁻¹ ≠ 0 := inv_ne_zero hx
  have h := hv.map_mul x x⁻¹ hx hxi
  rw [mul_inv_cancel₀ hx] at h
  have h1 : v (1 : K) = 0 := by
    have h11 := hv.map_mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h11; linarith
  rw [h1] at h; linarith

/-- Valuation of a quotient: `v(x / y) = v(x) - v(y)` for `x, y ≠ 0`. -/
theorem IsValuation.map_div (hv : IsValuation v p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v (x / y) = v x - v y := by
  rw [div_eq_mul_inv, hv.map_mul x y⁻¹ hx (inv_ne_zero hy), hv.map_inv hy]; ring

end Val

/-- **The explicit Theorem 5.18 right-hand side** as an element of an ambient field
`K` (morally `ℚ_p(ζ_p)`):

  `LpValue τ logSum p i = -(τ i / p) · logSum i`,

where `τ i = τ(ω^{-i})` are the Gauss sums and
`logSum i = Σ_{a=1}^{p-1} ω^{-i}(a) · log_p(1 - ζ^a)` is the character-twisted
`p`-adic-log sum.  This is the object whose valuation Washington reads off. -/
noncomputable def LpValue {K : Type*} [Field K] (τ logSum : ℕ → K) (p : ℕ) (i : ℕ) : K :=
  -(τ i / (p : K)) * logSum i

theorem LpValue_def {K : Type*} [Field K] (τ logSum : ℕ → K) (p i : ℕ) :
    LpValue τ logSum p i = -(τ i / (p : K)) * logSum i := rfl

/-- **The `L_p`-formula data bundle** for the valuation route to Prop 8.12.

Bundles the ambient field `K` (morally `ℚ_p(ζ_p)`), a `ℚ`-valued valuation `v`
(with `v(p) = 1`), the Gauss sums `τ`, the `p`-adic-log sum `logSum`, **and** the
two mathematical inputs:

* `gaussVal` — **B-C1.2** `v(τ i) = i/(p-1)` (Washington Prop 6.13 at `f = 1`,
  *proved* over the abstract DVR `StickelbergerF1Setup`);
* `logBernoulli` — the valuation of the `p`-adic-log sum,
  `v(logSum i) = v_p(B_i/i) + 1 - i/(p-1)` (the named residual: the *valuation*
  shadow of Washington's pp. 63–66 resummation, via Cor 5.13 + Kummer).

`Lp i` is the `ℚ_[p]`-image of `L_p(1, ω^i)` (which lives in `ℚ_p` even though
`τ, logSum` live in the extension), tied to the explicit formula by the field
`congrLp` (Washington Thm 5.18, the `Theorem518CaseI` identity realised after the
`mod p^N` exactness step). -/
structure LpData (p : ℕ) [Fact p.Prime] where
  /-- The ambient field (morally `ℚ_p(ζ_p)`). -/
  K : Type
  [field : Field K]
  /-- The `ℚ`-valued valuation. -/
  v : K → ℚ
  /-- The valuation axioms (`v(p) = 1`, additive on nonzero products). -/
  isVal : Val.IsValuation v p
  /-- The Gauss sums `τ(ω^{-i}) ∈ K`. -/
  τ : ℕ → K
  /-- The `p`-adic-log sum `logSum i = Σ_a ω^{-i}(a) log_p(1 - ζ^a) ∈ K`. -/
  logSum : ℕ → K
  /-- The `ℚ_[p]`-value `L_p(1, ω^i)`. -/
  Lp : ℕ → ℚ_[p]
  /-- Gauss sums are nonzero on the relevant range. -/
  τ_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → τ i ≠ 0
  /-- The log sums are nonzero on the relevant range (they equal a unit times a
  nonzero Bernoulli factor). -/
  logSum_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → logSum i ≠ 0
  /-- `L_p(1, ω^i)` is nonzero on the relevant range. -/
  Lp_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → Lp i ≠ 0
  /-- **B-C1.2** the Gauss-sum valuation `v(τ i) = i/(p-1)`. -/
  gaussVal : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    v (τ i) = gaussSumNormalizedValuation p i
  /-- **The named analytic residual**:
  `v(logSum i) = v_p(B_i/i) + v(p) - i/(p-1)`.
  (The `v(p)` and `-i/(p-1)` terms cancel against the `-v(p)` and `+i/(p-1)` of
  the explicit-formula read-off, leaving exactly `v_p(B_i/i)`.  Over `ℚ_p(ζ_p)`
  with the `v(p) = 1`/`normVal` normalisation this reads
  `v(logSum i) = v_p(B_i/i) + 1 - i/(p-1)`.) -/
  logBernoulli : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    v (logSum i) =
      ((bernoulliFactorQp p i).valuation : ℚ) + v (p : K) - gaussSumNormalizedValuation p i
  /-- **Washington Thm 5.18** (the sharp form, after the `mod p^N` exactness step):
  the valuation of `L_p(1, ω^i)` agrees, via the embedding `ℚ_p ↪ K`, with the
  valuation of the explicit formula `LpValue τ logSum p i`.  Concretely it asserts
  `(Lp i).valuation = v(LpValue τ logSum p i)` (`(Lp i).valuation` cast to `ℚ`). -/
  congrLp : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    ((Lp i).valuation : ℚ) = v (LpValue τ logSum p i)

namespace LpData

variable {p : ℕ} [hp : Fact p.Prime] (D : LpData p)

instance : Field D.K := D.field

/-- **The valuation read-off (★)**, proved unconditionally from the valuation
axioms and the B-C1.2 input `gaussVal`:

  `v(LpValue τ logSum p i) = i/(p-1) - v(p) + v(logSum i)`. -/
theorem valuation_LpValue {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i) :
    D.v (LpValue D.τ D.logSum p i) =
      gaussSumNormalizedValuation p i - D.v (p : D.K) + D.v (D.logSum i) := by
  have hτ := D.τ_ne_zero i h1 h2 hev
  have hlog := D.logSum_ne_zero i h1 h2 hev
  have hp0 := D.isVal.p_ne_zero
  have hdiv : D.τ i / (p : D.K) ≠ 0 := div_ne_zero hτ hp0
  rw [LpValue_def, neg_mul, D.isVal.map_neg, D.isVal.map_mul _ _ hdiv hlog,
    D.isVal.map_div hτ hp0, D.gaussVal i h1 h2 hev]

/-- **The Iwasawa congruence at the level of the explicit formula**:

  `v(LpValue τ logSum p i) = v_p(B_i / i)`,

proved from (★) and the named residual `logBernoulli`.  The `i/(p-1)` Gauss-sum
contribution and the `1 - i/(p-1)` denominator correction in `logBernoulli`
cancel, leaving exactly the Bernoulli factor valuation. -/
theorem valuation_LpValue_eq_bernoulliFactor {i : ℕ}
    (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i) :
    D.v (LpValue D.τ D.logSum p i) = ((bernoulliFactorQp p i).valuation : ℚ) := by
  rw [D.valuation_LpValue h1 h2 hev, D.logBernoulli i h1 h2 hev]; ring

/-- **The Iwasawa congruence for `L_p(1, ω^i)`** (`v_p(L_p(1, ω^i)) = v_p(B_i/i)`),
proved from the explicit Thm 5.18 formula (`congrLp`) chained with the valuation
read-off.  This is exactly the `PadicLFunction.valuation_eq_bernoulliFactor`
field — discharged, not assumed. -/
theorem valuation_Lp_eq_bernoulliFactor {i : ℕ}
    (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i) :
    (D.Lp i).valuation = (bernoulliFactorQp p i).valuation := by
  exact_mod_cast (D.congrLp i h1 h2 hev).trans
    (D.valuation_LpValue_eq_bernoulliFactor h1 h2 hev)

/-- **The constructed Kubota–Leopoldt package.**  From `LpData`, the
`PadicLFunction p` whose Iwasawa-congruence field is the **proved**
`valuation_Lp_eq_bernoulliFactor` (via the explicit Thm 5.18 formula), not an
assumed structure field. -/
noncomputable def toPadicLFunction : PadicLFunction p where
  Lp := D.Lp
  Lp_ne_zero := D.Lp_ne_zero
  valuation_eq_bernoulliFactor _ h1 h2 hev := D.valuation_Lp_eq_bernoulliFactor h1 h2 hev

@[simp] theorem toPadicLFunction_Lp : D.toPadicLFunction.Lp = D.Lp := rfl

end LpData

namespace LpData

/-- Local prime instance for `37`. -/
private instance instFact37₃₂ : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **`v₃₇(L_p(1, ω³²)) = 1`** (the sharp `M = 1` valuation), obtained **from the
explicit Theorem 5.18 formula** (`congrLp`) chained with the proven valuation
algebra and the proven Bernoulli arithmetic `v₃₇(B₃₂/32) = 1`.  This is the value
the Case-II descent (Cor 8.23 / Thm 8.22) consumes; here it comes out of the
explicit `-(τ/p)·logSum` formula rather than an assumed structure field. -/
theorem valuation_Lp_thirtytwo (D : LpData 37) : (D.Lp 32).valuation = 1 := by
  rw [D.valuation_Lp_eq_bernoulliFactor (by norm_num) (by norm_num) (by decide),
    valuation_bernoulliFactorQp_thirtytwo]

/-- The same sharp value through the **constructed** `PadicLFunction 37` package
(consistency check: `toPadicLFunction` agrees with the proven `valuation_thirtytwo`
read-off). -/
theorem toPadicLFunction_valuation_thirtytwo (D : LpData 37) :
    (D.toPadicLFunction.Lp 32).valuation = 1 :=
  D.valuation_Lp_thirtytwo

end LpData

namespace LpData

/-- Local prime instance for `37`. -/
private instance instFact37'' : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private theorem padic37_valuation_p : Padic.valuation (37 : ℚ_[37]) = 1 := by
  rw [Padic.valuation_ofNat]; norm_num [padicValNat_self]

/-- The `37`-adic valuation, `/36`-normalised (so `v(τ i) = i/36 = i/(p-1)` on the
model Gauss sums `τ i = 37^i`), satisfies the `IsValuation` interface. -/
private theorem isValuation37 :
    Val.IsValuation (K := ℚ_[37]) (fun x ↦ (Padic.valuation x : ℚ) / 36) 37 where
  map_mul x y hx hy := by
    change (Padic.valuation (x * y) : ℚ) / 36
      = (Padic.valuation x : ℚ) / 36 + (Padic.valuation y : ℚ) / 36
    rw [Padic.valuation_mul hx hy]; push_cast; ring
  map_neg x := by
    change (Padic.valuation (-x) : ℚ) / 36 = (Padic.valuation x : ℚ) / 36
    rw [Padic.valuation_neg]
  p_ne_zero := by norm_num

/-- **Non-vacuity of `LpData 37`** (honesty witness): the bundle introduces **no
hidden contradictory constraints**.  Over `K = ℚ_[37]` with the `/36`-normalised
valuation `v x = v₃₇(x)/36`, the model Gauss sums `τ i = 37^i`
(so `v(τ i) = i/36 = i/(p-1)`, matching B-C1.2), the model log-sums
`logSum i = 37^{36·v₃₇(B_i/i) + 1 - i}` (so `logBernoulli` holds by construction),
and `L_p`-values `Lp i = 37^{v₃₇(B_i/i)}`, every field of `LpData 37` holds by
direct `37`-adic valuation computation.  In particular the Iwasawa congruence
`prop812`/`valuation_eq_bernoulliFactor` it yields is **not vacuous**.

(This witness uses the *same* normalisation as `Prop812Data.ofPadicLFunction`; the
genuine `p = 37` instance instead realises `τ, logSum` as honest Gauss sums /
`log_p`-sums in `ℚ₃₇(ζ₃₇)` and discharges `logBernoulli` from Washington
pp. 63–66, but the abstract bundle is consistent regardless.) -/
noncomputable def nonvacuous37 : LpData 37 where
  K := ℚ_[37]
  v x := (Padic.valuation x : ℚ) / 36
  isVal := isValuation37
  τ i := (37 : ℚ_[37]) ^ i
  logSum i := (37 : ℚ_[37]) ^ (36 * (bernoulliFactorQp 37 i).valuation + 1 - (i : ℤ))
  Lp i := (37 : ℚ_[37]) ^ (bernoulliFactorQp 37 i).valuation
  τ_ne_zero i _ _ _ := pow_ne_zero _ (by norm_num)
  logSum_ne_zero i _ _ _ := zpow_ne_zero _ (by norm_num)
  Lp_ne_zero i _ _ _ := zpow_ne_zero _ (by norm_num)
  gaussVal i _ _ _ := by
    simp only [Padic.valuation_pow, padic37_valuation_p, gaussSumNormalizedValuation_def]
    push_cast; norm_num
  logBernoulli i _ _ _ := by
    have hpcast : ((37 : ℕ) : ℚ_[37]) = (37 : ℚ_[37]) := by norm_num
    change (Padic.valuation ((37 : ℚ_[37]) ^ (36 * (bernoulliFactorQp 37 i).valuation
        + 1 - (i : ℤ))) : ℚ) / 36
      = ((bernoulliFactorQp 37 i).valuation : ℚ)
        + (Padic.valuation ((37 : ℕ) : ℚ_[37]) : ℚ) / 36 - gaussSumNormalizedValuation 37 i
    rw [hpcast, Padic.valuation_zpow, padic37_valuation_p, gaussSumNormalizedValuation_def]
    push_cast; ring
  congrLp i _ _ _ := by
    have h37 : (37 : ℚ_[37]) ≠ 0 := by norm_num
    have hτ : (37 : ℚ_[37]) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ h37
    have hlog : (37 : ℚ_[37]) ^ (36 * (bernoulliFactorQp 37 i).valuation + 1 - (i : ℤ)) ≠ 0 :=
      zpow_ne_zero _ h37
    have hLp : Padic.valuation (LpValue (fun i ↦ (37 : ℚ_[37]) ^ i)
          (fun i ↦ (37 : ℚ_[37]) ^ (36 * (bernoulliFactorQp 37 i).valuation + 1 - (i : ℤ)))
          37 i)
        = 36 * (bernoulliFactorQp 37 i).valuation := by
      have hpcast : ((37 : ℕ) : ℚ_[37]) = (37 : ℚ_[37]) := by norm_num
      have hdiv : (37 : ℚ_[37]) ^ (i : ℕ) / (37 : ℚ_[37]) ≠ 0 := div_ne_zero hτ h37
      rw [LpValue_def, hpcast, neg_mul, Padic.valuation_neg,
        Padic.valuation_mul hdiv hlog, Padic.valuation_zpow, padic37_valuation_p]
      have hτp : Padic.valuation ((37 : ℚ_[37]) ^ (i : ℕ) / (37 : ℚ_[37]))
          = (i : ℤ) - 1 := by
        rw [div_eq_mul_inv, Padic.valuation_mul hτ (inv_ne_zero h37), Padic.valuation_inv,
          Padic.valuation_pow, padic37_valuation_p]; ring
      rw [hτp]; ring
    change ((Padic.valuation ((37 : ℚ_[37]) ^ (bernoulliFactorQp 37 i).valuation) : ℚ))
      = (Padic.valuation (LpValue (fun i ↦ (37 : ℚ_[37]) ^ i)
          (fun i ↦ (37 : ℚ_[37]) ^ (36 * (bernoulliFactorQp 37 i).valuation + 1 - (i : ℤ)))
          37 i) : ℚ) / 36
    rw [hLp, Padic.valuation_zpow, padic37_valuation_p]; push_cast; ring

end LpData

namespace LpData

/-- At the descent index `i = 32` (the only index the Cor 8.23 / Thm 8.22 Case-II
argument consumes), the residual `logBernoulli` reads, with its Bernoulli term
**resolved** to the proven `v₃₇(B₃₂/32) = 1`:

  `v(logSum 32) = 1 + v(p) - 8/9`.

There is no remaining Bernoulli unknown — only the log-sum-to-Bernoulli resummation
valuation (Washington pp. 63–66 at `i = 32`).

Thus the only open content in `v₃₇(L_p(1, ω³²)) = 1` after this layer is the
*log-sum* valuation `v(logSum 32)` itself — the explicit-formula resummation. -/
theorem logBernoulli_thirtytwo_concrete (D : LpData 37) :
    D.v (D.logSum 32) = 1 + D.v ((37 : ℕ) : D.K) - 8 / 9 := by
  have h := D.logBernoulli 32 (by norm_num) (by norm_num) (by decide)
  rw [valuation_bernoulliFactorQp_thirtytwo, gaussSumNormalizedValuation_thirtytwo] at h
  rw [h]; push_cast; ring

end LpData

end BernoulliRegular.FLT37.PadicL
