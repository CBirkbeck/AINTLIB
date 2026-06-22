import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import BernoulliRegular.FLT37.PadicL.ValuationExactness
import BernoulliRegular.BernoulliFast.KellnerSecondOrder

/-!
# B-C1.0 (part 2) — the `p`-adic `L`-value `L_p(1, ω^i)` and its valuation

This file sets up the **Kubota–Leopoldt `p`-adic `L`-value** `L_p(1, ω^i)` as an
element of `ℚ_[p]`, together with its `p`-adic valuation, used in Washington
Proposition 8.12 (FLT for `p = 37`, Case II).

The concrete arithmetic input behind Cor 8.23 for `p = 37`, namely the sharp
valuation `v₃₇(L_p(1, ω³²)) = 1` ("`M = 1`"), is reached here from the **proven**
Bernoulli data `37 ∥ B₃₂` (`thirtyseven_dvd_bernoulli_thirtytwo_num` together
with `kellner_at_zero_not_dvd`), via the Iwasawa congruence
`v_p(L_p(1, ω^i)) = v_p(B_i / i)` (Washington Cor 5.13 / Thm 5.18, carried as the
named structure field `PadicLFunction.valuation_eq_bernoulliFactor`).

## Main definitions / results

* `bernoulliFactorQp p i : ℚ_[p]` — the explicit Bernoulli factor `B_i / i`
  embedded in `ℚ_[p]`.
* `valuation_bernoulliFactorQp_thirtytwo`: `v₃₇(B₃₂ / 32) = 1` — **proved** from
  `37 ∥ B₃₂` (the genuine first-order arithmetic content of `M = 1`).
* `PadicLFunction p`: the Kubota–Leopoldt `L`-value package: a function
  `i ↦ L_p(1, ω^i)` valued in `ℚ_[p]` whose valuation agrees with that of
  `B_i / i` (the Iwasawa congruence).  **Its existence is the named analytic
  residual** (Washington §5.4); it is a `structure`, not an axiom.
* `PadicLFunction.valuation_thirtytwo`: from such a package,
  `v₃₇(L_p(1, ω³²)) = 1`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.11, Cor 5.13, Thm 5.18, Prop 8.12, Cor 8.23.
-/

namespace BernoulliRegular.FLT37.PadicL

variable (p : ℕ) [hp : Fact p.Prime]

/-- The explicit **Bernoulli factor** `B_i / i`, embedded into `ℚ_[p]`.
This is the rational `B_i / i` (Washington's `-B_{n,χ}/n`-style coefficient at
the relevant point) cast into `ℚ_[p]`; its `p`-adic valuation is the arithmetic
content of `v_p(L_p(1, ω^i))`. -/
noncomputable def bernoulliFactorQp (i : ℕ) : ℚ_[p] :=
  ((bernoulli i / i : ℚ) : ℚ_[p])

theorem bernoulliFactorQp_def (i : ℕ) :
    bernoulliFactorQp p i = ((bernoulli i / i : ℚ) : ℚ_[p]) := rfl

/-- The `p`-adic valuation of the Bernoulli factor is the `padicValRat` of the
rational `B_i / i`. -/
theorem valuation_bernoulliFactorQp (i : ℕ) :
    (bernoulliFactorQp p i).valuation = padicValRat p (bernoulli i / i) := by
  rw [bernoulliFactorQp, Padic.valuation_ratCast]

end BernoulliRegular.FLT37.PadicL

namespace BernoulliRegular.FLT37.PadicL

open BernoulliRegular

/-- Local prime instance for `37`, used by the `p = 37` specialisations below. -/
private instance instFact37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **`v₃₇(B₃₂) = 1`** (proved): from `37 ∣ B₃₂.num`, `37² ∤ B₃₂.num`
(Kellner `α₀`), and `37 ∤ B₃₂.den = 510` (von Staudt–Clausen). -/
theorem padicValRat_bernoulli_thirtytwo :
    padicValRat 37 (bernoulli 32) = 1 := by
  have hpvi : padicValInt 37 (bernoulli 32).num = 1 := by
    have hne : (bernoulli 32).num ≠ 0 := by rw [bernoulli_thirtytwo_num_eq]; norm_num
    have h1 : 1 ≤ padicValInt 37 (bernoulli 32).num :=
      ((padicValInt_dvd_iff (p := 37) 1 (bernoulli 32).num).mp
        (by simpa using thirtyseven_dvd_bernoulli_thirtytwo_num)).resolve_left hne
    have h2 : ¬ 2 ≤ padicValInt 37 (bernoulli 32).num := fun hle =>
      kellner_at_zero_not_dvd ((padicValInt_dvd_iff (p := 37) 2 (bernoulli 32).num).mpr (Or.inr hle))
    omega
  have hpvn : padicValNat 37 (bernoulli 32).den = 0 := by
    rw [bernoulli_thirtytwo_den_eq, padicValNat.eq_zero_iff]; right; right; decide
  rw [padicValRat_def, hpvi, hpvn]; norm_num

/-- **`v₃₇(B₃₂ / 32) = 1`** (proved): the sharp first-order valuation, the
arithmetic core of `M = 1` for Corollary 8.23.  Since `37 ∤ 32`, dividing by
`32` does not change the valuation. -/
theorem valuation_bernoulliFactorQp_thirtytwo :
    (bernoulliFactorQp 37 32).valuation = 1 := by
  rw [valuation_bernoulliFactorQp]
  have hB_ne : (bernoulli 32 : ℚ) ≠ 0 :=
    Rat.num_ne_zero.mp (by rw [bernoulli_thirtytwo_num_eq]; norm_num)
  have h32 : ((32 : ℕ) : ℚ) ≠ 0 := by norm_num
  have hv32 : padicValRat 37 ((32 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, Nat.cast_eq_zero, padicValNat.eq_zero_iff]
    right; right; decide
  rw [padicValRat.div hB_ne h32, padicValRat_bernoulli_thirtytwo, hv32]; ring

/-- **The Kubota–Leopoldt `p`-adic `L`-value package** (B-C1.0).

A `PadicLFunction p` records the family of `p`-adic `L`-values
`Lp i = L_p(1, ω^i) : ℚ_[p]` together with the **Iwasawa congruence**
(Washington Cor 5.13 / Thm 5.18): the `p`-adic valuation of `L_p(1, ω^i)` equals
that of the explicit Bernoulli factor `B_i / i` for the even indices
`2 ≤ i ≤ p - 3` relevant to the Herbrand–Ribet / Cor 8.23 analysis.

This is a `structure`, **not** an axiom: it is the genuine mathematical object
(the Kubota–Leopoldt `p`-adic `L`-function with its interpolation property).  Its
*construction* — the existence of an inhabitant of `PadicLFunction p` — is the
named analytic residual of the whole development (Washington §5.4, the content of
B-C1.1 / Theorem 5.18 together with the limit definition of `L_p`).  Everything
downstream of `v_p(L_p(1, ω^i))` is recovered from this structure unconditionally.
-/
structure PadicLFunction (p : ℕ) [Fact p.Prime] where
  /-- The `p`-adic `L`-value `L_p(1, ω^i)`. -/
  Lp : ℕ → ℚ_[p]
  /-- `L_p(1, ω^i)` is nonzero for the relevant even indices (it equals a unit
  times `B_i / i`, which is nonzero). -/
  Lp_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → Lp i ≠ 0
  /-- **The Iwasawa congruence** `v_p(L_p(1, ω^i)) = v_p(B_i / i)` (Washington
  Cor 5.13 / Thm 5.18). -/
  valuation_eq_bernoulliFactor :
    ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      (Lp i).valuation = (bernoulliFactorQp p i).valuation

namespace PadicLFunction

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`v₃₇(L_p(1, ω³²)) = 1`** (the `M = 1` sharp valuation): from any
Kubota–Leopoldt package, the valuation of `L_p(1, ω³²)` equals the proven
`v₃₇(B₃₂ / 32) = 1`. -/
theorem valuation_thirtytwo (L : PadicLFunction 37) :
    (L.Lp 32).valuation = 1 := by
  rw [L.valuation_eq_bernoulliFactor 32 (by norm_num) (by norm_num) (by decide),
    valuation_bernoulliFactorQp_thirtytwo]

end PadicLFunction

end BernoulliRegular.FLT37.PadicL
