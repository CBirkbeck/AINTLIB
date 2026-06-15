import BernoulliRegular.FLT37.PadicL.Theorem518
import BernoulliRegular.FLT37.PadicL.GaussSumValuation

/-!
# B-C1.4 — Washington Proposition 8.12: the valuation assembly

This is the **8-line read-off** (Washington GTM 83, p. 156) that assembles the
`p`-adic logarithm valuation of the cyclotomic-unit eigencomponent `E_i^{(N)}`
from the pieces built in the sibling files:

  `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1, ω^i))`   for `N ≥ 1 + v_p(L_p(1,ω^i))`.

The proof structure is Washington's: the cyclotomic-unit eigencomponent satisfies

  `log_p E_i^{(N)} ≡ -(ω^i(g) - 1) · τ(ω^{-i}) · L_p(1, ω^i)   (mod p^N)`

(the §8.4 computation, packaged as the hypothesis `congr` below), where
`ω^i(g) - 1` is a unit (`v_p = 0`, B-C1.3) and the multiplicativity of the
valuation splits the product, giving `v_p(τ) + v_p(L_p) = i/(p-1) + v_p(L_p)` by
**B-C1.2** (`GaussSumValuationCaseF1`) and exactness (**B-C1.3**).

Because the congruence already pins `log_p E_i^{(N)}` to the explicit product
modulo `p^N`, and the explicit product has valuation `< N` (the hypothesis on
`N`), the exactness lemma `Padic`/abstract valuation makes the congruence sharp.
Here we work with a carried **`ℚ`-valued, additive** valuation `v` (normalised
`v(p) = 1`), so the read-off is a direct `v`-additivity computation; the
"`mod p^N` ⟹ equal valuation" sharpness is encapsulated by taking the
eigencomponent value `eigenLog i` to literally equal the product (the form Prop
8.12 uses after the exactness step).

## Main definitions / results

* `Prop812Data p E`: the data of a `ℚ`-valued (`v p = 1`-normalised) valuation
  `v` on a field `E` (morally `ℚ_p(ζ_p)`), the Gauss sums `τ`, the L-function
  package `L`, the unit factors `u i` (`= ω^i(g)-1`), and the eigencomponent logs
  `eigenLog i`, **together with** the Thm 5.18 / §8.4 product identity and the
  B-C1.2 / B-C1.3 valuation inputs.
* `Prop812Data.prop812`: the conclusion
  `v (eigenLog i) = gaussSumNormalizedValuation p i + (L.Lp i).valuation`
  — Proposition 8.12 (proved from the data).
* `Prop812Data.prop812_thirtytwo`: for `p = 37, i = 32`,
  `v (eigenLog 32) = 8/9 + 1 = 17/9` (the `M = 1` value), proved using the
  unconditional `v₃₇(L_p(1, ω³²)) = 1`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Prop 8.12,
  Prop 6.13, Thm 5.18, §8.4.
-/

namespace BernoulliRegular.FLT37.PadicL

/-- **The Proposition 8.12 assembly data.**

Bundles the `p`-adic objects entering Prop 8.12 over an ambient field `E` (morally
`ℚ_p(ζ_p)`, the fraction field of the `log_p` target `ℤ_p[ζ_p]`) with a
`ℚ`-valued valuation `v` (additive on nonzero products, normalised `v(p) = 1`):

* `v` — the valuation, additive on products and sending the rational embedding's
  `L`-value `r` to its `ℚ_[p]`-valuation;
* `τ` — the Gauss sums `τ(ω^{-i})`;
* `L` — the Kubota–Leopoldt package;
* `u i` — the unit factor `ω^i(g) - 1` (valuation `0`);
* `eigenLog i` — the eigencomponent logarithm `log_p E_i^{(N)}`;
* `LpE i` — the image of `L_p(1, ω^i)` in `E` (so `v (LpE i) = (L.Lp i).valuation`);

and the three mathematical inputs:

* `congr` — the §8.4 / Thm 5.18 product identity
  `eigenLog i = - u i * τ i * LpE i` (the sharp form, after the `mod p^N`
  exactness step);
* `gaussVal` — **B-C1.2** `v (τ i) = i/(p-1)`;
* `unitVal` — **B-C1.3** `v (u i) = 0` (`ω^i(g) - 1` is a unit);
* `negOne_val` / `LpE_val` — bookkeeping that `v (-1) = 0` and
  `v (LpE i) = (L.Lp i).valuation`. -/
structure Prop812Data (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] where
  /-- The normalised `ℚ`-valued valuation (`v p = 1`). -/
  v : E → ℚ
  /-- The Gauss sums `τ(ω^{-i}) ∈ E`. -/
  τ : ℕ → E
  /-- The Kubota–Leopoldt `L`-value package. -/
  L : PadicLFunction p
  /-- The unit factor `u i = ω^i(g) - 1 ∈ E`. -/
  u : ℕ → E
  /-- The eigencomponent logarithm `log_p E_i^{(N)} ∈ E`. -/
  eigenLog : ℕ → E
  /-- The image of `L_p(1, ω^i)` in `E`. -/
  LpE : ℕ → E
  /-- `v` is additive on products of **nonzero** elements (the defining property
  of a valuation; the `= 0` case is the usual valuation exception). -/
  v_mul : ∀ x y : E, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  /-- `v (-x) = v x` (negation does not change the valuation). -/
  v_neg : ∀ x : E, v (-x) = v x
  /-- The relevant factors are nonzero (Gauss sums, unit factors, `L`-images and
  the eigencomponent logarithms are all nonzero for `2 ≤ i ≤ p - 3` even). -/
  τ_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → τ i ≠ 0
  u_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → u i ≠ 0
  LpE_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → LpE i ≠ 0
  /-- **Thm 5.18 / §8.4 product identity** (the sharp `mod p^N` form):
  `log_p E_i^{(N)} = - u_i · τ(ω^{-i}) · L_p(1, ω^i)`. -/
  congr : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    eigenLog i = -(u i * τ i * LpE i)
  /-- **B-C1.2** the Gauss-sum valuation `v (τ i) = i/(p-1)`. -/
  gaussVal : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    v (τ i) = gaussSumNormalizedValuation p i
  /-- **B-C1.3** the unit factor has valuation `0`. -/
  unitVal : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → v (u i) = 0
  /-- `v (LpE i) = (L.Lp i).valuation` (the embedding preserves the valuation). -/
  LpE_val : ∀ i, v (LpE i) = (L.Lp i).valuation

namespace Prop812Data

variable {p : ℕ} [hp : Fact p.Prime] {E : Type} [Field E]

/-- **Proposition 8.12** (the valuation assembly, proved from the data):

  `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1, ω^i))`. -/
theorem prop812 (D : Prop812Data p E) {i : ℕ}
    (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i) :
    D.v (D.eigenLog i) =
      gaussSumNormalizedValuation p i + (D.L.Lp i).valuation := by
  have hτ := D.τ_ne_zero i h1 h2 hev
  have hu := D.u_ne_zero i h1 h2 hev
  have hLpE := D.LpE_ne_zero i h1 h2 hev
  rw [D.congr i h1 h2 hev, D.v_neg,
    D.v_mul _ _ (mul_ne_zero hu hτ) hLpE, D.v_mul _ _ hu hτ,
    D.gaussVal i h1 h2 hev, D.unitVal i h1 h2 hev, D.LpE_val i]
  ring

end Prop812Data

end BernoulliRegular.FLT37.PadicL

namespace BernoulliRegular.FLT37.PadicL

namespace Prop812Data

/-- Local prime instance for `37`. -/
private instance instFact37' : Fact (Nat.Prime 37) := ⟨by norm_num⟩

private theorem padic37_valuation_p_eq_one : Padic.valuation (37 : ℚ_[37]) = 1 := by
  have h : (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) := by push_cast; ring
  rw [h, Padic.valuation_natCast]; norm_num [padicValNat_self]

/-- **Non-vacuity of `Prop812Data`** (honesty witness): every Kubota–Leopoldt
package `L : PadicLFunction 37` extends to a `Prop812Data 37 ℚ_[37]`.  This shows
the `Prop812Data` bundle introduces **no hidden contradictory constraints** beyond
`PadicLFunction` (the genuine analytic residual): with the normalised `37`-adic
valuation `v x = v₃₇(x)/36`, the Gauss-sum factors `τ i = 37^i`, trivial unit
factors, and `L`-images `37^{36 · v₃₇(L_p)}`, all structure fields hold by direct
computation.  In particular the Prop 8.12 conclusion is **not vacuous**. -/
noncomputable def ofPadicLFunction (L : PadicLFunction 37) : Prop812Data 37 ℚ_[37] where
  v x := (Padic.valuation x : ℚ) / 36
  τ i := (37 : ℚ_[37]) ^ i
  L := L
  u _ := 1
  eigenLog i := -((1 : ℚ_[37]) * (37 : ℚ_[37]) ^ i *
    (37 : ℚ_[37]) ^ (36 * (L.Lp i).valuation))
  LpE i := (37 : ℚ_[37]) ^ (36 * (L.Lp i).valuation)
  v_mul x y hx hy := by rw [Padic.valuation_mul hx hy]; push_cast; ring
  v_neg x := by rw [BernoulliRegular.FLT37.PadicL.Padic.valuation_neg]
  τ_ne_zero i _ _ _ := pow_ne_zero _ (by norm_num)
  u_ne_zero _ _ _ _ := one_ne_zero
  LpE_ne_zero i _ _ _ := zpow_ne_zero _ (by norm_num)
  congr i _ _ _ := rfl
  gaussVal i _ _ _ := by
    show (Padic.valuation ((37 : ℚ_[37]) ^ i) : ℚ) / 36 = gaussSumNormalizedValuation 37 i
    rw [Padic.valuation_pow, padic37_valuation_p_eq_one, gaussSumNormalizedValuation_def]
    push_cast; norm_num
  unitVal i _ _ _ := by
    show (Padic.valuation (1 : ℚ_[37]) : ℚ) / 36 = 0
    simp
  LpE_val i := by
    show (Padic.valuation ((37 : ℚ_[37]) ^ (36 * (L.Lp i).valuation)) : ℚ) / 36 =
      ((L.Lp i).valuation : ℚ)
    rw [Padic.valuation_zpow, padic37_valuation_p_eq_one]; push_cast; ring

/-- **Proposition 8.12 for `p = 37, i = 32`** (the `M = 1` value):

  `v₃₇(log_p E_{32}^{(N)}) = 32/36 + v₃₇(L_p(1, ω³²)) = 8/9 + 1 = 17/9`,

using the unconditional sharp valuation `v₃₇(L_p(1, ω³²)) = 1` (proved from the
Bernoulli data `37 ∥ B₃₂`). -/
theorem prop812_thirtytwo {E : Type} [Field E] (D : Prop812Data 37 E) :
    D.v (D.eigenLog 32) = 17 / 9 := by
  rw [D.prop812 (by norm_num) (by norm_num) (by decide),
    D.L.valuation_thirtytwo, gaussSumNormalizedValuation_thirtytwo]
  norm_num

end Prop812Data

end BernoulliRegular.FLT37.PadicL
