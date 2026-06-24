import BernoulliRegular.BernoulliFast.Tactic
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main
import Mathlib.Data.ZMod.Basic

/-!
# T-KELLNER-SECOND-ORDER: Kellner higher-order irregular-pair test

Per the 2026-05-07 reviewer followup, Kellner's Proposition 2.7 (Kellner
2007, Math. Comp. 76, arXiv:math/0409223) provides a finite test for
second-order irregularity at an irregular prime pair `(p, ℓ)`, avoiding
direct computation of large Bernoulli numbers.

The test:

1. Compute the Kellner invariants
   `α_j ≡ p^{-1} · B_{ℓ + j(p-1)} / (ℓ + j(p-1))  (mod p)`
   for `j = 0, 1`.
2. Form `Δ := α_1 - α_0  (mod p)`.
3. If `Δ ≢ 0 (mod p)`, then exactly one second-order irregular index
   `s ∈ {0, …, p-2}` exists, namely
   `s ≡ -α_0 · Δ^{-1}  (mod p)`.

For the FLT37 irregular pair `(37, 32)`:

* `α_0 = 37^{-1} · B_{32}/32 ≡ 1  (mod 37)` — uses small `B_{32}`.
* `α_1 = 37^{-1} · B_{68}/68 ≡ 22 (mod 37)` — uses small `B_{68}`.
* `Δ = 21`, `s_unique ≡ -1 · 21^{-1} ≡ 7  (mod 37)`.

Since `32 ≠ 7`, the index `s = 32` is **not** the second-order index;
hence `(37, 32, 32) ∉ Ψ_2^{irr}`, so `37² ∤ B_{1184}/1184`, hence
`37³ ∤ B_{1184}.num` (since `1184 = 32 · 37` contributes one factor of
`37`, and `36 ∤ 1184` so `37 ∤ B_{1184}.den`).

This file ships:

* The numerical Bernoulli divisibility data for `B_{32}` and `B_{68}`
  (verified via `bernoulli_decide`).
* The α-invariant verifications `α_0 = 1` and `α_1 = 22` mod `37`
  (encoded as `37² ∣ B_n - constant` integer-divisibility checks).
* The parametric Kellner Proposition 2.7 hypothesis specialised to the
  FLT37 irregular pair.
* The discharge of `NoSecondOrderIrregularPair 37 32` from the
  parametric Kellner hypothesis.

The substantive proof of Kellner's Proposition 2.7 (using higher-order
Kummer congruences in the Iwasawa-theoretic framework) is left as a
named-theorem boundary, consistent with the project's parametric
treatment of major mathematical results.

## References

* Kellner, *On irregular prime power divisors of the Bernoulli numbers*,
  Math. Comp. 76 (2007) 405–441; arXiv:math/0409223, Proposition 2.7.
* Reviewer followup, 2026-05-07.
-/

@[expose] public section

namespace BernoulliRegular

/-! ## Numerical Bernoulli divisibility data -/

/-- **B_{32} is irregular at 37**: the first-order irregular pair condition
`37 ∣ B_{32}.num`. Verified via `bernoulli_decide`. -/
theorem thirtyseven_dvd_bernoulli_thirtytwo_num :
    (37 : ℤ) ∣ (bernoulli 32).num := by bernoulli_decide

/-- **B_{32} numerator value**: `B_{32}.num = -7709321041217`. The
explicit value is needed for the α_0 verification. -/
theorem bernoulli_thirtytwo_num_eq : (bernoulli 32).num = -7709321041217 := by
  bernoulli_decide

/-- **B_{32} denominator value**: `B_{32}.den = 510 = 2 · 3 · 5 · 17`
(by von Staudt-Clausen). Required for the α_0 invariant computation. -/
theorem bernoulli_thirtytwo_den_eq : (bernoulli 32).den = 510 := by
  bernoulli_decide

/-- **B_{68} is irregular at 37**: by Kummer's congruence
`B_{68}/68 ≡ B_{32}/32  (mod 37)`, since `68 = 32 + (37 - 1)` and
`(37, 32)` is irregular. Required for the α_1 invariant. -/
theorem thirtyseven_dvd_bernoulli_sixtyeight_num :
    (37 : ℤ) ∣ (bernoulli 68).num := by bernoulli_decide

/-- **B_{68} denominator value**: `B_{68}.den = 30 = 2 · 3 · 5`
(by von Staudt-Clausen — primes `p` with `(p-1) ∣ 68`: 2, 3, 5). -/
theorem bernoulli_sixtyeight_den_eq : (bernoulli 68).den = 30 := by
  bernoulli_decide

/-! ## α-invariant verifications

The Kellner invariant `α_j ≡ p^{-1} · B_{ℓ + j(p-1)} / (ℓ + j(p-1)) (mod p)`
encoded as an integer-divisibility condition on `B_n.num`. After
multiplying through by `B_n.den · n` (a `p`-unit) and reducing mod `p`:

   `α_j ≡ a (mod p)`
   ⟺ `B_n.num / p ≡ a · B_n.den · n  (mod p)`
   ⟺ `p² ∣ B_n.num - p · ((a · B_n.den · n) mod p)`.

For `(p, ℓ) = (37, 32)`:

* `α_0 = 1` ⟺ `B_{32}.num / 37 ≡ 1 · 510 · 32 = 16320 ≡ 3 (mod 37)`
            ⟺ `37² ∣ B_{32}.num - 3·37 = B_{32}.num - 111`.

* `α_1 = 22` ⟺ `B_{68}.num / 37 ≡ 22 · 30 · 68 = 44880 ≡ -1 (mod 37)`
             ⟺ `37² ∣ B_{68}.num - (-1)·37 = B_{68}.num + 37`.
-/

/-- **α_0 = 1 (mod 37)** for the Kellner invariant of `(37, 32)`. Encoded
as `37² ∣ B_{32}.num - 111`. The constant `111 = 3·37` arises from
`1 · 510 · 32 ≡ 3 (mod 37)`. -/
theorem kellner_alpha_zero_thirtyseven_thirtytwo :
    (37 : ℤ) ^ 2 ∣ (bernoulli 32).num - 111 := by bernoulli_decide

/-- **α_1 = 22 (mod 37)** for the Kellner invariant of `(37, 32)`. Encoded
as `37² ∣ B_{68}.num + 37`. The `+ 37` arises from
`22 · 30 · 68 ≡ -1 (mod 37)`. -/
theorem kellner_alpha_one_thirtyseven_thirtytwo :
    (37 : ℤ) ^ 2 ∣ (bernoulli 68).num + 37 := by bernoulli_decide

/-! ## Δ verification and unique second-order index

From `α_0 = 1` and `α_1 = 22`:
* `Δ := α_1 - α_0 = 21 (mod 37)`, nonzero.
* `s_unique := -α_0 · Δ⁻¹ ≡ -1 · 21⁻¹  (mod 37)`.
* `21⁻¹ ≡ 30 (mod 37)` since `21 · 30 = 630 = 17·37 + 1`.
* `s_unique ≡ -30 ≡ 7  (mod 37)`.
-/

/-- Closed (`Fact`-free) arithmetic fact for `kellner_unique_second_order_index`:
`α_1 - α_0 = 22 - 1` is nonzero in `ZMod 37`. -/
private theorem kellner_unique_aux_ne : (22 : ZMod 37) - 1 ≠ 0 := by decide

/-- Closed (`Fact`-free) arithmetic fact for `kellner_unique_second_order_index`:
`-α_0 = 7 · (α_1 - α_0)` in `ZMod 37` (i.e. `-1 = 7 · 21`). -/
private theorem kellner_unique_aux_eq :
    -((1 : ZMod 37)) = 7 * ((22 : ZMod 37) - 1) := by decide

/-- **The unique second-order index for `(37, 32)` is 7**, computed via
Kellner's formula `s_unique = -α_0 · (α_1 - α_0)⁻¹ (mod p)`. -/
theorem kellner_unique_second_order_index :
    -((1 : ZMod 37)) * ((22 : ZMod 37) - 1)⁻¹ = 7 := by
  -- `decide` cannot evaluate the `ZMod 37` inverse (well-founded `gcdA`), and a
  -- local `Fact` instance breaks `decide`, so the closed arithmetic facts are
  -- discharged in `kellner_unique_aux_ne`/`kellner_unique_aux_eq` (no `Fact` in
  -- scope) and the field structure is used only to cancel `(22 - 1)`.
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  refine mul_right_cancel₀ kellner_unique_aux_ne ?_
  rw [mul_assoc, ZMod.inv_mul_of_unit _ kellner_unique_aux_ne.isUnit, mul_one]
  exact kellner_unique_aux_eq

/-- **The candidate `s = 32` is not the unique second-order index**:
`(32 : ZMod 37) ≠ 7`. -/
theorem kellner_thirtytwo_ne_unique : ((32 : ℕ) : ZMod 37) ≠ 7 := by decide

/-! ## Parametric Kellner Proposition 2.7 (FLT37 specialisation) -/

/-- **Parametric Kellner Proposition 2.7 for the FLT37 irregular pair**.

The substantive content of Kellner's Prop 2.7 specialised to
`(p, ℓ) = (37, 32)` with the verified invariants `α_0 = 1` and
`α_1 = 22 (mod 37)`:

> Among `s ∈ {0, …, 35}`, the unique index satisfying the second-order
> condition `37² ∣ \widehat B_{32 + 36 s}` is `s_unique = 7`. For any
> other `s`, `37² ∤ \widehat B_{32 + 36 s}`. Translated to integer
> divisibility: for `s ≠ 7` and `n := 32 + 36 s`,
>     `37 ∣ n  ⟹  ¬ 37³ ∣ B_n.num`,
>     `37 ∤ n  ⟹  ¬ 37² ∣ B_n.num`.

For the FLT37 candidate `s = 32`: `n = 32 + 36·32 = 1184 = 32·37`, so
`37 ∣ n` and the conclusion is `37³ ∤ B_{1184}.num`.

The proof would require formalising Kellner's Proposition 2.7 itself,
which uses higher-order Kummer congruences in the Iwasawa-theoretic
framework; this is left as a named-theorem boundary. -/
def KellnerProp27_thirtyseven_thirtytwo : Prop :=
  ∀ s : ℕ, s < 36 → s ≠ 7 →
    (if (37 : ℤ) ∣ (32 + s * 36 : ℤ)
      then ¬ (37 : ℤ) ^ 3 ∣ (bernoulli (32 + s * 36)).num
      else ¬ (37 : ℤ) ^ 2 ∣ (bernoulli (32 + s * 36)).num)

/-- **Discharge `NoSecondOrderIrregularPair 37 32`** from the parametric
Kellner hypothesis. Specialise the universal statement to `s = 32`,
where `32 + 32·36 = 1184 = 32·37`, and `37 ∣ 1184`. -/
theorem noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner
    (h : KellnerProp27_thirtyseven_thirtytwo) :
    NoSecondOrderIrregularPair 37 32 := by
  unfold NoSecondOrderIrregularPair
  -- 32 * 37 = 1184 = 32 + 32 * 36
  have h1184 : (32 : ℕ) * 37 = 32 + 32 * 36 := by decide
  rw [h1184]
  have hs := h 32 (by decide) (by decide)
  -- The `if` branch evaluates to "37 ∣ 32 + (32 : ℤ) * 36" which is true,
  -- so `hs` reduces directly to the desired conclusion.
  exact hs

/-! ## Direct discharge of small-`s` Kellner cases

For `s = 0` and `s = 1`, the Kellner Prop 2.7 conclusion is a divisibility
statement about `B_{32}` and `B_{68}` — small enough that the
α-invariant verifications already shipped above (specifically
`kellner_alpha_zero_thirtyseven_thirtytwo` and
`kellner_alpha_one_thirtyseven_thirtytwo`) directly imply
`37² ∤ B_{32}.num` and `37² ∤ B_{68}.num` respectively. -/

/-- **Kellner case `s = 0` (n = 32)**: `37² ∤ B_{32}.num`. Direct from
`α_0 = 1` (`37² ∣ B_{32}.num - 111`): if `37² ∣ B_{32}.num` also, then
`37² ∣ 111 = 3·37`, contradicting that `111` has only one factor of `37`. -/
theorem kellner_at_zero_not_dvd : ¬ (37 : ℤ) ^ 2 ∣ (bernoulli 32).num := by
  intro h_dvd
  have h_alpha : (37 : ℤ) ^ 2 ∣ (bernoulli 32).num - 111 :=
    kellner_alpha_zero_thirtyseven_thirtytwo
  have h_111 : (37 : ℤ) ^ 2 ∣ (111 : ℤ) := by
    have h_eq : (bernoulli 32).num - ((bernoulli 32).num - 111) = (111 : ℤ) := by ring
    have := h_dvd.sub h_alpha
    rwa [h_eq] at this
  -- 37^2 = 1369 > 111, contradiction.
  have h_le : (37 : ℤ) ^ 2 ≤ |(111 : ℤ)| := Int.le_of_dvd (by decide) h_111
  norm_num at h_le

/-- **Kellner case `s = 1` (n = 68)**: `37² ∤ B_{68}.num`. Direct from
`α_1 = 22` (`37² ∣ B_{68}.num + 37`): if `37² ∣ B_{68}.num` also, then
`37² ∣ 37`, contradiction. -/
theorem kellner_at_one_not_dvd : ¬ (37 : ℤ) ^ 2 ∣ (bernoulli 68).num := by
  intro h_dvd
  have h_alpha : (37 : ℤ) ^ 2 ∣ (bernoulli 68).num + 37 :=
    kellner_alpha_one_thirtyseven_thirtytwo
  have h_37 : (37 : ℤ) ^ 2 ∣ (37 : ℤ) := by
    have h_eq : (bernoulli 68).num + 37 - (bernoulli 68).num = (37 : ℤ) := by ring
    have := h_alpha.sub h_dvd
    rwa [h_eq] at this
  have h_le : (37 : ℤ) ^ 2 ≤ |(37 : ℤ)| := Int.le_of_dvd (by decide) h_37
  norm_num at h_le

/-- **Combined dispatch**: discharge `KellnerProp27_thirtyseven_thirtytwo` at
`s ∈ {0, 1}` (the only sub-cases reachable by direct B_n analysis at small n). -/
theorem kellner_at_small_s
    (s : ℕ) (hs : s = 0 ∨ s = 1) :
    (if (37 : ℤ) ∣ (32 + s * 36 : ℤ)
      then ¬ (37 : ℤ) ^ 3 ∣ (bernoulli (32 + s * 36)).num
      else ¬ (37 : ℤ) ^ 2 ∣ (bernoulli (32 + s * 36)).num) := by
  rcases hs with rfl | rfl
  · -- s = 0, n = 32, 37 ∤ 32, conclusion: ¬ 37² ∣ B_32.num
    change (if (37 : ℤ) ∣ ((32 : ℕ) + (0 : ℕ) * 36 : ℤ)
      then ¬ (37 : ℤ) ^ 3 ∣ (bernoulli ((32 : ℕ) + (0 : ℕ) * 36)).num
      else ¬ (37 : ℤ) ^ 2 ∣ (bernoulli ((32 : ℕ) + (0 : ℕ) * 36)).num)
    rw [show ((32 : ℕ) + (0 : ℕ) * 36 : ℕ) = 32 by decide]
    rw [if_neg (by decide : ¬ ((37 : ℤ) ∣ ((32 : ℕ) + (0 : ℕ) * 36 : ℤ)))]
    exact kellner_at_zero_not_dvd
  · -- s = 1, n = 68, 37 ∤ 68, conclusion: ¬ 37² ∣ B_68.num
    change (if (37 : ℤ) ∣ ((32 : ℕ) + (1 : ℕ) * 36 : ℤ)
      then ¬ (37 : ℤ) ^ 3 ∣ (bernoulli ((32 : ℕ) + (1 : ℕ) * 36)).num
      else ¬ (37 : ℤ) ^ 2 ∣ (bernoulli ((32 : ℕ) + (1 : ℕ) * 36)).num)
    rw [show ((32 : ℕ) + (1 : ℕ) * 36 : ℕ) = 68 by decide]
    rw [if_neg (by decide : ¬ ((37 : ℤ) ∣ ((32 : ℕ) + (1 : ℕ) * 36 : ℤ)))]
    exact kellner_at_one_not_dvd

/-! ## The FLT37 second-order target -/

/-- **`¬ 37³ ∣ B_{1184}.num` from Kellner Prop 2.7** (Reviewer guidance
2026-05-22). The bare statement of the FLT37 target case is the
specialisation of `KellnerProp27_thirtyseven_thirtytwo` at `s = 32`:
since the unique second-order index is `s = 7 ≠ 32`, and `37 ∣ 1184`,
the Kellner Prop 2.7 conclusion at `s = 32` is `¬ 37³ ∣ B_{1184}.num`.

Avoids the direct `bernoulli_decide` route (which times out on B_{1184}). -/
theorem kellner_at_thirtytwo_not_dvd_pCubed_of_kellner
    (h_kellner : KellnerProp27_thirtyseven_thirtytwo) :
    ¬ (37 : ℤ) ^ 3 ∣ (bernoulli (32 + 32 * 36)).num := by
  have h_unique : (32 : ℕ) ≠ 7 := by decide
  have hs := h_kellner 32 (by decide : (32 : ℕ) < 36) h_unique
  -- The if-branch evaluates: 37 ∣ 32 + 32*36 = 1184, so the conclusion is
  -- ¬ 37³ ∣ B_{1184}.num.
  have h_div : (37 : ℤ) ∣ (32 + (32 : ℕ) * 36 : ℤ) := by decide
  rw [if_pos h_div] at hs
  exact hs

/-- **`NoSecondOrderIrregularPair 37 32` from the parametric Kellner Prop 2.7
hypothesis**, alias of `noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner`.
This replaces the previous bare `sorry`-based forms `kellner_at_thirtytwo_not_dvd_pCubed`
and `noSecondOrderIrregularPair_thirtyseven_thirtytwo`: the substantive `B_1184`
divisibility is genuinely Kellner Prop 2.7 / Iwasawa-theoretic content (direct
computation times out), so it is carried as the explicit named `Prop`
`KellnerProp27_thirtyseven_thirtytwo` rather than a hidden `sorry`. -/
theorem noSecondOrderIrregularPair_thirtyseven_thirtytwo_via_kellner
    (h_kellner : KellnerProp27_thirtyseven_thirtytwo) :
    NoSecondOrderIrregularPair 37 32 :=
  noSecondOrderIrregularPair_thirtyseven_thirtytwo_of_kellner h_kellner

end BernoulliRegular
