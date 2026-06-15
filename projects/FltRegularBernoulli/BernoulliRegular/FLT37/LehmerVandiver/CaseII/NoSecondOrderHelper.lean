import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main

/-!
# Decidability helper for `NoSecondOrderIrregularPair`

The predicate `NoSecondOrderIrregularPair p i := ¬ p^3 ∣ B_{ip}.num`
is decidable in principle (a finite computation on `bernoulli (i*p)`).
This file provides a `Decidable` instance plus a converter from the
underlying numerical fact.

For `p = 37`, `i = 32`, we'd need `37³ ∤ B_{1184}.num` — a substantial
computation (B_{1184} has thousands of digits in numerator and
denominator). Shipping the `Decidable` instance allows future tactics
(e.g., `bernoulli_decide` once optimised) or external numerical
verification to discharge the predicate.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-- **`NoSecondOrderIrregularPair` is decidable.** Direct from the
underlying integer divisibility being decidable. -/
instance NoSecondOrderIrregularPair.decidable (p i : ℕ) :
    Decidable (NoSecondOrderIrregularPair p i) := by
  unfold NoSecondOrderIrregularPair
  infer_instance

/-- **`NoSecondOrderIrregularPair` from explicit non-divisibility.**
Constructor wrapper: given `¬ p³ ∣ B_{ip}.num`, get the predicate. -/
theorem NoSecondOrderIrregularPair.of_not_dvd_bernoulli_num
    {p i : ℕ} (h : ¬ (p : ℤ) ^ 3 ∣ (bernoulli (i * p)).num) :
    NoSecondOrderIrregularPair p i := h

/-- **`NoSecondOrderIrregularPair` extraction.** Forward direction:
get the underlying non-divisibility fact. -/
theorem NoSecondOrderIrregularPair.not_dvd_bernoulli_num
    {p i : ℕ} (h : NoSecondOrderIrregularPair p i) :
    ¬ (p : ℤ) ^ 3 ∣ (bernoulli (i * p)).num := h

end BernoulliRegular

end
