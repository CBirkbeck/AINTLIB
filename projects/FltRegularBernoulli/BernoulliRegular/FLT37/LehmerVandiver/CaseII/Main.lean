import BernoulliRegular.HilbertClassField
import BernoulliRegular.TotallyRealSubfield.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Bernoulli

/-!
# LV009 + LV010: Case II bridges

Washington Theorem 9.4 (case II under `p ∤ h⁺` + a second-order Bernoulli
condition): for `p` an odd prime with `p ∤ h⁺(ℚ(ζ_p))` AND a
second-order non-irregularity condition (Kellner: `(p, ℓ, ℓ) ∉ Ψ_2^irr`,
equivalently `p² ∤ B_{ℓp}/(ℓp)` for the relevant irregular index `ℓ`),
case II of FLT for `p` holds.

The Bernoulli condition is essential — `¬ p ∣ h⁺` alone does not suffice
for case II. For `p = 37` and irregular index `32`, the condition is
`37² ∤ B_{32·37}/(32·37)`, equivalently `37³ ∤ numerator(B_{1184})`.
This is one finite Bernoulli computation, decidable in principle but
substantial in practice.

The proof requires Washington §9.1 cyclotomic unit decomposition (LV009)
+ specialised case II argument (LV010). Both substantial. We package
the implication as a single `CaseIIBridge` data structure for parametric
chaining in LV011.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **No second-order irregular pair predicate**: for `p` an odd prime
and `i` an even index in `[2, p-3]`, this predicate captures Washington/
Kellner's second-order non-irregularity at `(p, i)`. Concretely:
`p² ∤ B_{i·p} / (i·p)`, equivalently `p³ ∤ numerator(B_{i·p})`.

The exact decidable form is left for the bridge's eventual fill; we
expose it as an opaque `Prop` here so downstream code can chain
parametrically. -/
def NoSecondOrderIrregularPair (p i : ℕ) : Prop :=
  ¬ (p : ℤ) ^ 3 ∣ (bernoulli (i * p)).num

/-- **LV009 + LV010 case II bridge (Washington Theorem 9.4)**: under
`¬ p ∣ hPlus K` AND the second-order non-irregularity condition for
the irregular index `i`, case II of FLT holds for `p`.

The bridge field captures the case II content: for any FLT case II
scenario (coprime integers `a`, `b`, `c` with `p ∣ abc` and
`a^p + b^p = c^p`), no such solution exists.

Note: the Bernoulli condition is **required** for Washington Theorem 9.4
— `¬ p ∣ hPlus K` alone is not sufficient.

Filled by Washington Theorem 9.4 / LV009 + LV010 (substantial work
deferred). -/
structure CaseIIBridge (i : ℕ) where
  /-- The case II implication: under `¬ p ∣ hPlus K` AND the second-order
  non-irregularity condition, no FLT case II solution exists. -/
  no_caseII_solution :
    ¬ (p : ℕ) ∣ hPlus K →
      NoSecondOrderIrregularPair p i →
      ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 →
        ({a, b, c} : Finset ℤ).gcd id = 1 →
        ((p : ℤ) ∣ a * b * c) → a ^ p + b ^ p ≠ c ^ p

end BernoulliRegular

end
