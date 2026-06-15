import BernoulliRegular.UnitQuotient.Washington814ForwardD
import BernoulliRegular.UnitQuotient.Washington816
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.Washington83
import BernoulliRegular.BernoulliFast.Tactic

/-!
# `¬ 37 ∣ h⁺` via the unit-side §8.3 route, with the forward step discharged

`Washington814ForwardD.lean` proves, unconditionally on the §8.3 forward boundary,

  `flt37_not_dvd_hPlus_of_pollaczekUnit_classes_ne_zero :`
  `(∀ even i ∈ [2,34], [pollaczekUnit i]_{mod 37} ≠ 0) → ¬ 37 ∣ h⁺`.

This file assembles the `h_all` hypothesis from the two genuine inputs:

* `i = 32`: the **proven** certificate (`flt37_pollaczekUnit_class_in_modp_freepart_ne_zero`),
* `i ≠ 32`: Washington Theorem 8.16 in **class form** (`[pollaczekUnit i] = 0 ⟹ 37 ∣ B_i`)
  contraposed against the finite Bernoulli table (`37 ∤ B_i` for even `i ≠ 32`).

Compared with `not_dvd_hPlus_of_washington83`, the `Washington814Forward37` boundary is now
**discharged** (by the eigenspace + index bridge of `Washington814ForwardD.lean`); only the
Theorem-8.16 boundary (class form) and the Bernoulli table remain as hypotheses.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.3 Thm 8.14, Thm 8.16.
-/

@[expose] public section

open NumberField

namespace BernoulliRegular.FLT37.Sinnott

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **`¬ 37 ∣ h⁺` with the forward step discharged.** Uses the proven eigenspace/index bridge
`flt37_not_dvd_hPlus_of_pollaczekUnit_classes_ne_zero`; only Theorem 8.16 (class form) and the
Bernoulli table remain as hypotheses (the certificate at `i = 32` is already proven). -/
theorem flt37_not_dvd_hPlus_of_washington816_class
    (h_816 : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
      cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) i)) = 0 →
        (37 : ℤ) ∣ (bernoulli i).num)
    (h_table : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 →
      ¬ (37 : ℤ) ∣ (bernoulli i).num) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := by
  apply FLT37.flt37_not_dvd_hPlus_of_pollaczekUnit_classes_ne_zero
  intro i hi_even hi2 hi34
  rw [← cyclotomicUnitToFreePartModPAdd_apply]
  by_cases hi32 : i = 32
  · subst hi32
    exact FLT37.flt37_pollaczekUnit_class_in_modp_freepart_ne_zero
  · intro hzero
    exact h_table i hi_even hi2 hi34 hi32 (h_816 i hi_even hi2 hi34 hzero)

/-- **`¬ 37 ∣ h⁺` for `ℚ(ζ₃₇)`, with both §8.3 boundaries discharged.** The forward step
(Thm 8.14) is the proven eigenspace/index bridge; Theorem 8.16 (class form) is now the proven
`flt37_dvd_bernoulli_of_pollaczek_class_eq_zero`. Only the finite Bernoulli table
(`37 ∤ B_i` for even `i ≠ 32` in range — the irregularity data) remains as a hypothesis. -/
theorem flt37_not_dvd_hPlus_of_bernoulli_table
    (h_table : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 →
      ¬ (37 : ℤ) ∣ (bernoulli i).num) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
  flt37_not_dvd_hPlus_of_washington816_class
    (fun i hi_even hi2 hi34 hzero =>
      FLT37.flt37_dvd_bernoulli_of_pollaczek_class_eq_zero i hi_even hi2 hi34 hzero)
    h_table

omit [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The finite Bernoulli table for `37`**: `37 ∤ B_i` for every even `2 ≤ i ≤ 34` with `i ≠ 32`
(the only irregular even index of `37` in this range is `32`). Proved by direct computation of
each Bernoulli numerator modulo `37` (`bernoulli_decide`). This is the *first-order* irregularity
data, distinct from the second-order `NoSecondOrderIrregularPair 37 32`. -/
theorem flt37_bernoulli_table : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 →
    ¬ (37 : ℤ) ∣ (bernoulli i).num := by
  intro i hi_even hi2 hi34 hi32
  interval_cases i <;>
    first
      | exact absurd hi_even (by decide)
      | exact absurd rfl hi32
      | bernoulli_decide

/-- **`¬ 37 ∣ h⁺(ℚ(ζ₃₇))`, unconditionally.** Both §8.3 boundaries are proven (Thm 8.14 forward
via the eigenspace/index bridge, Thm 8.16 via the class-form computation) and the Bernoulli
table is discharged by computation, so Vandiver's conjecture holds for the prime `37`. -/
theorem flt37_not_dvd_hPlus : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
  flt37_not_dvd_hPlus_of_bernoulli_table flt37_bernoulli_table

end BernoulliRegular.FLT37.Sinnott

end
