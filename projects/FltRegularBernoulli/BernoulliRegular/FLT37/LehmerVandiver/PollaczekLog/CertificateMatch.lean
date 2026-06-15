module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PollaczekLog
public import BernoulliRegular.FLT37.LehmerVandiver.Certificate

/-!
# Certificate match: `lehmerVandiverProduct² = lehmerVandiverPrefactor² ↔ ±` (LV004g-3)

This file converts the chain endpoint
`lehmerVandiverProduct² = lehmerVandiverPrefactor²` (in `ZMod ℓ`) to the
disjunction
`lehmerVandiverProduct = lehmerVandiverPrefactor`
or
`lehmerVandiverProduct = -lehmerVandiverPrefactor`,
matching the certificate predicate `lehmerVandiverNonTrivial`.

The substantive content is the elementary field-algebra fact
`x² = y² ↔ x = ±y` for `ZMod ℓ` with `ℓ` prime
(`ZMod_sq_eq_sq_iff_eq_or_neg_eq` in `PollaczekLog.lean`).

## Main results

* `lehmerVandiverProduct_sq_eq_iff_pm_prefactor`: the algebraic identity
  `product² = prefactor² ↔ product = prefactor ∨ product = -prefactor`.
* `lehmerVandiverProduct_ne_pm_prefactor_iff`: the negated form, useful
  for combining with `lehmerVandiverNonTrivial`.
* `lehmerVandiverProduct_sq_ne_prefactor_sq_of_nontrivial_strong`:
  the sufficient condition feeding the closing chain — if both
  `product ≠ prefactor` and `product ≠ -prefactor`, then
  `product² ≠ prefactor²`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Theorem 9.5, p. 176.
-/

@[expose] public section

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

/-- **Algebraic identity (`x² = y² ↔ x = ±y`) at the LV certificate.**
For the LV-certificate sides `lehmerVandiverProduct` and
`lehmerVandiverPrefactor` (elements of `ZMod ℓ`) and `ℓ` an odd
auxiliary prime,

  product² = prefactor²  ↔  product = prefactor ∨ product = -prefactor.

Direct application of `ZMod_sq_eq_sq_iff_eq_or_neg_eq` from
`PollaczekLog.lean`. This is Goal A of LV004g-3. -/
theorem lehmerVandiverProduct_sq_eq_iff_pm_prefactor
    (p i ℓ t k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] :
    lehmerVandiverProduct p i ℓ t k ^ 2 = lehmerVandiverPrefactor p i ℓ t k ^ 2 ↔
      lehmerVandiverProduct p i ℓ t k = lehmerVandiverPrefactor p i ℓ t k ∨
      lehmerVandiverProduct p i ℓ t k = -lehmerVandiverPrefactor p i ℓ t k :=
  BernoulliRegular.FLT37.ZMod_sq_eq_sq_iff_eq_or_neg_eq ℓ
    (lehmerVandiverProduct p i ℓ t k) (lehmerVandiverPrefactor p i ℓ t k)

/-- **Negated form of `lehmerVandiverProduct_sq_eq_iff_pm_prefactor`.**
For the LV-certificate sides `lehmerVandiverProduct` and
`lehmerVandiverPrefactor` (elements of `ZMod ℓ`) and `ℓ` an odd
auxiliary prime,

  (product ≠ prefactor) ∧ (product ≠ -prefactor)  ↔  product² ≠ prefactor².

This is the form useful for combining with `lehmerVandiverNonTrivial`
(which is `prefactor ≠ product`). This is Goal B of LV004g-3. -/
theorem lehmerVandiverProduct_ne_pm_prefactor_iff
    (p i ℓ t k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] :
    (lehmerVandiverProduct p i ℓ t k ≠ lehmerVandiverPrefactor p i ℓ t k ∧
     lehmerVandiverProduct p i ℓ t k ≠ -lehmerVandiverPrefactor p i ℓ t k) ↔
      lehmerVandiverProduct p i ℓ t k ^ 2 ≠ lehmerVandiverPrefactor p i ℓ t k ^ 2 := by
  rw [ne_eq (lehmerVandiverProduct p i ℓ t k ^ 2),
    lehmerVandiverProduct_sq_eq_iff_pm_prefactor, not_or]

/-- **Sufficient condition for `lehmerVandiverProduct² ≠ lehmerVandiverPrefactor²`.**
The "strong" certificate hypothesis (both `product ≠ prefactor` and
`product ≠ -prefactor`) implies `product² ≠ prefactor²`.

This is what closes the LV004g chain: if the strong certificate holds,
the squaring lemma at `lehmerVandiverPrime` (LV004g-2) can be inverted to
deduce non-`p`-th-power-ness of the underlying cyclotomic-unit factor.
This is Goal C of LV004g-3. -/
theorem lehmerVandiverProduct_sq_ne_prefactor_sq_of_nontrivial_strong
    (p i ℓ t k : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (h_neq : lehmerVandiverProduct p i ℓ t k ≠ lehmerVandiverPrefactor p i ℓ t k)
    (h_neq_neg : lehmerVandiverProduct p i ℓ t k ≠ -lehmerVandiverPrefactor p i ℓ t k) :
    lehmerVandiverProduct p i ℓ t k ^ 2 ≠ lehmerVandiverPrefactor p i ℓ t k ^ 2 :=
  (lehmerVandiverProduct_ne_pm_prefactor_iff p i ℓ t k).mp ⟨h_neq, h_neq_neg⟩

end LehmerVandiver

end FLT37

end BernoulliRegular

end
