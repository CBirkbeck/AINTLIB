import BernoulliRegular.FLT37.Arithmetic
import BernoulliRegular.FLT37.Principalization
import BernoulliRegular.FLT37.PrimaryConj
import BernoulliRegular.FLT37.CaseI
import BernoulliRegular.FLT37.MirimanoffDescent
import BernoulliRegular.FLT37.CaseII
import BernoulliRegular.BernoulliFast.PrimesUpTo100
import Mathlib.NumberTheory.FLT.Basic
import FltRegular.MayAssume.Lemmas

/-!
# FLT for `p = 37` from Vandiver Theorem III (ticket FLT37h, conditional)

This module packages the *reduction* `Vandiver III ⇒ FermatLastTheoremFor 37`.

The standing arithmetic inputs for `ℓ = 37` are now all in place:

* `37 ≡ 1 (mod 4)` — discharged by `decide`.
* every irregular index of `37` has even `k` — proved in `FLT37/Arithmetic.lean`
  as `irregular_index_even_thirtyseven`, combining
  `not_dvd_bernoulli_num_of_odd_index_thirtyseven` (nine `bernoulli_decide`
  computations) with the witness
  `BernoulliRegular.thirtyseven_dvd_bernoulli_thirtytwo_num`.

What remains is **Vandiver Theorem III** itself:

```text
For every odd prime ℓ ≡ 1 (mod 4) such that every irregular Bernoulli
index of ℓ is even, FermatLastTheoremFor ℓ holds.
```

This file provides the conditional statement; the unconditional proof
follows once tickets FLT37b – FLT37g are completed.

## Status

Conditional. The `fermatLastTheoremFor_thirtyseven_of_vandiverIII` reduction
is unconditional; the eponymous unconditional theorem awaits FLT37g.
-/

namespace BernoulliRegular

namespace FLT37

/-- An **irregular index** of `ℓ` is a positive integer `k` with
`2k ≤ ℓ - 3` and `ℓ ∣ num(B_{2k})`. -/
def IsIrregularIndex (ℓ k : ℕ) : Prop :=
  1 ≤ k ∧ 2 * k ≤ ℓ - 3 ∧ (ℓ : ℤ) ∣ (bernoulli (2 * k)).num

/-- An irregular index is positive. -/
theorem IsIrregularIndex.one_le {ℓ k : ℕ} (h : IsIrregularIndex ℓ k) : 1 ≤ k :=
  h.1

/-- An irregular index satisfies `2k ≤ ℓ - 3`. -/
theorem IsIrregularIndex.two_mul_le_sub_three {ℓ k : ℕ}
    (h : IsIrregularIndex ℓ k) : 2 * k ≤ ℓ - 3 :=
  h.2.1

/-- An irregular index witnesses `ℓ ∣ num(B_{2k})`. -/
theorem IsIrregularIndex.dvd_bernoulli_num {ℓ k : ℕ}
    (h : IsIrregularIndex ℓ k) : (ℓ : ℤ) ∣ (bernoulli (2 * k)).num :=
  h.2.2

/-- Constructor: given the three pieces of data, build an `IsIrregularIndex`. -/
theorem IsIrregularIndex.mk {ℓ k : ℕ} (h_pos : 1 ≤ k) (h_le : 2 * k ≤ ℓ - 3)
    (h_dvd : (ℓ : ℤ) ∣ (bernoulli (2 * k)).num) :
    IsIrregularIndex ℓ k :=
  ⟨h_pos, h_le, h_dvd⟩

/-- For an irregular index, `2k` lies in `[2, ℓ - 3]`. -/
theorem IsIrregularIndex.two_le_two_mul {ℓ k : ℕ} (h : IsIrregularIndex ℓ k) :
    2 ≤ 2 * k :=
  Nat.mul_le_mul_left 2 h.one_le

/-- For an irregular index, `k < ℓ`. -/
theorem IsIrregularIndex.lt {ℓ k : ℕ} (h : IsIrregularIndex ℓ k) (hℓ : 0 < ℓ) :
    k < ℓ := by
  have h_le : 2 * k ≤ ℓ - 3 := h.two_mul_le_sub_three
  omega

/-- For an irregular index, `2 * k + 3 ≤ ℓ` whenever `ℓ ≥ 3`. -/
theorem IsIrregularIndex.two_mul_add_three_le {ℓ k : ℕ}
    (h : IsIrregularIndex ℓ k) (hℓ : 3 ≤ ℓ) :
    2 * k + 3 ≤ ℓ := by
  have h_le : 2 * k ≤ ℓ - 3 := h.two_mul_le_sub_three
  omega

/-- The hypothesis package used by Vandiver's Theorem III: the prime is
`≡ 1 (mod 4)` and every irregular Bernoulli index in the relevant range has
even `k`. -/
def VandiverIIIHypothesis (ℓ : ℕ) : Prop :=
  ℓ % 4 = 1 ∧
  ∀ k, 1 ≤ k → 2 * k ≤ ℓ - 3 → (ℓ : ℤ) ∣ (bernoulli (2 * k)).num → Even k

/-- The Vandiver III hypothesis equivalently says every irregular index
has even `k`. -/
theorem VandiverIIIHypothesis_iff_isIrregularIndex (ℓ : ℕ) :
    VandiverIIIHypothesis ℓ ↔
      ℓ % 4 = 1 ∧ ∀ k, IsIrregularIndex ℓ k → Even k := by
  unfold VandiverIIIHypothesis IsIrregularIndex
  refine ⟨?_, ?_⟩
  · rintro ⟨h4, h⟩
    exact ⟨h4, fun k ⟨h1, h2, hd⟩ ↦ h k h1 h2 hd⟩
  · rintro ⟨h4, h⟩
    exact ⟨h4, fun k h1 h2 hd ↦ h k ⟨h1, h2, hd⟩⟩

/-- The Vandiver III hypothesis is verified for `ℓ = 37`. -/
theorem vandiverIIIHypothesis_thirtyseven : VandiverIIIHypothesis 37 :=
  ⟨by decide, irregular_index_even_thirtyseven⟩

/-- Vandiver's Theorem III as a quantified statement: every odd prime
`ℓ ≡ 1 (mod 4)` whose irregular Bernoulli indices are all even satisfies
`FermatLastTheoremFor ℓ`. -/
def VandiverIII : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → VandiverIIIHypothesis ℓ → FermatLastTheoremFor ℓ

/-- The first-case half of Vandiver Theorem III: the parity hypothesis on
irregular indices implies Case I of FLT for `ℓ`. -/
def VandiverIIICaseI : Prop :=
  ∀ ⦃a b c : ℤ⦄ {ℓ : ℕ}, ℓ.Prime → VandiverIIIHypothesis ℓ →
    ¬ (ℓ : ℤ) ∣ a * b * c → a ^ ℓ + b ^ ℓ ≠ c ^ ℓ

/-- The second-case half of Vandiver Theorem III: the parity hypothesis
implies Case II of FLT for `ℓ`. The hypothesis package mirrors
`flt-regular`'s `caseII` after the `MayAssume.coprime` reduction. -/
def VandiverIIICaseII : Prop :=
  ∀ ⦃a b c : ℤ⦄ {ℓ : ℕ}, ℓ.Prime → VandiverIIIHypothesis ℓ →
    a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
    ((ℓ : ℤ) ∣ a * b * c) → a ^ ℓ + b ^ ℓ ≠ c ^ ℓ

/-- **Vandiver III decomposition.** `VandiverIIICaseI` and `VandiverIIICaseII`
together imply `VandiverIII`. -/
theorem vandiverIII_of_caseI_caseII
    (hI : VandiverIIICaseI) (hII : VandiverIIICaseII) :
    VandiverIII := by
  intro ℓ hℓ hVH
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc heq
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime heq hprod
  let d : ℤ := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : (ℓ : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact hII hℓ hVH hprod' hgcd case e'
  · exact hI hℓ hVH case e'

/-- **Conditional FLT for 37.** Assuming Vandiver Theorem III,
`FermatLastTheoremFor 37` holds. -/
theorem fermatLastTheoremFor_thirtyseven_of_vandiverIII
    (h_VT3 : VandiverIII) :
    FermatLastTheoremFor 37 :=
  h_VT3 37 (by decide) vandiverIIIHypothesis_thirtyseven

/-- **Direct conditional FLT for 37.** Assuming `VandiverIIICaseI` and
`VandiverIIICaseII`, `FermatLastTheoremFor 37` holds. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseI_caseII
    (hI : VandiverIIICaseI) (hII : VandiverIIICaseII) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_vandiverIII (vandiverIII_of_caseI_caseII hI hII)

/-- Specialisation of `VandiverIIICaseI` to `ℓ = 37`. The parity hypothesis
is already verified for 37, so this is the bare Case I statement. -/
theorem caseI_thirtyseven_of_VandiverIIICaseI (hI : VandiverIIICaseI) :
    ∀ ⦃a b c : ℤ⦄, ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  fun _ _ _ ↦ hI (by decide) vandiverIIIHypothesis_thirtyseven

/-- Specialisation of `VandiverIIICaseII` to `ℓ = 37`, in the
post-coprimification form. -/
theorem caseII_thirtyseven_of_VandiverIIICaseII (hII : VandiverIIICaseII) :
    ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  fun _ _ _ ↦ hII (by decide) vandiverIIIHypothesis_thirtyseven

/-- **ℓ = 37 conditional case I via `MirimanoffBernoulliConclusion`.**
Takes the higher-level Bernoulli-divisibility predicate directly. -/
theorem caseI_thirtyseven_of_bernoulli_conclusion
    {a b c : ℤ}
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (hc : ¬ (37 : ℤ) ∣ c) (hb : ¬ (37 : ℤ) ∣ b)
    (hMC : haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
      MirimanoffBernoulliConclusion 37 a b) :
    False := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact flt_caseI_contradiction_of_bernoulli_conclusion_strong
    (p := 37) (by omega) (by decide) (by decide)
    (fltCaseI_t_ne_one_of_p_not_dvd heq hc hb)
    hMC vandiverIIIHypothesis_thirtyseven.2

/-- **ℓ = 37 final assembly via `MirimanoffBernoulliConclusion`.**
The case I Bernoulli-divisibility predicate together with `VandiverIIICaseII`
yields `FermatLastTheoremFor 37`. -/
theorem fermatLastTheoremFor_thirtyseven_of_conclusion_and_caseII
    (h_conclusion : ∀ ⦃a b c : ℤ⦄, a ^ 37 + b ^ 37 = c ^ 37 →
      ¬ (37 : ℤ) ∣ b → ¬ (37 : ℤ) ∣ c →
      haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
      MirimanoffBernoulliConclusion 37 a b)
    (hII : VandiverIIICaseII) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc heq
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime heq hprod
  set d : ℤ := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : (37 : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact hII (by decide) vandiverIIIHypothesis_thirtyseven hprod' hgcd case e'
  · have h_not_b : ¬ (37 : ℤ) ∣ (b / d) := fun h ↦ case ((h.mul_left _).mul_right _)
    have h_not_c : ¬ (37 : ℤ) ∣ (c / d) := fun h ↦ case (h.mul_left _)
    exact caseI_thirtyseven_of_bernoulli_conclusion e' h_not_c h_not_b
      (h_conclusion e' h_not_b h_not_c)

/-- **ℓ = 37 final assembly via 37-specific predicates.** Uses the 37-specific
case II predicate `VandiverLemma1Thirtyseven` (instead of the universal
`VandiverIIICaseII`), giving a tighter conditional statement. -/
theorem fermatLastTheoremFor_thirtyseven_of_conclusion_and_vandiverLemma1
    (h_conclusion : ∀ ⦃a b c : ℤ⦄, a ^ 37 + b ^ 37 = c ^ 37 →
      ¬ (37 : ℤ) ∣ b → ¬ (37 : ℤ) ∣ c →
      haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
      MirimanoffBernoulliConclusion 37 a b)
    (h_caseII : VandiverLemma1Thirtyseven) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc heq
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime heq hprod
  set d : ℤ := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : (37 : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact h_caseII hprod' hgcd case e'
  · have h_not_b : ¬ (37 : ℤ) ∣ (b / d) := fun h ↦ case ((h.mul_left _).mul_right _)
    have h_not_c : ¬ (37 : ℤ) ∣ (c / d) := fun h ↦ case (h.mul_left _)
    exact caseI_thirtyseven_of_bernoulli_conclusion e' h_not_c h_not_b
      (h_conclusion e' h_not_b h_not_c)

/-- **ℓ = 37 case I reduction: MBI ⟹ `a ≡ b (mod 37)`.** From an FLT case I
solution at 37 and `MirimanoffBernoulliIdentity 37 a b`, the congruence
`a ≡ b (mod 37)` holds. -/
theorem caseI_thirtyseven_a_eq_b_of_mbi
    {a b c : ℤ}
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (ha : ¬ (37 : ℤ) ∣ a) (hb : ¬ (37 : ℤ) ∣ b) (hc : ¬ (37 : ℤ) ∣ c)
    (hMI : haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
      MirimanoffBernoulliIdentity 37 a b) :
    (a : ZMod 37) = (b : ZMod 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact fltCaseI_a_eq_b_mod_p_of_mbi_and_parity (p := 37)
    (by omega) (by decide) (by decide) heq ha hb hc hMI
    vandiverIIIHypothesis_thirtyseven.2

/-- **ℓ = 37 case I reduction: MBI ⟹ `MirimanoffPolynomialVanishingOdd 37`.**
The polynomial-level form of `caseI_thirtyseven_a_eq_b_of_mbi` (both encode
`t = -1`). -/
theorem caseI_thirtyseven_polynomialVanishing_of_mbi
    {a b c : ℤ}
    (heq : a ^ 37 + b ^ 37 = c ^ 37)
    (ha : ¬ (37 : ℤ) ∣ a) (hb : ¬ (37 : ℤ) ∣ b) (hc : ¬ (37 : ℤ) ∣ c)
    (hMI : haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
      MirimanoffBernoulliIdentity 37 a b) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩;
    MirimanoffPolynomialVanishingOdd 37 a b := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact mirimanoffPolynomialVanishingOdd_of_mbi_and_parity (p := 37)
    (by omega) (by decide) (by decide) heq ha hb hc hMI
    vandiverIIIHypothesis_thirtyseven.2

/-- **ℓ = 37 descent sum bridge.** For descent data `w` with constant `C`,
the weighted sum `∑ w k * t ^ k` equals `C * φ₃(t)`. -/
theorem caseI_thirtyseven_wIntDescent_sum_eq_const_mul_phi_three
    {w : ℕ → ZMod 37} {C t : ZMod 37}
    (h : WIntDescentData 37 w C) :
    (∑ k ∈ Finset.Ico 1 37, w k * t ^ k) =
      C * (mirimanoffPolynomial 37 3).eval t := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact WIntDescentData.sum_eq_const_mul_mirimanoffPolynomial_three h

/-- Vanishing form of the `ℓ = 37` descent sum bridge. -/
theorem caseI_thirtyseven_wIntDescent_sum_eq_zero_of_phi_three_eq_zero
    {w : ℕ → ZMod 37} {C t : ZMod 37}
    (h : WIntDescentData 37 w C)
    (hφ : (mirimanoffPolynomial 37 3).eval t = 0) :
    (∑ k ∈ Finset.Ico 1 37, w k * t ^ k) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact WIntDescentData.sum_eq_zero_of_phi_three_eq_zero h hφ

instance fact_prime_thirtyseven : Fact (Nat.Prime 37) :=
  ⟨by decide⟩

instance cyclotomicField_thirtyseven_isCyclotomicExtension :
    IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ) :=
  CyclotomicField.isCyclotomicExtension 37 ℚ

/-- **`IsCMField`** instance for `CyclotomicField 37 ℚ`. -/
instance cyclotomicField_thirtyseven_isCMField :
    NumberField.IsCMField (CyclotomicField 37 ℚ) :=
  isCMField_of_cyclotomic
    (p := 37) (hp_odd := by norm_num) (K := CyclotomicField 37 ℚ)

/-- **Vandiver's plus-side coprimality at `ℓ = 37`.**

Asserts `(37 : ℕ).Coprime (hPlus (CyclotomicField 37 ℚ))`. This is a
particular case of Vandiver's conjecture (`p ∤ h⁺` for the cyclotomic
field of conductor `p`) — verified computationally for `p = 37` but
not yet formalised here. -/
def Vandiver37PlusCoprime : Prop :=
  (37 : ℕ).Coprime (hPlus (CyclotomicField 37 ℚ))

/-- The explicit non-divisibility form of `Vandiver37PlusCoprime`. -/
theorem vandiver37PlusCoprime_iff_not_dvd_hPlus :
    Vandiver37PlusCoprime ↔ ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := by
  simpa [Vandiver37PlusCoprime] using
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)
      (n := hPlus (CyclotomicField 37 ℚ)))

/-- `Vandiver37PlusCoprime` rules out 37-divisibility of the plus class number. -/
theorem not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
    (h : Vandiver37PlusCoprime) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
  vandiver37PlusCoprime_iff_not_dvd_hPlus.mp h

end FLT37

end BernoulliRegular
