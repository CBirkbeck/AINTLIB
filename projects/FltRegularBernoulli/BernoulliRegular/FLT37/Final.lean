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
    exact ⟨h4, fun k ⟨h1, h2, hd⟩ => h k h1 h2 hd⟩
  · rintro ⟨h4, h⟩
    exact ⟨h4, fun k h1 h2 hd => h k ⟨h1, h2, hd⟩⟩

/-- The hypothesis is verified for `ℓ = 37`. The two conjuncts come from a
trivial `decide` and `irregular_index_even_thirtyseven` (FLT37a). -/
theorem vandiverIIIHypothesis_thirtyseven : VandiverIIIHypothesis 37 :=
  ⟨by decide, irregular_index_even_thirtyseven⟩

/-- Vandiver's Theorem III as a quantified statement. Once tickets FLT37b–g
discharge this, the unconditional `FermatLastTheoremFor 37` is immediate. -/
def VandiverIII : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → VandiverIIIHypothesis ℓ → FermatLastTheoremFor ℓ

/-- The first-case half of Vandiver Theorem III: the parity hypothesis on
irregular indices implies Case I of FLT for `ℓ`. Used in the planned
decomposition `VandiverIIICaseI ∧ VandiverIIICaseII → VandiverIII`
(ticket FLT37g). -/
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

/-- **Vandiver III decomposition (FLT37g).**

The two halves combine into `VandiverIII` exactly as
`flt-regular`'s `flt_regular` combines `caseI` and `caseII`:

* reduce to integers via `fermatLastTheoremFor_iff_int`,
* coprimify via `MayAssume.coprime`,
* split on `ℓ ∣ a*b*c`. -/
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

/-- **Conditional FLT for 37 (FLT37h skeleton).** Assuming Vandiver Theorem III,
`FermatLastTheoremFor 37` follows by combining `VandiverIIIHypothesis 37` —
which is unconditional and built from FLT37a + the existing irregularity
witness for 37 — with the Vandiver III hypothesis. -/
theorem fermatLastTheoremFor_thirtyseven_of_vandiverIII
    (h_VT3 : VandiverIII) :
    FermatLastTheoremFor 37 :=
  h_VT3 37 (by decide) vandiverIIIHypothesis_thirtyseven

/-- **Direct conditional FLT for 37.** Assuming `VandiverIIICaseI` and
`VandiverIIICaseII`, `FermatLastTheoremFor 37` follows. This composes
the Case-decomposition (`vandiverIII_of_caseI_caseII`) with the
specialisation to `ℓ = 37` (`fermatLastTheoremFor_thirtyseven_of_vandiverIII`),
making the remaining mathematical content (FLT37e, FLT37f) the only
outstanding work. -/
theorem fermatLastTheoremFor_thirtyseven_of_caseI_caseII
    (hI : VandiverIIICaseI) (hII : VandiverIIICaseII) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_vandiverIII (vandiverIII_of_caseI_caseII hI hII)

/-! ## Concrete `ℓ = 37` specialisations

For convenience, the universal `VandiverIIICaseI`/`II` hypotheses can be
instantiated at `ℓ = 37` using `vandiverIIIHypothesis_thirtyseven`. The
result is exactly Case I (resp. Case II) of FLT for `37` — concrete
proof targets for tickets FLT37e and FLT37f. -/

/-- Specialisation of `VandiverIIICaseI` to `ℓ = 37`. The parity hypothesis
is already verified for 37, so this is the bare Case I statement. -/
theorem caseI_thirtyseven_of_VandiverIIICaseI (hI : VandiverIIICaseI) :
    ∀ ⦃a b c : ℤ⦄, ¬ (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  fun _ _ _ => hI (by decide) vandiverIIIHypothesis_thirtyseven

/-- Specialisation of `VandiverIIICaseII` to `ℓ = 37`, in the
post-coprimification form. -/
theorem caseII_thirtyseven_of_VandiverIIICaseII (hII : VandiverIIICaseII) :
    ∀ ⦃a b c : ℤ⦄, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  fun _ _ _ => hII (by decide) vandiverIIIHypothesis_thirtyseven

/-! ## ℓ = 37 case I conditional theorems

The case I conditional closure for `ℓ = 37` runs through the
`MirimanoffBernoulliConclusion` predicate (the per-`n` Bernoulli
divisibility statement) combined with the verified parity hypothesis
`vandiverIIIHypothesis_thirtyseven`.

The previous `MirimanoffPolynomialVanishing + MirimanoffBernoulliIdentity`
chain (theorems `caseI_thirtyseven_under_predicates`,
`fermatLastTheoremFor_thirtyseven_of_predicates_and_caseII`, and the
`φ_3` / `a ≡ b` specialisations) has been removed: with the corrected
product-form `MBI` (`φ_n(t)·B_{p-n} ≡ 0 (mod p)`) the bridge step
`MV + MBI ⟹ MBC` is no longer logically sound. See the comment in
`CaseI.lean` for details. -/

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
Cleaner version of `fermatLastTheoremFor_thirtyseven_of_predicates_and_caseII`
that takes the higher-level Bernoulli-divisibility predicate directly. -/
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
  set d : ℤ := ({a, b, c} : Finset ℤ).gcd id with hd_def
  by_cases case : (37 : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact hII (by decide) vandiverIIIHypothesis_thirtyseven hprod' hgcd case e'
  · have h_not_b : ¬ (37 : ℤ) ∣ (b / d) := fun h => case ((h.mul_left _).mul_right _)
    have h_not_c : ¬ (37 : ℤ) ∣ (c / d) := fun h => case (h.mul_left _)
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
  set d : ℤ := ({a, b, c} : Finset ℤ).gcd id with hd_def
  by_cases case : (37 : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact h_caseII hprod' hgcd case e'
  · have h_not_b : ¬ (37 : ℤ) ∣ (b / d) := fun h => case ((h.mul_left _).mul_right _)
    have h_not_c : ¬ (37 : ℤ) ∣ (c / d) := fun h => case (h.mul_left _)
    exact caseI_thirtyseven_of_bernoulli_conclusion e' h_not_c h_not_b
      (h_conclusion e' h_not_b h_not_c)

/-! ## ℓ = 37 reduction: MBI + parity ⟹ `a ≡ b (mod 37)`

The bridge `fltCaseI_a_eq_b_mod_p_of_mbi_and_parity` (in `CaseI.lean`)
specialises to `ℓ = 37` to give the integer congruence directly from
`MirimanoffBernoulliIdentity`. This isolates the substantive F37-A
content (discharging MBI) from the case II / Vandiver Lemma 1 closure
(F37-D). -/

/-- **ℓ = 37 case I reduction: MBI ⟹ `a ≡ b (mod 37)`.**

Specialises `fltCaseI_a_eq_b_mod_p_of_mbi_and_parity` to `ℓ = 37`,
using the verified parity hypothesis `vandiverIIIHypothesis_thirtyseven`.
Inputs are an FLT case I solution at 37 and the per-solution
`MirimanoffBernoulliIdentity 37 a b`. -/
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

Specialises `mirimanoffPolynomialVanishingOdd_of_mbi_and_parity` to
`ℓ = 37`. Equivalent in content to `caseI_thirtyseven_a_eq_b_of_mbi`
(both encode `t = -1`), expressed at the polynomial level. -/
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

/-- **ℓ = 37 specialisation of the F37-A3 descent sum bridge.**

Once F37-A2 supplies proportional descent data for the `(ζ - 1)^2`
coefficients `w_k`, their weighted sum is a scalar multiple of `φ_3(t)`. -/
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

/-! ## ℓ = 37: Vandiver's plus-side coprimality predicate

The case I decomposition (`fltCaseI_*_of_regular` family in `CaseI.lean`)
currently requires full regularity `(37 : ℕ).Coprime |Cl(𝓞 K)|`. For
`p = 37` this is *false* — `37` is irregular and `37 ∣ h⁻(K)` (witness
`B_32` divisibility, see `thirtyseven_dvd_bernoulli_thirtytwo_num`).

The classical Vandiver-style approach for irregular primes is to use
the weaker "plus-side coprimality" `(37 : ℕ).Coprime h⁺(K)`, which is
asserted by Vandiver's conjecture and verified computationally for all
primes `< 1.6 × 10⁸` (Buhler/Crandall/Sompolski). For `p = 37`, this
fact is true but its formalised proof requires class-number computation
that is currently out of scope.

We expose it here as the predicate `Vandiver37PlusCoprime`, to be
discharged either:

* externally as a hypothesis (currently);
* eventually via a formalised computation of
  `hPlus (CyclotomicField 37 ℚ)`. -/

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
not yet formalised here.

Together with the Vandiver III parity hypothesis (irregular indices
have even `k`) and T044 reflection, it discharges the regularity
hypothesis used by the case I decomposition for irregular `p = 37`. -/
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
