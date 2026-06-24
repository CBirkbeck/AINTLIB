module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.FLT37.Principalization
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import BernoulliRegular.FLT37.Mirimanoff.FLTCaseIFactorizationAndDivisibility

/-!
# Mirimanoff subfield trick (ticket FLT37d, scaffold)

For an odd prime `ℓ ≡ 1 (mod 4)`, the "Mirimanoff trick" uses the fact
that `-1` is a square mod `ℓ` (so `(ZMod ℓ)ˣ` has an element of order 4).
The corresponding Galois automorphism `ζ ↦ ζ^ω` (where `ω² = -1` in
`ZMod ℓ`) generates a cyclic subgroup of order 4 in `Gal(K/ℚ)`.

The fixed field `k' ⊂ K⁺` of the order-2 subgroup gives a subfield
where Vandiver's odd-index analysis simplifies.

This file establishes the basic infrastructure: the Mirimanoff square
root `ω` and its key properties.

## References

* Vandiver 1929, *FLT and the Second Factor in the Cyclotomic Class Number*.
* Borevich–Shafarevich, *Number Theory*, §4.9.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

section MirimanoffPolynomial

section PartialPowerSum

/-- **Faulhaber consequence**: for `p` prime and `1 ≤ e ≤ p - 2`, the
partial power sum `S_e(p - 1) = ∑_{j=1}^{p-1} j^e ≡ 0 (mod p)`.

This is the classical fact that `∑_{j=1}^{p-1} j^e ≡ 0 (mod p)` whenever
`(p-1) ∤ e`, which holds in the range `1 ≤ e ≤ p - 2`. Combined with
`mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial`, the
`X^p` correction term vanishes in `(ZMod p)[X]`, giving the cleaner
identity

`(1 - X) · ∑_{k=1}^{p-1} C(S_e(k)) · X^k = mirimanoffPolynomial p (e + 1)`

for `e` in the relevant range. -/
theorem partialPowerSum_p_sub_one_eq_zero (p : ℕ) [hp : Fact p.Prime]
    {e : ℕ} (he₁ : 1 ≤ e) (he₂ : e ≤ p - 2) :
    partialPowerSum p e (p - 1) = 0 := by
  have hp_two : 2 ≤ p := hp.out.two_le
  -- Step 1: rewrite `∑_{j ∈ Ico 1 p}` as `∑_{j ∈ range p}`, since the `j = 0`
  -- term is `0^e = 0` for `e ≥ 1`.
  have h_rewrite : partialPowerSum p e (p - 1) =
      ∑ j ∈ Finset.range p, (j : ZMod p) ^ e := by
    unfold partialPowerSum
    have h_succ : p - 1 + 1 = p := by omega
    rw [h_succ, Finset.sum_range_eq_add_Ico (f := fun j ↦ (j : ZMod p) ^ e)
        (by omega : 0 < p)]
    simp only [Nat.cast_zero, zero_pow (Nat.one_le_iff_ne_zero.mp he₁), zero_add]
  -- Step 2: rewrite `∑_{j ∈ range p}` as `∑_{x : ZMod p}` via the bijection
  -- `j ↦ (j : ZMod p)`, which is bijective on `range p` since `p` is the
  -- characteristic.
  have h_bij : (∑ j ∈ Finset.range p, (j : ZMod p) ^ e) =
      ∑ x : ZMod p, x ^ e := by
    apply Finset.sum_bij (fun (j : ℕ) (_ : j ∈ Finset.range p) ↦ (j : ZMod p))
    · intro j _; exact Finset.mem_univ _
    · intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      have : (a : ZMod p).val = (b : ZMod p).val := by rw [hab]
      rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
    · intro x _
      refine ⟨x.val, ?_, ?_⟩
      · rw [Finset.mem_range]; exact ZMod.val_lt x
      · exact ZMod.natCast_zmod_val x
    · intro a _; rfl
  -- Step 3: apply `FiniteField.sum_pow_lt_card_sub_one` with `q = p`.
  have h_card : Fintype.card (ZMod p) = p := ZMod.card p
  have h_lt : e < Fintype.card (ZMod p) - 1 := by rw [h_card]; omega
  rw [h_rewrite, h_bij, FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) e h_lt]

/-- **Ribenboim 1.32, clean form** for `1 ≤ e ≤ p - 2`.

Combines `mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial`
with `partialPowerSum_p_sub_one_eq_zero` (the Faulhaber consequence) to
remove the `X^p` correction term, yielding the clean identity

`(1 - X) · ∑_{k=1}^{p-1} C(S_e(k)) · X^k = mirimanoffPolynomial p (e + 1)`

in `(ZMod p)[X]`. The hypothesis `1 ≤ e ≤ p - 2` (equivalently
`2 ≤ e + 1 ≤ p - 1`) is the Mirimanoff polynomial range. -/
theorem mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial_clean
    (p : ℕ) [hp : Fact p.Prime] {e : ℕ} (he₁ : 1 ≤ e) (he₂ : e ≤ p - 2) :
    (1 - Polynomial.X) * partialPowerSumPolynomial p e =
      mirimanoffPolynomial p (e + 1) := by
  rw [mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial,
      partialPowerSum_p_sub_one_eq_zero p he₁ he₂, Polynomial.C_0,
      zero_mul, sub_zero]

/-- **Evaluated Ribenboim 1.32** at `t ∈ ZMod p` with `t ≠ 1`, for
`1 ≤ e ≤ p - 2`:

`(1 - t) · ∑_{k=1}^{p-1} S_e(k) · t^k = (mirimanoffPolynomial p (e + 1)).eval t`

Together with `t ≠ 1`, this gives the closed form
`∑_{k=1}^{p-1} S_e(k) · t^k = (mirimanoffPolynomial p (e+1)).eval t / (1 - t)`. -/
theorem mirimanoffPolynomial_eval_eq_one_sub_t_mul_partialPowerSum_eval
    (p : ℕ) [hp : Fact p.Prime] {e : ℕ} (he₁ : 1 ≤ e) (he₂ : e ≤ p - 2)
    (t : ZMod p) :
    (1 - t) * ∑ k ∈ Finset.Ico 1 p, partialPowerSum p e k * t ^ k =
      (mirimanoffPolynomial p (e + 1)).eval t := by
  have h := mirimanoffPolynomial_eq_one_sub_X_mul_partialPowerSumPolynomial_clean
    p he₁ he₂
  have heval := congrArg (Polynomial.eval t) h
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X] at heval
  rw [← heval]
  congr 1
  unfold partialPowerSumPolynomial
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl
    (fun k _ ↦ by rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                       Polynomial.eval_X])

end PartialPowerSum

end MirimanoffPolynomial

/-! ## Mirimanoff fixed subfield -/

section MirimanoffFixedSubfield

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (h_mod_4 : ℓ % 4 = 1)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {ℓ} ℚ K]

/-- The **Mirimanoff fixed subfield** of `K = ℚ(ζ_ℓ)`: the subfield
fixed by `mirimanoffGalAut`. For `ℓ ≡ 1 mod 4`, this is a degree
`(ℓ - 1)/4` extension of `ℚ`, contained in `K⁺`. -/
noncomputable def mirimanoffFixedSubfield : IntermediateField ℚ K :=
  IntermediateField.fixedField (Subgroup.zpowers (mirimanoffGalAut ℓ h_mod_4 K))

/-- The relative dimension `[K : k']` is exactly `4`, where `k'` is the
Mirimanoff fixed subfield. -/
theorem finrank_K_over_mirimanoffFixedSubfield :
    Module.finrank (mirimanoffFixedSubfield ℓ h_mod_4 K) K = 4 := by
  rw [mirimanoffFixedSubfield, IntermediateField.finrank_fixedField_eq_card,
    nat_card_zpowers_mirimanoffGalAut]

/-- The dimension of the Mirimanoff fixed subfield over `ℚ` is `(ℓ - 1) / 4`. -/
theorem finrank_mirimanoffFixedSubfield_over_rat :
    Module.finrank ℚ (mirimanoffFixedSubfield ℓ h_mod_4 K) = (ℓ - 1) / 4 := by
  have h_mul := Module.finrank_mul_finrank ℚ
    (mirimanoffFixedSubfield ℓ h_mod_4 K) K
  rw [finrank_K_over_mirimanoffFixedSubfield] at h_mul
  have h_K : Module.finrank ℚ K = ℓ - 1 := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hℓ.1.pos)]
    exact Nat.totient_prime hℓ.1
  rw [h_K] at h_mul
  omega

/-- Every element of the Mirimanoff fixed subfield is fixed by complex
conjugation. This expresses the inclusion `k' ⊂ K⁺`. -/
theorem complexConjRat_apply_of_mem_mirimanoffFixedSubfield [IsCMField K]
    {x : K} (hx : x ∈ mirimanoffFixedSubfield ℓ h_mod_4 K) :
    BernoulliRegular.complexConjRat (p := ℓ) (K := K) (by omega : (ℓ : ℕ) ≠ 2) x = x := by
  rw [mirimanoffFixedSubfield, IntermediateField.mem_fixedField_iff] at hx
  exact hx _ (complexConjRat_mem_zpowers_mirimanoffGalAut ℓ h_mod_4 K)

/-- Every element of the Mirimanoff fixed subfield is fixed by
`mirimanoffGalAut`. -/
theorem mirimanoffGalAut_apply_of_mem_mirimanoffFixedSubfield
    {x : K} (hx : x ∈ mirimanoffFixedSubfield ℓ h_mod_4 K) :
    mirimanoffGalAut ℓ h_mod_4 K x = x := by
  rw [mirimanoffFixedSubfield, IntermediateField.mem_fixedField_iff] at hx
  exact hx _ (Subgroup.mem_zpowers _)

/-- Membership in `mirimanoffFixedSubfield` is equivalent to being
fixed by `mirimanoffGalAut`. -/
theorem mem_mirimanoffFixedSubfield_iff (x : K) :
    x ∈ mirimanoffFixedSubfield ℓ h_mod_4 K ↔ mirimanoffGalAut ℓ h_mod_4 K x = x := by
  refine ⟨mirimanoffGalAut_apply_of_mem_mirimanoffFixedSubfield ℓ h_mod_4 K, fun hx ↦ ?_⟩
  rw [mirimanoffFixedSubfield, IntermediateField.mem_fixedField_iff]
  -- The set of automorphisms fixing x is a subgroup; mirimanoffGalAut is in it,
  -- so the whole zpowers subgroup is in it.
  have h_stab : mirimanoffGalAut ℓ h_mod_4 K ∈ MulAction.stabilizer Gal(K/ℚ) x :=
    MulAction.mem_stabilizer_iff.mpr hx
  intro f hf
  exact MulAction.mem_stabilizer_iff.mp <|
    Subgroup.zpowers_le.mpr h_stab hf

/-- The Mirimanoff fixed subfield is contained in `K⁺`: every element fixed
by `mirimanoffGalAut` is fixed by complex conjugation. -/
theorem mem_maximalRealSubfield_of_mem_mirimanoffFixedSubfield [IsCMField K]
    {x : K} (hx : x ∈ mirimanoffFixedSubfield ℓ h_mod_4 K) :
    x ∈ NumberField.maximalRealSubfield K := by
  rw [← NumberField.IsCMField.complexConj_eq_self_iff]
  have h_rat := complexConjRat_apply_of_mem_mirimanoffFixedSubfield ℓ h_mod_4 K hx
  -- complexConjRat ... x = complexConj K x by complexConjRat_apply (rfl)
  exact h_rat

end MirimanoffFixedSubfield

end FLT37

end BernoulliRegular

end
