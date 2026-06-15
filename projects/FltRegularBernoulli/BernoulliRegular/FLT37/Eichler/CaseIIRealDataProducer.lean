import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ProductDescent

/-!
# [FLT37-CASEII-REAL-PRODUCER] Real Case-II descent data from an integer FLT solution

The Case-II descent machinery of `ProductDescent.lean` runs on `RealCaseIIData37` (the
reality-restricted datum `σx = x`, `σy = y`), but the existing integer producer
`exists_caseIIData37_of_caseII_int_solution` (`SpecificChain.lean`) only delivers the general
`CaseIIData37`, forgetting the reality invariant.

This file supplies the **reality-preserving producer** (Piece (1) of the genuine Case-II reroute):
from an integer Case-II FLT solution, build a `RealCaseIIData37`.  The base variables `x, y` are
integer casts `(x : ℤ) → 𝓞 K`, hence fixed by complex conjugation (`map_intCast` on the ring
homomorphism `ringOfIntegersComplexConj K`).  Only `x, y` need to be real for the σ-stable pair
machinery — `z'` (the `(ζ-1)`-multiplicity quotient of `z`) may move under σ, which is why the
`RealCaseIIData37` structure does not record `z_real`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent runs on real data).
* `SpecificChain.lean` `exists_caseIIData37_of_Int_solution` (the general producer this mirrors).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

/-- **Integer casts are real.** The image in `𝓞 K` of an integer is fixed by complex conjugation,
because `ringOfIntegersComplexConj K` is a ring homomorphism (so it commutes with `Int.cast`). -/
theorem ringOfIntegersComplexConj_intCast_eq
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K] (n : ℤ) :
    NumberField.IsCMField.ringOfIntegersComplexConj K (n : 𝓞 K) = (n : 𝓞 K) :=
  map_intCast (NumberField.IsCMField.ringOfIntegersComplexConj K) n

set_option backward.isDefEq.respectTransparency false in
/-- **Real Case-II datum from the integer second-case normal form** `¬ 37 ∣ y`, `37 ∣ z`,
`z ≠ 0`, `x^37 + y^37 = z^37`.

Identical multiplicity extraction to `exists_caseIIData37_of_Int_solution`, but the constructed
datum is a `RealCaseIIData37`: the reality fields `x_real`, `y_real` hold because `x, y` enter as
integer casts. -/
theorem exists_realCaseIIData37_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ (x y z : ℤ), ¬ (37 : ℤ) ∣ y ∧ (37 : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ 37 + y ^ 37 = z ^ 37) →
    ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  intro h
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  haveI := CyclotomicField.isCyclotomicExtension 37 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField 37 ℚ)) (Set.mem_singleton 37)
    (by decide : (37 : ℕ) ≠ 0)
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField 37 ℚ) hζ (n := n)
  rcases h with ⟨x, y, z, hy_int, hz_int, hz_ne, e⟩
  have hy : ¬ (hζ.toInteger - 1) ∣ (y : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro hdiv
    exact hy_int ((h_dvd_iff y).mp hdiv)
  have hz : (hζ.toInteger - 1) ∣ (z : 𝓞 (CyclotomicField 37 ℚ)) :=
    (h_dvd_iff z).mpr hz_int
  have hz_ne_OK : (z : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := by
    rwa [ne_eq, Int.cast_eq_zero]
  have eOK :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 +
        (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (z : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]
  letI : WfDvdMonoid (𝓞 (CyclotomicField 37 ℚ)) :=
    IsNoetherianRing.wfDvdMonoid
  obtain ⟨n, z', hn, hz_n, hz_eq⟩ :
      ∃ n z', 1 ≤ n ∧ ¬ ((hζ.toInteger - 1) ∣ z') ∧
        (z : 𝓞 (CyclotomicField 37 ℚ)) = (hζ.toInteger - 1) ^ n * z' := by
    classical
    have H : FiniteMultiplicity
        (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ)) :=
      FiniteMultiplicity.of_not_isUnit hζ.zeta_sub_one_prime'.not_unit
        hz_ne_OK
    obtain ⟨z', hfac⟩ := pow_multiplicity_dvd (hζ.toInteger - 1)
      (z : 𝓞 (CyclotomicField 37 ℚ))
    refine ⟨_, _, ?_, ?_, hfac⟩
    · rwa [← Nat.cast_le (α := ENat),
        ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h_dvd
      have := mul_dvd_mul_left
        ((hζ.toInteger - 1) ^ multiplicity (hζ.toInteger - 1)
          (z : 𝓞 (CyclotomicField 37 ℚ))) h_dvd
      rw [← pow_succ, ← hfac] at this
      refine not_pow_dvd_of_emultiplicity_lt ?_ this
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  refine ⟨n - 1, ⟨?_⟩⟩
  refine
    { ζ := ζ
      hζ := hζ
      x := (x : 𝓞 (CyclotomicField 37 ℚ))
      y := (y : 𝓞 (CyclotomicField 37 ℚ))
      z := z'
      ε := 1
      equation := ?_
      hy := hy
      hz := hz_n
      x_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) x
      y_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) y }
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hz_eq] at eOK
  simpa [hn_eq] using eOK

/-- **Real Case-II datum from the coprime integer second-case normal form** (`37 ∣ z`). -/
theorem exists_realCaseIIData37_of_Int_solution'
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧
      (37 : ℤ) ∣ z ∧ z ≠ 0 ∧ x ^ 37 + y ^ 37 = z ^ 37) →
    ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  rintro ⟨x, y, z, hgcd, hz, hz_ne, e⟩
  refine exists_realCaseIIData37_of_Int_solution
    ⟨x, y, z, ?_, hz, hz_ne, e⟩
  intro hy
  have h_dvd : (37 : ℤ) ∣ x ^ 37 := by
    have := dvd_sub (dvd_pow hz (by decide : (37 : ℕ) ≠ 0))
      (dvd_pow hy (by decide : (37 : ℕ) ≠ 0))
    rw [← e, add_sub_cancel_right] at this
    exact this
  have hp_x : (37 : ℤ) ∣ x :=
    (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).dvd_of_dvd_pow h_dvd
  apply (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, hp_x]

/-- **Piece (1): a real Case-II datum from an integer Case-II FLT solution.**

From an integer FLT solution `a^37 + b^37 = c^37` with `abc ≠ 0`, `gcd = 1`, and `37 ∣ abc`
(Case II), build a `RealCaseIIData37 (CyclotomicField 37 ℚ) m` for some `m`.  After the standard
permutation moving the `37`-divisible variable to the `z` slot, the two remaining variables enter
as integer casts and are therefore real (`x_real`, `y_real`).  This is the reality-preserving
entry point for the σ-stable pair-product descent, mirroring
`exists_caseIIData37_of_caseII_int_solution`. -/
theorem exists_realCaseIIData37_of_caseII_int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ}
    (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37) :
    ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨ha0, hb0⟩, hc0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two (by decide : Nat.Prime 37)
    (by decide : (37 : ℕ) ≠ 2)
  obtain hab | hc :=
    (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).dvd_or_dvd hcase
  · obtain ha | hb :=
      (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).dvd_or_dvd hab
    · refine exists_realCaseIIData37_of_Int_solution'
        ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine exists_realCaseIIData37_of_Int_solution'
        ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact exists_realCaseIIData37_of_Int_solution'
      ⟨a, b, c, hgcd, hc, hc0, e⟩

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

end
