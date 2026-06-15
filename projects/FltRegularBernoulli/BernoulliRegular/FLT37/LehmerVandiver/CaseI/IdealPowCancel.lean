import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealConjugate
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# LV010-class-eq-1b: Ideal p-th root cancellation in Dedekind domains

For a Dedekind domain `R`, the monoid `Ideal R` is a unique factorization
monoid. From `A^n = B^n` with `A, B ≠ 0` and `n ≠ 0`, we conclude
`A = B` via `normalizedFactors_pow` + `Multiset` left cancellation.

This is the key cancellation step in the Vandiver class-equality
discharge: from `(α/σα) = (β)^p` (Kummer's lemma output, fractional ideal
form), we get `(𝔞·σ𝔞⁻¹) = (β)`, hence `[𝔞] = [σ𝔞]` in the class group.

## References

* `Mathlib.RingTheory.DedekindDomain.Ideal.Basic`:
  `Ideal.uniqueFactorizationMonoid`.
* `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors`:
  `normalizedFactors_pow`, `associated_iff_normalizedFactors_eq_normalizedFactors`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

set_option backward.isDefEq.respectTransparency false in
/-- **Ideal p-th root cancellation in a Dedekind domain.** For ideals
`A, B` of a Dedekind domain `R` with `A, B ≠ ⊥` and `n ≠ 0`,
`A^n = B^n ⟹ A = B`.

Proof: `Ideal R` is a UniqueFactorizationMonoid. From `A^n = B^n` and
`normalizedFactors_pow`, `n • normalizedFactors A = n • normalizedFactors B`.
By `Multiset` torsion-freeness (`IsAddTorsionFree.nsmul_right_injective`),
`normalizedFactors A = normalizedFactors B`. By
`associated_iff_normalizedFactors_eq_normalizedFactors`, `A` and `B` are
associated. For non-zero ideals in `Ideal R`, associated ⟺ equal. -/
theorem Ideal.pow_left_inj_of_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {n : ℕ} (hn : n ≠ 0) {A B : Ideal R} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (h : A ^ n = B ^ n) :
    A = B := by
  -- Step 1: nonzero powers
  have hAn : A ^ n ≠ 0 := pow_ne_zero n hA
  have hBn : B ^ n ≠ 0 := pow_ne_zero n hB
  -- Step 2: normalized factors equal
  have hfact : UniqueFactorizationMonoid.normalizedFactors (A ^ n) =
      UniqueFactorizationMonoid.normalizedFactors (B ^ n) := by
    rw [h]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow] at hfact
  -- Step 3: Multiset cancellation
  have hfact' : UniqueFactorizationMonoid.normalizedFactors A =
      UniqueFactorizationMonoid.normalizedFactors B :=
    IsAddTorsionFree.nsmul_right_injective hn hfact
  -- Step 4: A and B are associated
  have hassoc : Associated A B :=
    (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
      hA hB).mpr hfact'
  -- Step 5: For ideals, associated ⟹ equal (units are just ⊤)
  obtain ⟨u, hu⟩ := hassoc
  have h_top : (u : Ideal R) = ⊤ := Ideal.isUnit_iff.mp u.isUnit
  rw [← hu, h_top, Ideal.mul_top]

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
