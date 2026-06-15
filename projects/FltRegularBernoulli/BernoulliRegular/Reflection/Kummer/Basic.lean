module

public import Mathlib.FieldTheory.KummerExtension
public import BernoulliRegular.Reflection.WeakSplitting.UnconditionalGlobal

/-!
# Abstract Kummer extension `K(η^{1/p})` (REF-15a)

For a field `K` containing the `p`-th roots of unity and a nonzero element
`η : K`, this file gives the abstract Kummer extension
`L = K(η^{1/p})` as the splitting field of `X^p - C η` over `K`, and proves
the key iff
$$
[L : K] = 1 \iff \eta \in K^{\times p}.
$$

This is the unblocked piece of REF-15: it depends only on mathlib's
`Mathlib.FieldTheory.KummerExtension`. The downstream specialisation to
the project's concrete `η` (chosen in REF-13/14) is REF-15b, which is
blocked on those.

The iff is the input REF-21i needs to specialise
`weakSplittingLemma_of_splits` (REF-21h, in
`WeakSplitting/UnconditionalGlobal.lean`) to conclude `η ∈ K^{×p}` from
"almost all primes split completely in `K(η^{1/p})`".

## Main results

* `BernoulliRegular.Kummer.splits_X_pow_sub_C_iff_isPow`:
  for `K` containing primitive `p`-th roots of unity, `p` an odd prime,
  and `η ∈ K`, `(X^p - C η).Splits` over `K` iff `∃ β : K, β^p = η`.
* `BernoulliRegular.Kummer.finrank_splittingField_eq_one_iff_isPow`:
  for the same hypotheses, `Module.finrank K (SplittingField (X^p - C η)) = 1`
  iff `∃ β : K, β^p = η`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Kummer

open Polynomial
open scoped NumberField

variable {K : Type*} [Field K]

/--
The polynomial `X^p - C η` splits over `K` iff `η = β^p` for some `β : K`,
provided `K` contains a primitive `p`-th root of unity and `p` is an odd prime.
-/
theorem splits_X_pow_sub_C_iff_isPow {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2)
    (hζ : (primitiveRoots p K).Nonempty) (η : K) :
    (X ^ p - C η).Splits ↔ ∃ β : K, β ^ p = η := by
  obtain ⟨ζ, hζmem⟩ := hζ
  have hp_pos : 0 < p := hp.pos
  rw [mem_primitiveRoots hp_pos] at hζmem
  refine ⟨fun h_split => ?_, fun ⟨β, hβ⟩ => X_pow_sub_C_splits_of_isPrimitiveRoot hζmem hβ⟩
  by_contra! h_no_pow
  have h_irred : Irreducible (X ^ p - C η) := by
    rw [show p = p ^ 1 from (pow_one p).symm]
    exact (X_pow_sub_C_irreducible_iff_of_prime_pow hp hp' one_ne_zero).mpr h_no_pow
  have h_deg_one : (X ^ p - C η).natDegree = 1 := h_split.natDegree_eq_one_of_irreducible h_irred
  rw [natDegree_X_pow_sub_C] at h_deg_one
  exact absurd h_deg_one hp.one_lt.ne'

/--
The splitting field of `X^p - C η` over `K` is trivial (`finrank K = 1`) iff
`η = β^p` for some `β : K`.

This is the key iff for REF-21i: combined with `weakSplittingLemma_of_splits`,
it lets us conclude `η ∈ K^{×p}` from the splits-completely hypothesis.
-/
theorem finrank_splittingField_eq_one_iff_isPow {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2)
    (hζ : (primitiveRoots p K).Nonempty) (η : K) :
    Module.finrank K (SplittingField (X ^ p - C η)) = 1 ↔ ∃ β : K, β ^ p = η := by
  rw [← splits_X_pow_sub_C_iff_isPow hp hp' hζ η,
    Polynomial.IsSplittingField.splits_iff (SplittingField (X ^ p - C η)) (X ^ p - C η),
    ← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- If `η` is not a global `p`-th power, the Kummer splitting field of
`X^p - η` has degree exactly `p`. -/
theorem finrank_splittingField_eq_prime_of_not_isPow {p : ℕ} (hp : p.Prime)
    (hp' : p ≠ 2) (hζ : (primitiveRoots p K).Nonempty) {η : K}
    (hη : ¬ ∃ β : K, β ^ p = η) :
    Module.finrank K (SplittingField (X ^ p - C η)) = p := by
  have H : Irreducible (X ^ p - C η) := by
    rw [show p = p ^ 1 from (pow_one p).symm]
    refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp hp' one_ne_zero).mpr ?_
    intro β hβ
    exact hη ⟨β, hβ⟩
  exact finrank_of_isSplittingField_X_pow_sub_C hζ H (SplittingField (X ^ p - C η))

/-- The chosen root of `X^p - eta` in any splitting field is integral over
`O_K` when `eta` is integral. -/
theorem rootOfSplitsXPowSubC_isIntegral_ringOfIntegers
    [NumberField K] {p : ℕ} [NeZero p] (η : 𝓞 K)
    (L : Type*) [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C (η : K))] :
    IsIntegral (𝓞 K)
      (rootOfSplitsXPowSubC (NeZero.pos p) (η : K) L) := by
  refine ⟨X ^ p - C η, monic_X_pow_sub_C η (NeZero.ne p), ?_⟩
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [rootOfSplitsXPowSubC_pow (a := (η : K)) (L := L)]
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L η, sub_self]

/-- The chosen Kummer root, bundled as an algebraic integer in the target
number field. -/
noncomputable def integralRootOfSplitsXPowSubC
    [NumberField K] {p : ℕ} [NeZero p] (η : 𝓞 K)
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C (η : K))] : 𝓞 L :=
  ⟨rootOfSplitsXPowSubC (NeZero.pos p) (η : K) L,
    isIntegral_trans (R := ℤ) (A := 𝓞 K) (B := L)
      (rootOfSplitsXPowSubC (NeZero.pos p) (η : K) L)
      (rootOfSplitsXPowSubC_isIntegral_ringOfIntegers (K := K) η L)⟩

@[simp]
theorem integralRootOfSplitsXPowSubC_coe
    [NumberField K] {p : ℕ} [NeZero p] (η : 𝓞 K)
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C (η : K))] :
    (integralRootOfSplitsXPowSubC (K := K) (p := p) η L : L) =
      rootOfSplitsXPowSubC (NeZero.pos p) (η : K) L :=
  rfl

/-- The chosen root of `X^p - eta` in a splitting field has minimal polynomial
`X^p - eta` when `eta` is not a global `p`-th power. -/
theorem minpoly_rootOfSplitsXPowSubC_eq_X_pow_sub_C {p : ℕ}
    (hp : p.Prime) (hp' : p ≠ 2) {η : K}
    (hη : ¬ ∃ β : K, β ^ p = η)
    (L : Type*) [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C η)] :
    minpoly K (rootOfSplitsXPowSubC hp.pos η L) = X ^ p - C η := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_irred : Irreducible (X ^ p - C η) := by
    rw [show p = p ^ 1 from (pow_one p).symm]
    refine (X_pow_sub_C_irreducible_iff_of_prime_pow hp hp' one_ne_zero).mpr ?_
    intro β hβ
    exact hη ⟨β, hβ⟩
  have h_root :
      aeval (rootOfSplitsXPowSubC hp.pos η L) (X ^ p - C η) = 0 := by
    rw [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [rootOfSplitsXPowSubC_pow (a := η) (L := L), sub_self]
  exact (minpoly.eq_of_irreducible_of_monic h_irred h_root
    (monic_X_pow_sub_C η hp.ne_zero)).symm

/-- The ring-of-integers minimal polynomial of the chosen integral Kummer root
is `X^p - eta`, provided `eta` is not a global `p`-th power. -/
theorem minpoly_integralRootOfSplitsXPowSubC_eq_X_pow_sub_C
    [NumberField K] {p : ℕ} [NeZero p] (hp : p.Prime) (hp' : p ≠ 2)
    (η : 𝓞 K) (hη : ¬ ∃ β : K, β ^ p = (η : K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C (η : K))] :
    minpoly (𝓞 K) (integralRootOfSplitsXPowSubC (K := K) (p := p) η L) =
      X ^ p - C η := by
  let x : 𝓞 L := integralRootOfSplitsXPowSubC (K := K) (p := p) η L
  have hxint : IsIntegral (𝓞 K) x := Algebra.IsIntegral.isIntegral x
  have h_fraction :
      minpoly K (algebraMap (𝓞 L) L x) =
        (minpoly (𝓞 K) x).map (algebraMap (𝓞 K) K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions
      (R := 𝓞 K) (S := 𝓞 L) (K := K) (L := L) hxint
  have h_field :
      minpoly K (algebraMap (𝓞 L) L x) = X ^ p - C (η : K) := by
    change minpoly K (x : L) = X ^ p - C (η : K)
    simpa [x] using
      (minpoly_rootOfSplitsXPowSubC_eq_X_pow_sub_C
        (K := K) hp hp' hη L)
  apply Polynomial.map_injective (f := algebraMap (𝓞 K) K)
    NumberField.RingOfIntegers.coe_injective
  calc
    (minpoly (𝓞 K) x).map (algebraMap (𝓞 K) K)
        = minpoly K (algebraMap (𝓞 L) L x) := h_fraction.symm
    _ = X ^ p - C (η : K) := h_field
    _ = (X ^ p - C η : (𝓞 K)[X]).map (algebraMap (𝓞 K) K) := by
      simp

/-- Reducing the ring-of-integers minimal polynomial of the chosen Kummer root
gives the expected residue polynomial. -/
theorem minpoly_integralRootOfSplitsXPowSubC_map_quotient_eq_X_pow_sub_C
    [NumberField K] {p : ℕ} [NeZero p] (hp : p.Prime) (hp' : p ≠ 2)
    (η : 𝓞 K) (hη : ¬ ∃ β : K, β ^ p = (η : K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsSplittingField K L (X ^ p - C (η : K))]
    (q : Ideal (𝓞 K)) :
    (minpoly (𝓞 K) (integralRootOfSplitsXPowSubC (K := K) (p := p) η L)).map
        (Ideal.Quotient.mk q) =
      (X ^ p - C (Ideal.Quotient.mk q η) : (𝓞 K ⧸ q)[X]) := by
  rw [minpoly_integralRootOfSplitsXPowSubC_eq_X_pow_sub_C
    (K := K) hp hp' η hη L]
  simp

/--
**REF-15c (closing API).** For a number field `K` containing primitive `p`-th
roots of unity (with `p` an odd prime), and `η : K`: if all but finitely many
`K`-primes split completely in `SplittingField (X^p - C η)`, then `η ∈ K^{×p}`.

This is the composition of:
* REF-21h's `weakSplittingLemma_of_splits` (giving `[L : K] = 1`), and
* REF-15a's `finrank_splittingField_eq_one_iff_isPow` (giving `[L : K] = 1 ↔ ∃ β, β^p = η`).

The hypothesis `hsplits` packages the "almost all primes split completely"
input as: there is a finite "bad" set `S` of nonzero prime ideals of `𝓞 K`,
and every `K`-prime above any rational prime, but outside `S`, splits
completely in the ring of integers of the Kummer extension.
-/
theorem isPow_of_almost_all_split
    [NumberField K] {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2)
    (hζ : (primitiveRoots p K).Nonempty) (η : K)
    [NumberField (SplittingField (X ^ p - C η))]
    (S : Finset (Ideal (NumberField.RingOfIntegers K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (hsplits : ∀ q : ℕ, q.Prime →
      ∀ P ∈ (IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers K)) \ S,
        BernoulliRegular.Ideal.SplitsCompletely
          (NumberField.RingOfIntegers (SplittingField (X ^ p - C η))) P) :
    ∃ β : K, β ^ p = η := by
  rw [← finrank_splittingField_eq_one_iff_isPow hp hp' hζ η]
  exact BernoulliRegular.WeakSplitting.weakSplittingLemma_of_splits
    (SplittingField (X ^ p - C η)) K S hS_ne hS_prime hsplits Module.finrank_pos

end Kummer

end BernoulliRegular
