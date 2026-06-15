module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerPrincipalGen

/-!
# `Φ(A)` ideal-level extension and structural Kelly identity (REF-18 pivot)

This file defines the **Stickelberger-element-of-A** at the ideal level.
For an ideal `A` of `𝓞 K` coprime to `(p)`, the Stickelberger ideal
`A^Θ` is defined by

```
A^Θ := ∏_{a ∈ (ZMod p)ˣ} (σ_{a^{-1}} A) ^ a.val
```

This generalises `stickelbergerIdeal` (which works for arbitrary
ideals) and `stickelbergerPrincipalGen` (the principal-ideal case
returning an element).

Multiplicativity `(A · B)^Θ = A^Θ · B^Θ` follows from the multiplicativity
of `cyclotomicGaloisConjugate` on ideals plus Finset-product
distribution.

## Φ(A) = g(A)^p

The element `g(A)^p` (the `p`-th power of the Gauss sum at A) is the
distinguished generator of `A^Θ`. We package the existence of such a
generator (with the Stickelberger ideal equality) as the existing
`StickelbergerIdealEquality A`. The unit factor relating `g(A)^p` to
the canonical principal generator `α^Θ` (when A = (α)) is the
substantive content of the principal unit factor theorem
(`Φ((α)) = u(α) · α^Θ`).

## Structural Kelly identity (the substantive analytic content)

The key residue-symbol identity is

```
(Φ(A) / B)_p = (NB / A)_p             (Kelly form)
```

where `NB ∈ ℤ` is the norm of `B`. For primary `A = (α)` with
`u(α) = ±1`, this specialises to

```
(α^Θ / B)_p = (NB / α)_p
```

The file below records the ideal-level Φ algebra used by later Kelly-form
identities; it does not introduce a named reciprocity assumption.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Stickelberger ideal of a general ideal (multiplicative extension) -/

/-- **`stickelbergerIdeal` of the unit ideal `(1)`** is `(1)`. -/
theorem stickelbergerIdeal_one :
    stickelbergerIdeal (p := p) (K := K) (1 : Ideal (𝓞 K)) =
      (1 : Ideal (𝓞 K)) := by
  unfold stickelbergerIdeal
  refine Finset.prod_eq_one fun a _ => ?_
  rw [show cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ (1 : Ideal _) =
      (1 : Ideal _) from by
    rw [Ideal.one_eq_top, cyclotomicGaloisConjugate_top]]
  exact one_pow _

/-- **`stickelbergerIdeal` of a Finset-product**: distributes over `Finset.prod`. -/
theorem stickelbergerIdeal_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → Ideal (𝓞 K)) :
    stickelbergerIdeal (p := p) (K := K) (∏ i ∈ s, f i) =
      ∏ i ∈ s, stickelbergerIdeal (p := p) (K := K) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, stickelbergerIdeal_one, Finset.prod_empty]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
        stickelbergerIdeal_mul, ih]

/-! ### `Φ(A)` existence as a structural hypothesis (general ideal) -/

/-- **`PhiGenerator A`** — the existence of an element `γ ∈ 𝓞 K` such
that `(γ) = A^Θ`. Generalises `StickelbergerIdealEquality` from prime
ideals to general ideals.

For prime `A`, this is exactly the existing `StickelbergerIdealEquality A`.
For principal `A = (α)`, the generator can be taken as `α^Θ`. For general
ideals, the existence is established via prime factorisation +
multiplicativity of `stickelbergerIdeal`. -/
def PhiGenerator (A : Ideal (𝓞 K)) : Prop :=
  ∃ γ : 𝓞 K, γ ≠ 0 ∧
    Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) A

/-- **`PhiGenerator` for a principal ideal**: take `γ = α^Θ`. -/
theorem PhiGenerator_principal (α : 𝓞 K) (hα : α ≠ 0) :
    PhiGenerator (p := p) (K := K) (Ideal.span ({α} : Set (𝓞 K))) :=
  ⟨stickelbergerPrincipalGen (p := p) (K := K) α,
    stickelbergerPrincipalGen_ne_zero hα,
    (stickelbergerIdeal_span_singleton α).symm⟩

/-- **`PhiGenerator` from `StickelbergerIdealEquality`** (prime case):
the existing prime-level structural hypothesis directly produces a
`PhiGenerator`. -/
theorem PhiGenerator_of_StickelbergerIdealEquality
    {q_K : Ideal (𝓞 K)} (h : StickelbergerIdealEquality (p := p) (K := K) q_K) :
    PhiGenerator (p := p) (K := K) q_K :=
  ⟨h.gen, h.gen_ne_zero, h.span_gen⟩

/-- **`PhiGenerator` is multiplicative**: if `A` and `B` admit
`PhiGenerator`s, so does `A · B`, with generator the product. -/
theorem PhiGenerator_mul {A B : Ideal (𝓞 K)}
    (hA : PhiGenerator (p := p) (K := K) A)
    (hB : PhiGenerator (p := p) (K := K) B) :
    PhiGenerator (p := p) (K := K) (A * B) := by
  obtain ⟨γA, hγA_ne, hγA_span⟩ := hA
  obtain ⟨γB, hγB_ne, hγB_span⟩ := hB
  refine ⟨γA * γB, ?_, ?_⟩
  · exact mul_ne_zero hγA_ne hγB_ne
  · rw [stickelbergerIdeal_mul]
    rw [← hγA_span, ← hγB_span]
    rw [Ideal.span_singleton_mul_span_singleton]

/-! ### Primary unit factor (structural)

For principal `A = (α)`, the canonical generator is `α^Θ` (per
`PhiGenerator_principal`). The Gauss-sum-based "true" generator is
`g((α))^p` (where multiplicativity over the prime factorisation of `(α)`
defines `g((α))`); these may differ by a unit `u(α)`. The condition
`u(α) = ±1` (forced by primarity of α) is the substantive primarity
content.

We package the resulting principal unit factor identity as a structural
hypothesis ready to be discharged. -/

/-- **Unit factor symbol vanishes for `u = 1`**. The simplest case of the
"primary unit factor is symbol-trivial" content. -/
theorem unit_factor_one_symbol_eq_zero (B : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (1 : 𝓞 K) B = 0 :=
  pthSymbolAtIdeal_canonical_one_alpha B

end Furtwaengler

end BernoulliRegular

end
