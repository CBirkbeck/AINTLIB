module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiIdeal

/-!
# Kelly's prime-level identity (REF-18 Phase 2, sub-piece K)

This file builds the Kelly-form prime identity for `α^Θ / P'`:

```
(α^Θ / P')_p = (NP' / α)_p
```

via three steps (K1–K3 in `.mathlib-quality/ref18_phase2_plan.md`):

* **K1**: `(α^Θ / P')_p = ∑_a a.val · (σ_{a^{-1}} α / P')_p` (left-slot
  Galois sum at a single prime).
* **K2**: integer-against-prime symbol formula for `(n / P')_p`.
* **K3**: the substantive Stickelberger-Eisenstein combination
  `∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Kelly identities -/

/-- Ideal-level Kelly identity: the canonical residue symbol of `α^Θ`
against `B` decomposes as the sum of integer-norm symbols over the prime
factorization of `B`. -/
def KellyIdealIdentity (α : 𝓞 K) (B : Ideal (𝓞 K)) : Prop :=
  pthSymbolAtIdeal_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) B =
    ((normalizedFactors B).map
      (fun P => pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))))).sum

/-- `KellyIdealIdentity α ⊤` holds unconditionally. -/
theorem KellyIdealIdentity_top (α : 𝓞 K) :
    KellyIdealIdentity (p := p) (K := K) α (⊤ : Ideal (𝓞 K)) := by
  unfold KellyIdealIdentity
  rw [pthSymbolAtIdeal_canonical_top, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one]
  simp

/-- `KellyIdealIdentity α ⊥` holds unconditionally. -/
theorem KellyIdealIdentity_bot (α : 𝓞 K) :
    KellyIdealIdentity (p := p) (K := K) α (⊥ : Ideal (𝓞 K)) := by
  unfold KellyIdealIdentity
  rw [pthSymbolAtIdeal_canonical_bot,
    show (⊥ : Ideal (𝓞 K)) = (0 : Ideal (𝓞 K)) from rfl,
    UniqueFactorizationMonoid.normalizedFactors_zero]
  simp

/-- `KellyIdealIdentity 0 B` holds unconditionally. -/
theorem KellyIdealIdentity_zero (B : Ideal (𝓞 K)) :
    KellyIdealIdentity (p := p) (K := K) (0 : 𝓞 K) B := by
  unfold KellyIdealIdentity
  rw [stickelbergerPrincipalGen_zero, pthSymbolAtIdeal_canonical_zero_alpha]
  rw [show (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) = ⊥ from by simp]
  symm
  refine Multiset.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hx
  exact pthSymbolAtIdeal_canonical_bot _

/-- From the concrete prime-level Kelly equality at every prime to the
ideal-level identity. -/
theorem KellyIdealIdentity_of_kellyPrimeEquality_all
    {α : 𝓞 K}
    (h : ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))))
    {B : Ideal (𝓞 K)} (_hB : B ≠ ⊥) :
    KellyIdealIdentity (p := p) (K := K) α B := by
  classical
  unfold KellyIdealIdentity pthSymbolAtIdeal_canonical
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun P hP => ?_
  obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  haveI : P.IsPrime := hP_max.isPrime
  have h_kelly := h P hP_ne_bot
  rw [show pthSymbolAtPrime_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) P =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) P from ?_]
  · exact h_kelly
  · rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
      (stickelbergerPrincipalGen (p := p) (K := K) α) hP_ne_bot]

/-! ### K1 — α^Θ symbol left-Galois sum at a single ideal -/

/-- **K1: Left-slot Galois sum for `(α^Θ / B)_p`** at any ideal `B`.

Generalises `pthSymbolAtPrincipal_canonical_principalGen_left_eq_galois_sum`
from principal `(γ)` to arbitrary ideals `B`. The hypothesis is that
each `σ_{a^{-1}} α` is coprime to every prime factor of `B`. -/
theorem pthSymbolAtIdeal_canonical_principalGen_eq_galois_sum
    (α : 𝓞 K) (B : Ideal (𝓞 K))
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B := by
  classical
  unfold stickelbergerPrincipalGen
  -- Distribute pthSymbolAtIdeal_canonical over Finset-prod numerator.
  rw [pthSymbolAtIdeal_canonical_finset_prod_α (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val))
    (I := B)
    (fun a _ P hP h_in_pow => ?_)]
  · -- Each (σ_{a^{-1}} α)^a.val term unfolds via _pow_α.
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pthSymbolAtIdeal_canonical_pow_α (p := p)
      (fun P hP => h_coprime a P hP) ((a : ZMod p).val)]
  · -- side condition for finset_prod: (σ_{a^{-1}} α)^a.val ∉ P.
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    haveI hP_prime : P.IsPrime := hP_max.isPrime
    have h_in : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∈ P :=
      hP_prime.mem_of_pow_mem ((a : ZMod p).val) h_in_pow
    exact (h_coprime a P hP) h_in

/-- **K1 specialised to a single non-bot prime `P'`**: the Galois sum
collapses to a single prime-level term per Galois index. -/
theorem pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P' := by
  classical
  -- Apply the general form, then translate ideal-symbol → prime-symbol at P'.
  rw [pthSymbolAtIdeal_canonical_principalGen_eq_galois_sum α P' ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    -- pthSymbolAtIdeal_canonical _ P' = pthSymbolAtPrime_canonical _ P' (P' prime).
    rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) hP'_ne]
  · -- coprimality at every prime factor of P'.
    intro a P hP
    -- normalizedFactors P' = {P'} for prime P'.
    have hP_eq : P = P' := by
      have h_factors :
          UniqueFactorizationMonoid.normalizedFactors P' = ({P'} : Multiset _) := by
        have h_prime_in_R : Prime P' := (Ideal.prime_iff_isPrime hP'_ne).mpr inferInstance
        have h_irreducible : Irreducible P' := h_prime_in_R.irreducible
        have h_assoc :=
          UniqueFactorizationMonoid.normalizedFactors_irreducible h_irreducible
        rw [show normalize P' = P' from normalize_eq P'] at h_assoc
        exact h_assoc
      rw [h_factors] at hP
      exact Multiset.mem_singleton.mp hP
    rw [hP_eq]
    exact h_coprime a

/-! ### K2 — integer-against-prime symbol formula (structural hypothesis)

The substantive content connecting `Σ_a a.val · (σ_{a^{-1}} α / P')_p`
to `(NP' / α)_p` is the **Stickelberger / Gauss-sum norm relation**:
the Galois-weighted sum on the LHS reconstitutes a single integer-norm
symbol on the RHS via the identity `g(χ_{P'}) · g(χ_{P'}^{-1}) = ±NP'`
in the appropriate cyclotomic ring.

We package this as a structural hypothesis `StickelbergerNormRelation α P'`
to be discharged by the substantive Gauss-sum chain.

Note: For `α` Galois-invariant (`α ∈ ℤ ⊆ 𝓞 K`), the LHS sum equals
`(Σ a.val) · (α / P')_p = 0` (since `Σ_{a ∈ (ZMod p)ˣ} a.val ≡ 0
(mod p)` for odd p — `SumUnitsValEqZeroHypothesis`). And the RHS
`(NP' / α)_p` for α ∈ ℤ requires a separate computation; it is NOT
generally zero. So `StickelbergerNormRelation` is a substantive identity
when α is non-trivial in the Galois orbit. -/

/-- Arithmetic identity used in the Galois-invariant special case:
`Σ_{a ∈ (ZMod p)ˣ} a.val ≡ 0 (mod p)`. -/
def SumUnitsValEqZeroHypothesis : Prop :=
  (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p)) = 0

/-- **`StickelbergerNormRelation α P'`** — the substantive identity
relating the Galois-weighted sum to the integer-norm symbol:
```
∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p   in ZMod p.
```
This is the Stickelberger-Eisenstein norm relation at the prime level. -/
def StickelbergerNormRelation (α : 𝓞 K) (P' : Ideal (𝓞 K)) : Prop :=
  (∑ a : CyclotomicUnitDelta p,
      ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))

/-! ### K3 — concrete Kelly prime equality from K1 + K2 -/

/-- **K3: concrete Kelly prime equality from K1 + K2**.

Given:
* the Galois-sum decomposition `(α^Θ / P')_p = ∑_a a.val · (σ_{a^{-1}} α / P')_p`
  (K1, with appropriate coprimality), and
* the Stickelberger norm relation
  `∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p` (K2),

the canonical Kelly identity `(α^Θ / P')_p = (NP' / α)_p` follows by
chaining the two. -/
theorem kellyPrimeEquality_of_StickelbergerNormRelation
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_norm : StickelbergerNormRelation (p := p) (K := K) α P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  -- Apply K1 to the LHS, then K2.
  rw [pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
    α hP'_ne h_coprime]
  -- Now: ∑_a a.val · (σ_{a^{-1}} α / P')_p = (NP' / α)_p — that's K2.
  exact h_norm

/-- **End-to-end Phase-2 K-chain**: universal Stickelberger-norm relations
give the concrete Kelly equality at every nonzero prime. -/
theorem kellyPrimeEquality_all_of_StickelbergerNormRelation
    {α : 𝓞 K}
    (h_coprime : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_norm : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      StickelbergerNormRelation (p := p) (K := K) α P') :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := fun P' hP'_inst hP'_ne =>
  kellyPrimeEquality_of_StickelbergerNormRelation α hP'_ne
    (h_coprime P' hP'_inst hP'_ne) (h_norm P' hP'_inst hP'_ne)

/-! ### Trivial discharge cases for `StickelbergerNormRelation`

The trivial cases `α = 0` and `α = 1` of `StickelbergerNormRelation` hold
unconditionally; we prove them here. -/

/-- **`StickelbergerNormRelation` at `α = 1`**: holds unconditionally,
both sides are `0`. -/
theorem StickelbergerNormRelation_one
    (P' : Ideal (𝓞 K)) :
    StickelbergerNormRelation (p := p) (K := K) (1 : 𝓞 K) P' := by
  unfold StickelbergerNormRelation
  -- LHS: each (σ_{a^{-1}} 1 / P')_p = (1 / P')_p = 0.
  -- RHS: (NP' / Ideal.span {1})_p = (NP' / ⊤)_p = 0.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ 1) P') = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (1 : 𝓞 K) =
        (1 : 𝓞 K) from map_one _]
    -- pthSymbolAtPrime_canonical 1 P' = 0 (from PthSymbolCanonical.lean).
    by_cases hbot : P' = ⊥
    · subst hbot
      rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot 1, mul_zero]
    by_cases hmax : P'.IsMaximal
    · rw [pthSymbolAtPrime_canonical_one (p := p) (K := K) hbot hmax, mul_zero]
    · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax, mul_zero]
  rw [h_lhs]
  -- RHS: pthSymbolAtIdeal_canonical _ (Ideal.span {1}) = 0 since (1) = ⊤.
  rw [Ideal.span_singleton_one, pthSymbolAtIdeal_canonical_top]

/-- **`StickelbergerNormRelation` at `α = 0`**: holds unconditionally,
both sides are `0`. -/
theorem StickelbergerNormRelation_zero
    (P' : Ideal (𝓞 K)) :
    StickelbergerNormRelation (p := p) (K := K) (0 : 𝓞 K) P' := by
  unfold StickelbergerNormRelation
  -- LHS: each (σ_{a^{-1}} 0 / P')_p = (0 / P')_p = 0 since 0 ∈ P'.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ 0) P') = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (0 : 𝓞 K) =
        (0 : 𝓞 K) from map_zero _]
    by_cases hbot : P' = ⊥
    · subst hbot
      rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot 0, mul_zero]
    by_cases hmax : P'.IsMaximal
    · rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax (Submodule.zero_mem _),
        mul_zero]
    · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax, mul_zero]
  rw [h_lhs]
  -- RHS: pthSymbolAtIdeal_canonical _ (Ideal.span {0}) = pthSymbolAtIdeal_canonical _ ⊥ = 0.
  rw [show (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) = ⊥ from by simp,
    pthSymbolAtIdeal_canonical_bot]

/-! ### `StickelbergerNormRelation` for integer α (trivially primary)

For `α = (n : 𝓞 K)` coming from `n ∈ ℤ`, the relation holds with both
sides vanishing in `ZMod p` (for odd `p`):

* **LHS**: `Σ_a a.val · (σ_{a^{-1}} α / P')_p = (Σ a.val) · (α / P')_p`
  since σ_a fixes integer α. By `Σ a.val ≡ 0 (mod p)` (for odd p),
  this is 0.

* **RHS**: `pthSymbolAtIdeal_canonical (NP' : 𝓞 K) (Ideal.span {α})` for
  α ∈ ℤ — vanishes by the Galois-orbit summation argument
  (the prime factors of `(α)` split into Galois orbits, and within each
  orbit the integer-against-prime symbols sum to 0).

The remaining open content for general primary α (NOT just integers) is
the substantive Stickelberger / Gauss-sum norm relation. -/

/-- **For Galois-invariant α (e.g. `α = (n : 𝓞 K)` with `n ∈ ℤ`)**, the
LHS of `StickelbergerNormRelation α P'` equals `(Σ a.val) · (α / P')_p`. -/
theorem stickelberger_norm_lhs_galois_invariant
    (α : 𝓞 K) (P' : Ideal (𝓞 K))
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α = α) :
    (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') =
    (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p)) *
      pthSymbolAtPrime_canonical (p := p) (K := K) α P' := by
  rw [Finset.sum_congr rfl (fun a _ => by rw [h_inv a])]
  rw [← Finset.sum_mul]

/-- **For Galois-invariant β**, the principal symbol against `β^Θ` is the
unit-index sum times the principal symbol against `β`. -/
theorem pthSymbolAtPrincipal_canonical_principalGen_galois_invariant
    (α : 𝓞 K) {β : 𝓞 K} (hβ : β ≠ 0)
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β = β) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α
        (stickelbergerPrincipalGen (p := p) (K := K) β) =
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p)) *
        pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  rw [pthSymbolAtPrincipal_canonical_principalGen_eq_galois_sum α hβ]
  rw [Finset.sum_congr rfl (fun a _ => by rw [h_inv a])]
  rw [← Finset.sum_mul]

/-- **`StickelbergerNormRelation` for Galois-invariant α with vanishing
unit sum**: under the arithmetic hypothesis `Σ a.val ≡ 0 (mod p)` and
the structural hypothesis that the integer-norm symbol vanishes (e.g.,
when α ∈ ℤ via Galois-orbit summation), both sides are 0. -/
theorem StickelbergerNormRelation_of_galois_invariant
    (α : 𝓞 K) (P' : Ideal (𝓞 K))
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α = α)
    (h_sum_zero : SumUnitsValEqZeroHypothesis (p := p))
    (h_norm_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) = 0) :
    StickelbergerNormRelation (p := p) (K := K) α P' := by
  unfold StickelbergerNormRelation
  rw [stickelberger_norm_lhs_galois_invariant α P' h_inv]
  unfold SumUnitsValEqZeroHypothesis at h_sum_zero
  rw [h_sum_zero, zero_mul]
  exact h_norm_zero.symm

/-! ### Re-indexing identity for `Σ a.val = Σ a⁻¹.val` -/

/-- **Re-indexing identity**: `Σ_a (a⁻¹).val = Σ_a a.val` in `ZMod p`. -/
theorem sum_inv_val_eq_sum_val :
    (∑ a : CyclotomicUnitDelta p,
        (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val : ZMod p)) =
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p)) := by
  -- Σ_a f (a^{-1}) = Σ_a f a, where the equivalence a ↦ a^{-1} acts.
  exact Equiv.sum_comp (Equiv.inv (CyclotomicUnitDelta p))
    (fun a : CyclotomicUnitDelta p => ((a : ZMod p).val : ZMod p))

/-- **Σ a⁻¹.val = 0** for odd p (follows from arithmetic identity). -/
theorem sum_inv_val_eq_zero
    (h_sum_zero : SumUnitsValEqZeroHypothesis (p := p)) :
    (∑ a : CyclotomicUnitDelta p,
        (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val : ZMod p)) = 0 := by
  rw [sum_inv_val_eq_sum_val]
  exact h_sum_zero

/-! ### Galois-invariant β + arithmetic identity ⟹ symbol vanishes -/

/-- **`(α / (β^Θ))_p = 0` for Galois-invariant β + `Σ a.val ≡ 0 mod p`**.

For β with σ_a β = β for all a (e.g. β ∈ ℤ ⊆ 𝓞 K), the right-slot
Galois-sum decomposition simplifies to `(Σ a.val) · (α / β)_p`. With
`Σ a.val ≡ 0 mod p` (the arithmetic identity for odd p), this vanishes. -/
theorem pthSymbolAtPrincipal_canonical_principalGen_galois_invariant_eq_zero
    (α : 𝓞 K) {β : 𝓞 K} (hβ : β ≠ 0)
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β = β)
    (h_sum_zero : SumUnitsValEqZeroHypothesis (p := p)) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α
        (stickelbergerPrincipalGen (p := p) (K := K) β) = 0 := by
  rw [pthSymbolAtPrincipal_canonical_principalGen_galois_invariant α hβ h_inv]
  unfold SumUnitsValEqZeroHypothesis at h_sum_zero
  rw [h_sum_zero, zero_mul]

/-! ### Trivial discharges of the concrete Kelly equality -/

/-- `α^Θ` at α = 0 is 0. -/
theorem stickelbergerPrincipalGen_zero_eq_zero :
    stickelbergerPrincipalGen (p := p) (K := K) (0 : 𝓞 K) = 0 :=
  stickelbergerPrincipalGen_zero

/-- **Concrete Kelly equality at α = 0**: holds unconditionally. -/
theorem kellyPrimeEquality_zero (P' : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (0 : 𝓞 K)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) := by
  -- LHS: (0^Θ / P')_p = (0 / P')_p = 0.
  rw [stickelbergerPrincipalGen_zero]
  rw [show (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) = ⊥ from by simp]
  -- LHS now: pthSymbolAtIdeal_canonical 0 P'.
  -- RHS: pthSymbolAtIdeal_canonical NP' ⊥ = 0.
  rw [pthSymbolAtIdeal_canonical_bot, pthSymbolAtIdeal_canonical_zero_alpha]

/-- **Concrete Kelly equality at α = 1**: holds unconditionally. -/
theorem kellyPrimeEquality_one (P' : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (1 : 𝓞 K)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({(1 : 𝓞 K)} : Set (𝓞 K))) := by
  -- α^Θ for α = 1: each factor (σ_{a^{-1}} 1)^a.val = 1^a.val = 1, product = 1.
  have h_one : stickelbergerPrincipalGen (p := p) (K := K) (1 : 𝓞 K) = 1 := by
    unfold stickelbergerPrincipalGen
    refine Finset.prod_eq_one fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (1 : 𝓞 K) =
        (1 : 𝓞 K) from map_one _]
    exact one_pow _
  rw [h_one]
  -- LHS: (1 / P')_p = 0.
  -- RHS: (NP' / Ideal.span {1})_p = (NP' / ⊤)_p = 0.
  rw [Ideal.span_singleton_one, pthSymbolAtIdeal_canonical_top]
  -- LHS now: pthSymbolAtIdeal_canonical 1 P'.
  exact pthSymbolAtIdeal_canonical_one_alpha _

/-- At a nonzero prime containing `(p)`, the left side of Kelly's prime
identity vanishes by the canonical target-prime convention. The remaining
content at such primes is the right-hand primary/λ correction. -/
theorem kellyPrimeEquality_lhs_eq_zero_of_p_mem
    {α : 𝓞 K} {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hp_in : (p : 𝓞 K) ∈ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) α) P' = 0 :=
  pthSymbolAtIdeal_canonical_eq_zero_of_p_mem_prime
    (stickelbergerPrincipalGen (p := p) (K := K) α) hP'_ne hp_in

/-- For singular `η`, the right side of Kelly's prime identity vanishes:
`(NP' / (η))_p = 0` because `(η) = b^p`. -/
theorem kellyPrimeEquality_rhs_eq_zero_of_singular
    {η : 𝓞 K} {b P' : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K))) = 0 := by
  rw [h_eta]
  exact pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero
    (p := p) (K := K) ((P'.absNorm : ℤ) : 𝓞 K) b

/-- For singular `η`, Kelly's prime identity forces the target symbol of
`η^Θ = stickelbergerPrincipalGen η` to vanish. This isolates the exact
Kelly-side output available before the separate λ/primary comparison from
`η^Θ` back to `η`. -/
theorem kellyPrimeEquality_lhs_eq_zero_of_singular
    {η : 𝓞 K} {b P' : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
      (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  rw [h_kelly]
  exact kellyPrimeEquality_rhs_eq_zero_of_singular h_eta

/-- If singular `η` satisfies Kelly away from primes above `p`, then the
target symbol of `η^Θ` vanishes at every nonzero prime. Away from `p` this is
`kellyPrimeEquality_lhs_eq_zero_of_singular`; above `p` it is the canonical
target-prime convention from `kellyPrimeEquality_lhs_eq_zero_of_p_mem`. -/
theorem stickelbergerPrincipalGen_symbol_eq_zero_of_singular_Kelly_awayFromP
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (h_kelly_away : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (p : 𝓞 K) ∉ P' →
        pthSymbolAtIdeal_canonical (p := p) (K := K)
            (stickelbergerPrincipalGen (p := p) (K := K) η) P' =
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({η} : Set (𝓞 K)))) :
    ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) η) P' = 0 := by
  intro P' hP'_prime hP'_ne
  haveI : P'.IsPrime := hP'_prime
  by_cases hp_in : (p : 𝓞 K) ∈ P'
  · exact kellyPrimeEquality_lhs_eq_zero_of_p_mem hP'_ne hp_in
  · exact kellyPrimeEquality_lhs_eq_zero_of_singular h_eta
      (h_kelly_away P' hP'_prime hP'_ne hp_in)

/-! ### Discharge of `SumUnitsValEqZeroHypothesis` for odd p -/

/-- `Σ_{a ∈ (ZMod p)ˣ} (a : ZMod p) = 0` for odd prime p, via `a ↔ -a`. -/
theorem sum_units_coe_eq_zero_of_odd (hp_odd : p ≠ 2) :
    (∑ a : CyclotomicUnitDelta p, ((a : (ZMod p)ˣ) : ZMod p)) = 0 := by
  classical
  set S : ZMod p :=
    ∑ a : CyclotomicUnitDelta p, ((a : (ZMod p)ˣ) : ZMod p) with hS_def
  have h_reindex : S =
      (∑ a : CyclotomicUnitDelta p, (((-a) : (ZMod p)ˣ) : ZMod p)) :=
    (Equiv.sum_comp (Equiv.neg (CyclotomicUnitDelta p))
      (fun a : CyclotomicUnitDelta p => ((a : (ZMod p)ˣ) : ZMod p))).symm
  have h_neg :
      (∑ a : CyclotomicUnitDelta p, (((-a) : (ZMod p)ˣ) : ZMod p)) = -S := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Units.val_neg a
  have h_self_neg : S = -S := h_reindex.trans h_neg
  have h_two_S : S + S = 0 := by
    nth_rewrite 2 [h_self_neg]; ring
  have h_two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hp_prime : p.Prime := Fact.out
    have h2_dvd : p ∣ 2 := by
      have h_eq : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rwa [ZMod.natCast_eq_zero_iff] at h_eq
    rcases (Nat.dvd_prime Nat.prime_two).mp h2_dvd with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · exact hp_odd h
  have h_two_S' : (2 : ZMod p) * S = 0 := by rw [two_mul]; exact h_two_S
  exact mul_left_cancel₀ h_two_ne (h_two_S'.trans (mul_zero _).symm)

/-- **Discharge of `SumUnitsValEqZeroHypothesis` for odd prime p**.

The arithmetic identity `Σ_{a ∈ (ZMod p)ˣ} a.val ≡ 0 (mod p)` holds for
every odd prime, by reducing through `ZMod.natCast_zmod_val` to
`sum_units_coe_eq_zero_of_odd`. -/
theorem sumUnitsValEqZero (hp_odd : p ≠ 2) :
    SumUnitsValEqZeroHypothesis (p := p) := by
  unfold SumUnitsValEqZeroHypothesis
  have hp_prime : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have h_eq :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p)) =
      (∑ a : CyclotomicUnitDelta p, ((a : (ZMod p)ˣ) : ZMod p)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ZMod.natCast_zmod_val ((a : (ZMod p)ˣ) : ZMod p)
  rw [h_eq]
  exact sum_units_coe_eq_zero_of_odd hp_odd

/-! ### K2 for perfect p-th powers `α = β^p`

Both sides of `StickelbergerNormRelation` vanish unconditionally for `α = β^p`:

* **LHS**: `σ_{a⁻¹}(β^p) = (σ_{a⁻¹} β)^p`, and
  `pthSymbolAtPrime_canonical ((σ β)^p) P' = 0` by
  `pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond`.

* **RHS**: `Ideal.span {β^p} = (Ideal.span {β})^p`, and
  `pthSymbolAtIdeal_canonical _ (I^p) = 0` by
  `pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero`.

This is the cleanest non-trivial substantive discharge of K2 — it relies
only on the unconditional p-th-power kill at the leaf level, not on
Stickelberger / Gauss-sum content. -/

/-- **`StickelbergerNormRelation` at `α = β^p`**: holds unconditionally,
both sides equal 0 via the p-th-power kill. -/
theorem StickelbergerNormRelation_pow_p
    (β : 𝓞 K) (P' : Ideal (𝓞 K)) :
    StickelbergerNormRelation (p := p) (K := K) (β ^ p) P' := by
  unfold StickelbergerNormRelation
  -- LHS: each (σ_{a^{-1}} (β^p) / P')_p = ((σ_{a^{-1}} β)^p / P')_p = 0.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (β ^ p)) P') = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (β ^ p) =
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) ^ p from
      map_pow _ β p]
    rw [pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond
      (p := p) (K := K) (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) P',
      mul_zero]
  rw [h_lhs]
  -- RHS: the denominator ideal `(β^p)` is `(β)^p`, so the ideal-side
  -- p-th-power kill applies.
  rw [show (Ideal.span ({β ^ p} : Set (𝓞 K))) =
      (Ideal.span ({β} : Set (𝓞 K))) ^ p from
    (Ideal.span_singleton_pow β p).symm]
  rw [pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero]

/-- **`stickelbergerPrincipalGen (β^p) = (stickelbergerPrincipalGen β)^p`**.
Direct from the definition: `(β^p)^Θ = ∏_a (σ_{a⁻¹}(β^p))^a.val
= ∏_a (σ_{a⁻¹} β)^(p · a.val) = (∏_a (σ_{a⁻¹} β)^a.val)^p = (β^Θ)^p`. -/
theorem stickelbergerPrincipalGen_pow_p (β : 𝓞 K) :
    stickelbergerPrincipalGen (p := p) (K := K) (β ^ p) =
      (stickelbergerPrincipalGen (p := p) (K := K) β) ^ p := by
  unfold stickelbergerPrincipalGen
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (β ^ p) =
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) ^ p from
    map_pow _ β p, ← pow_mul, ← pow_mul, mul_comm]

/-- **Concrete Kelly equality at `α = β^p`**: holds unconditionally.

Both sides equal 0 via the unconditional p-th-power kill:

* **LHS**: `((β^p)^Θ / P')_p = ((β^Θ)^p / P')_p = 0` via
  `pthSymbolAtIdeal_canonical_pow_p_α_eq_zero_uncond`.

* **RHS**: `(NP' / (β^p))_p = (NP' / (β)^p)_p = 0` via
  `pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero`.

This is a direct discharge bypassing K1's coprimality requirement. -/
theorem kellyPrimeEquality_pow_p (β : 𝓞 K) (P' : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (β ^ p)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({β ^ p} : Set (𝓞 K))) := by
  -- LHS: ((β^p)^Θ / P')_p = ((β^Θ)^p / P')_p = 0.
  rw [stickelbergerPrincipalGen_pow_p β]
  rw [pthSymbolAtIdeal_canonical_pow_p_α_eq_zero_uncond
    (stickelbergerPrincipalGen (p := p) (K := K) β) P']
  -- RHS: (NP' / (β^p))_p = (NP' / (β)^p)_p = 0.
  rw [show (Ideal.span ({β ^ p} : Set (𝓞 K))) =
      (Ideal.span ({β} : Set (𝓞 K))) ^ p from
    (Ideal.span_singleton_pow β p).symm]
  rw [pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero]

/-- The concrete Kelly equality at `α = β^p` holds at every nonzero prime. -/
theorem kellyPrimeEquality_all_pow_p (β : 𝓞 K) :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) (β ^ p)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K)
          (Ideal.span ({β ^ p} : Set (𝓞 K))) := by
  intro P' _ _; exact kellyPrimeEquality_pow_p β P'

/-! ### K2 multiplicativity: reducing `α · β^p` to `α`

When `β` is coprime to `P'` at every Galois index, multiplying by `β^p`
contributes 0 to both sides of `StickelbergerNormRelation`:

* **LHS**: `pthSymbolAtPrime_canonical (σ_{a⁻¹}(α · β^p)) P' =
  pthSymbolAtPrime_canonical (σ_{a⁻¹} α) P' +
  pthSymbolAtPrime_canonical ((σ_{a⁻¹} β)^p) P' =
  pthSymbolAtPrime_canonical (σ_{a⁻¹} α) P' + 0` (multiplicativity at q + p-th-power kill).

* **RHS**: `pthSymbolAtIdeal_canonical NP' ((α) · (β)^p) =
  pthSymbolAtIdeal_canonical NP' (α) + 0` (ideal multiplicativity + ideal pow-p kill).

So `K2(α · β^p) ⟺ K2(α)` under the coprimality hypothesis. -/

/-- **K2 multiplicativity for `β^p`**: `StickelbergerNormRelation (α · β^p) P'`
follows from `StickelbergerNormRelation α P'` when `β` is coprime to `P'`
at every Galois index. -/
theorem StickelbergerNormRelation_mul_pow_p
    {α β : 𝓞 K} (hα_ne : α ≠ 0) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} (hP'_ne : P' ≠ ⊥) [P'.IsPrime]
    (hα_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα : StickelbergerNormRelation (p := p) (K := K) α P') :
    StickelbergerNormRelation (p := p) (K := K) (α * β ^ p) P' := by
  unfold StickelbergerNormRelation at hα ⊢
  haveI hP'_max : P'.IsMaximal :=
    (Ideal.IsPrime.isMaximal (inferInstance : P'.IsPrime) hP'_ne)
  -- LHS: ∑_a a.val · (σ_{a⁻¹}(α · β^p) / P')_p = ∑_a a.val · (σ_{a⁻¹} α / P')_p.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β ^ p)) P') =
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hβp_cop :
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) ^ p ∉ P' := fun h =>
      hβ_cop a ((Ideal.IsPrime.mem_of_pow_mem
        (inferInstance : P'.IsPrime) p h))
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β ^ p) =
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α *
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) ^ p from by
      rw [map_mul, map_pow]]
    rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K)
      hP'_ne hP'_max (hα_cop a) hβp_cop]
    rw [pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond
      (p := p) (K := K) (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) P']
    rw [add_zero]
  rw [h_lhs, hα]
  -- RHS: pthSymbolAtIdeal_canonical NP' (α · β^p) = pthSymbolAtIdeal_canonical NP' (α) + 0.
  have hα_span_ne : Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hβp_span_ne : Ideal.span ({β ^ p} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero p hβ_ne
  rw [show (Ideal.span ({α * β ^ p} : Set (𝓞 K))) =
      Ideal.span ({α} : Set (𝓞 K)) * Ideal.span ({β ^ p} : Set (𝓞 K)) from
    (Ideal.span_singleton_mul_span_singleton _ _).symm]
  rw [pthSymbolAtIdeal_canonical_mul_ideal _ hα_span_ne hβp_span_ne]
  rw [show (Ideal.span ({β ^ p} : Set (𝓞 K))) =
      (Ideal.span ({β} : Set (𝓞 K))) ^ p from
    (Ideal.span_singleton_pow β p).symm]
  rw [pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero, add_zero]

/-- **K3 multiplicativity for `β^p`**: the concrete Kelly equality for
`α · β^p` follows from the concrete Kelly equality for `α` under the same
coprimality. -/
theorem kellyPrimeEquality_mul_pow_p
    {α β : 𝓞 K} (hα_ne : α ≠ 0) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hα_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (α * β ^ p)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({α * β ^ p} : Set (𝓞 K))) := by
  -- Discharge via K3: K1 + K2 ⟹ K3, with K2 from multiplicativity.
  refine kellyPrimeEquality_of_StickelbergerNormRelation (α * β ^ p) hP'_ne ?_ ?_
  · -- σ_{a^{-1}} (α · β^p) ∉ P' since each factor is.
    intro a
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β ^ p) =
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α *
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) ^ p from by
      rw [map_mul, map_pow]]
    intro h
    haveI hP'_prime : P'.IsPrime := inferInstance
    rcases hP'_prime.mem_or_mem h with h₁ | h₂
    · exact hα_cop a h₁
    · exact hβ_cop a (hP'_prime.mem_of_pow_mem p h₂)
  · -- StickelbergerNormRelation (α · β^p) P' from multiplicativity.
    -- We need K2(α) first; extract from kellyPrimeEquality α P' via K1+K3.
    -- Actually kellyPrimeEquality α is the conclusion, so derive K2(α) from it
    -- via the K1+K3 reverse: K3 ↔ K1 + K2 (with coprimality). Use the
    -- fact that K1 holds with hα_cop, so K3 ⟺ K2.
    have h_K2_α : StickelbergerNormRelation (p := p) (K := K) α P' := by
      unfold StickelbergerNormRelation
      rw [← pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
        α hP'_ne hα_cop]
      exact hα
    exact StickelbergerNormRelation_mul_pow_p hα_ne hβ_ne hP'_ne hα_cop hβ_cop h_K2_α

/-! ### General K2 multiplicativity

Both sides of `StickelbergerNormRelation` are additive in α (under
appropriate coprimality at every Galois conjugate of α and β with P',
and the per-α coprimality on the RHS factor decomposition). So
`K2(α · β) ⟺ K2(α)` AND `K2(β)` are equivalent under those conditions. -/

/-- **K2 multiplicativity (forward)**: `K2(α · β) ⟸ K2(α)` AND `K2(β)`,
under Galois coprimality of α, β with P', and α, β nonzero. -/
theorem StickelbergerNormRelation_mul
    {α β : 𝓞 K} (hα_ne : α ≠ 0) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hα_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα : StickelbergerNormRelation (p := p) (K := K) α P')
    (hβ : StickelbergerNormRelation (p := p) (K := K) β P') :
    StickelbergerNormRelation (p := p) (K := K) (α * β) P' := by
  unfold StickelbergerNormRelation at hα hβ ⊢
  haveI hP'_max : P'.IsMaximal :=
    (Ideal.IsPrime.isMaximal (inferInstance : P'.IsPrime) hP'_ne)
  -- LHS: split via multiplicativity at each index.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β)) P') =
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') +
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) P') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β) =
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α *
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β from map_mul _ α β]
    rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K)
      hP'_ne hP'_max (hα_cop a) (hβ_cop a)]
    ring
  rw [h_lhs, hα, hβ]
  -- RHS: split via Ideal.span_singleton_mul_span_singleton + ideal multiplicativity.
  have hα_span_ne : Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hβ_span_ne : Ideal.span ({β} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [show (Ideal.span ({α * β} : Set (𝓞 K))) =
      Ideal.span ({α} : Set (𝓞 K)) * Ideal.span ({β} : Set (𝓞 K)) from
    (Ideal.span_singleton_mul_span_singleton _ _).symm]
  rw [pthSymbolAtIdeal_canonical_mul_ideal _ hα_span_ne hβ_span_ne]

/-- **K3 multiplicativity (forward)**: the concrete Kelly equality for
`α · β` follows from the concrete Kelly equalities for `α` and `β`. -/
theorem kellyPrimeEquality_mul
    {α β : 𝓞 K} (hα_ne : α ≠ 0) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hα_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))))
    (hβ :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) β) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({β} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (α * β)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({α * β} : Set (𝓞 K))) := by
  refine kellyPrimeEquality_of_StickelbergerNormRelation (α * β) hP'_ne ?_ ?_
  · -- σ_{a^{-1}} (α · β) ∉ P': product not in prime, so neither factor in.
    intro a
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β) =
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α *
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β from map_mul _ α β]
    intro h
    haveI hP'_prime : P'.IsPrime := inferInstance
    rcases hP'_prime.mem_or_mem h with h₁ | h₂
    · exact hα_cop a h₁
    · exact hβ_cop a h₂
  · -- StickelbergerNormRelation (α · β) P' from multiplicativity.
    have h_K2_α : StickelbergerNormRelation (p := p) (K := K) α P' := by
      unfold StickelbergerNormRelation
      rw [← pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
        α hP'_ne hα_cop]
      exact hα
    have h_K2_β : StickelbergerNormRelation (p := p) (K := K) β P' := by
      unfold StickelbergerNormRelation
      rw [← pthSymbolAtIdeal_canonical_principalGen_at_prime_eq_galois_sum
        β hP'_ne hβ_cop]
      exact hβ
    exact StickelbergerNormRelation_mul hα_ne hβ_ne hP'_ne hα_cop hβ_cop
      h_K2_α h_K2_β

/-! ### Unconditional consumers via _pow_p multiplicativity

Combining the `α = β^p` discharge with multiplicativity by `β^p` gives
unconditional discharges for `α₀ · β^p` whenever `α₀` has a known
the concrete Kelly equality, under coprimality of β.

The most general consumer: for η of the form `α₀ · β^p` where α₀
has a discharged Kelly identity, the full chain produces
the concrete Kelly equality for `α₀ · β^p` at every nonzero prime. -/

/-- **Concrete Kelly equality for `α₀ · β^p` from the equality for `α₀`**:
the multiplicativity discharge, packaged for direct consumption by the
chain. Requires nonzero α₀, β and full Galois coprimality at P'. -/
theorem kellyPrimeEquality_of_mul_pow_p
    {α₀ β : 𝓞 K} (hα₀_ne : α₀ ≠ 0) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hα₀_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α₀ ∉ P')
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα₀ :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α₀) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α₀} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (α₀ * β ^ p)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({α₀ * β ^ p} : Set (𝓞 K))) :=
  kellyPrimeEquality_mul_pow_p hα₀_ne hβ_ne hP'_ne hα₀_cop hβ_cop hα₀

/-- Universal concrete Kelly equality for `α₀ · β^p` from the corresponding
universal equality for `α₀`; requires Galois coprimality of β with every
nonzero prime. -/
theorem kellyPrimeEquality_all_of_mul_pow_p
    {α₀ β : 𝓞 K} (hα₀_ne : α₀ ≠ 0) (hβ_ne : β ≠ 0)
    (hα₀_cop : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α₀ ∉ P')
    (hβ_cop : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    (hα₀ : ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α₀) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α₀} : Set (𝓞 K)))) :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) (α₀ * β ^ p)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K)
          (Ideal.span ({α₀ * β ^ p} : Set (𝓞 K))) := fun P' hP'_inst hP'_ne =>
  kellyPrimeEquality_of_mul_pow_p hα₀_ne hβ_ne hP'_ne
    (hα₀_cop P' hP'_inst hP'_ne)
    (hβ_cop P' hP'_inst hP'_ne)
    (hα₀ P' hP'_ne)

/-! ### Unconditional `_of_odd` consumers (no arithmetic hypothesis needed) -/

/-- **Stickelberger norm relation for Galois-invariant α and odd p**. -/
theorem StickelbergerNormRelation_of_galois_invariant_of_odd
    (hp_odd : p ≠ 2) (α : 𝓞 K) (P' : Ideal (𝓞 K))
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α = α)
    (h_norm_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) = 0) :
    StickelbergerNormRelation (p := p) (K := K) α P' :=
  StickelbergerNormRelation_of_galois_invariant α P' h_inv
    (sumUnitsValEqZero hp_odd) h_norm_zero

/-- **Galois-invariant β symbol vanishing for odd p, no arithmetic hypothesis**. -/
theorem pthSymbolAtPrincipal_canonical_principalGen_galois_invariant_eq_zero_of_odd
    (hp_odd : p ≠ 2)
    (α : 𝓞 K) {β : 𝓞 K} (hβ : β ≠ 0)
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β = β) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α
        (stickelbergerPrincipalGen (p := p) (K := K) β) = 0 :=
  pthSymbolAtPrincipal_canonical_principalGen_galois_invariant_eq_zero
    α hβ h_inv (sumUnitsValEqZero hp_odd)

/-- **Concrete Kelly equality for Galois-invariant α with vanishing integer-norm
symbol — odd `p`, no arithmetic hypothesis**.

Given:
* α Galois-invariant (σ_a α = α for all a),
* α ∉ P' (so each Galois conjugate of α is also outside P'),
* The integer-norm symbol (NP'/α)_p vanishes,

the canonical Kelly identity holds at P'. -/
theorem kellyPrimeEquality_of_galois_invariant_of_odd
    (hp_odd : p ≠ 2)
    (α : 𝓞 K) {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (h_inv : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α = α)
    (h_α_notin : α ∉ P')
    (h_norm_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) = 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  refine kellyPrimeEquality_of_StickelbergerNormRelation α hP'_ne ?_ ?_
  · -- Each Galois conjugate equals α, so the membership condition reduces to α ∉ P'.
    intro a; rw [h_inv a]; exact h_α_notin
  · -- Stickelberger norm relation discharged via _of_galois_invariant_of_odd.
    exact StickelbergerNormRelation_of_galois_invariant_of_odd hp_odd α P' h_inv h_norm_zero

/-! ### Concrete Kelly equality for unit α — special cases -/

end Furtwaengler

end BernoulliRegular

end
