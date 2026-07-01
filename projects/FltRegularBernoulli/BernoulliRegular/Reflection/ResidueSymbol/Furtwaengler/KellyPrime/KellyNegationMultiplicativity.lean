module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KellyPrime.StickelbergerNormRelation

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

/-- **α = -1 has trivial `α^Θ` (up to powers of `-1`)**: in particular,
σ_a(-1) = -1 for every Galois automorphism. -/
theorem cyclotomicRingOfIntegersEquiv_neg_one (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (-1 : 𝓞 K) = -1 := by
  rw [show ((-1 : 𝓞 K)) = -(1 : 𝓞 K) from rfl, map_neg, map_one]

/-- **Concrete Kelly equality at α = -1 for odd `p`**: holds unconditionally.

Both sides equal 0:
* LHS: `((-1)^Θ / P')_p = 0` since `(-1)` is Galois-invariant and the
  Stickelberger generator of `(-1)` reduces to a power of `-1`, whose
  symbol vanishes for odd p.
* RHS: `(NP' / Ideal.span {-1})_p = (NP' / ⊤)_p = 0` since `Ideal.span {-1} = ⊤`. -/
theorem kellyPrimeEquality_neg_one_of_odd
    (hp_odd : p ≠ 2)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (-1 : 𝓞 K)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({(-1 : 𝓞 K)} : Set (𝓞 K))) := by
  refine kellyPrimeEquality_of_galois_invariant_of_odd hp_odd (-1 : 𝓞 K) hP'_ne
    cyclotomicRingOfIntegersEquiv_neg_one ?_ ?_
  · -- -1 ∉ P': if -1 ∈ P', then by closure under negation, 1 ∈ P', so P' = ⊤,
    -- contradicting IsPrime.
    intro h
    have hneg : (1 : 𝓞 K) ∈ P' := by
      have := P'.neg_mem h; simpa using this
    exact (Ideal.IsPrime.one_notMem ‹P'.IsPrime›) hneg
  · -- (NP' / Ideal.span {-1})_p = 0 since Ideal.span {-1} = ⊤.
    rw [show (Ideal.span ({(-1 : 𝓞 K)} : Set (𝓞 K))) = ⊤ from
        Ideal.span_singleton_eq_top.mpr (isUnit_one.neg)]
    exact pthSymbolAtIdeal_canonical_top _

/-- The concrete Kelly equality at `α = -1` holds at every nonzero prime
when `p` is odd. -/
theorem kellyPrimeEquality_all_neg_one_of_odd (hp_odd : p ≠ 2) :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) (-1 : 𝓞 K)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({(-1 : 𝓞 K)} : Set (𝓞 K))) := by
  intro P' hP'_inst hP'_ne
  exact kellyPrimeEquality_neg_one_of_odd (p := p) (K := K) hp_odd hP'_ne

/-- The concrete Kelly equality at `α = 1` holds at every nonzero prime. -/
theorem kellyPrimeEquality_all_one :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) (1 : 𝓞 K)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({(1 : 𝓞 K)} : Set (𝓞 K))) := by
  intro P' _ _; exact kellyPrimeEquality_one P'

/-- The concrete Kelly equality at `α = 0` holds at every nonzero prime. -/
theorem kellyPrimeEquality_all_zero :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) (0 : 𝓞 K)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) := by
  intro P' _ _; exact kellyPrimeEquality_zero P'

/-! ### K2 / K3 negation for odd p

For odd p, `pthSymbolAtPrime_canonical (-α) P' = pthSymbolAtPrime_canonical α P'`
unconditionally — the contribution of `(-1)` vanishes because `(-1) = (-1)^p`
for odd p, and the symbol of any p-th power is 0.

Combined with `Ideal.span {-α} = Ideal.span {α}` (since `-1` is a unit),
this yields `K2(-α) ⟺ K2(α)` and `K3(-α) ⟺ K3(α)` for odd p. -/

/-- **`pthSymbolAtPrime_canonical (-α) P' = pthSymbolAtPrime_canonical α P'`
unconditionally for odd p**. The `(-1)` contribution vanishes via
`(-1) = (-1)^p` (odd p) + `pow_p_eq_zero_uncond`. -/
theorem pthSymbolAtPrime_canonical_neg_uncond_of_odd
    (hp_odd : Odd p) (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (-α) q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  by_cases hbot : q = ⊥
  · subst hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
      pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]
  by_cases hmax : q.IsMaximal
  · haveI hq_prime : q.IsPrime := hmax.isPrime
    by_cases hα : α ∈ q
    · have h_neg_α_in : -α ∈ q := q.neg_mem hα
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax h_neg_α_in,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα]
    · -- α ∉ q. Use pthSymbolAtPrime_canonical_neg + (-1)^p = -1 for odd p.
      rw [pthSymbolAtPrime_canonical_neg hbot hmax hα]
      have h_neg_one_eq : (-1 : 𝓞 K) = ((-1 : 𝓞 K)) ^ p := by
        rw [Odd.neg_one_pow hp_odd]
      rw [show pthSymbolAtPrime_canonical (p := p) (K := K) (-1 : 𝓞 K) q =
          pthSymbolAtPrime_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ p) q from by
        rw [← h_neg_one_eq]]
      rw [pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond, add_zero]
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax,
      pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax]

/-- **K2 negation invariance for odd p**: `K2(-α) ⟺ K2(α)`. -/
theorem StickelbergerNormRelation_neg_iff_of_odd
    (hp_odd : Odd p) (α : 𝓞 K) (P' : Ideal (𝓞 K)) :
    StickelbergerNormRelation (p := p) (K := K) (-α) P' ↔
      StickelbergerNormRelation (p := p) (K := K) α P' := by
  unfold StickelbergerNormRelation
  -- LHS sum: each term σ_{a⁻¹}(-α) ↦ -σ_{a⁻¹}(α), and pthSymbolAtPrime_canonical
  -- (-x) P' = pthSymbolAtPrime_canonical x P' for odd p.
  have h_lhs :
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (-α)) P') =
      (∑ a : CyclotomicUnitDelta p, ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P') := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (-α) =
        -(cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) from
      map_neg _ α]
    rw [pthSymbolAtPrime_canonical_neg_uncond_of_odd hp_odd
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) P']
  rw [h_lhs]
  -- RHS: Ideal.span {-α} = Ideal.span {α} (since -1 is a unit).
  rw [show (Ideal.span ({-α} : Set (𝓞 K))) = Ideal.span ({α} : Set (𝓞 K)) from by
    rw [show (-α : 𝓞 K) = (-1 : 𝓞 K) * α from by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_one.neg α]

/-- **K2 negation discharge for odd p**: `K2(-α) ⟸ K2(α)`. -/
theorem StickelbergerNormRelation_neg_of_odd
    (hp_odd : Odd p) {α : 𝓞 K} {P' : Ideal (𝓞 K)}
    (hα : StickelbergerNormRelation (p := p) (K := K) α P') :
    StickelbergerNormRelation (p := p) (K := K) (-α) P' :=
  (StickelbergerNormRelation_neg_iff_of_odd hp_odd α P').mpr hα

/-- **`pthSymbolAtIdeal_canonical ((-1)^c · α) I = pthSymbolAtIdeal_canonical α I`
unconditionally for odd p**. By induction on `c`, peeling off one `(-1)` factor
each step via `_neg_uncond_of_odd`. -/
theorem pthSymbolAtIdeal_canonical_neg_pow_mul_uncond_of_odd
    (hp_odd : Odd p) (c : ℕ) (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ c * α) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  induction c with
  | zero =>
    rw [pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ, mul_assoc, show (-1 : 𝓞 K) * α = -α from by ring]
    rw [show ((-1 : 𝓞 K) ^ k * (-α)) = -((-1 : 𝓞 K) ^ k * α) from by ring]
    rw [pthSymbolAtIdeal_canonical_neg_uncond_of_odd hp_odd _ I]
    exact ih

/-- **K3 negation invariance for odd p**: `K3(-α) ⟺ K3(α)`. -/
theorem kellyPrimeEquality_neg_iff_of_odd
    (hp_odd : Odd p) (α : 𝓞 K) (P' : Ideal (𝓞 K)) :
    (pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (-α)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({-α} : Set (𝓞 K)))) ↔
      (pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) := by
  -- LHS: stickelbergerPrincipalGen (-α) = (-1)^c · stickelbergerPrincipalGen α.
  have h_neg_Θ :
      stickelbergerPrincipalGen (p := p) (K := K) (-α) =
        ((-1 : 𝓞 K) ^ (∑ a : CyclotomicUnitDelta p, (a : ZMod p).val)) *
          stickelbergerPrincipalGen (p := p) (K := K) α := by
    unfold stickelbergerPrincipalGen
    -- (-1)^(∑ a.val) · ∏_a (σ_{a⁻¹} α)^a.val = ∏_a ((-1) · σ_{a⁻¹} α)^a.val
    --                                       = ∏_a (σ_{a⁻¹} (-α))^a.val
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (-α) =
        -(cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) from map_neg _ α]
    rw [show -(cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) =
        (-1) * cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α from by ring]
    rw [mul_pow]
  rw [h_neg_Θ,
    pthSymbolAtIdeal_canonical_neg_pow_mul_uncond_of_odd hp_odd _ _ P']
  -- RHS: Ideal.span {-α} = Ideal.span {α} (since -1 is a unit).
  rw [show (Ideal.span ({-α} : Set (𝓞 K))) = Ideal.span ({α} : Set (𝓞 K)) from by
    rw [show (-α : 𝓞 K) = (-1 : 𝓞 K) * α from by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_one.neg α]

/-- **K3 negation discharge for odd p**: `K3(-α) ⟸ K3(α)`. -/
theorem kellyPrimeEquality_neg_of_odd
    (hp_odd : Odd p) {α : 𝓞 K} {P' : Ideal (𝓞 K)}
    (hα :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) (-α)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({-α} : Set (𝓞 K))) :=
  (kellyPrimeEquality_neg_iff_of_odd hp_odd α P').mpr hα

/-! ### Unconditional discharge for `-β^p` (odd p) -/

/-- **Concrete Kelly equality for `-β^p` (odd p)**: unconditional except for
Galois coprimality of β. The case α₀ = -1 of `kellyPrimeEquality_of_mul_pow_p`,
using `kellyPrimeEquality_neg_one_of_odd` as the α₀-side discharge. -/
theorem kellyPrimeEquality_neg_pow_p_of_odd
    (hp_odd : p ≠ 2) (β : 𝓞 K) (hβ_ne : β ≠ 0)
    {P' : Ideal (𝓞 K)} [P'.IsPrime] (hP'_ne : P' ≠ ⊥)
    (hβ_cop : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) ((-1 : 𝓞 K) * β ^ p)) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K)
        (Ideal.span ({(-1 : 𝓞 K) * β ^ p} : Set (𝓞 K))) := by
  refine kellyPrimeEquality_of_mul_pow_p ?_ hβ_ne hP'_ne ?_ hβ_cop
    (kellyPrimeEquality_neg_one_of_odd hp_odd hP'_ne)
  · -- -1 ≠ 0
    exact neg_ne_zero.mpr one_ne_zero
  · -- σ_{a⁻¹}(-1) = -1 ∉ P' (-1 is a unit)
    intro a
    rw [cyclotomicRingOfIntegersEquiv_neg_one a]
    intro h
    have hneg : (1 : 𝓞 K) ∈ P' := by
      have := P'.neg_mem h; simpa using this
    exact (Ideal.IsPrime.one_notMem inferInstance) hneg

/-- Universal concrete Kelly equality for `-β^p` when `p` is odd, under
Galois coprimality of β. -/
theorem kellyPrimeEquality_all_neg_pow_p_of_odd
    (hp_odd : p ≠ 2) (β : 𝓞 K) (hβ_ne : β ≠ 0)
    (hβ_cop : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P') :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) ((-1 : 𝓞 K) * β ^ p)) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K)
          (Ideal.span ({(-1 : 𝓞 K) * β ^ p} : Set (𝓞 K))) := by
  intro P' hP'_inst hP'_ne
  exact kellyPrimeEquality_neg_pow_p_of_odd hp_odd β hβ_ne hP'_ne
      (hβ_cop P' hP'_inst hP'_ne)

/-! ### `KellyIdealIdentity` for non-bot B (special α discharges) -/

/-- **`KellyIdealIdentity 1 B`** for `B ≠ ⊥`: from the universal equality at `1`
via the multiplicative ideal extension. -/
theorem KellyIdealIdentity_one_of_ne_bot {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    KellyIdealIdentity (p := p) (K := K) (1 : 𝓞 K) B :=
  KellyIdealIdentity_of_kellyPrimeEquality_all kellyPrimeEquality_all_one hB

/-- **`KellyIdealIdentity (-1) B`** for `B ≠ ⊥` and odd p. -/
theorem KellyIdealIdentity_neg_one_of_odd_of_ne_bot
    (hp_odd : p ≠ 2) {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    KellyIdealIdentity (p := p) (K := K) (-1 : 𝓞 K) B :=
  KellyIdealIdentity_of_kellyPrimeEquality_all
    (kellyPrimeEquality_all_neg_one_of_odd hp_odd) hB

/-- **`KellyIdealIdentity (β^p) B`** for `B ≠ ⊥`. -/
theorem KellyIdealIdentity_pow_p_of_ne_bot
    (β : 𝓞 K) {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    KellyIdealIdentity (p := p) (K := K) (β ^ p) B :=
  KellyIdealIdentity_of_kellyPrimeEquality_all
    (kellyPrimeEquality_all_pow_p β) hB

/-- **`KellyIdealIdentity (-β^p) B`** for `B ≠ ⊥` and odd p, under
Galois coprimality of β with every prime. -/
theorem KellyIdealIdentity_neg_pow_p_of_odd_of_ne_bot
    (hp_odd : p ≠ 2) (β : 𝓞 K) (hβ_ne : β ≠ 0)
    (hβ_cop : ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β ∉ P')
    {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) :
    KellyIdealIdentity (p := p) (K := K) ((-1 : 𝓞 K) * β ^ p) B :=
  KellyIdealIdentity_of_kellyPrimeEquality_all
    (kellyPrimeEquality_all_neg_pow_p_of_odd hp_odd β hβ_ne hβ_cop) hB

end Furtwaengler

end BernoulliRegular

end
