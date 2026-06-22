module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolNoncanonical
public import BernoulliRegular.FLT37.Primary
public import BernoulliRegular.UnitQuotient.DeltaAction


/-!
# Cyclotomic ideal-action support

This file contains the reusable algebraic infrastructure for cyclotomic
Galois actions on ideals and residue-symbol power identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]

/-! ### Auxiliary algebraic lemmas (engine for c.4) -/

/-- The symbol vanishes at `1`. Follows from multiplicativity:
`s(1·1) = s(1) + s(1)` forces `s(1) = 0`. -/
theorem pthSymbolAtPrime_one {K : Type*} [Field K] [NumberField K]
    {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) :
    pthSymbolAtPrime (p := p) (1 : 𝓞 K) q = 0 := by
  haveI hqp : q.IsPrime := hmax.isPrime
  have h1 : (1 : 𝓞 K) ∉ q := hqp.one_notMem
  have h := pthSymbolAtPrime_mul (p := p) (α := (1 : 𝓞 K)) (β := 1)
    hbot hmax h1 h1
  rw [one_mul] at h
  -- `h : s = s + s` in `ZMod p`; subtract `s` from both sides.
  linear_combination -h

/-- The symbol of `α^n` is `n · symbol α q` in `ZMod p`. By induction
using `pthSymbolAtPrime_mul`. -/
theorem pthSymbolAtPrime_pow {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) (n : ℕ) :
    pthSymbolAtPrime (p := p) (α ^ n) q =
      (n : ZMod p) * pthSymbolAtPrime (p := p) α q := by
  haveI hqp : q.IsPrime := hmax.isPrime
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact pthSymbolAtPrime_one (p := p) hbot hmax
  | succ k ih =>
    have hpow : α ^ k ∉ q := fun h => hα (hqp.mem_of_pow_mem k h)
    rw [pow_succ, pthSymbolAtPrime_mul (p := p) hbot hmax hpow hα, ih]
    push_cast; ring

/-- **Vanishing engine for hyperprimary reciprocity.** The symbol of any
`p`-th-power input is `0` in `ZMod p`, since `(p : ZMod p) = 0`. This is
the algebraic identity that lets hyperprimary kill the λ-correction in
the c.4 symmetric assembly. -/
theorem pthSymbolAtPrime_pow_p_eq_zero {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) :
    pthSymbolAtPrime (p := p) (α ^ p) q = 0 := by
  rw [pthSymbolAtPrime_pow (p := p) hbot hmax hα p, ZMod.natCast_self, zero_mul]

/-! ### Ideal-symbol versions -/

/-- The ideal-level symbol of `α^n` equals `n · (α/I)_p`. Reduces to the
prime-level statement term-by-term over the prime factorization of `I`. -/
theorem pthSymbolAtIdeal_pow {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (n : ℕ) :
    pthSymbolAtIdeal (p := p) (α ^ n) I =
      (n : ZMod p) * pthSymbolAtIdeal (p := p) α I := by
  unfold pthSymbolAtIdeal
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime (p := p) (α ^ n) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => (n : ZMod p) * pthSymbolAtPrime (p := p) α P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_pow (p := p) hP_ne_bot hP_max (hα P hP) n
  rw [hmap, Multiset.sum_map_mul_left]

/-- **Vanishing engine, ideal version.** The ideal-level symbol of any
`p`-th-power input is `0`. -/
theorem pthSymbolAtIdeal_pow_p_eq_zero {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P) :
    pthSymbolAtIdeal (p := p) (α ^ p) I = 0 := by
  rw [pthSymbolAtIdeal_pow (p := p) hα p, ZMod.natCast_self, zero_mul]

/-- **The symbol of `1` at any ideal is `0`**. Each prime factor of `I`
is maximal and non-zero, so `pthSymbolAtPrime 1 P = 0` term-by-term. -/
@[simp] theorem pthSymbolAtIdeal_one_alpha {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal (p := p) (1 : 𝓞 K) I = 0 := by
  unfold pthSymbolAtIdeal
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime (p := p) (1 : 𝓞 K) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from ?_]
  · simp
  · refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_one (p := p) hP_ne_bot hP_max

/-- **The symbol of `0` at any ideal is `0`**. For non-trivial primes,
`0 ∈ P` so `pthSymbolAtPrime 0 P = 0`; for `I = ⊥`, the sum is empty. -/
@[simp] theorem pthSymbolAtIdeal_zero_alpha {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal (p := p) (0 : 𝓞 K) I = 0 := by
  unfold pthSymbolAtIdeal
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime (p := p) (0 : 𝓞 K) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from ?_]
  · simp
  · refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_eq_zero_of_mem (p := p) hP_ne_bot hP_max P.zero_mem

/-! ### Principal-symbol versions

Basic principal-symbol API (`_one`, `_mul_left`, `_mul_right`) appears above.
Here we add the power lemmas used by denominator descent.
-/

/-- The principal symbol with α = 1 vanishes at any β. -/
@[simp] theorem pthSymbolAtPrincipal_one_left {K : Type*}
    [Field K] [NumberField K] (β : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) (1 : 𝓞 K) β = 0 :=
  pthSymbolAtIdeal_one_alpha _

/-- The principal symbol with α = 0 vanishes at any β. -/
@[simp] theorem pthSymbolAtPrincipal_zero_left {K : Type*}
    [Field K] [NumberField K] (β : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) (0 : 𝓞 K) β = 0 :=
  pthSymbolAtIdeal_zero_alpha _

/-- **Principal symbol pow in the denominator**: `(α / β^n)_p = n · (α/β)_p`. -/
theorem pthSymbolAtPrincipal_pow_right {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) (n : ℕ) :
    pthSymbolAtPrincipal (p := p) α (β ^ n) =
      (n : ZMod p) * pthSymbolAtPrincipal (p := p) α β := by
  unfold pthSymbolAtPrincipal
  rw [show (Ideal.span ({β ^ n} : Set (𝓞 K))) =
        (Ideal.span ({β} : Set (𝓞 K))) ^ n from
        (Ideal.span_singleton_pow β n).symm]
  exact pthSymbolAtIdeal_pow_ideal α (Ideal.span ({β} : Set (𝓞 K))) n

/-- **The principal symbol with a unit denominator vanishes**:
`(α / ε)_p = 0` for any unit `ε`. (`Ideal.span {ε} = ⊤`.) -/
@[simp] theorem pthSymbolAtPrincipal_isUnit_right {K : Type*}
    [Field K] [NumberField K] {ε : 𝓞 K} (α : 𝓞 K) (hε : IsUnit ε) :
    pthSymbolAtPrincipal (p := p) α ε = 0 := by
  unfold pthSymbolAtPrincipal
  rw [show (Ideal.span ({ε} : Set (𝓞 K))) = ⊤ from
        Ideal.span_singleton_eq_top.mpr hε]
  exact pthSymbolAtIdeal_top _

/-- **Vanishing engine in the denominator slot.** The principal symbol
with a `p`-th-power denominator vanishes: `(α / β^p)_p = 0`. -/
theorem pthSymbolAtPrincipal_pow_p_right_eq_zero {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α (β ^ p) = 0 := by
  rw [pthSymbolAtPrincipal_pow_right α β p, ZMod.natCast_self, zero_mul]

/-- **Self-pow vanishing**: `(α / α^n)_p = 0`. From `_pow_right` and
the self-symbol vanishing. -/
@[simp] theorem pthSymbolAtPrincipal_self_pow {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) (n : ℕ) :
    pthSymbolAtPrincipal (p := p) α (α ^ n) = 0 := by
  rw [pthSymbolAtPrincipal_pow_right α α n, pthSymbolAtPrincipal_self_eq_zero,
      mul_zero]

/-- The principal symbol is invariant under negation in the denominator. -/
@[simp] theorem pthSymbolAtPrincipal_neg_right {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α (-β) = pthSymbolAtPrincipal (p := p) α β := by
  unfold pthSymbolAtPrincipal
  congr 1
  exact Ideal.span_singleton_neg β

/-- The principal symbol depends on the denominator only up to associativity:
multiplying by a unit doesn't change it. -/
theorem pthSymbolAtPrincipal_mul_unit_right {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) {ε : 𝓞 K} (hε : IsUnit ε) :
    pthSymbolAtPrincipal (p := p) α (β * ε) = pthSymbolAtPrincipal (p := p) α β := by
  unfold pthSymbolAtPrincipal
  congr 1
  rw [Ideal.span_singleton_eq_span_singleton]
  exact Associated.symm ⟨hε.unit, rfl⟩

/-- **Self-mul-unit vanishing**: `(α / α · ε)_p = 0` for ε a unit. -/
@[simp] theorem pthSymbolAtPrincipal_self_mul_unit {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) {ε : 𝓞 K} (hε : IsUnit ε) :
    pthSymbolAtPrincipal (p := p) α (α * ε) = 0 := by
  rw [pthSymbolAtPrincipal_mul_unit_right α α hε]
  exact pthSymbolAtPrincipal_self_eq_zero α

/-- A unit is not in any prime ideal of `𝓞 K` (those that arise as
factors of a non-trivial principal ideal). -/
theorem unit_notMem_normalizedFactors {K : Type*}
    [Field K] [NumberField K] {ε : 𝓞 K} (hε : IsUnit ε) (β : 𝓞 K)
    (P : Ideal (𝓞 K))
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K)))) :
    ε ∉ P := by
  obtain ⟨_, _, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  intro h
  exact hP_max.ne_top (P.eq_top_of_isUnit_mem h hε)

/-- If `x ∉ P` for every prime factor `P` of `(β)`, then `x^n ∉ P` for
every such `P`. -/
theorem pow_notMem_normalizedFactors {K : Type*}
    [Field K] [NumberField K] {x : 𝓞 K}
    (β : 𝓞 K)
    (hx : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), x ∉ P)
    (n : ℕ) :
    ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), x ^ n ∉ P := by
  intro P hP h_pow_mem
  obtain ⟨hP_prime, _, _⟩ := isPrime_of_mem_normalizedFactors hP
  haveI := hP_prime
  exact hx P hP (hP_prime.mem_of_pow_mem n h_pow_mem)

/-- **Self-mul-pow-p vanishing**: `(α / α · γ^p)_p = 0` for any α, γ ≠ 0. -/
@[simp] theorem pthSymbolAtPrincipal_self_mul_pow_p {K : Type*}
    [Field K] [NumberField K] {α : 𝓞 K} (hα : α ≠ 0) {γ : 𝓞 K} (hγ : γ ≠ 0) :
    pthSymbolAtPrincipal (p := p) α (α * γ ^ p) = 0 := by
  unfold pthSymbolAtPrincipal
  rw [show Ideal.span ({α * γ ^ p} : Set (𝓞 K)) =
      Ideal.span ({α} : Set (𝓞 K)) * Ideal.span ({γ ^ p} : Set (𝓞 K)) from
        (Ideal.span_singleton_mul_span_singleton _ _).symm]
  rw [pthSymbolAtIdeal_mul_ideal _
        (by rwa [Ne, Ideal.span_singleton_eq_bot])
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero p hγ)]
  -- LHS = pthSymbolAtIdeal α (span α) + pthSymbolAtIdeal α (span γ^p) = 0 + 0
  rw [show Ideal.span ({γ ^ p} : Set (𝓞 K)) =
      (Ideal.span ({γ} : Set (𝓞 K))) ^ p from
        (Ideal.span_singleton_pow γ p).symm,
      pthSymbolAtIdeal_pow_ideal _ _ p]
  rw [show pthSymbolAtIdeal (p := p) α (Ideal.span ({α} : Set (𝓞 K))) = 0 from
        (pthSymbolAtPrincipal_self_eq_zero α)]
  simp

/-- **Pow-p-mul-self vanishing (commuted form)**: `(α / γ^p · α)_p = 0`. -/
@[simp] theorem pthSymbolAtPrincipal_pow_p_mul_self {K : Type*}
    [Field K] [NumberField K] {α : 𝓞 K} (hα : α ≠ 0) {γ : 𝓞 K} (hγ : γ ≠ 0) :
    pthSymbolAtPrincipal (p := p) α (γ ^ p * α) = 0 := by
  rw [mul_comm]
  exact pthSymbolAtPrincipal_self_mul_pow_p hα hγ

/-- **For a prime ideal, the ideal-symbol equals the prime-symbol**:
`pthSymbolAtIdeal α P = pthSymbolAtPrime α P` when `P` is a maximal
non-zero (hence irreducible) ideal. -/
theorem pthSymbolAtIdeal_prime_eq_pthSymbolAtPrime {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) {P : Ideal (𝓞 K)}
    (hP_max : P.IsMaximal) (hP_ne : P ≠ ⊥) :
    pthSymbolAtIdeal (p := p) α P = pthSymbolAtPrime (p := p) α P := by
  unfold pthSymbolAtIdeal
  -- normalizedFactors P = {P} since P is irreducible.
  haveI : P.IsPrime := hP_max.isPrime
  have hP_irred : Irreducible P :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      (Ideal.prime_of_isPrime hP_ne hP_max.isPrime)
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP_irred]
  -- normalize P = P (the only unit in Ideal is ⊤, so normalize is identity
  -- for non-top ideals).
  rw [show normalize P = P from normalize_eq P]
  simp

/-- The principal-symbol of `α^n` equals `n · (α/β)_p`. -/
theorem pthSymbolAtPrincipal_pow_left {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) (n : ℕ)
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({β} : Set (𝓞 K))), α ∉ P) :
    pthSymbolAtPrincipal (p := p) (α ^ n) β =
      (n : ZMod p) * pthSymbolAtPrincipal (p := p) α β := by
  unfold pthSymbolAtPrincipal
  exact pthSymbolAtIdeal_pow (p := p) hα n

/-- **Vanishing engine, principal version.** The principal-symbol of any
`p`-th-power input is `0`. -/
theorem pthSymbolAtPrincipal_pow_p_left_eq_zero {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K)
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({β} : Set (𝓞 K))), α ∉ P) :
    pthSymbolAtPrincipal (p := p) (α ^ p) β = 0 := by
  rw [pthSymbolAtPrincipal_pow_left (p := p) α β p hα, ZMod.natCast_self,
    zero_mul]

/-! ### c.1.0 — Galois conjugate of an ideal of `𝓞 K`

The cyclotomic Galois group `Gal(K/ℚ)` acts on `𝓞 K` via
`cyclotomicRingOfIntegersEquiv`. This lifts to an action on `Ideal (𝓞 K)`
by the standard `Ideal.map`. For each `a ∈ (ZMod p)ˣ`, the conjugate
`σ_a · q` is itself a prime ideal lying above the same rational prime as
`q`. This sets up the indexing of the Galois orbit of a prime needed to
state the Stickelberger ideal theorem (c.1).
-/

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The Galois conjugate of an ideal of `𝓞 K` indexed by `a ∈ (ZMod p)ˣ`,
defined as the image under the corresponding `cyclotomicRingOfIntegersEquiv`. -/
noncomputable def cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.map (cyclotomicRingOfIntegersEquiv (p := p) K a) q

/-- The Galois conjugate at the identity is the original ideal. -/
@[simp] theorem cyclotomicGaloisConjugate_one (q : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) 1 q = q := by
  unfold cyclotomicGaloisConjugate
  apply Ideal.ext
  intro x
  rw [Ideal.mem_map_of_equiv]
  refine ⟨?_, fun hx => ⟨x, hx, ?_⟩⟩
  · rintro ⟨y, hy, hxy⟩
    rw [cyclotomicRingOfIntegersEquiv_one_apply (p := p) (K := K) y] at hxy
    exact hxy ▸ hy
  · exact cyclotomicRingOfIntegersEquiv_one_apply (p := p) (K := K) x

/-- The Galois conjugate is multiplicative in the index: `(ab) · q = a · (b · q)`. -/
theorem cyclotomicGaloisConjugate_mul
    (a b : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) (a * b) q =
      cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) b q) := by
  unfold cyclotomicGaloisConjugate
  apply Ideal.ext
  intro x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_map_of_equiv]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨cyclotomicRingOfIntegersEquiv (p := p) K b y, ?_, ?_⟩
    · rw [Ideal.mem_map_of_equiv]; exact ⟨y, hy, rfl⟩
    · exact (cyclotomicRingOfIntegersEquiv_mul_apply
        (p := p) (K := K) a b y).symm
  · rintro ⟨z, hz, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy,
      cyclotomicRingOfIntegersEquiv_mul_apply (p := p) (K := K) a b y⟩

/-- The Galois conjugate of a prime ideal is prime. -/
instance cyclotomicGaloisConjugate_isPrime
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) [q.IsPrime] :
    (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsPrime := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_isPrime_of_equiv (cyclotomicRingOfIntegersEquiv (p := p) K a)

/-- The Galois conjugate of `⊥` is `⊥`. -/
@[simp] theorem cyclotomicGaloisConjugate_bot (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (⊥ : Ideal (𝓞 K)) = ⊥ := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_bot

/-- The Galois conjugate of `⊤` is `⊤`. -/
@[simp] theorem cyclotomicGaloisConjugate_top (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (⊤ : Ideal (𝓞 K)) = ⊤ := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_top _

/-- The Galois conjugate of a maximal ideal is maximal. -/
instance cyclotomicGaloisConjugate_isMaximal
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) [hq : q.IsMaximal] :
    (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_isMaximal_of_equiv (cyclotomicRingOfIntegersEquiv (p := p) K a)

/-- The Galois conjugate of a non-`⊥` ideal is non-`⊥`. -/
theorem cyclotomicGaloisConjugate_ne_bot
    (a : CyclotomicUnitDelta p) {q : Ideal (𝓞 K)} (hq : q ≠ ⊥) :
    cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ := by
  intro hbot
  apply hq
  have h := cyclotomicGaloisConjugate_mul (p := p) (K := K) a⁻¹ a q
  rw [inv_mul_cancel, cyclotomicGaloisConjugate_one] at h
  rw [h, hbot]
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_bot

/-- The Galois conjugate lies above the same rational prime as `q`. This is
the key compatibility for indexing primes above a rational prime by
elements of `(ZMod p)ˣ`. -/
theorem cyclotomicGaloisConjugate_under_eq
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a q).under ℤ =
      q.under ℤ := by
  -- Translate `Ideal.map σ q = Ideal.comap σ.symm q`, then merge nested
  -- `comap`s via `Ideal.comap_comap`. The composite ring hom
  -- `σ.symm.comp (algebraMap ℤ (𝓞 K))` equals `algebraMap ℤ (𝓞 K)` by
  -- uniqueness of `ℤ`-ring homomorphisms (`RingHom.ext_int`).
  unfold cyclotomicGaloisConjugate Ideal.under
  -- Any two ring homs `ℤ → 𝓞 K` agree (`RingHom.ext_int`), so for any
  -- `n : ℤ`, `σ (algebraMap n) = algebraMap n`. From this the membership
  -- condition is equivalent on both sides.
  have h_fix : ∀ n : ℤ,
      cyclotomicRingOfIntegersEquiv (p := p) K a (algebraMap ℤ (𝓞 K) n) =
        algebraMap ℤ (𝓞 K) n := by
    intro n
    have heq : ((cyclotomicRingOfIntegersEquiv (p := p) K a) :
        𝓞 K →+* 𝓞 K).comp (algebraMap ℤ (𝓞 K)) =
          (algebraMap ℤ (𝓞 K)) := RingHom.ext_int _ _
    exact DFunLike.congr_fun heq n
  apply Ideal.ext
  intro n
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_map_of_equiv]
  refine ⟨?_, fun hn => ⟨algebraMap ℤ (𝓞 K) n, hn, h_fix n⟩⟩
  rintro ⟨y, hy, hxy⟩
  -- `hxy : σ y = algebraMap n`, σ injective, σ (algebraMap n) = algebraMap n,
  -- so y = algebraMap n; then hy gives the goal.
  have hsy : y = algebraMap ℤ (𝓞 K) n :=
    (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (hxy.trans (h_fix n).symm)
  exact hsy ▸ hy

/-- The Galois action of `(ZMod p)ˣ` on `Ideal (𝓞 K)` via the cyclotomic
Galois group. -/
noncomputable instance : MulAction (CyclotomicUnitDelta p) (Ideal (𝓞 K)) where
  smul a := cyclotomicGaloisConjugate (p := p) (K := K) a
  one_smul := cyclotomicGaloisConjugate_one
  mul_smul := cyclotomicGaloisConjugate_mul

@[simp] theorem cyclotomicMulAction_smul_def
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    a • q = cyclotomicGaloisConjugate (p := p) (K := K) a q := rfl

section FrobeniusFiber

open scoped Pointwise

/-- A cyclotomic conjugate fixes a prime above `ℓ` exactly when its
`(ZMod p)ˣ` index lies in the subgroup generated by the Frobenius class
`ℓ mod p`.

This is the non-split decomposition-group form: the right side is a
`Subgroup.zpowers`, so repeated conjugates are kept as a Frobenius orbit
instead of being forced to be distinct. -/
theorem cyclotomicGaloisConjugate_eq_self_iff_mem_frobenius_zpowers
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓp : ℓ.Coprime p) (c : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) c P = P ↔
      c ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) := by
  have hstab :
      (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) =
        Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) :=
    IsCyclotomicExtension.Rat.galEquivZMod_stabilizer
      (n := p) (K := K) (p := ℓ) (P := P) hℓp
  constructor
  · intro hc
    rw [← hstab, MulEquiv.mapSubgroup_apply, Subgroup.mem_map]
    refine ⟨cyclotomicSigmaOfUnit (p := p) K c, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      change cyclotomicGaloisConjugate (p := p) (K := K) c P = P
      exact hc
    · simpa [cyclotomicGalEquivZMod] using
        cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) c
  · intro hc
    have hc' :
        c ∈ (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := by
      rwa [hstab]
    rw [MulEquiv.mapSubgroup_apply, Subgroup.mem_map] at hc'
    obtain ⟨σ, hσ, hσc⟩ := hc'
    have hσ_eq : σ = cyclotomicSigmaOfUnit (p := p) K c := by
      rw [cyclotomicSigmaOfUnit, ← hσc]
      exact ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm_apply_apply σ).symm
    rw [hσ_eq] at hσ
    rw [MulAction.mem_stabilizer_iff] at hσ
    change cyclotomicGaloisConjugate (p := p) (K := K) c P = P at hσ
    exact hσ

/-- **Cyclotomic Frobenius fiber theorem.** For a prime `P` of
`𝓞 K` above `ℓ`, the fiber of `b ↦ σ_{b⁻¹} P` over `σ_{a⁻¹} P` is
the Frobenius/decomposition coset generated by `ℓ mod p`.

No residue-degree-one hypothesis appears: if `ℓ` has residue degree
`f > 1`, then the `Subgroup.zpowers` condition records exactly the
collapsed Frobenius orbit, and the Stickelberger product must count the
resulting repeated factors with multiplicity. -/
theorem cyclotomicGaloisConjugate_inv_eq_inv_iff_mul_mem_frobenius_zpowers
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ))]
    (hℓp : ℓ.Coprime p) (a b : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ P =
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ↔
      a * b⁻¹ ∈ Subgroup.zpowers (ZMod.unitOfCoprime ℓ hℓp) := by
  rw [← cyclotomicGaloisConjugate_eq_self_iff_mem_frobenius_zpowers
    (p := p) (K := K) P hℓp (a * b⁻¹)]
  constructor
  · intro h
    have h' := congrArg
      (fun I : Ideal (𝓞 K) =>
        cyclotomicGaloisConjugate (p := p) (K := K) a I) h
    change cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ P) =
      cyclotomicGaloisConjugate (p := p) (K := K) a
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P) at h'
    rw [← cyclotomicGaloisConjugate_mul,
      ← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one] at h'
    exact h'
  · intro h
    have h' := congrArg
      (fun I : Ideal (𝓞 K) =>
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ I) h
    change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        (cyclotomicGaloisConjugate (p := p) (K := K) (a * b⁻¹) P) =
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P at h'
    rw [← cyclotomicGaloisConjugate_mul] at h'
    have hmul : a⁻¹ * (a * b⁻¹) = b⁻¹ := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hmul] at h'
    exact h'

end FrobeniusFiber

/-- The action distributes over ideal multiplication. -/
theorem cyclotomicGaloisConjugate_mul_ideal
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (I * J) =
      cyclotomicGaloisConjugate (p := p) (K := K) a I *
        cyclotomicGaloisConjugate (p := p) (K := K) a J := by
  unfold cyclotomicGaloisConjugate
  exact Ideal.map_mul _ I J

/-- The Galois conjugate is monotone in the ideal (preserves ≤). -/
theorem cyclotomicGaloisConjugate_le_iff
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    cyclotomicGaloisConjugate (p := p) (K := K) a I ≤
        cyclotomicGaloisConjugate (p := p) (K := K) a J ↔ I ≤ J := by
  refine ⟨?_, ?_⟩
  · intro h
    -- Apply σ_a⁻¹ to both sides, gets back to I ≤ J.
    have hh := h
    have h1 : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        (cyclotomicGaloisConjugate (p := p) (K := K) a I) = I := by
      rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
        cyclotomicGaloisConjugate_one]
    have h2 : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        (cyclotomicGaloisConjugate (p := p) (K := K) a J) = J := by
      rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
        cyclotomicGaloisConjugate_one]
    rw [← h1, ← h2]
    exact Ideal.map_mono h
  · intro h
    unfold cyclotomicGaloisConjugate
    exact Ideal.map_mono h

/-- The action commutes with ideal powers. -/
theorem cyclotomicGaloisConjugate_pow_ideal
    (a : CyclotomicUnitDelta p) (I : Ideal (𝓞 K)) (n : ℕ) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (I ^ n) =
      cyclotomicGaloisConjugate (p := p) (K := K) a I ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, cyclotomicGaloisConjugate_mul_ideal, ih]

/-! ### c.1.1 — Galois orbit of a prime ideal -/

/-- The set of Galois conjugates of `q` under the cyclotomic action
indexed by `(ZMod p)ˣ`. Always finite (image of a finite set). -/
noncomputable def cyclotomicConjugates (q : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K)) :=
  haveI : DecidableEq (Ideal (𝓞 K)) := Classical.decEq _
  (Finset.univ : Finset (CyclotomicUnitDelta p)).image
    (fun a => cyclotomicGaloisConjugate (p := p) (K := K) a q)

/-- `q` itself is in its set of cyclotomic conjugates. -/
theorem self_mem_cyclotomicConjugates (q : Ideal (𝓞 K)) :
    q ∈ cyclotomicConjugates (p := p) (K := K) q := by
  classical
  unfold cyclotomicConjugates
  rw [Finset.mem_image]
  exact ⟨1, Finset.mem_univ _, cyclotomicGaloisConjugate_one q⟩

/-- Membership in the conjugate set is exactly being a Galois translate. -/
theorem mem_cyclotomicConjugates_iff (q I : Ideal (𝓞 K)) :
    I ∈ cyclotomicConjugates (p := p) (K := K) q ↔
      ∃ a : CyclotomicUnitDelta p,
        cyclotomicGaloisConjugate (p := p) (K := K) a q = I := by
  classical
  unfold cyclotomicConjugates
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, _, ha⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, Finset.mem_univ _, ha⟩

/-- Every element of the cyclotomic conjugate set is prime. -/
theorem isPrime_of_mem_cyclotomicConjugates
    {q I : Ideal (𝓞 K)} [q.IsPrime]
    (hI : I ∈ cyclotomicConjugates (p := p) (K := K) q) : I.IsPrime := by
  obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mp hI
  rw [← ha]
  infer_instance

/-- Every cyclotomic conjugate of `q` lies above the same rational prime. -/
theorem under_eq_of_mem_cyclotomicConjugates
    {q I : Ideal (𝓞 K)}
    (hI : I ∈ cyclotomicConjugates (p := p) (K := K) q) :
    I.under ℤ = q.under ℤ := by
  obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mp hI
  rw [← ha]
  exact cyclotomicGaloisConjugate_under_eq a q

/-! ### c.1.2 (preliminary) — Galois transitivity on primes above `ℓ`

Galois transitivity (Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`)
implies that any two prime ideals of `𝓞 K` lying above the same rational
prime are in the same cyclotomic conjugate class. Combined with
`under_eq_of_mem_cyclotomicConjugates` above, this gives an iff.
-/

/-- For any prime `q` of `𝓞 K`, the cyclotomic Galois group acts
transitively on primes of `𝓞 K` lying above `q.under ℤ`.

The Mathlib instance `IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K)` is derived from
`IsGalois ℚ K` (which holds for cyclotomic extensions). Combined with
`Ideal.exists_smul_eq_of_isGaloisGroup`, this gives the transitivity. -/
theorem exists_mem_cyclotomicConjugates_of_under_eq
    {q I : Ideal (𝓞 K)} [hq : q.IsPrime] [hI : I.IsPrime]
    (hqI : q.under ℤ = I.under ℤ) :
    I ∈ cyclotomicConjugates (p := p) (K := K) q := by
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := ({p} : Set ℕ)) ℚ K
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ K
  haveI : q.LiesOver (q.under ℤ) := ⟨rfl⟩
  haveI : I.LiesOver (q.under ℤ) := ⟨hqI⟩
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup
      (A := ℤ) (B := 𝓞 K) (p := q.under ℤ) (P := q) (Q := I) (G := Gal(K/ℚ))
  refine (mem_cyclotomicConjugates_iff (p := p) (K := K) q I).mpr
    ⟨cyclotomicGalEquivZMod (p := p) K σ, ?_⟩
  have ha : cyclotomicSigmaOfUnit (p := p) K
      (cyclotomicGalEquivZMod (p := p) K σ) = σ := by
    unfold cyclotomicSigmaOfUnit
    exact (cyclotomicGalEquivZMod (p := p) K).symm_apply_apply σ
  unfold cyclotomicGaloisConjugate
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K
        (cyclotomicGalEquivZMod (p := p) K σ) =
      MulSemiringAction.toRingEquiv (Gal(K/ℚ)) (𝓞 K) σ by
    unfold cyclotomicRingOfIntegersEquiv
    rw [ha]]
  exact hσ

/-- Membership in `cyclotomicConjugates q` is equivalent to lying above
the same rational prime as `q`. -/
theorem mem_cyclotomicConjugates_iff_under_eq
    {q I : Ideal (𝓞 K)} [hq : q.IsPrime] [hI : I.IsPrime] :
    I ∈ cyclotomicConjugates (p := p) (K := K) q ↔
      I.under ℤ = q.under ℤ :=
  ⟨under_eq_of_mem_cyclotomicConjugates,
   fun h => exists_mem_cyclotomicConjugates_of_under_eq h.symm⟩

/-- The orbit is closed under the Galois action: applying `σ_a` to any
element of `cyclotomicConjugates q` stays in the orbit. -/
theorem smul_mem_cyclotomicConjugates
    (a : CyclotomicUnitDelta p) {q I : Ideal (𝓞 K)}
    [hq : q.IsPrime] [hI : I.IsPrime]
    (hI_in : I ∈ cyclotomicConjugates (p := p) (K := K) q) :
    cyclotomicGaloisConjugate (p := p) (K := K) a I ∈
      cyclotomicConjugates (p := p) (K := K) q := by
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a I).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a I
  refine mem_cyclotomicConjugates_iff_under_eq.mpr ?_
  rw [cyclotomicGaloisConjugate_under_eq, under_eq_of_mem_cyclotomicConjugates hI_in]

/-- The Galois action permutes `cyclotomicConjugates q_K`. -/
theorem cyclotomicConjugates_image_galois_action
    (b : CyclotomicUnitDelta p) {q : Ideal (𝓞 K)} [hq : q.IsPrime]
    (_hq_ne : q ≠ ⊥) :
    Finset.image (cyclotomicGaloisConjugate (p := p) (K := K) b)
        (cyclotomicConjugates (p := p) (K := K) q) =
      cyclotomicConjugates (p := p) (K := K) q := by
  classical
  ext I
  refine ⟨?_, fun hI_in => ?_⟩
  · rintro hI
    rw [Finset.mem_image] at hI
    obtain ⟨q', hq'_in, rfl⟩ := hI
    haveI : q'.IsPrime := isPrime_of_mem_cyclotomicConjugates hq'_in
    exact smul_mem_cyclotomicConjugates b hq'_in
  · -- I ∈ orbit ⟹ ∃ q' ∈ orbit, σ_b q' = I. Use σ_{b⁻¹}.
    haveI : I.IsPrime := isPrime_of_mem_cyclotomicConjugates hI_in
    rw [Finset.mem_image]
    refine ⟨cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ I, ?_, ?_⟩
    · -- σ_{b⁻¹} I ∈ orbit.
      exact smul_mem_cyclotomicConjugates b⁻¹ hI_in
    · -- σ_b (σ_{b⁻¹} I) = I.
      rw [← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
        cyclotomicGaloisConjugate_one]

/-- The Galois orbit is well-defined on the orbit class: any element of
the orbit has the same orbit. (Equivalence-class property.) -/
theorem cyclotomicConjugates_eq_of_mem
    {q I : Ideal (𝓞 K)} [hq : q.IsPrime] [hI : I.IsPrime]
    (hI_in : I ∈ cyclotomicConjugates (p := p) (K := K) q) :
    cyclotomicConjugates (p := p) (K := K) I =
      cyclotomicConjugates (p := p) (K := K) q := by
  have hIq : I.under ℤ = q.under ℤ := under_eq_of_mem_cyclotomicConjugates hI_in
  ext J
  classical
  constructor
  · intro hJ_in
    obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) I J).mp hJ_in
    haveI : J.IsPrime := by rw [← ha]; infer_instance
    have : J.under ℤ = q.under ℤ := by
      rw [under_eq_of_mem_cyclotomicConjugates hJ_in, hIq]
    exact mem_cyclotomicConjugates_iff_under_eq.mpr this
  · intro hJ_in
    obtain ⟨a, ha⟩ := (mem_cyclotomicConjugates_iff (p := p) (K := K) q J).mp hJ_in
    haveI : J.IsPrime := by rw [← ha]; infer_instance
    have : J.under ℤ = I.under ℤ := by
      rw [under_eq_of_mem_cyclotomicConjugates hJ_in, hIq.symm]
    exact mem_cyclotomicConjugates_iff_under_eq.mpr this

/-! ### c.2 (partial) — Galois-equivariance of `pthSymbolAtPrime`

The full Galois-equivariance statement
`pthSymbolAtPrime (σ_a α) (σ_a • q) = pthSymbolAtPrime α q`
is blocked by the `Classical.choose` of a primitive `p`-th root of unity in
each residue field appearing inside `pthSymbolAtPrime`. Two unrelated
choices in `(𝓞K/q)ˣ` and `(𝓞K/(σ_a q))ˣ` would in general give exponents
differing by a unit factor in `(ZMod p)ˣ`.

This section provides the **conditional** Galois-equivariance: assuming
that the chosen primitive `p`-th roots in the two residue fields are
compatible (i.e., the chosen `ζ` for `σ_a • q` is the image of the chosen
`ζ` for `q` under the quotient ring isomorphism induced by `σ_a`), the
symbols agree. -/

/-- `α ∈ q` iff `σ_a α ∈ σ_a • q`. (`σ_a` is a ring isomorphism, so
images and preimages of ideals are well-behaved.) -/
theorem mem_cyclotomicGaloisConjugate_iff
    (a : CyclotomicUnitDelta p) {α : 𝓞 K} {q : Ideal (𝓞 K)} :
    cyclotomicRingOfIntegersEquiv (p := p) K a α ∈
        cyclotomicGaloisConjugate (p := p) (K := K) a q ↔ α ∈ q := by
  unfold cyclotomicGaloisConjugate
  rw [Ideal.mem_map_of_equiv]
  refine ⟨?_, fun h => ⟨α, h, rfl⟩⟩
  rintro ⟨x, hx, hxα⟩
  -- σ_a x = σ_a α ⟹ x = α (σ_a injective).
  have : x = α :=
    (cyclotomicRingOfIntegersEquiv (p := p) K a).injective hxα
  exact this ▸ hx

/-- `σ_a α ∉ σ_a • q` iff `α ∉ q`. -/
theorem notMem_cyclotomicGaloisConjugate_iff
    (a : CyclotomicUnitDelta p) {α : 𝓞 K} {q : Ideal (𝓞 K)} :
    cyclotomicRingOfIntegersEquiv (p := p) K a α ∉
        cyclotomicGaloisConjugate (p := p) (K := K) a q ↔ α ∉ q :=
  not_congr (mem_cyclotomicGaloisConjugate_iff a)

/-- The quotient ring isomorphism
`(𝓞K / q) ≃+* (𝓞K / σ_a • q)` induced by the Galois action `σ_a`. -/
noncomputable def cyclotomicGaloisQuotientEquiv
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    (𝓞 K ⧸ q) ≃+* (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
  Ideal.quotientEquiv q (cyclotomicGaloisConjugate (p := p) (K := K) a q)
    (cyclotomicRingOfIntegersEquiv (p := p) K a) rfl

/-- The quotient ring iso sends `Ideal.Quotient.mk q α` to
`Ideal.Quotient.mk (σ_a • q) (σ_a α)`. -/
@[simp] theorem cyclotomicGaloisQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) (α : 𝓞 K) :
    cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q
        (Ideal.Quotient.mk q α) =
      Ideal.Quotient.mk (cyclotomicGaloisConjugate (p := p) (K := K) a q)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α) := rfl

/-- `Fintype.card (𝓞K/q) = Fintype.card (𝓞K/(σ_a • q))` via the quotient
ring iso induced by `σ_a`. -/
theorem cyclotomicGaloisConjugate_quotient_card_eq
    (a : CyclotomicUnitDelta p) {q : Ideal (𝓞 K)} (hq : q ≠ ⊥) :
    haveI : NeZero q := ⟨hq⟩
    haveI : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
      ⟨cyclotomicGaloisConjugate_ne_bot a hq⟩
    Fintype.card (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      Fintype.card (𝓞 K ⧸ q) := by
  haveI : NeZero q := ⟨hq⟩
  haveI : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
    ⟨cyclotomicGaloisConjugate_ne_bot a hq⟩
  exact Fintype.card_congr
    (cyclotomicGaloisQuotientEquiv (p := p) (K := K) a q).toEquiv.symm

end Furtwaengler

end BernoulliRegular
