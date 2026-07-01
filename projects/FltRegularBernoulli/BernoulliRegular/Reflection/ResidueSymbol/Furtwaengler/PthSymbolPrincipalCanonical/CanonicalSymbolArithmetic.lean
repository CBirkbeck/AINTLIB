module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical.CanonicalIdealSymbol

/-!
# Canonical `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` and the unconditional c.3 closed form

This file mirrors the `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` API on top
of `pthSymbolAtPrime_canonical`, and uses the explicit Galois-action
transformation from `PthSymbolCanonical.lean` to derive the
**unconditional c.3 closed form**:

```
pthSymbolAtPrincipal_canonical α h_stick.gen =
  ∑ a : CyclotomicUnitDelta p,
    pthSymbolAtPrime_canonical (σ_a α) q_K
```

Compared to the conditional theorem
`pthSymbolAtPrincipal_eq_galois_sum_of_hypothesis` (in
`KummerFurtwaengler.lean`), the canonical version is *unconditional*:
the explicit `(a : ZMod p)` factor in the Galois-action transformation
cancels the digit-sum `a.val` factor, so the closed form eliminates
both the `a.val` weights and the `StickelbergerGaloisHypothesis` input.

## Main definitions and theorems

* `pthSymbolAtIdeal_canonical α I` — the canonical residue symbol at an
  integral ideal, defined as the multiset sum of
  `pthSymbolAtPrime_canonical α P` over the prime factors `P` of `I`.
* `pthSymbolAtPrincipal_canonical α β` — the canonical principal symbol,
  defined as `pthSymbolAtIdeal_canonical α (Ideal.span {β})`.
* `pthSymbolAtPrincipal_canonical_eq_galois_sum` — the **c.3 unconditional
  closed form** taking only `StickelbergerIdealEquality q_K`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The canonical principal symbol with α = 1 vanishes at any β. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_one_left
    (β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (1 : 𝓞 K) β = 0 :=
  pthSymbolAtIdeal_canonical_one_alpha _

/-- The canonical principal symbol with α = 0 vanishes at any β. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_zero_left
    (β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (0 : 𝓞 K) β = 0 :=
  pthSymbolAtIdeal_canonical_zero_alpha _

/-- **The canonical principal symbol with a unit denominator vanishes**:
`(α / ε)_canonical = 0` for any unit `ε`. (`Ideal.span {ε} = ⊤`.) -/
@[simp] theorem pthSymbolAtPrincipal_canonical_isUnit_right
    {ε : 𝓞 K} (α : 𝓞 K) (hε : IsUnit ε) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α ε = 0 := by
  unfold pthSymbolAtPrincipal_canonical
  rw [show (Ideal.span ({ε} : Set (𝓞 K))) = ⊤ from
        Ideal.span_singleton_eq_top.mpr hε]
  exact pthSymbolAtIdeal_canonical_top _

/-- **Canonical principal symbol pow in the denominator**:
`(α / β^n)_canonical = n · (α/β)_canonical`. Direct from
`pthSymbolAtIdeal_canonical_pow_ideal` and `Ideal.span_singleton_pow`. -/
theorem pthSymbolAtPrincipal_canonical_pow_right
    (α β : 𝓞 K) (n : ℕ) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (β ^ n) =
      (n : ZMod p) * pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  unfold pthSymbolAtPrincipal_canonical
  rw [show (Ideal.span ({β ^ n} : Set (𝓞 K))) =
        (Ideal.span ({β} : Set (𝓞 K))) ^ n from
        (Ideal.span_singleton_pow β n).symm]
  exact pthSymbolAtIdeal_canonical_pow_ideal α (Ideal.span ({β} : Set (𝓞 K))) n

/-- **Vanishing engine in the denominator slot.** The canonical principal
symbol with a `p`-th-power denominator vanishes:
`(α / β^p)_canonical = 0`. -/
theorem pthSymbolAtPrincipal_canonical_pow_p_right_eq_zero
    (α β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (β ^ p) = 0 := by
  rw [pthSymbolAtPrincipal_canonical_pow_right α β p, ZMod.natCast_self, zero_mul]

/-- The canonical principal symbol is invariant under negation in the
denominator: `(α / -β)_canonical = (α / β)_canonical`. Direct from
`Ideal.span_singleton_neg`. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_neg_right
    (α β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (-β) =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  unfold pthSymbolAtPrincipal_canonical
  congr 1
  exact Ideal.span_singleton_neg β

/-- The canonical principal symbol depends on the denominator only up to
associativity: multiplying by a unit doesn't change it. -/
theorem pthSymbolAtPrincipal_canonical_mul_unit_right
    (α β : 𝓞 K) {ε : 𝓞 K} (hε : IsUnit ε) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (β * ε) =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  unfold pthSymbolAtPrincipal_canonical
  congr 1
  rw [Ideal.span_singleton_eq_span_singleton]
  exact Associated.symm ⟨hε.unit, rfl⟩

/-- **Power formula in the numerator slot at the principal level.**
`(α^n / β)_canonical = n · (α/β)_canonical` whenever α is coprime to
every prime factor of `(β)`. Direct from `pthSymbolAtIdeal_canonical_pow_α`. -/
theorem pthSymbolAtPrincipal_canonical_pow_left
    (α β : 𝓞 K) (n : ℕ)
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({β} : Set (𝓞 K))), α ∉ P) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (α ^ n) β =
      (n : ZMod p) * pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  unfold pthSymbolAtPrincipal_canonical
  exact pthSymbolAtIdeal_canonical_pow_α (p := p) hα n

/-- **Vanishing engine, principal-level pow-p in `α`.** Whenever α is
coprime to every prime factor of `(β)`, `(α^p / β)_canonical = 0`. -/
theorem pthSymbolAtPrincipal_canonical_pow_p_left_eq_zero
    (α β : 𝓞 K)
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({β} : Set (𝓞 K))), α ∉ P) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (α ^ p) β = 0 := by
  rw [pthSymbolAtPrincipal_canonical_pow_left (p := p) α β p hα,
    ZMod.natCast_self, zero_mul]

/-- **Multiplicativity in `α` at the principal level.** Whenever both `α` and
`β` are coprime to every prime factor of `(γ)`,
`(α · β / γ)_canonical = (α / γ)_canonical + (β / γ)_canonical`. Direct from
`pthSymbolAtIdeal_canonical_mul_α`. -/
theorem pthSymbolAtPrincipal_canonical_mul_left
    {α β γ : 𝓞 K}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({γ} : Set (𝓞 K))), α ∉ P)
    (hβ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({γ} : Set (𝓞 K))), β ∉ P) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (α * β) γ =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α γ +
        pthSymbolAtPrincipal_canonical (p := p) (K := K) β γ := by
  unfold pthSymbolAtPrincipal_canonical
  exact pthSymbolAtIdeal_canonical_mul_α (p := p) hα hβ

/-! ### Negation API for `pthSymbolAtPrime_canonical`

Negation lemmas for the canonical residue symbol. The key observation is
that `(-α) = (-1) * α`, and `pthSymbolAtPrime_canonical` is multiplicative
in the numerator. Since `(-1)` is a unit, it lies outside every prime ideal
automatically. -/

omit [NumberField K] in
/-- `(-1 : 𝓞 K) ∉ q` for any maximal ideal `q`. This is automatic because
`-1` is a unit and a maximal ideal cannot contain a unit. -/
theorem neg_one_notMem_of_isMaximal {q : Ideal (𝓞 K)} (hmax : q.IsMaximal) :
    (-1 : 𝓞 K) ∉ q := fun h =>
  hmax.ne_top (q.eq_top_of_isUnit_mem h isUnit_one.neg)

/-- **`pthSymbolAtPrime_canonical` of `(-α)` splits as a sum.** For a non-bot
maximal prime `q` with `α ∉ q`, the canonical symbol of `-α` decomposes as
`pthSymbolAtPrime_canonical (-α) q = pthSymbolAtPrime_canonical α q +
pthSymbolAtPrime_canonical (-1) q`. Direct from `_mul`, using `(-α) = (-1) · α`
and the fact that `-1` is a unit (hence `∉ q`). -/
theorem pthSymbolAtPrime_canonical_neg
    {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∉ q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (-α) q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q +
        pthSymbolAtPrime_canonical (p := p) (K := K) (-1 : 𝓞 K) q := by
  have h_neg_one : (-1 : 𝓞 K) ∉ q := neg_one_notMem_of_isMaximal hmax
  have h_eq : (-α : 𝓞 K) = (-1) * α := by ring
  rw [h_eq, pthSymbolAtPrime_canonical_mul hbot hmax h_neg_one hα]
  ring

/-! ### Negation API for `pthSymbolAtIdeal_canonical`

Mirrors the prime-level negation API at the ideal level. The `(α^n)`-form
uses `pthSymbolAtIdeal_canonical_pow_α` after observing that `(-1)` is a
unit (`unit_notMem_normalizedFactors`). -/

/-- `(-1)` is coprime to every prime factor of any ideal `(β)`, since `(-1)`
is a unit. -/
theorem neg_one_notMem_normalizedFactors (β : 𝓞 K) :
    ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), (-1 : 𝓞 K) ∉ P :=
  fun P hP => unit_notMem_normalizedFactors isUnit_one.neg β P hP

/-- **`pthSymbolAtIdeal_canonical` at `(-1)^n`.** Direct from
`pthSymbolAtIdeal_canonical_pow_α` (with `α := -1`) using that `(-1)` is a
unit (so coprime to every prime factor of `I`). -/
theorem pthSymbolAtIdeal_canonical_neg_one_pow
    (I : Ideal (𝓞 K)) (n : ℕ) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ n) I =
      (n : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) (-1 : 𝓞 K) I := by
  refine pthSymbolAtIdeal_canonical_pow_α (p := p) ?_ n
  intro P hP
  obtain ⟨_, _, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  exact neg_one_notMem_of_isMaximal hP_max

/-- **Vanishing engine, ideal-level for `(-1)^p`.** Whenever `I` is any
ideal, `pthSymbolAtIdeal_canonical ((-1)^p) I = 0`. -/
theorem pthSymbolAtIdeal_canonical_neg_one_pow_p_eq_zero
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ p) I = 0 := by
  rw [pthSymbolAtIdeal_canonical_neg_one_pow (p := p) I p,
    ZMod.natCast_self, zero_mul]

/-- **`pthSymbolAtIdeal_canonical` of `(-α)` splits as a sum.** Whenever `α`
is coprime to every prime factor of `I`, the canonical symbol of `-α`
decomposes as `pthSymbolAtIdeal_canonical (-α) I = pthSymbolAtIdeal_canonical
α I + pthSymbolAtIdeal_canonical (-1) I`. Reduces, term-by-term, to
`pthSymbolAtPrime_canonical_neg`. -/
theorem pthSymbolAtIdeal_canonical_neg
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (-α) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I +
        pthSymbolAtIdeal_canonical (p := p) (K := K) (-1 : 𝓞 K) I := by
  have h_eq : (-α : 𝓞 K) = (-1) * α := by ring
  have h_neg_one : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      (-1 : 𝓞 K) ∉ P := by
    intro P hP
    obtain ⟨_, _, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact neg_one_notMem_of_isMaximal hP_max
  rw [h_eq, pthSymbolAtIdeal_canonical_mul_α (p := p) h_neg_one hα, add_comm]

/-- **Unconditional `(-α)` formula for odd p**: `pthSymbolAtIdeal_canonical
(-α) I = pthSymbolAtIdeal_canonical α I` unconditionally (no coprimality
required), valid for odd p. Uses `(-1) = (-1)^p` for odd p. -/
theorem pthSymbolAtIdeal_canonical_neg_uncond_of_odd
    (hp_odd : Odd p) (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (-α) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  classical
  unfold pthSymbolAtIdeal_canonical
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun P hP => ?_
  obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  by_cases hα : α ∈ P
  · haveI hP_prime : P.IsPrime := hP_max.isPrime
    have h_neg_α_in : -α ∈ P := P.neg_mem hα
    rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hP_ne_bot hP_max h_neg_α_in,
      pthSymbolAtPrime_canonical_eq_zero_of_mem hP_ne_bot hP_max hα]
  · -- α ∉ P. Use pthSymbolAtPrime_canonical_neg.
    rw [pthSymbolAtPrime_canonical_neg hP_ne_bot hP_max hα]
    have h_neg_one_pth :
        pthSymbolAtPrime_canonical (p := p) (K := K) (-1 : 𝓞 K) P = 0 := by
      have h_neg_one_eq : (-1 : 𝓞 K) = (-1 : 𝓞 K) ^ p :=
        (Odd.neg_one_pow hp_odd).symm
      rw [h_neg_one_eq]
      have h_neg_one_notMem : (-1 : 𝓞 K) ∉ P :=
        neg_one_notMem_of_isMaximal hP_max
      exact pthSymbolAtPrime_canonical_pow_p_eq_zero hP_ne_bot hP_max
        h_neg_one_notMem
    rw [h_neg_one_pth, add_zero]

/-! ### Negation API for `pthSymbolAtPrincipal_canonical` -/

/-- **`pthSymbolAtPrincipal_canonical_neg_left`.** Whenever `α` is coprime to
every prime factor of `(β)`, `(-α / β)_canonical = (α / β)_canonical +
(-1 / β)_canonical`. Direct from `pthSymbolAtIdeal_canonical_neg`. -/
theorem pthSymbolAtPrincipal_canonical_neg_left
    {α β : 𝓞 K}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({β} : Set (𝓞 K))), α ∉ P) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) (-α) β =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α β +
        pthSymbolAtPrincipal_canonical (p := p) (K := K) (-1 : 𝓞 K) β := by
  unfold pthSymbolAtPrincipal_canonical
  exact pthSymbolAtIdeal_canonical_neg (p := p) hα

/-- **`pthSymbolAtPrincipal_canonical` at `(-1)^n` in the numerator.** Direct
from `pthSymbolAtIdeal_canonical_neg_one_pow`. -/
theorem pthSymbolAtPrincipal_canonical_neg_one_pow_left
    (β : 𝓞 K) (n : ℕ) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ n) β =
      (n : ZMod p) *
        pthSymbolAtPrincipal_canonical (p := p) (K := K) (-1 : 𝓞 K) β := by
  unfold pthSymbolAtPrincipal_canonical
  exact pthSymbolAtIdeal_canonical_neg_one_pow (p := p) _ n

/-- **Vanishing engine, principal-level for `(-1)^p` in the numerator.**
`((-1)^p / β)_canonical = 0`. -/
theorem pthSymbolAtPrincipal_canonical_neg_one_pow_p_left_eq_zero
    (β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) ((-1 : 𝓞 K) ^ p) β = 0 := by
  rw [pthSymbolAtPrincipal_canonical_neg_one_pow_left (p := p) β p,
    ZMod.natCast_self, zero_mul]

/-! ### Compatibility lemmas: canonical vs. non-canonical

Building on `pthSymbolAtPrime_eq_canonical_up_to_unit`, we record the corner
cases (`q = ⊥`, `α ∈ q`) where both versions trivially vanish, giving an
unconditional equality. -/

/-- For `q = ⊥`, both the non-canonical and canonical prime symbols vanish. -/
theorem pthSymbolAtPrime_eq_canonical_of_eq_bot (α : 𝓞 K) :
    pthSymbolAtPrime (p := p) α (⊥ : Ideal (𝓞 K)) =
      pthSymbolAtPrime_canonical (p := p) (K := K) α (⊥ : Ideal (𝓞 K)) := by
  rw [pthSymbolAtPrime_eq_zero_of_eq_bot,
    pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]

/-- For a non-bot maximal prime `q` with `α ∈ q`, both the non-canonical and
canonical symbols vanish. -/
theorem pthSymbolAtPrime_eq_canonical_of_mem
    {α : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∈ q) :
    pthSymbolAtPrime (p := p) α q =
      pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  rw [pthSymbolAtPrime_eq_zero_of_mem (p := p) hbot hmax hα,
    pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα]

/-! ### Derived API: vanishing characterizations

Convenient sufficient conditions for the canonical ideal/principal symbol to
vanish. These reduce to the prime-level vanishing lemmas
(`pthSymbolAtPrime_canonical_eq_zero_*`). -/

/-- **Vanishing characterization at the ideal level.** If the canonical
prime-level symbol vanishes on every prime factor of `I`, then the canonical
ideal symbol vanishes too. (The converse can fail because the symbol is a
sum, not a product, in `ZMod p`.) -/
theorem pthSymbolAtIdeal_canonical_eq_zero_of_forall_prime
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (h : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
            pthSymbolAtPrime_canonical (p := p) (K := K) α P = 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α I = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) α P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from Multiset.map_congr rfl (fun P hP => h P hP)]
  simp

/-- **Per-prime vanishing characterization at the principal level.** If the
canonical prime symbol vanishes on every prime factor of `(β)`, then the
canonical principal symbol `(α / β)_canonical` vanishes. Direct from
`pthSymbolAtIdeal_canonical_eq_zero_of_forall_prime`. -/
theorem pthSymbolAtPrincipal_canonical_eq_zero_of_forall_prime
    {α β : 𝓞 K}
    (h : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))),
          pthSymbolAtPrime_canonical (p := p) (K := K) α P = 0) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α β = 0 :=
  pthSymbolAtIdeal_canonical_eq_zero_of_forall_prime (p := p) h

/-- **Top-level corollary**: vanishing of the canonical principal symbol on a
"singular canonical chain". If `(η) = (b^p)` is singular (a perfect `p`-th
power as a principal ideal) and the canonical KFR identification holds, then
`(η/(γ))_canonical = (γ/(η))_canonical = (γ/(b^p))_canonical = 0` via the
denominator-slot vanishing engine `pthSymbolAtPrincipal_canonical_pow_p_right_eq_zero`.
This exposes a direct path through the principal API for downstream KFR
consumers. -/
theorem pthSymbolAtPrincipal_canonical_eq_zero_of_singular_canonical_chain
    {η γ b : 𝓞 K}
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = Ideal.span ({b ^ p} : Set (𝓞 K)))
    (h_kfr : pthSymbolAtPrincipal_canonical (p := p) (K := K) η γ =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) γ η) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) η γ = 0 := by
  rw [h_kfr]
  unfold pthSymbolAtPrincipal_canonical
  rw [hsing,
      show (Ideal.span ({b ^ p} : Set (𝓞 K))) =
        (Ideal.span ({b} : Set (𝓞 K))) ^ p from
        (Ideal.span_singleton_pow b p).symm,
      pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero]

/-! ### Derived API: associated and equal ideals

The canonical symbol depends on the ideal slot only through the ideal
itself (not its representation). For `Ideal R` with `R` Dedekind, units are
unique, so `Associated I J ↔ I = J`; we provide congruence-style lemmas to
make rewriting easy. -/

/-- **Equality of canonical ideal symbols under ideal equality.** A
`congr`-style helper that lets you swap an ideal for an equal one when
rewriting. -/
theorem pthSymbolAtIdeal_canonical_congr
    {α α' : 𝓞 K} {I I' : Ideal (𝓞 K)}
    (hα : α = α') (hI : I = I') :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α' I' := by
  subst hα; subst hI; rfl

/-- **Equality of canonical ideal symbols under associated ideals.** Since
ideals form a `NormalizationMonoid` with unique units (`Ideal.uniqueUnits`),
`Associated I I'` actually forces `I = I'`. This makes the canonical symbol
trivially associate-invariant, but the lemma is convenient in chains of
rewriting where one only knows the ideals are associated. -/
theorem pthSymbolAtIdeal_canonical_eq_of_associated
    {α : 𝓞 K} {I I' : Ideal (𝓞 K)} (hII' : Associated I I') :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I' :=
  pthSymbolAtIdeal_canonical_congr rfl (associated_iff_eq.mp hII')

/-- **Equality of canonical principal symbols under associated denominators.**
If `β ~ β'` (i.e., they generate the same principal ideal up to a unit), then
their principal symbols agree. Direct from
`Ideal.span_singleton_eq_span_singleton`. -/
theorem pthSymbolAtPrincipal_canonical_eq_of_associated_right
    {α β β' : 𝓞 K} (hββ' : Associated β β') :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α β =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α β' := by
  unfold pthSymbolAtPrincipal_canonical
  refine pthSymbolAtIdeal_canonical_congr rfl ?_
  exact Ideal.span_singleton_eq_span_singleton.mpr hββ'

/-! ### Ergonomic API for downstream use -/

/-- **Self-symbol vanishes**: `(α / α)_canonical = 0`. Each prime factor `P`
of `Ideal.span {α}` contains `α` (since `(α) ⊆ P`), so by
`pthSymbolAtPrime_canonical_eq_zero_of_mem` every term in the multiset is
zero, and so is the sum. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_self_eq_zero
    (α : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α α = 0 := by
  refine pthSymbolAtPrincipal_canonical_eq_zero_of_forall_prime ?_
  intro P hP
  obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  -- `α ∈ Ideal.span {α} ⊆ P` since `P ∣ Ideal.span {α}` (i.e., `Ideal.span {α} ⊆ P`).
  have hα_in_span : α ∈ Ideal.span ({α} : Set (𝓞 K)) := Ideal.subset_span rfl
  have hSpan_le : Ideal.span ({α} : Set (𝓞 K)) ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  exact pthSymbolAtPrime_canonical_eq_zero_of_mem hP_ne_bot hP_max
    (hSpan_le hα_in_span)

/-- **Self-pow-vanishing**: `(α / α^n)_canonical = 0` for any `n`. Direct from
the self-vanishing and `_pow_right`. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_self_pow
    (α : 𝓞 K) (n : ℕ) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (α ^ n) = 0 := by
  rw [pthSymbolAtPrincipal_canonical_pow_right α α n,
    pthSymbolAtPrincipal_canonical_self_eq_zero, mul_zero]

/-- **Symbol on the zero denominator vanishes**: `(α / 0)_canonical = 0`. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_zero_right
    (α : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α 0 = 0 := by
  unfold pthSymbolAtPrincipal_canonical
  rw [show (Ideal.span ({(0 : 𝓞 K)} : Set (𝓞 K))) = ⊥ from
        Ideal.span_singleton_eq_bot.mpr rfl]
  exact pthSymbolAtIdeal_canonical_bot α

/-- **Multiplicative form for the principal denominator slot**:
`(α / β·γ)_canonical = (α / β)_canonical + (α / γ)_canonical` for non-zero
`β, γ`. Direct from `pthSymbolAtIdeal_canonical_mul_ideal` together with
`Ideal.span_singleton_mul_span_singleton`. -/
theorem pthSymbolAtPrincipal_canonical_mul_right
    (α : 𝓞 K) {β γ : 𝓞 K} (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α (β * γ) =
      pthSymbolAtPrincipal_canonical (p := p) (K := K) α β +
        pthSymbolAtPrincipal_canonical (p := p) (K := K) α γ := by
  unfold pthSymbolAtPrincipal_canonical
  rw [show (Ideal.span ({β * γ} : Set (𝓞 K))) =
        Ideal.span ({β} : Set (𝓞 K)) * Ideal.span ({γ} : Set (𝓞 K)) from
        (Ideal.span_singleton_mul_span_singleton β γ).symm]
  refine pthSymbolAtIdeal_canonical_mul_ideal α ?_ ?_
  · rwa [Ne, Ideal.span_singleton_eq_bot]
  · rwa [Ne, Ideal.span_singleton_eq_bot]

/-- The canonical principal symbol vanishes when β = 1. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_one_right
    (α : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α 1 = 0 := by
  unfold pthSymbolAtPrincipal_canonical
  rw [Ideal.span_singleton_one]
  exact pthSymbolAtIdeal_canonical_top α

/-- Convenience alias: the principal-symbol triviality from canonical KFR
plus singularity, packaged as the value at the principal ideal. -/
theorem pthSymbolAtIdeal_canonical_eq_zero_of_kfr_and_singular
    {η γ : 𝓞 K} (B : Ideal (𝓞 K))
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (h_kfr : pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) γ
        (Ideal.span ({η} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0 :=
  pthSymbolAtPrincipal_canonical_eq_zero_of_kfr_singular B hsing h_kfr

end Furtwaengler

end BernoulliRegular
