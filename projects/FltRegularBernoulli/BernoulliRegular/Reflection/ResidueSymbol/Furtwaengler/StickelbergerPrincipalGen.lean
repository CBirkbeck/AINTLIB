module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolIdealGaloisAction


/-!
# `α^Θ`: the Stickelberger principal generator

This file defines the **element-level** Stickelberger generator `α^Θ`
for `α : 𝓞 K`, where `Θ = ∑_a a · σ_{a^{-1}}` is the Stickelberger
element of `ℤ[(ZMod p)ˣ]`. Concretely:

```
α^Θ := ∏_{a ∈ (ZMod p)ˣ} (σ_{a^{-1}} α) ^ a.val.
```

This is the principal-ideal specialisation of the Stickelberger
factorisation: at the ideal level, the existing
`stickelbergerIdeal q_K = ∏_a (σ_{a^{-1}} q_K)^{a.val}` for primes
extends multiplicatively, and for `A = Ideal.span {α}` the factorisation
generator is exactly `α^Θ`.

This is the right intermediate object for the strategy pivot
(see `.mathlib-quality/ref18_pivot.md`):

* Φ(A) = g(A)^p has ideal `(Φ(A)) = A^Θ`.
* For principal A = (α), `Φ((α)) = u(α) · α^Θ` (principal unit factor).
* Primary α ⟹ u(α) = ±1 ⟹ the unit factor's residue symbol is trivial.
* Norm-form Kelly theorem `(Φ(A)/B)_p = (NB/A)_p` then gives Eisenstein
  reciprocity directly.

## Main definitions

* `stickelbergerPrincipalGen α` — the element `α^Θ ∈ 𝓞 K`.
* `stickelbergerPrincipalGen_zero` — `0^Θ = 0`.
* `stickelbergerPrincipalGen_one` — `1^Θ = 1`.
* `stickelbergerPrincipalGen_mul` — multiplicativity.
* `stickelbergerPrincipalGen_ne_zero` — `α ≠ 0 ⟹ α^Θ ≠ 0`.
* `span_stickelbergerPrincipalGen` — `(α^Θ) = stickelbergerIdeal_principal α`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **The Stickelberger principal generator** `α^Θ ∈ 𝓞 K`, where
`Θ = ∑_a a · σ_{a^{-1}}` is the Stickelberger element. Defined as
`∏_a (σ_{a^{-1}} α)^a.val`. -/
noncomputable def stickelbergerPrincipalGen (α : 𝓞 K) : 𝓞 K :=
  ∏ a : CyclotomicUnitDelta p,
    (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val)

/-- **`α^Θ` evaluated at `α = 0` is `0`** (one factor in the product is
`σ_{a^{-1}} 0 = 0` raised to a positive power since `a ≠ 0` ⟹ `a.val ≥ 1`).
Actually, since the indexing set `(ZMod p)ˣ` only has units, the
relevant `a.val` can be 1 (when a = 1). The factor at a = 1 is
`(σ_1 α)^1.val = (σ_1 α)^1 = α`. So if α = 0, the product is 0. -/
theorem stickelbergerPrincipalGen_zero :
    stickelbergerPrincipalGen (p := p) (K := K) (0 : 𝓞 K) = 0 := by
  unfold stickelbergerPrincipalGen
  -- Find the factor a = 1; (σ_1 0)^1 = 0; product with a zero factor is 0.
  refine Finset.prod_eq_zero (Finset.mem_univ (1 : CyclotomicUnitDelta p)) ?_
  -- Need: (cyclotomicRingOfIntegersEquiv K (1⁻¹) 0)^(1 : ZMod p).val = 0.
  change (cyclotomicRingOfIntegersEquiv (p := p) K (1⁻¹) 0) ^ ((1 : ZMod p).val) = 0
  rw [show (1⁻¹ : CyclotomicUnitDelta p) = 1 from inv_one,
      cyclotomicRingOfIntegersEquiv_one_apply]
  -- Now: (0 : 𝓞 K)^((1 : ZMod p).val) = 0
  -- Need (1 : ZMod p).val ≠ 0, i.e. ≥ 1.
  rw [show ((1 : ZMod p).val) = 1 from ?_]
  · simp
  · -- (1 : ZMod p).val = 1 since p ≥ 2.
    have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt hp_two

/-- **`α^Θ` is multiplicative**: `(α · β)^Θ = α^Θ · β^Θ`. -/
theorem stickelbergerPrincipalGen_mul (α β : 𝓞 K) :
    stickelbergerPrincipalGen (p := p) (K := K) (α * β) =
      stickelbergerPrincipalGen (p := p) (K := K) α *
      stickelbergerPrincipalGen (p := p) (K := K) β := by
  unfold stickelbergerPrincipalGen
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ (α * β) =
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α *
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β from
    map_mul _ α β, mul_pow]

/-- **`α^Θ ≠ 0` when `α ≠ 0`**. Each factor `(σ_{a^{-1}} α)^{a.val}` is non-zero
since σ is injective and the exponent `a.val ≥ 1` for `a ∈ (ZMod p)ˣ`. -/
theorem stickelbergerPrincipalGen_ne_zero {α : 𝓞 K} (hα : α ≠ 0) :
    stickelbergerPrincipalGen (p := p) (K := K) α ≠ 0 := by
  unfold stickelbergerPrincipalGen
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  -- Need: (σ_{a^{-1}} α)^a.val ≠ 0.
  have hσα_ne : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ≠ 0 := by
    intro h
    apply hα
    have h_inj := (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹).injective
    have : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α =
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ 0 := by
      rw [h, map_zero]
    exact h_inj this
  exact pow_ne_zero _ hσα_ne

/-- If an ideal contains `α`, then it contains the Stickelberger principal
generator `α^Θ`. The product defining `α^Θ` has the `a = 1` factor equal to
`α`. -/
theorem stickelbergerPrincipalGen_mem_of_mem
    {α : 𝓞 K} {I : Ideal (𝓞 K)} (hα : α ∈ I) :
    stickelbergerPrincipalGen (p := p) (K := K) α ∈ I := by
  classical
  unfold stickelbergerPrincipalGen
  rw [← Finset.mul_prod_erase Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val))
    (Finset.mem_univ (1 : CyclotomicUnitDelta p))]
  have hval_one : (((1 : CyclotomicUnitDelta p) : ZMod p).val) = 1 := by
    change ((1 : ZMod p).val) = 1
    have hp_two : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt hp_two
  rw [show (1⁻¹ : CyclotomicUnitDelta p) = 1 from inv_one,
    cyclotomicRingOfIntegersEquiv_one_apply, hval_one, pow_one]
  exact Ideal.mul_mem_right _ I hα

/-- **`(α^Θ)` is the Stickelberger ideal of `(α)`**: the principal-ideal
specialisation of the Stickelberger factorisation. -/
theorem span_stickelbergerPrincipalGen (α : 𝓞 K) :
    Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) α} : Set (𝓞 K)) =
      ∏ a : CyclotomicUnitDelta p,
        Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α} :
          Set (𝓞 K)) ^ ((a : ZMod p).val) := by
  unfold stickelbergerPrincipalGen
  rw [show
      Ideal.span ({∏ a : CyclotomicUnitDelta p,
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val)}
          : Set (𝓞 K)) =
        ∏ a : CyclotomicUnitDelta p,
          Ideal.span ({(cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^
              ((a : ZMod p).val)} : Set (𝓞 K)) from ?_]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Ideal.span_singleton_pow]
  · -- span singleton of a finite product = product of span singletons.
    rw [← Ideal.prod_span_singleton]

/-! ### Connection to `stickelbergerIdeal` for principal ideals

Specialise the existing `stickelbergerIdeal` (defined for ideals of `𝓞 K`)
to a principal ideal `Ideal.span {α}`. The result equals
`Ideal.span {α^Θ}` where `α^Θ = stickelbergerPrincipalGen α`.
-/

/-- **Stickelberger ideal of `(α)` equals `(α^Θ)`**: for any `α : 𝓞 K`,
the Stickelberger ideal of the principal ideal `(α)` is itself principal,
generated by `α^Θ`. -/
theorem stickelbergerIdeal_span_singleton (α : 𝓞 K) :
    stickelbergerIdeal (p := p) (K := K) (Ideal.span ({α} : Set (𝓞 K))) =
      Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) α} :
        Set (𝓞 K)) := by
  rw [span_stickelbergerPrincipalGen]
  unfold stickelbergerIdeal
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [cyclotomicGaloisConjugate_span_singleton]

/-- The Stickelberger ideal of the unit ideal is the unit ideal. -/
@[simp] theorem stickelbergerIdeal_top :
    stickelbergerIdeal (p := p) (K := K) (⊤ : Ideal (𝓞 K)) = ⊤ := by
  classical
  unfold stickelbergerIdeal
  rw [← Ideal.one_eq_top]
  refine Finset.prod_eq_one
    (f := fun a : CyclotomicUnitDelta p =>
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ (1 : Ideal (𝓞 K)) ^
        ((a : ZMod p).val)) fun a _ => ?_
  change cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
    (1 : Ideal (𝓞 K)) ^ ((a : ZMod p).val) = 1
  rw [Ideal.one_eq_top, cyclotomicGaloisConjugate_top, Ideal.top_pow]

/-- Stickelberger ideal formation is multiplicative in the input ideal. -/
theorem stickelbergerIdeal_mul (A B : Ideal (𝓞 K)) :
    stickelbergerIdeal (p := p) (K := K) (A * B) =
      stickelbergerIdeal (p := p) (K := K) A *
        stickelbergerIdeal (p := p) (K := K) B := by
  unfold stickelbergerIdeal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [cyclotomicGaloisConjugate_mul_ideal, mul_pow]

/-- Stickelberger ideal formation commutes with natural powers. -/
theorem stickelbergerIdeal_pow (A : Ideal (𝓞 K)) (n : ℕ) :
    stickelbergerIdeal (p := p) (K := K) (A ^ n) =
      (stickelbergerIdeal (p := p) (K := K) A) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, stickelbergerIdeal_mul, ih, pow_succ]

/-- If `(η) = b^p`, then `(η^Θ) = (b^Θ)^p` at the ideal level. -/
theorem span_stickelbergerPrincipalGen_of_span_eq_pow
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p) :
    Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
        Set (𝓞 K)) =
      (stickelbergerIdeal (p := p) (K := K) b) ^ p := by
  rw [← stickelbergerIdeal_span_singleton, hη, stickelbergerIdeal_pow]

/-- Principal-specialized form: if `(η) = (μ)^p`, then
`(η^Θ) = ((μ^Θ)^p)`. -/
theorem span_stickelbergerPrincipalGen_of_span_eq_span_pow
    {η μ : 𝓞 K}
    (hη : Ideal.span ({η} : Set (𝓞 K)) =
      Ideal.span ({μ} : Set (𝓞 K)) ^ p) :
    Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
        Set (𝓞 K)) =
      Ideal.span ({(stickelbergerPrincipalGen (p := p) (K := K) μ) ^ p} :
        Set (𝓞 K)) := by
  rw [span_stickelbergerPrincipalGen_of_span_eq_pow hη,
    stickelbergerIdeal_span_singleton, Ideal.span_singleton_pow]

/-- Element form of the singular ideal-power theorem: if `(η) = b^p` and
`b^Θ = (μ)`, then `η^Θ` is a unit times `μ^p`. -/
theorem exists_unit_principalGen_eq_pow_of_singular_stickelbergerIdeal_span
    {η μ : 𝓞 K} {b : Ideal (𝓞 K)}
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hμ : stickelbergerIdeal (p := p) (K := K) b =
      Ideal.span ({μ} : Set (𝓞 K))) :
    ∃ u : (𝓞 K)ˣ,
      stickelbergerPrincipalGen (p := p) (K := K) η = (u : 𝓞 K) * μ ^ p := by
  have hspan : Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
        Set (𝓞 K)) =
      Ideal.span ({μ ^ p} : Set (𝓞 K)) := by
    rw [span_stickelbergerPrincipalGen_of_span_eq_pow hη, hμ,
      Ideal.span_singleton_pow]
  have h_assoc : Associated (stickelbergerPrincipalGen (p := p) (K := K) η)
      (μ ^ p) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨u, hu⟩ := h_assoc
  refine ⟨u⁻¹, ?_⟩
  have h_inv_mul : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * μ ^ p =
      stickelbergerPrincipalGen (p := p) (K := K) η := by
    rw [← hu]
    rw [show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        (stickelbergerPrincipalGen (p := p) (K := K) η * (u : 𝓞 K)) =
        stickelbergerPrincipalGen (p := p) (K := K) η *
          (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) by ring]
    rw [h_inv_mul, mul_one]
  exact this.symm

/-- Principal-specialized element form: if `(η) = (μ)^p`, then `η^Θ` is a
unit times `(μ^Θ)^p`. -/
theorem exists_unit_principalGen_eq_principalGen_pow_of_span_pow
    {η μ : 𝓞 K}
    (hη : Ideal.span ({η} : Set (𝓞 K)) =
      Ideal.span ({μ} : Set (𝓞 K)) ^ p) :
    ∃ u : (𝓞 K)ˣ,
      stickelbergerPrincipalGen (p := p) (K := K) η =
        (u : 𝓞 K) * (stickelbergerPrincipalGen (p := p) (K := K) μ) ^ p :=
  exists_unit_principalGen_eq_pow_of_singular_stickelbergerIdeal_span
    (p := p) (K := K) hη (stickelbergerIdeal_span_singleton μ)

/-- If `(η) = b^p` and the Stickelberger quotient of `b` is principal,
`b^Θ = b · (β)`, then `η^Θ = η · (u · β^p)` for some unit `u`.

This is the precise element-level numerator comparison supplied by a
principal witness for `b^Θ / b`; the separate REF-18 endpoint still needs the
extracted unit to have trivial residue symbols. -/
theorem exists_unit_principalGen_eq_eta_mul_pow_of_stickelbergerIdeal_eq_mul
    {η β : 𝓞 K} {b : Ideal (𝓞 K)}
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hβ : stickelbergerIdeal (p := p) (K := K) b =
      b * Ideal.span ({β} : Set (𝓞 K))) :
    ∃ u : (𝓞 K)ˣ,
      stickelbergerPrincipalGen (p := p) (K := K) η =
        η * ((u : 𝓞 K) * β ^ p) := by
  have hspan : Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
        Set (𝓞 K)) =
      Ideal.span ({η * β ^ p} : Set (𝓞 K)) := by
    calc
      Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
          Set (𝓞 K))
          = (stickelbergerIdeal (p := p) (K := K) b) ^ p :=
              span_stickelbergerPrincipalGen_of_span_eq_pow hη
      _ = (b * Ideal.span ({β} : Set (𝓞 K))) ^ p := by rw [hβ]
      _ = b ^ p * Ideal.span ({β} : Set (𝓞 K)) ^ p := by rw [mul_pow]
      _ = Ideal.span ({η} : Set (𝓞 K)) *
          Ideal.span ({β ^ p} : Set (𝓞 K)) := by
            rw [← hη, Ideal.span_singleton_pow]
      _ = Ideal.span ({η * β ^ p} : Set (𝓞 K)) := by
            rw [Ideal.span_singleton_mul_span_singleton]
  have h_assoc : Associated (stickelbergerPrincipalGen (p := p) (K := K) η)
      (η * β ^ p) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨u, hu⟩ := h_assoc
  refine ⟨u⁻¹, ?_⟩
  have h_inv_mul : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have h_unit_left : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (η * β ^ p) =
      stickelbergerPrincipalGen (p := p) (K := K) η := by
    rw [← hu]
    rw [show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        (stickelbergerPrincipalGen (p := p) (K := K) η * (u : 𝓞 K)) =
        stickelbergerPrincipalGen (p := p) (K := K) η *
          (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) by ring]
    rw [h_inv_mul, mul_one]
  calc
    stickelbergerPrincipalGen (p := p) (K := K) η =
        ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (η * β ^ p) := h_unit_left.symm
    _ = η * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * β ^ p) := by ring

/-- If `(η) = b^p` and `b^Θ = b`, then `η^Θ = η · u` for some unit `u`.

This is the `β = 1` specialization of the quotient-principal comparison. -/
theorem exists_unit_principalGen_eq_eta_mul_of_stickelbergerIdeal_eq_self
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb : stickelbergerIdeal (p := p) (K := K) b = b) :
    ∃ u : (𝓞 K)ˣ,
      stickelbergerPrincipalGen (p := p) (K := K) η = η * (u : 𝓞 K) := by
  have hβ : stickelbergerIdeal (p := p) (K := K) b =
      b * Ideal.span ({(1 : 𝓞 K)} : Set (𝓞 K)) := by
    rw [hb, Ideal.span_singleton_one, Ideal.mul_top]
  obtain ⟨u, hu⟩ :=
    exists_unit_principalGen_eq_eta_mul_pow_of_stickelbergerIdeal_eq_mul
      (p := p) (K := K) (β := (1 : 𝓞 K)) hη hβ
  refine ⟨u, ?_⟩
  simpa using hu

/-- **Conversely**: if a `StickelbergerIdealEquality` holds for the
principal ideal `(α)`, then any generator `γ` is associate to `α^Θ`. -/
theorem StickelbergerIdealEquality.span_eq_span_principalGen
    {α : 𝓞 K}
    (h : StickelbergerIdealEquality (p := p) (K := K)
      (Ideal.span ({α} : Set (𝓞 K)))) :
    Ideal.span ({h.gen} : Set (𝓞 K)) =
      Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) α} :
        Set (𝓞 K)) := by
  rw [h.span_gen, stickelbergerIdeal_span_singleton]

/-! ### Symbol of `α` against `(β^Θ)` as a Galois sum

The canonical residue symbol `(α / (β^Θ))_p` decomposes as a sum over
Galois indices of the principal symbols `(α / (σ_{a^{-1}} β))_p`.

This is the principal-ideal analogue of
`pthSymbolAtPrincipal_canonical_eq_stickelberger_sum` for general
principal `(β)` (not just primes with a Stickelberger ideal equality). -/

/-- **Galois-sum decomposition of `(α/(β^Θ))_p`**: for `α, β : 𝓞 K` with `β ≠ 0`,
the canonical residue symbol on the principal ideal `(β^Θ)` decomposes as
```
∑_{a ∈ (ZMod p)ˣ} a.val · (α / (σ_{a^{-1}} β))_p.
```
-/
theorem pthSymbolAtPrincipal_canonical_principalGen_eq_galois_sum
    (α : 𝓞 K) {β : 𝓞 K} (hβ : β ≠ 0) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α
        (stickelbergerPrincipalGen (p := p) (K := K) β) =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrincipal_canonical (p := p) (K := K) α
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β) := by
  classical
  unfold pthSymbolAtPrincipal_canonical
  -- Step 1: rewrite (β^Θ) ideal as the product of (σ_{a^{-1}} β)^{a.val}.
  rw [span_stickelbergerPrincipalGen]
  -- Step 2: distribute pthSymbolAtIdeal_canonical α over the finset product.
  rw [pthSymbolAtIdeal_canonical_finset_prod (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β} : Set (𝓞 K))
        ^ ((a : ZMod p).val))
    α (fun a _ => ?_)]
  · -- Step 3: each pow factor unfolds via pthSymbolAtIdeal_canonical_pow_ideal.
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [pthSymbolAtIdeal_canonical_pow_ideal α
      (Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β} :
        Set (𝓞 K))) ((a : ZMod p).val)]
  · -- side condition: (σ_{a^{-1}} β)-span ^ a.val ≠ ⊥ (here written as ≠ 0).
    have h_ne : Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β}
        : Set (𝓞 K)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      intro h_zero
      apply hβ
      have h_inj := (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹).injective
      have : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β =
          cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ 0 := by
        rw [h_zero, map_zero]
      exact h_inj this
    -- pow_ne_zero needs `ne 0`, and `0 = ⊥` for Ideals.
    have h_pow_ne : (Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ β}
        : Set (𝓞 K))) ^ ((a : ZMod p).val) ≠ ⊥ := by
      rw [show ((⊥ : Ideal (𝓞 K)) = (0 : Ideal _)) from (Ideal.zero_eq_bot).symm]
      exact pow_ne_zero _ (by
        rw [show ((0 : Ideal (𝓞 K)) = ⊥) from Ideal.zero_eq_bot]
        exact h_ne)
    exact h_pow_ne

/-! ### Helper: prod-induction pattern for `pthSymbolAtIdeal_canonical_mul_α`

A `Finset.prod` of integral elements, each coprime to every prime factor
of an ideal, can be expanded under `pthSymbolAtIdeal_canonical` slot 1
into a sum of individual symbols.
-/

/-- **Finset-product version of `pthSymbolAtIdeal_canonical_mul_α`**.
For a finset `s : Finset ι` indexing elements `f i : 𝓞 K`, with each
`f i` coprime to every prime factor of `I`, the canonical residue symbol
in the numerator slot satisfies
`(∏_i f i / I)_p = ∑_i (f i / I)_p`. -/
theorem pthSymbolAtIdeal_canonical_finset_prod_α {ι : Type*}
    (s : Finset ι) (f : ι → 𝓞 K) {I : Ideal (𝓞 K)}
    (hf : ∀ i ∈ s, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, f i ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (∏ i ∈ s, f i) I =
      ∑ i ∈ s, pthSymbolAtIdeal_canonical (p := p) (K := K) (f i) I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, pthSymbolAtIdeal_canonical_one_alpha,
      Finset.sum_empty]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [pthSymbolAtIdeal_canonical_mul_α (p := p)
      (hf i (Finset.mem_insert_self i s))]
    · rw [ih (fun j hj P hP => hf j (Finset.mem_insert_of_mem hj) P hP)]
    · -- ∀ P ∈ normalizedFactors I, ∏_{j ∈ s} f j ∉ P (P prime).
      intro P hP h_in_prod
      obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
      haveI : P.IsPrime := hP_max.isPrime
      -- ∏ f ∈ P (prime) ⟹ some f j ∈ P.
      obtain ⟨j, hj_mem, hj_in⟩ :=
        Ideal.IsPrime.prod_mem_iff.mp h_in_prod
      exact (hf j (Finset.mem_insert_of_mem hj_mem) P hP) hj_in

/-! ### Left-slot Galois sum for `(α^Θ / γ)_p`

The principal symbol with `α^Θ` in the numerator and `γ` in the denominator
expands as a Galois-weighted sum:
```
(α^Θ / γ)_p = ∑_a a.val · (σ_{a^{-1}} α / γ)_p
```
This uses the multiplicativity and power form of the canonical symbol in
its first (numerator) slot, applied to the explicit Finset-product
expression for `α^Θ`. -/

/-- **Galois-sum decomposition of `(α^Θ / γ)_p`** on the LEFT slot.

For `α : 𝓞 K` and `γ : 𝓞 K`, with `σ_{a^{-1}} α ∉ P` for every prime
factor `P` of `(γ)` and every Galois index `a`, the canonical residue
symbol on `α^Θ` against the principal ideal `(γ)` decomposes as
```
∑_{a ∈ (ZMod p)ˣ} a.val · (σ_{a^{-1}} α / (γ))_p.
```
-/
theorem pthSymbolAtPrincipal_canonical_principalGen_left_eq_galois_sum
    (α γ : 𝓞 K)
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({γ} : Set (𝓞 K))) →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) γ =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrincipal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) γ := by
  classical
  unfold pthSymbolAtPrincipal_canonical stickelbergerPrincipalGen
  -- Step 1: distribute pthSymbolAtIdeal_canonical over Finset-prod numerator.
  rw [pthSymbolAtIdeal_canonical_finset_prod_α (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val))
    (I := Ideal.span ({γ} : Set (𝓞 K)))
    (fun a _ P hP h_in_pow => ?_)]
  · -- Step 2: each (σ_{a^{-1}} α)^a.val term unfolds via _pow_α.
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pthSymbolAtIdeal_canonical_pow_α (p := p)
      (fun P hP => h_coprime a P hP) ((a : ZMod p).val)]
  · -- side condition for finset_prod: (σ_{a^{-1}} α)^a.val ∉ P.
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    haveI hP_prime : P.IsPrime := hP_max.isPrime
    have h_in : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∈ P :=
      hP_prime.mem_of_pow_mem ((a : ZMod p).val) h_in_pow
    exact (h_coprime a P hP) h_in

/-- **Ideal-denominator Galois-sum decomposition of `(α^Θ / B)_p`**.

This is the arbitrary-ideal analogue of
`pthSymbolAtPrincipal_canonical_principalGen_left_eq_galois_sum`. It is the
form needed for Eisenstein reciprocity, where the denominator is a general
integral ideal `B` before specializing to a rational principal ideal. -/
theorem pthSymbolAtIdeal_canonical_principalGen_left_eq_galois_sum
    (α : 𝓞 K) (B : Ideal (𝓞 K))
    (h_coprime : ∀ (a : CyclotomicUnitDelta p)
      (P : Ideal (𝓞 K)), P ∈ UniqueFactorizationMonoid.normalizedFactors B →
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtIdeal_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) B := by
  classical
  unfold stickelbergerPrincipalGen
  rw [pthSymbolAtIdeal_canonical_finset_prod_α (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α) ^ ((a : ZMod p).val))
    (I := B)
    (fun a _ P hP h_in_pow => ?_)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [pthSymbolAtIdeal_canonical_pow_α (p := p)
      (fun P hP => h_coprime a P hP) ((a : ZMod p).val)]
  · obtain ⟨_, _hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    haveI hP_prime : P.IsPrime := hP_max.isPrime
    have h_in : cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∈ P :=
      hP_prime.mem_of_pow_mem ((a : ZMod p).val) h_in_pow
    exact (h_coprime a P hP) h_in

end Furtwaengler

end BernoulliRegular

end
