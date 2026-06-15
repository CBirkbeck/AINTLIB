module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical

/-!
# `phi` as an ideal-class-invariant function (REF-20 — structural reduction)

This file packages the **structural reduction** that turns the
universal REF-19 hypothesis (the canonical residue symbol of a
hyperprimary `η` vanishes on every nonzero principal ideal) into the
ideal-class-invariance statement underlying REF-20:

  `pthSymbolAtIdeal_canonical η (I · (γ)) = pthSymbolAtIdeal_canonical η I`

for every nonzero ideal `I` and nonzero `γ ∈ 𝓞 K`.

This is exactly the well-definedness condition for the `phi` map of
REF-20, viewed at the integer-ideal level (before the lift to
`ClassGroup (𝓞 K)`).

## Strategy

The substantive content is the universal REF-19 hypothesis; the
class-invariance is then a one-line application of
`pthSymbolAtIdeal_canonical_mul_ideal` (multiplicativity in the ideal
slot).

This separation makes explicit that REF-20's well-definedness reduces
**purely structurally** to REF-19 in its universal form, and that the
remaining work to fully realise REF-20 is to construct the lift from
the integer-ideal level to `ClassGroup (𝓞 K)` (a standard `Quotient.lift`
once the universal REF-19 hypothesis is established).

## Main definitions

* `Ref19UniversalHypothesis η` — the universal REF-19 hypothesis: the
  canonical residue symbol vanishes on every nonzero principal ideal
  for the hyperprimary input `η`.

* `pthSymbolAtIdeal_canonical_mul_principal_eq_self` — the
  ideal-class-invariance statement: `pthSymbolAtIdeal_canonical η
  (I · (γ)) = pthSymbolAtIdeal_canonical η I`.

* `pthSymbolAtIdeal_canonical_eq_of_principalIdeal_factor` — generalised
  invariance under multiplication by any product of principal ideals.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Universal REF-19 hypothesis** for a fixed hyperprimary `η : 𝓞 K`.
Asserts that the canonical residue symbol of `η` vanishes on every
nonzero principal ideal of `𝓞 K`.

This is the universal-quantification strengthening of the per-`γ`
REF-19 conclusion `pthSymbolAtIdeal_canonical η ((γ)) = 0` produced
by the canonical chain (`KummerFurtwaenglerCanonical_REF19` and
variants) at specific `γ` coming from the Stickelberger / Dwork
chain. -/
def Ref19UniversalHypothesis (η : 𝓞 K) : Prop :=
  ∀ γ : 𝓞 K, γ ≠ 0 →
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0

/-- **Class-invariance under principal-ideal multiplication.**

Given the universal REF-19 hypothesis for `η`, the canonical residue
symbol is invariant under multiplying any nonzero ideal by a nonzero
principal ideal. This is the integer-ideal-level well-definedness
content underlying REF-20's lift to `ClassGroup (𝓞 K)`. -/
theorem pthSymbolAtIdeal_canonical_mul_principal_eq_self
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {γ : 𝓞 K} (hγ : γ ≠ 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (I * Ideal.span ({γ} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  have hγI : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hγ
  rw [pthSymbolAtIdeal_canonical_mul_ideal (p := p) η hI hγI,
      h_ref19 γ hγ, add_zero]

/-- **Symmetric form**: invariance also holds when the principal factor
is on the left. Direct from `mul_comm` and the right-side version. -/
theorem pthSymbolAtIdeal_canonical_principal_mul_eq_self
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {γ : 𝓞 K} (hγ : γ ≠ 0)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K)) * I) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [mul_comm]
  exact pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hI hγ

/-- **Generalised: invariance under multiplication by a finite product
of principal ideals.** The class-invariance extends to arbitrary
products of nonzero principal ideals via induction. -/
theorem pthSymbolAtIdeal_canonical_eq_of_principalIdeal_factor
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {ι : Type*} (s : Finset ι) (γ : ι → 𝓞 K)
    (hγ : ∀ i ∈ s, γ i ≠ 0)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (I * ∏ i ∈ s, Ideal.span ({γ i} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hγi : γ i ≠ 0 := hγ i (Finset.mem_insert_self _ _)
    have hγs : ∀ j ∈ s, γ j ≠ 0 := fun j hj =>
      hγ j (Finset.mem_insert_of_mem hj)
    -- I * (span(γi) * ∏) = (I * span(γi)) * ∏ = (I * ∏) * span(γi)
    -- via associativity and commutativity. Reduce in two steps:
    -- 1. mult by span(γi) (via principal_mul_eq_self),
    -- 2. mult by ∏ (via inductive hypothesis).
    rw [show I * (Ideal.span ({γ i} : Set (𝓞 K)) *
        ∏ j ∈ s, Ideal.span ({γ j} : Set (𝓞 K))) =
        (I * ∏ j ∈ s, Ideal.span ({γ j} : Set (𝓞 K))) *
          Ideal.span ({γ i} : Set (𝓞 K)) by ring]
    have hProd_ne : (∏ j ∈ s, Ideal.span ({γ j} : Set (𝓞 K))) ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
      push Not
      intro j hj
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hγs j hj
    have hIs : I * ∏ j ∈ s, Ideal.span ({γ j} : Set (𝓞 K)) ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero]
      push Not
      refine ⟨by rwa [Ideal.zero_eq_bot], ?_⟩
      rwa [Ideal.zero_eq_bot]
    rw [pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hIs hγi,
        ih hγs]

/-- **Class-invariance under principal-ideal absorption.** Given the
universal REF-19 hypothesis, if `J = I * (γ)` for some nonzero `γ`, then
`phi η J = phi η I`.

This is the bridge form needed for downstream class-group calculations
that need to identify ideal classes by absorbing principal factors. -/
theorem pthSymbolAtIdeal_canonical_eq_of_principal_factor
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    {γ : 𝓞 K} (hγ : γ ≠ 0)
    (hfac : J = I * Ideal.span ({γ} : Set (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η J =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [hfac, pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hI hγ]

/-! ### `phi` factors through the elementary `p`-quotient

The canonical residue symbol on integer ideals is `p`-torsion in `ZMod p`:
multiplying any ideal `I` by a `p`-th power `J^p` leaves the symbol
unchanged. Combined with class invariance, this means `phi η` factors
through the elementary `p`-quotient at the integer-ideal level. -/

/-- **`phi` is invariant under `p`-th-power multiplication.**
`pthSymbolAtIdeal_canonical η (I · J^p) = pthSymbolAtIdeal_canonical η I`
for any nonzero `I, J`. The proof uses multiplicativity in the ideal
slot together with `pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero`. -/
theorem pthSymbolAtIdeal_canonical_mul_pow_p_eq_self
    (η : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I * J ^ p) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  have hJp : J ^ p ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, pow_eq_zero_iff (Fact.out : p.Prime).pos.ne']
    rwa [Ideal.zero_eq_bot]
  rw [pthSymbolAtIdeal_canonical_mul_ideal η hI hJp,
      pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero, add_zero]

/-- **`phi` is invariant under `p`-th-power factor on the left.** -/
theorem pthSymbolAtIdeal_canonical_pow_p_mul_eq_self
    (η : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (J ^ p * I) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [mul_comm]
  exact pthSymbolAtIdeal_canonical_mul_pow_p_eq_self η hI hJ

/-- **Combined invariance: principal ideal × `p`-th power.** Under
`Ref19UniversalHypothesis`, `phi η (I · (γ) · J^p) = phi η I`.
This is the full content of `phi η` factoring through the elementary
`p`-quotient of the ideal class group. -/
theorem pthSymbolAtIdeal_canonical_mul_principal_mul_pow_p_eq_self
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    {γ : 𝓞 K} (hγ : γ ≠ 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (I * Ideal.span ({γ} : Set (𝓞 K)) * J ^ p) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  have hI_principal_ne : I * Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero]
    push Not
    refine ⟨by rwa [Ideal.zero_eq_bot], ?_⟩
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hγ
  rw [pthSymbolAtIdeal_canonical_mul_pow_p_eq_self η hI_principal_ne hJ]
  exact pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hI hγ

/-- **Equal symbols on ideals related by principal factor + `p`-th power.**

If `J = I · (γ) · K^p` for nonzero `γ`, `K`, then `phi η J = phi η I`.
This is the integer-ideal-level statement of "phi factors through
ClassGroupModP". -/
theorem pthSymbolAtIdeal_canonical_eq_of_eq_principal_mul_pow_p
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I J Ip : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hIp : Ip ≠ ⊥)
    {γ : 𝓞 K} (hγ : γ ≠ 0)
    (hJ : J = I * Ideal.span ({γ} : Set (𝓞 K)) * Ip ^ p) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η J =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [hJ]
  exact pthSymbolAtIdeal_canonical_mul_principal_mul_pow_p_eq_self
    h_ref19 hI hIp hγ

/-- **Symmetric class-invariance**: equal symbols on ideals differing by
a principal factor on either side. -/
theorem pthSymbolAtIdeal_canonical_eq_of_eq_principal_mul
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    {γ δ : 𝓞 K} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (heq : I * Ideal.span ({γ} : Set (𝓞 K)) =
           J * Ideal.span ({δ} : Set (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η J := by
  have h1 : pthSymbolAtIdeal_canonical (p := p) (K := K) η
      (I * Ideal.span ({γ} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I :=
    pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hI hγ
  have h2 : pthSymbolAtIdeal_canonical (p := p) (K := K) η
      (J * Ideal.span ({δ} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η J :=
    pthSymbolAtIdeal_canonical_mul_principal_eq_self h_ref19 hJ hδ
  rw [← h1, heq, h2]

end Furtwaengler

end BernoulliRegular
