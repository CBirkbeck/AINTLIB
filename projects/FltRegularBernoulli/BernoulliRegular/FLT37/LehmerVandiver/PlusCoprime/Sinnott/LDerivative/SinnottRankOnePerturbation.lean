import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.EmbeddingIndexBijectivity

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`q(familyIndexAsUnit i) ≠ 1`** in `CyclotomicEvenDelta p`. Direct from
`familyIndexAsUnit_ne_one_and_neg_one`: q-equality with 1 means the unit
itself is in `⟨-1⟩ = {1, -1}`. -/
theorem familyIndexAsUnit_quotient_ne_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) ≠ 1 := by
  classical
  intro h
  -- q(a) = 1 iff a ∈ kernel = CyclotomicEvenDeltaSubgroup = ⟨-1⟩.
  have h_mem : familyIndexAsUnit p K hp_odd hp_three i ∈
      BernoulliRegular.CyclotomicEvenDeltaSubgroup p := by
    rw [← QuotientGroup.eq_one_iff]
    exact h
  rw [BernoulliRegular.CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at h_mem
  obtain ⟨k, hk⟩ := h_mem
  have h_sq : ((-1 : BernoulliRegular.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ne_one, h_ne_neg_one⟩ :=
    familyIndexAsUnit_ne_one_and_neg_one (p := p) K hp_odd hp_three hp_ge_five i
  rcases h_mod with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact h_ne_one hk.symm
  · rw [h1, zpow_one] at hk
    exact h_ne_neg_one hk.symm

/-- **`familyIndexAsUnit` is injective**: distinct family indices give
distinct `(ZMod p)ˣ` units.

Reason: the underlying ZMod p-value of `familyIndexAsUnit i` is `idx_i + 2`,
which is determined by the family index `i`. -/
theorem familyIndexAsUnit_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Function.Injective (familyIndexAsUnit p K hp_odd hp_three) := by
  classical
  intro i₁ i₂ h_eq
  -- Same unit → same val → same idx → same Fin → same i.
  have h_val_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
    rw [h_eq]
  have h_p_prime : Nat.Prime p := hp.out
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨n, hn⟩
  set j₁ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₁).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₁_def
  set j₂ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₂).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₂_def
  have h_j₁_lt : j₁.val < (p - 3) / 2 := Fin.isLt _
  have h_j₂_lt : j₂.val < (p - 3) / 2 := Fin.isLt _
  have h_lt_p₁ : j₁.val + 2 < p := by omega
  have h_lt_p₂ : j₂.val + 2 < p := by omega
  have h_v1 : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      j₁.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₁
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₁
  have h_v2 : ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
      j₂.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₂
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₂
  rw [h_v1, h_v2] at h_val_eq
  have h_fin_eq : j₁.val = j₂.val := by omega
  have h_fin : j₁ = j₂ := Fin.ext h_fin_eq
  -- j₁ = Fin.cast _ (eqFR.symm i₁), and similarly for j₂.
  -- Since cast is injective: eqFR.symm i₁ = eqFR.symm i₂.
  have h_symm_eq : (NumberField.Units.equivFinRank
      (NumberField.maximalRealSubfield K)).symm i₁ =
      (NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i₂ := by
    have h_val_symm : (((NumberField.Units.equivFinRank
          (NumberField.maximalRealSubfield K)).symm i₁) : ℕ) =
        (((NumberField.Units.equivFinRank
          (NumberField.maximalRealSubfield K)).symm i₂) : ℕ) := h_fin_eq
    exact Fin.ext h_val_symm
  exact (NumberField.Units.equivFinRank
      (NumberField.maximalRealSubfield K)).symm.injective h_symm_eq

/-- **`q ∘ familyIndexAsUnit` is injective**: distinct family indices give
distinct quotient elements in `CyclotomicEvenDelta p`.

Reason: `familyIndexAsUnit i` has value in `[2, (p-1)/2]` as a `ZMod p`
element. Negating sends this to `[(p+1)/2, p-2]` (the val of `-a` is `p - val(a)`),
which is disjoint from `[2, (p-1)/2]` for `p ≥ 5`. So
`familyIndexAsUnit i₁ ≠ -familyIndexAsUnit i₂`. Combined with
`familyIndexAsUnit_injective`, the composite `q ∘ familyIndexAsUnit` is
injective. -/
theorem familyIndexAsUnit_quotient_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (fun i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =>
      BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i)) := by
  classical
  intro i₁ i₂ h_eq
  simp only at h_eq
  -- The familyIndexAsUnit values are equal in the quotient.
  have h_div : familyIndexAsUnit p K hp_odd hp_three i₁ /
      familyIndexAsUnit p K hp_odd hp_three i₂ ∈
      BernoulliRegular.CyclotomicEvenDeltaSubgroup p :=
    QuotientGroup.eq_iff_div_mem.mp h_eq
  rw [div_eq_mul_inv, BernoulliRegular.CyclotomicEvenDeltaSubgroup,
      Subgroup.mem_zpowers_iff] at h_div
  obtain ⟨k, hk⟩ := h_div
  have h_sq : ((-1 : BernoulliRegular.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ge_one, h_le_one⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₁
  obtain ⟨h_ge_two, h_le_two⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₂
  rcases h_mod with h0 | h1
  · -- Case 1: a₁ * a₂⁻¹ = 1. So a₁ = a₂, hence i₁ = i₂.
    rw [h0, zpow_zero] at hk
    have h_a_eq : familyIndexAsUnit p K hp_odd hp_three i₁ =
        familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, one_mul] at this
    exact familyIndexAsUnit_injective (p := p) K hp_odd hp_three h_a_eq
  · -- Case 2: a₁ * a₂⁻¹ = -1. So a₁ = -a₂. But val(a₁), val(a₂) ∈ [2, (p-1)/2],
    -- val(-a₂) = p - val(a₂) ∈ [(p+1)/2, p-2], disjoint range. Contradiction.
    rw [h1, zpow_one] at hk
    have h_neg : familyIndexAsUnit p K hp_odd hp_three i₁ =
        -familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          -1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, neg_one_mul] at this
    -- val of (-a₂) is p - val(a₂).
    have h_p_prime : Nat.Prime p := hp.out
    haveI : NeZero p := ⟨h_p_prime.ne_zero⟩
    haveI : NeZero ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p) := by
      refine ⟨?_⟩
      intro h_zero
      rw [show ((((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p)).val) = 0 from
        by rw [h_zero]; exact ZMod.val_zero] at h_ge_two
      omega
    have h_v_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
        ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_neg]
    have h_v_neg : ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      change ((-((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p))).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val
      exact ZMod.val_neg_of_ne_zero _
    rw [h_v_neg] at h_v_eq
    -- `v₁ = p - v₂`, while both indices lie in incompatible half ranges.
    omega

/-- **Row-side bijection** (cardinality form): the family-index set
`{w_K⁺ // w ≠ w₀}` bijects to `{c : CyclotomicEvenDelta p // c ≠ 1}`.

Both have cardinality `(p-3)/2`. Established via `Fintype.equivOfCardEq` after
proving the cardinality equality via the canonical embedding-index bijection. -/
noncomputable def familyIndexEquivNonTrivialCE
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_odd : p ≠ 2) (_hp_three : 3 ≤ p)
    (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Fintype.equivOfCardEq ?_
  -- Use the canonical bijection InfinitePlace K⁺ ≃ CyclotomicEvenDelta p
  -- and reduce the subtype cardinalities to (p-1)/2 - 1 = (p-3)/2 each.
  have h_bij : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical
      (p := p) K hp_two
  -- LHS = # InfinitePlace K⁺ - 1
  -- RHS = # CyclotomicEvenDelta p - 1
  -- Equal because both ambient cardinalities are equal via h_bij.
  rw [Fintype.card_subtype_compl (p := fun w ↦
    w = NumberField.Units.dirichletUnitTheorem.w₀)]
  rw [Fintype.card_subtype_compl (p := fun c ↦ c = 1)]
  rw [Fintype.card_congr h_bij]
  rfl

/-- **Row-side bijection bundle** (functional form): for each family-index `i`,
`q(familyIndexAsUnit i)` lies in `{c : CyclotomicEvenDelta p // c ≠ 1}`.

Packages `familyIndexAsUnit_quotient_ne_one` into a function with codomain
restricted to the non-trivial subtype. -/
noncomputable def familyIndexAsCEnotOne
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1} :=
  ⟨BernoulliRegular.cyclotomicEvenDeltaQuotient p
      (familyIndexAsUnit p K hp_odd hp_three i),
    familyIndexAsUnit_quotient_ne_one (p := p) K hp_odd hp_three hp_ge_five i⟩

/-- **`familyIndexAsCEnotOne` is injective**: bundles
`familyIndexAsUnit_quotient_injective` into the subtype codomain form. -/
theorem familyIndexAsCEnotOne_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) := by
  intro i₁ i₂ h_eq
  have h_eq_val : (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₁).val =
      (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₂).val := by
    rw [h_eq]
  exact familyIndexAsUnit_quotient_injective (p := p) K hp_odd hp_three hp_ge_five h_eq_val

/-- **Row-side bijection** as an `Equiv` via `familyIndexAsCEnotOne`.

Bundles `familyIndexAsCEnotOne_injective` + cardinality equality
(`familyIndexEquivNonTrivialCE`) into a noncomputable `Equiv` from
the family-index set to `{c : CyclotomicEvenDelta p // c ≠ 1}`. -/
noncomputable def familyIndexAsCEnotOneEquiv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Equiv.ofBijective
    (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) ?_
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨familyIndexAsCEnotOne_injective (p := p) K hp_odd hp_three hp_ge_five, ?_⟩
  -- Cardinality equality from the shipped familyIndexEquivNonTrivialCE.
  exact Fintype.card_congr
    (familyIndexEquivNonTrivialCE (p := p) K hp_odd hp_three hp_two)

/-- **Specification of `familyIndexAsCEnotOneEquiv`**: the apply value
unwraps to `q(familyIndexAsUnit i)`. -/
@[simp]
theorem familyIndexAsCEnotOneEquiv_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (familyIndexAsCEnotOneEquiv (p := p) K hp_odd hp_three hp_ge_five hp_two i).val =
      BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) :=
  rfl

/-- **Specification of `KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical`**:
the canonical bijection sends `v` to `kplusEmbeddingIndexQuotient v`. -/
@[simp]
theorem KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    (v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :
    KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical (p := p) K hp_two v =
      kplusEmbeddingIndexQuotient (p := p) K v :=
  rfl

/-- **Cardinality of `{c : CyclotomicEvenDelta p // c ≠ 1}`** equals `(p-3)/2`.

Direct from `Fintype.card_subtype_compl` + `cyclotomicEvenDelta_card`. -/
theorem fintype_card_nonTrivialCE_eq (hp_two : 2 < p) :
    Fintype.card {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1} =
      (p - 1) / 2 - 1 := by
  classical
  rw [Fintype.card_subtype_compl (p := fun c ↦ c = 1)]
  rw [BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two]
  rw [Fintype.card_subtype_eq]

/-- **Shifted K⁺-place embedding-index quotient**: divides
`kplusEmbeddingIndexQuotient` by `kplusEmbeddingIndexQuotient w₀`, so that
the distinguished place `w₀` maps to `1` in `CyclotomicEvenDelta p`.

Useful for matrix-level reindexing where one wants the excluded "base"
column to correspond to the identity element of `CyclotomicEvenDelta p`. -/
noncomputable def kplusEmbeddingIndexQuotientShifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :
    BernoulliRegular.CyclotomicEvenDelta p :=
  kplusEmbeddingIndexQuotient (p := p) K v *
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹

/-- **Shifted quotient sends `w₀` to `1`**. -/
@[simp]
theorem kplusEmbeddingIndexQuotientShifted_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    kplusEmbeddingIndexQuotientShifted (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 := by
  unfold kplusEmbeddingIndexQuotientShifted
  exact mul_inv_cancel _

/-- **Shifted quotient is a bijection**: the shifted version of the K⁺-place
embedding-index quotient is also a bijection `InfinitePlace K⁺ ≃
CyclotomicEvenDelta p`. Multiplication by `k(w₀)⁻¹` is a group bijection
(an `Equiv` of CE with itself), so the composition with the bijective
`kplusEmbeddingIndexQuotient` is a bijection. -/
theorem kplusEmbeddingIndexQuotientShifted_bijective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    Function.Bijective (kplusEmbeddingIndexQuotientShifted (p := p) K) := by
  classical
  -- Compose the shipped column-side bijection with right-multiplication
  -- by (k(w₀))⁻¹ in the abelian group CyclotomicEvenDelta p.
  set kw₀_inv : BernoulliRegular.CyclotomicEvenDelta p :=
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹ with h_kw₀_inv
  have h_mul_bij : Function.Bijective
      (fun c : BernoulliRegular.CyclotomicEvenDelta p ↦ c * kw₀_inv) :=
    Group.mulRight_bijective kw₀_inv
  exact h_mul_bij.comp (kplusEmbeddingIndexQuotient_bijective (p := p) K hp_two)

/-- **Shifted K⁺-place ↔ CyclotomicEvenDelta p Equiv**: bundles the shifted
bijection that sends `w₀ → 1` into a noncomputable `Equiv`. -/
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
  Equiv.ofBijective (kplusEmbeddingIndexQuotientShifted (p := p) K)
    (kplusEmbeddingIndexQuotientShifted_bijective (p := p) K hp_two)

/-- **Apply spec for shifted bijection**: `_apply v = k(v) * k(w₀)⁻¹`. -/
@[simp]
theorem KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    (v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted (p := p) K hp_two v =
      kplusEmbeddingIndexQuotientShifted (p := p) K v :=
  rfl

/-- **Shifted Apply at `w₀`**: the shifted bijection at the distinguished
place `w₀` gives `1` (the identity element of `CyclotomicEvenDelta p`). -/
@[simp]
theorem KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted (p := p) K hp_two
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
  kplusEmbeddingIndexQuotientShifted_w₀ (p := p) K

/-- **K⁺-place sum equals CyclotomicEvenDelta p sum via the canonical bijection**:
for any function `f : CyclotomicEvenDelta p → ℂ`, summing `f ∘ kplusEmbeddingIndexQuotient`
over `InfinitePlace K⁺` equals summing `f` over `CyclotomicEvenDelta p`. -/
theorem sum_kplus_eq_sum_CE
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    ∑ v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K),
        f (kplusEmbeddingIndexQuotient (p := p) K v) =
      ∑ c : BernoulliRegular.CyclotomicEvenDelta p, f c := by
  classical
  rw [← Equiv.sum_comp
    (KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical (p := p) K hp_two) f]
  rfl

/-- **Restricted sum**: sum over `{w_K⁺ // w ≠ w₀}` of any function
`f : CyclotomicEvenDelta p → ℂ` composed with `kplusEmbeddingIndexQuotientShifted`
equals sum over `CE \ {1}` directly.

Uses the shifted bijection which sends `w₀ ↦ 1`, so the restriction to
`{w ≠ w₀}` corresponds to `CE \ {1}`. -/
theorem sum_kplus_ne_w₀_shifted_eq_sum_CE_ne_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Fintype {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1}]
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    ∑ v : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
        f (kplusEmbeddingIndexQuotientShifted (p := p) K v.val) =
      ∑ c : {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1}, f c.val := by
  classical
  -- Use the shifted bijection restricted to subtypes via Equiv.subtypeEquiv.
  -- v ≠ w₀ ↔ shifted_apply v ≠ shifted_apply w₀ = 1.
  let e : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted (p := p) K hp_two
  have h_w₀_eq : e NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀ (p := p) K hp_two
  let e_sub : {w // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : BernoulliRegular.CyclotomicEvenDelta p // c ≠ 1} :=
    e.subtypeEquiv (fun v ↦ by
      constructor
      · intro h h_eq
        apply h
        rw [← h_w₀_eq] at h_eq
        exact e.injective h_eq
      · intro h h_eq
        apply h
        rw [h_eq, h_w₀_eq])
  rw [← Equiv.sum_comp e_sub (fun c ↦ f c.val)]
  rfl

/-- **Character-weighted column sum of `convolutionMatrixLogNormEven`**:

  `∑ c : CyclotomicEvenDelta p, ξ(c) · M_even[c, b] = ξ(b⁻¹) · qe(ξ)`.

Direct from `quotientEigenvalue`'s definition and a `c ↦ c · b⁻¹` substitution. -/
theorem sum_char_convolutionMatrixLogNormEven_col
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    ∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        ξ c * convolutionMatrixLogNormEven p c b =
      ξ b⁻¹ * quotientEigenvalue p ξ := by
  classical
  unfold quotientEigenvalue convolutionMatrixLogNormEven
  -- Apply ∑ c, ξ(c) · M[c, b] = ∑ c, ξ(c) · f(c·b) = ξ(b⁻¹) · ∑ c', ξ(c') · f(c')
  -- via the substitution c ↦ c · b⁻¹.
  rw [Finset.mul_sum]
  -- Use the bijection `c ↦ c·b⁻¹` in reverse.
  -- Apply Equiv.sum_comp with `Equiv.mulRight b` to rewrite LHS sum.
  rw [show (∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        ξ c * (Matrix.of fun a b ↦ convolutionLogNormDescended p (a * b)) c b) =
      ∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        ξ (c * b⁻¹) * (Matrix.of fun a b' ↦ convolutionLogNormDescended p (a * b'))
          (c * b⁻¹) b from
    (Equiv.sum_comp (Equiv.mulRight b⁻¹) _).symm]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [Matrix.of_apply]
  -- (c · b⁻¹) · b = c.
  have h_simp : (c * b⁻¹) * b = c := by group
  rw [h_simp, map_mul, map_inv]
  ring

/-- **Character-weighted sum of `M_even[c, b] - M_even[c, 1]`**:

  `∑_c ξ(c) · (M_even[c, b] - M_even[c, 1]) = (ξ(b⁻¹) - 1) · qe(ξ)`.

Direct: subtract the two character-weighted column sums via
`sum_char_convolutionMatrixLogNormEven_col`, using `ξ(1⁻¹) = ξ(1) = 1`. -/
theorem sum_char_convolutionMatrixLogNormEven_col_diff
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    ∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        ξ c * (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      (ξ b⁻¹ - 1) * quotientEigenvalue p ξ := by
  classical
  have h_sub : ∀ c : BernoulliRegular.CyclotomicEvenDelta p,
      ξ c * (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      ξ c * convolutionMatrixLogNormEven p c b -
        ξ c * convolutionMatrixLogNormEven p c 1 := by
    intro c; ring
  rw [Finset.sum_congr rfl (fun c _ ↦ h_sub c)]
  rw [Finset.sum_sub_distrib]
  rw [sum_char_convolutionMatrixLogNormEven_col, sum_char_convolutionMatrixLogNormEven_col]
  rw [inv_one, MulChar.map_one]
  ring

/-- **Trivial-character eigenvalue of `M_even[·, b] - M_even[·, 1]` vanishes**:

  `∑_c (M_even[c, b] - M_even[c, 1]) = 0`

(for any `b ∈ CyclotomicEvenDelta p`).

Direct corollary of `sum_char_convolutionMatrixLogNormEven_col_diff` at
the trivial character ξ = 1: `(1(b⁻¹) - 1) · qe(1) = 0 · qe(1) = 0`. This
is the structural reason the matrix `(A - B)` has 'rank deficiency at
the trivial character' — its trivial-character row-sum vanishes for
any column index. -/
theorem sum_convolutionMatrixLogNormEven_col_diff_eq_zero
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    ∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) = 0 := by
  classical
  have h := sum_char_convolutionMatrixLogNormEven_col_diff (p := p) 1 b
  -- At trivial character, ξ c = 1(c) = 1 (for c ∈ units; matched on CyclotomicEvenDelta
  -- p via the trivial MulChar on the group). So the LHS becomes the unweighted sum.
  -- And (1(b⁻¹) - 1) = (1 - 1) = 0, hence RHS = 0.
  have h_one : ∀ c : BernoulliRegular.CyclotomicEvenDelta p,
      (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) c *
        (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      convolutionMatrixLogNormEven p c b -
        convolutionMatrixLogNormEven p c 1 := by
    intro c
    rw [MulChar.one_apply (Group.isUnit c)]
    ring
  rw [Finset.sum_congr rfl (fun c _ ↦ h_one c)] at h
  rw [h]
  rw [show ((1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) b⁻¹ - 1) = 0 from by
    rw [MulChar.one_apply (Group.isUnit _)]; ring]
  ring

/-- **Restricted character-weighted sum of column-difference**: summing
`(M_even[c, b] - M_even[c, 1])` weighted by `ξ(c)` over `c ≠ c₀` for some
fixed `c₀` (typically `kplusEmbeddingIndexQuotient w₀`) equals the full sum
minus the c = c₀ term:

  `∑_{c ≠ c₀} ξ(c) · (M_even[c, b] - M_even[c, 1])
   = (ξ(b⁻¹) - 1) · qe(ξ) - ξ(c₀) · (M_even[c₀, b] - M_even[c₀, 1])`.

This is the "correction term" structure: the restricted sum equals the
full sum minus the excluded term. Useful for matrix-restriction analysis. -/
theorem sum_char_convolutionMatrixLogNormEven_col_diff_restricted
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (b c₀ : BernoulliRegular.CyclotomicEvenDelta p) :
    ∑ c ∈ (Finset.univ : Finset (BernoulliRegular.CyclotomicEvenDelta p)).erase c₀,
        ξ c * (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      (ξ b⁻¹ - 1) * quotientEigenvalue p ξ -
        ξ c₀ * (convolutionMatrixLogNormEven p c₀ b -
          convolutionMatrixLogNormEven p c₀ 1) := by
  classical
  have h_split :
      ∑ c : BernoulliRegular.CyclotomicEvenDelta p,
        ξ c * (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      ξ c₀ * (convolutionMatrixLogNormEven p c₀ b -
          convolutionMatrixLogNormEven p c₀ 1) +
        ∑ c ∈ (Finset.univ : Finset (BernoulliRegular.CyclotomicEvenDelta p)).erase c₀,
          ξ c * (convolutionMatrixLogNormEven p c b -
            convolutionMatrixLogNormEven p c 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)]
  have h_full := sum_char_convolutionMatrixLogNormEven_col_diff (p := p) ξ b
  linear_combination h_full - h_split

/-- **Restricted character-weighted sum at the trivial character vanishes
modulo the w₀-correction**: instantiating the restricted sum at `ξ = 1`,

  `∑_{c ≠ c₀} (M_even[c, b] - M_even[c, 1])
   = - (M_even[c₀, b] - M_even[c₀, 1])`.

Direct corollary of `sum_char_convolutionMatrixLogNormEven_col_diff_restricted`
at `ξ = 1` (where the full sum vanishes by
`sum_convolutionMatrixLogNormEven_col_diff_eq_zero`). -/
theorem sum_convolutionMatrixLogNormEven_col_diff_restricted_trivial
    (b c₀ : BernoulliRegular.CyclotomicEvenDelta p) :
    ∑ c ∈ (Finset.univ : Finset (BernoulliRegular.CyclotomicEvenDelta p)).erase c₀,
        (convolutionMatrixLogNormEven p c b -
          convolutionMatrixLogNormEven p c 1) =
      -(convolutionMatrixLogNormEven p c₀ b -
          convolutionMatrixLogNormEven p c₀ 1) := by
  classical
  have h := sum_convolutionMatrixLogNormEven_col_diff_eq_zero (p := p) b
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)] at h
  linear_combination h

/-- **Character-weighted sum of `(sinnottMatrixA - sinnottMatrixB)[i, ·]`**:

For any character `ξ : MulChar (CyclotomicEvenDelta p) ℂ`, summing
`(sinnottMatrixA - sinnottMatrixB)[i, w]` with weight
`ξ(kplusEmbeddingIndexQuotient w.val)` over all `w : {InfinitePlace K⁺ // ≠ w₀}`
equals the restricted character-weighted column-difference sum at
`c₀ = kplusEmbeddingIndexQuotient w₀`.

This is the matrix-level character analysis applied to the (A - B) matrix:
the χ-eigenvalue is a specific sum over `CyclotomicEvenDelta p`. -/
theorem sum_char_sinnottMatrix_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (_hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ∑ w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      ξ (kplusEmbeddingIndexQuotient (p := p) K w.val) *
        ((((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      ∑ w : {w : NumberField.InfinitePlace
          (NumberField.maximalRealSubfield K) //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
        ξ (kplusEmbeddingIndexQuotient (p := p) K w.val) *
          (convolutionMatrixLogNormEven p
              (kplusEmbeddingIndexQuotient (p := p) K w.val)
              (BernoulliRegular.cyclotomicEvenDeltaQuotient p
                (familyIndexAsUnit p K hp_odd hp_three i)) -
            convolutionMatrixLogNormEven p
              (kplusEmbeddingIndexQuotient (p := p) K w.val) 1) := by
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]

/-- **Restricted K⁺-place subtype ↔ `CE \ {k(w₀)}` subtype bijection**:
under the canonical (non-shifted) bijection `kplusEmbeddingIndexQuotient`,
the subtype `{w // ≠ w₀}` maps bijectively to
`{c : CyclotomicEvenDelta p // c ≠ kplusEmbeddingIndexQuotient w₀}`. -/
noncomputable def KplusInfinitePlaceNotW₀Equiv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀} := by
  classical
  let e : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical (p := p) K hp_two
  refine e.subtypeEquiv (fun v ↦ ?_)
  constructor
  · intro h h_eq
    exact h <| e.injective h_eq
  · intro h h_eq
    apply h
    rw [h_eq]
    exact KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical_apply
      (p := p) K hp_two _

/-- **Sum over `{w ≠ w₀}` of `f ∘ k`** equals sum over `CE \ {k(w₀)}` of `f`. -/
theorem sum_kplus_not_w₀_eq_sum_CE_not_kw₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Fintype {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    ∑ w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      f (kplusEmbeddingIndexQuotient (p := p) K w.val) =
    ∑ c : {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀},
      f c.val := by
  classical
  rw [← Equiv.sum_comp
    (KplusInfinitePlaceNotW₀Equiv (p := p) K hp_two) (fun c ↦ f c.val)]
  rfl

/-- **Character-weighted sum of `(A - B)` rows in CE-subtype form**:

For any character `ξ`, the character-weighted sum of
`(sinnottMatrixA - sinnottMatrixB)[i, w]` over `{w ≠ w₀}` translates
(via the canonical bijection) to a restricted CE-subtype sum:

  ∑_{w ≠ w₀} ξ(k(w)) · ((A-B)[i,w] : ℂ)
  = ∑_{c ≠ k(w₀)} ξ(c) · (M_even[c, q(famIdx i)] - M_even[c, 1])

This is the K⁺-side ↔ CE-side bridge applied to the `(A - B)`-shape. -/
theorem sum_kplus_not_w₀_char_sinnottMatrix_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Fintype {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ∑ w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      ξ (kplusEmbeddingIndexQuotient (p := p) K w.val) *
        ((((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
    ∑ c : {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀},
      ξ c.val * (convolutionMatrixLogNormEven p c.val
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p c.val 1) := by
  rw [sum_char_sinnottMatrix_A_sub_B (p := p) K hp_odd hp_three hp_two ξ i]
  exact sum_kplus_not_w₀_eq_sum_CE_not_kw₀ (p := p) K hp_two (fun c ↦ ξ c *
      (convolutionMatrixLogNormEven p c
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p c 1))


/-- **`KplusInfinitePlaceNotW₀Equiv_apply`**: the subtype bijection acts as
`kplusEmbeddingIndexQuotient` on the underlying value. -/
@[simp]
theorem KplusInfinitePlaceNotW₀Equiv_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    (v : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (KplusInfinitePlaceNotW₀Equiv (p := p) K hp_two v).val =
      kplusEmbeddingIndexQuotient (p := p) K v.val :=
  rfl

end Sinnott

end FLT37

end BernoulliRegular

end
