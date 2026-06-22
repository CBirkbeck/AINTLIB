module

public import BernoulliRegular.Reflection.ClassGroupModP.PhiGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerPrincipalGen
public import BernoulliRegular.Reflection.ClassGroupModP.PhiGaloisEigenspace.Part1

/-!
# Phi-Galois compatibility at general Galois weight (Section 6 of plan)

For η with eigenspace condition `σ_a η = η^{a^i} · u^p` (mod K^{×p}),
the phi-Galois compatibility takes the form

```
phi (galAction a v) = a^{1-i} · phi v.
```

This generalises `phiOnClassGroup_galois_of_fixed` (the `i = 0`, weight `k = 1`
case where σ_a η = η directly).

The chain uses:
1. `pthSymbolAtIdeal_canonical_galoisAction_of_fixed`: the Galois-shift
   formula on the residue symbol with σ_a-fixed numerator.
2. The hypothesis `σ_a η = η^{a^i} · u^p`: η has eigenspace `i` modulo
   `K^{×p}` under the Galois action.
3. Numerator-power formula plus p-th-power vanishing absorb the
   `η^{a^i}` factor and discharge the `u^p` factor, leaving the weight
   `k = 1 - i`.

This file provides the structural reduction. The eigenspace hypothesis
is supplied as `EigenspaceCondition`.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

set_option backward.isDefEq.respectTransparency false in
/-- **`EigenspaceCondition` closure under ℕ-power at any eigenspace i**:
if η satisfies eigenspace i, then η^n also does. -/
theorem eigenspaceCondition_pow_of_eigenspace_general
    {η : 𝓞 K} {i : ℕ} (h : EigenspaceCondition (p := p) (K := K) η i) (n : ℕ) :
    EigenspaceCondition (p := p) (K := K) (η ^ n) i := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u ^ n, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η ^ n) =
    (cyclotomicRingOfIntegersEquiv (p := p) K a η) ^ n from map_pow _ _ _,
    map_pow, map_pow, hu, mul_pow]
  ring

/-- **`StrongEigenspaceCondition` closure under ℕ-power at any eigenspace
i**: if η satisfies strong eigenspace i, then η^n also does, with new u
= u^n. The eigenspace is preserved (V_i + V_i = V_i in the same-i sense). -/
theorem strongEigenspaceCondition_pow_of_eigenspace_general
    {η : 𝓞 K} {i : ℕ} (h : StrongEigenspaceCondition (p := p) (K := K) η i)
    (n : ℕ) :
    StrongEigenspaceCondition (p := p) (K := K) (η ^ n) i := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u ^ n, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η ^ n) =
    (cyclotomicRingOfIntegersEquiv (p := p) K a η) ^ n from map_pow _ _ _]
  rw [hu, mul_pow]
  ring

/-- **`StrongEigenspaceCondition` closure under ℕ-power at eigenspace 0**:
if η satisfies strong eigenspace 0, then η^n also does, with new u = u^n. -/
theorem strongEigenspaceCondition_pow_of_eigenspace_zero
    {η : 𝓞 K} (h : StrongEigenspaceCondition (p := p) (K := K) η 0) (n : ℕ) :
    StrongEigenspaceCondition (p := p) (K := K) (η ^ n) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u ^ n, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η ^ n) =
    (cyclotomicRingOfIntegersEquiv (p := p) K a η) ^ n from map_pow _ _ _]
  simp only [pow_zero, pow_one] at hu ⊢
  rw [hu, mul_pow]
  ring

/-- **Per-prime numerator transform under StrongEigenspaceCondition at a
good prime**: for η satisfying strong eigenspace i with witness u(a),
at any prime Q ≠ ⊥, maximal, with η ∉ Q AND u(a) ∉ Q,
`pthSymbolAtPrime_canonical (σ_a η) Q = ((a : ZMod p)^i)^? · pthSymbolAtPrime_canonical η Q`.
The power transform handles the `η^{a^i}` factor; the `u^p` factor vanishes. -/
theorem pthSymbolAtPrime_canonical_galois_numerator_of_strong
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    {Q : Ideal (𝓞 K)} (hbot : Q ≠ ⊥) (hmax : Q.IsMaximal)
    (hη : η ∉ Q) (huQ : u ∉ Q) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) Q =
      ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K) η Q := by
  rw [hu]
  haveI hQ_prime : Q.IsPrime := hmax.isPrime
  have hη_pow : η ^ ((a : ZMod p).val ^ i : ℕ) ∉ Q := fun h ↦
    hη (hQ_prime.mem_of_pow_mem _ h)
  have hu_pow : u ^ p ∉ Q := fun h ↦
    huQ (hQ_prime.mem_of_pow_mem _ h)
  rw [pthSymbolAtPrime_canonical_mul hbot hmax hη_pow hu_pow,
    pthSymbolAtPrime_canonical_pow hbot hmax hη _,
    pthSymbolAtPrime_canonical_pow_p_eq_zero hbot hmax huQ, add_zero,
    Nat.cast_pow]

/-- **Ideal-level numerator transform under StrongEigenspaceCondition**:
for η satisfying strong eigenspace i with witness u, at any nonzero ideal
I such that u is coprime to all prime factors of I,
`pthSymbolAtIdeal_canonical (σ_a η) I = ((a.val^i : ZMod p)) · pthSymbolAtIdeal_canonical η I`. -/
theorem pthSymbolAtIdeal_canonical_galois_numerator_of_strong
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (I : Ideal (𝓞 K))
    (h_u_coprime : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, u ∉ Q) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) I =
      ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P ↦ pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a η) P)).sum =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P ↦ ((a : ZMod p).val ^ i : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) η P)).sum from ?_]
  · rw [← Multiset.sum_map_mul_left]
  · apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro Q hQ
    obtain ⟨_, hQ_ne_bot, hQ_max⟩ :=
      isPrime_of_mem_normalizedFactors hQ
    by_cases hη : η ∈ Q
    · -- Both sides are 0 since η ∈ Q forces σ_a η ∈ Q.
      have hη_pow : η ^ ((a : ZMod p).val ^ i : ℕ) ∈ Q := by
        haveI : Q.IsPrime := hQ_max.isPrime
        have ha_val_pos : 0 < (a : ZMod p).val :=
          ZMod.val_pos.mpr (Units.ne_zero a)
        have h_pos : 0 < (a : ZMod p).val ^ i :=
          pow_pos ha_val_pos i
        exact Q.pow_mem_of_mem hη _ h_pos
      have hσ_in : cyclotomicRingOfIntegersEquiv (p := p) K a η ∈ Q := by
        rw [hu]
        exact Q.mul_mem_right _ hη_pow
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hQ_ne_bot hQ_max hσ_in,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hQ_ne_bot hQ_max hη, mul_zero]
    · exact pthSymbolAtPrime_canonical_galois_numerator_of_strong a hu
        hQ_ne_bot hQ_max hη (h_u_coprime Q hQ)

/-- **Weight (1-i) Galois transform on pthSymbolAtIdeal_canonical (combined form)**:
for η satisfying strong eigenspace i with witness u (at index a),
combining the unconditional Galois shift with the numerator transform
gives:
  ((a.val^i : ZMod p)) * pthSymbolAtIdeal_canonical η (σ_a I)
    = (a : ZMod p) * pthSymbolAtIdeal_canonical η I.
This is the weight `(1 - i)` formula in pre-divided form. -/
theorem pthSymbolAtIdeal_canonical_galois_weight_one_minus_i
    {η u : 𝓞 K} {i : ℕ} (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h_u_coprime_σ : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a I), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) η I := by
  rw [← pthSymbolAtIdeal_canonical_galois_numerator_of_strong a hu
    (cyclotomicGaloisConjugate (p := p) (K := K) a I) h_u_coprime_σ]
  exact pthSymbolAtIdeal_canonical_galoisAction_unconditional a η hI

/-- **Phi-Galois weight (1-i) transform (pre-divided form)**: under
StrongEigenspaceCondition i + u-coprimality, on phi at the integer-ideal
representative level. -/
theorem phiOnClassGroup_galois_weight_one_minus_i_mk0
    {η u : 𝓞 K} {i : ℕ}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (I : (Ideal (𝓞 K))⁰)
    (h_u_coprime_σ : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
      (cyclotomicGaloisConjugate (p := p) (K := K) a I.val), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        phiOnClassGroup h_ref19
          (cyclotomicGalActionOnClassGroup (p := p) (K := K) a
            (ClassGroup.mk0 I)) =
      (a : ZMod p) * phiOnClassGroup h_ref19 (ClassGroup.mk0 I) := by
  rw [cyclotomicGalActionOnClassGroup_mk0]
  have hI_ne : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hσI_ne : cyclotomicGaloisConjugate (p := p) (K := K) a I.val ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hI_ne
  have h_shifted_eq :
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I =
        ClassGroup.mk0
          ⟨cyclotomicGaloisConjugate (p := p) (K := K) a I.val,
           mem_nonZeroDivisors_iff_ne_zero.mpr hσI_ne⟩ := rfl
  rw [h_shifted_eq, phiOnClassGroup_mk0 h_ref19, phiOnClassGroup_mk0 h_ref19]
  exact pthSymbolAtIdeal_canonical_galois_weight_one_minus_i a hu hI_ne
    h_u_coprime_σ

/-- **Phi-Galois weight (1-i) transform on Cl(𝓞 K)** (extending mk0 form
to arbitrary classes): given the u-coprimality at every representative. -/
theorem phiOnClassGroup_galois_weight_one_minus_i_class
    {η u : 𝓞 K} {i : ℕ}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (c : ClassGroup (𝓞 K))
    (h_u_coprime : ∀ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c →
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a I.val), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        phiOnClassGroup h_ref19
          (cyclotomicGalActionOnClassGroup (p := p) (K := K) a c) =
      (a : ZMod p) * phiOnClassGroup h_ref19 c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  exact phiOnClassGroup_galois_weight_one_minus_i_mk0 h_ref19 a hu I
    (h_u_coprime I rfl)

/-- **Phi-Galois weight (1-i) transform on linearised Additive ClassGroupModP**:
the linearised form of the weight (1-i) transform consumed by
`EndToEndReflectionAtoms.phi_galois`. -/
theorem phiOnClassGroupModPLinear_galois_weight_one_minus_i
    {η u : 𝓞 K} {i : ℕ}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (v : Additive (ClassGroupModP K p))
    (h_u_coprime : ∀ I : (Ideal (𝓞 K))⁰,
      Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
        ClassGroupModP K p) = v →
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a I.val), u ∉ Q) :
    ((a : ZMod p).val ^ i : ZMod p) *
        phiOnClassGroupModPLinear h_ref19
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * phiOnClassGroupModPLinear h_ref19 v := by
  obtain ⟨w, hw⟩ : ∃ w : ClassGroupModP K p, Additive.ofMul w = v := ⟨v.toMul, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ClassGroup (𝓞 K), QuotientGroup.mk c = w :=
    QuotientGroup.mk_surjective _
  subst hw
  subst hc
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  -- Reduce to the integer-rep form via the linearisation chain.
  have h_phi : ∀ J : (Ideal (𝓞 K))⁰,
      phiOnClassGroupModPLinear h_ref19
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 J) :
          ClassGroupModP K p)) =
      phiOnClassGroup h_ref19 (ClassGroup.mk0 J) := fun _ ↦ rfl
  rw [h_phi I]
  have h_galAction :
      cyclotomicGalActionInstance (p := p) (K := K) a
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
          ClassGroupModP K p)) =
      Additive.ofMul (QuotientGroup.mk
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a
          (ClassGroup.mk0 I)) : ClassGroupModP K p) := by
    change Additive.ofMul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      Additive.ofMul (QuotientGroup.mk
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a
          (ClassGroup.mk0 I)) : ClassGroupModP K p)
    rfl
  rw [h_galAction]
  rw [show phiOnClassGroupModPLinear h_ref19
      (Additive.ofMul (QuotientGroup.mk
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a
          (ClassGroup.mk0 I)) : ClassGroupModP K p)) =
    phiOnClassGroup h_ref19
      (cyclotomicGalActionMonoidHom (p := p) (K := K) a
        (ClassGroup.mk0 I)) from rfl]
  exact phiOnClassGroup_galois_weight_one_minus_i_mk0 h_ref19 a hu I
    (h_u_coprime I rfl)

/-- **Phi-Galois weight (1-i) — divided form on linearised ClassGroupModP**:
divides the pre-divided form by a^i (a unit in ZMod p) to give:
  phi(σ_a v) = (a : ZMod p) · ((a : ZMod p)^i)⁻¹ · phi(v).

Concretely, in additive index notation, the weight is `1 - i` (mod p-1). -/
theorem phiOnClassGroupModPLinear_galois_divided
    {η u : 𝓞 K} {i : ℕ}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (v : Additive (ClassGroupModP K p))
    (h_u_coprime : ∀ I : (Ideal (𝓞 K))⁰,
      Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
        ClassGroupModP K p) = v →
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a I.val), u ∉ Q) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * ((a : ZMod p) ^ i)⁻¹ *
        phiOnClassGroupModPLinear h_ref19 v := by
  have h := phiOnClassGroupModPLinear_galois_weight_one_minus_i h_ref19 a hu v
    h_u_coprime
  -- h: ((a.val^i : ZMod p)) * phi (σ_a v) = a * phi v.
  -- In ZMod p, (a.val^i : ZMod p) = (a : ZMod p)^i (cast simp).
  have h_cast : ((a : ZMod p).val ^ i : ZMod p) = (a : ZMod p) ^ i := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [h_cast] at h
  -- h: (a : ZMod p)^i * phi (σ_a v) = a * phi v.
  -- Divide both sides by (a : ZMod p)^i.
  have h_a_unit : IsUnit ((a : ZMod p) ^ i) := (Units.isUnit a).pow i
  have h_a_ne : (a : ZMod p) ^ i ≠ 0 := h_a_unit.ne_zero
  apply mul_left_cancel₀ h_a_ne
  rw [h]
  rw [show (a : ZMod p) ^ i * ((a : ZMod p) * ((a : ZMod p) ^ i)⁻¹ *
      phiOnClassGroupModPLinear h_ref19 v) =
    ((a : ZMod p) ^ i * ((a : ZMod p) ^ i)⁻¹) * ((a : ZMod p) *
      phiOnClassGroupModPLinear h_ref19 v) from by ring]
  rw [IsUnit.mul_inv_cancel h_a_unit, one_mul]

/-- **`StrongEigenspaceCondition` for `(0 : 𝓞 K)` at any positive index**:
holds with u = 0 since both sides reduce to 0. -/
theorem strongEigenspaceCondition_zero (i : ℕ) (_hi : 0 < i) :
    StrongEigenspaceCondition (p := p) (K := K) (0 : 𝓞 K) i := by
  intro a
  refine ⟨0, ?_⟩
  rw [map_zero]
  have hi_pow : 0 < (a : ZMod p).val ^ i := by
    have ha_val_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr (Units.ne_zero a)
    exact pow_pos ha_val_pos i
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hi_pow), zero_pow (Nat.pos_iff_ne_zero.mp hp_pos),
    zero_mul]

/-- **σ-fixed η phi-Galois transform via `phiOnClassGroupModPLinear_galois_divided`**:
specialization to u = 1 (vacuous coprimality) and i = 0, giving weight 1.
Recovers the existing `phiOnClassGroupModPLinear_galois_of_fixed` via
the substantive transform machinery. -/
theorem phiOnClassGroupModPLinear_galois_of_strongFixed
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * phiOnClassGroupModPLinear h_ref19 v := by
  have hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ 0 : ℕ) * (1 : 𝓞 K) ^ p := by
    rw [hη_fixed, pow_zero, pow_one, one_pow, mul_one]
  have h_u_coprime : ∀ I : (Ideal (𝓞 K))⁰,
      Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
        ClassGroupModP K p) = v →
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a I.val), (1 : 𝓞 K) ∉ Q := by
    intros _ _ Q hQ
    obtain ⟨_, _, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
    exact hQ_max.isPrime.one_notMem
  have h := phiOnClassGroupModPLinear_galois_divided h_ref19 a hu v h_u_coprime
  -- a · (a^0)⁻¹ = a · 1⁻¹ = a · 1 = a.
  rw [pow_zero, inv_one, mul_one] at h
  exact h

/-- **Phi-Galois divided form when u is a unit** (u-coprimality is automatic):
if u ∈ (𝓞 K)ˣ, then u ∉ Q for any proper prime Q, so the u-coprimality
hypothesis is vacuous. -/
theorem phiOnClassGroupModPLinear_galois_divided_of_unit_u
    {η u : 𝓞 K} {i : ℕ}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hu_unit : IsUnit u)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * ((a : ZMod p) ^ i)⁻¹ *
        phiOnClassGroupModPLinear h_ref19 v := by
  apply phiOnClassGroupModPLinear_galois_divided h_ref19 a hu v
  intros _ _ Q hQ
  obtain ⟨_, _, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
  exact fun h_in ↦ hQ_max.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ h_in hu_unit)


/-- **Stronger `StrongEigenspaceCondition` for β^p with β unit**: also
records that the witness u is a unit. -/
theorem strongEigenspaceCondition_pow_p_of_isUnit_with_unit_witness
    {β : 𝓞 K} (hβ : IsUnit β) (a : CyclotomicUnitDelta p) :
    ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a (β ^ p) =
        (β ^ p) ^ ((a : ZMod p).val ^ 0 : ℕ) * u ^ p := by
  set α := cyclotomicRingOfIntegersEquiv (p := p) K a β with hα_def
  have hα_unit : IsUnit α := by
    rw [hα_def]
    exact (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom.isUnit_map hβ
  obtain ⟨β_inv, hβ_inv_left, hβ_inv_right⟩ :
      ∃ b : 𝓞 K, β * b = 1 ∧ b * β = 1 := by
    obtain ⟨u, hu⟩ := hβ
    exact ⟨u.inv, hu ▸ u.val_inv, hu ▸ u.inv_val⟩
  have hβ_inv_unit : IsUnit β_inv := IsUnit.of_mul_eq_one β hβ_inv_right
  refine ⟨α * β_inv, hα_unit.mul hβ_inv_unit, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (β ^ p) = α ^ p from
    map_pow _ _ _]
  rw [pow_zero, pow_one, mul_pow]
  have hβp_inv : β ^ p * β_inv ^ p = 1 := by
    rw [← mul_pow, hβ_inv_left, one_pow]
  calc α ^ p
      = α ^ p * (β ^ p * β_inv ^ p) := by rw [hβp_inv, mul_one]
    _ = β ^ p * (α ^ p * β_inv ^ p) := by ring

/-- **Phi-Galois weight 1 for η = β^p with β unit** via the substantive
machinery: combines `strongEigenspaceCondition_pow_p_of_isUnit_with_unit_witness`
with `phiOnClassGroupModPLinear_galois_divided_of_unit_u`. -/
theorem phiOnClassGroupModPLinear_galois_pow_p_of_isUnit
    {β : 𝓞 K} (hβ : IsUnit β)
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) (β ^ p))
    (a : CyclotomicUnitDelta p) (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * phiOnClassGroupModPLinear h_ref19 v := by
  obtain ⟨u, hu_unit, hu⟩ :=
    strongEigenspaceCondition_pow_p_of_isUnit_with_unit_witness (p := p) (K := K) hβ a
  have h := phiOnClassGroupModPLinear_galois_divided_of_unit_u h_ref19 a hu hu_unit v
  rw [pow_zero, inv_one, mul_one] at h
  exact h

/-- **Phi-Galois weight 0 (σ-invariant phi) for η satisfying StrongEigenspaceCondition 1**:
specialization to i = 1, giving phi(σ_a v) = phi(v) (constant under σ_a). -/
theorem phiOnClassGroupModPLinear_galois_eigenspace_one
    {η u : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ 1 : ℕ) * u ^ p)
    (hu_unit : IsUnit u)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      phiOnClassGroupModPLinear h_ref19 v := by
  have h := phiOnClassGroupModPLinear_galois_divided_of_unit_u h_ref19 a hu hu_unit v
  rw [pow_one] at h
  -- h : phi(σ_a v) = a · ((a : ZMod p))⁻¹ · phi v.
  have h_a_unit : IsUnit (a : ZMod p) := Units.isUnit a
  rw [IsUnit.mul_inv_cancel h_a_unit, one_mul] at h
  exact h

/-- **Atom-D form for η ∈ V_0 with u unit (k = 1)**: `phi(σ_a v) = (a:ZMod p)^1 · phi v`.
Direct expression in `EndToEndReflectionAtoms.phi_galois` shape. -/
theorem phi_galois_atomD_of_eigenspace_zero_unit_u
    {η u : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ 0 : ℕ) * u ^ p)
    (hu_unit : IsUnit u)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ 1) * phiOnClassGroupModPLinear h_ref19 v := by
  rw [pow_one]
  have h := phiOnClassGroupModPLinear_galois_divided_of_unit_u h_ref19 a hu hu_unit v
  rw [pow_zero, inv_one, mul_one] at h
  exact h

/-- **Atom-D form for η ∈ V_1 with u unit (k = 0)**: `phi(σ_a v) = (a:ZMod p)^0 · phi v = phi v`.
Direct expression in `EndToEndReflectionAtoms.phi_galois` shape. -/
theorem phi_galois_atomD_of_eigenspace_one_unit_u
    {η u : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hu : cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ 1 : ℕ) * u ^ p)
    (hu_unit : IsUnit u)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      ((a : ZMod p) ^ 0) * phiOnClassGroupModPLinear h_ref19 v := by
  rw [pow_zero, one_mul]
  exact phiOnClassGroupModPLinear_galois_eigenspace_one h_ref19 a hu hu_unit v

/-- **Universal Atom-D phi_galois (k = 1, eigenspace 0, u unit)**: produces
the universal `phi_galois` form (over all a ∈ (ZMod p)ˣ and v) for
η ∈ V_0 with u a unit witness. The hypothesis is universal: for every
a, ∃ a unit u(a) such that StrongEigenspaceCondition holds. -/
theorem phi_galois_universal_eigenspace_zero_unit
    {η : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ 0 : ℕ) * u ^ p) :
    ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      phiOnClassGroupModPLinear h_ref19
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ 1) * phiOnClassGroupModPLinear h_ref19 v := by
  intro a v
  obtain ⟨u, hu_unit, hu⟩ := h a
  exact phi_galois_atomD_of_eigenspace_zero_unit_u h_ref19 a hu hu_unit v

/-- **Universal Atom-D phi_galois (k = 0, eigenspace 1, u unit)**: produces
the universal `phi_galois` form for η ∈ V_1 with u a unit witness. -/
theorem phi_galois_universal_eigenspace_one_unit
    {η : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ 1 : ℕ) * u ^ p) :
    ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      phiOnClassGroupModPLinear h_ref19
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ 0) * phiOnClassGroupModPLinear h_ref19 v := by
  intro a v
  obtain ⟨u, hu_unit, hu⟩ := h a
  exact phi_galois_atomD_of_eigenspace_one_unit_u h_ref19 a hu hu_unit v

/-- **Conversion lemma**: for `a ∈ (ZMod p)ˣ` and `i ∈ [0, p]`,
`(a : ZMod p)^(p - i) = (a : ZMod p) * ((a : ZMod p)^i)⁻¹`.
Combines `ZMod.pow_card` (Fermat's little theorem) with cancellation. -/
theorem zmod_pow_p_sub_i_eq_mul_inv {a : (ZMod p)ˣ} {i : ℕ} (hi : i ≤ p) :
    ((a : ZMod p) ^ (p - i)) = (a : ZMod p) * ((a : ZMod p) ^ i)⁻¹ := by
  have h_fermat : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card _
  have h_a_unit : IsUnit ((a : ZMod p) ^ i) := (Units.isUnit a).pow i
  have h_a_ne : (a : ZMod p) ^ i ≠ 0 := h_a_unit.ne_zero
  apply mul_right_cancel₀ h_a_ne
  rw [mul_assoc, IsUnit.inv_mul_cancel h_a_unit, mul_one, ← pow_add,
    Nat.sub_add_cancel hi]
  exact h_fermat

/-- **Universal Atom-D phi_galois with weight (p - i) for general i, u unit**:
combines `phiOnClassGroupModPLinear_galois_divided_of_unit_u` with
`zmod_pow_p_sub_i_eq_mul_inv` to express the divided form as
`(a : ZMod p)^(p - i)`. -/
theorem phi_galois_universal_eigenspace_unit
    {η : 𝓞 K}
    (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (i : ℕ) (hi : i ≤ p)
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p) :
    ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      phiOnClassGroupModPLinear h_ref19
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ (p - i)) *
          phiOnClassGroupModPLinear h_ref19 v := by
  intro a v
  obtain ⟨u, hu_unit, hu⟩ := h a
  have h_div := phiOnClassGroupModPLinear_galois_divided_of_unit_u
    h_ref19 a hu hu_unit v
  rw [zmod_pow_p_sub_i_eq_mul_inv hi]
  exact h_div

/-- **`StrongEigenspaceCondition` closure under multiplication at the same eigenspace**:
if η₁, η₂ both satisfy strong eigenspace i, then η₁ · η₂ also does. -/
theorem strongEigenspaceCondition_mul_at_same
    {η₁ η₂ : 𝓞 K} {i : ℕ}
    (h₁ : StrongEigenspaceCondition (p := p) (K := K) η₁ i)
    (h₂ : StrongEigenspaceCondition (p := p) (K := K) η₂ i) :
    StrongEigenspaceCondition (p := p) (K := K) (η₁ * η₂) i := by
  intro a
  obtain ⟨u₁, hu₁⟩ := h₁ a
  obtain ⟨u₂, hu₂⟩ := h₂ a
  refine ⟨u₁ * u₂, ?_⟩
  rw [map_mul, hu₁, hu₂, mul_pow]
  ring

/-- **EigenspaceCondition closure under natural-number power for eigenspace 0**:
if η satisfies eigenspace 0, then η^n also satisfies eigenspace 0. -/
theorem eigenspaceCondition_pow_of_eigenspace_zero
    {η : 𝓞 K} (h : EigenspaceCondition (p := p) (K := K) η 0) (n : ℕ) :
    EigenspaceCondition (p := p) (K := K) (η ^ n) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u ^ n, ?_⟩
  simp only [pow_zero, pow_one] at hu ⊢
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η ^ n) =
    (cyclotomicRingOfIntegersEquiv (p := p) K a η) ^ n from map_pow _ _ _,
    map_pow, map_pow, hu, mul_pow]
  ring

/-- **EigenspaceCondition for natural-number cast (eigenspace 0)**: any
ℕ-cast (n : 𝓞 K) is fixed by σ_a (since cyclotomicRingOfIntegersEquiv is
a ring hom), hence eigenspace 0 holds. -/
theorem eigenspaceCondition_natCast (n : ℕ) :
    EigenspaceCondition (p := p) (K := K) (n : 𝓞 K) 0 := by
  apply eigenspaceCondition_zero_of_fixed
  intro a
  exact map_natCast _ _

/-- **EigenspaceCondition for integer cast (eigenspace 0)**: any ℤ-cast
(z : 𝓞 K) is fixed by σ_a, hence eigenspace 0 holds. -/
theorem eigenspaceCondition_intCast (z : ℤ) :
    EigenspaceCondition (p := p) (K := K) (z : 𝓞 K) 0 := by
  apply eigenspaceCondition_zero_of_fixed
  intro a
  exact map_intCast _ _

/-- **EigenspaceCondition closure under multiplication at the same eigenspace**:
if η₁, η₂ both satisfy eigenspace i, then η₁ · η₂ also does. The new u
is `u₁ * u₂`. Eigenspaces are closed under multiplication at the same
level (V_i + V_i = V_i in the eigenspace decomposition). -/
theorem eigenspaceCondition_mul_at_same_eigenspace
    {η₁ η₂ : 𝓞 K} {i : ℕ}
    (h₁ : EigenspaceCondition (p := p) (K := K) η₁ i)
    (h₂ : EigenspaceCondition (p := p) (K := K) η₂ i) :
    EigenspaceCondition (p := p) (K := K) (η₁ * η₂) i := by
  intro a
  obtain ⟨u₁, hu₁⟩ := h₁ a
  obtain ⟨u₂, hu₂⟩ := h₂ a
  refine ⟨u₁ * u₂, ?_⟩
  rw [map_mul, map_mul, map_mul, hu₁, hu₂, mul_pow]
  ring

/-- **EigenspaceCondition closure under multiplication for eigenspace 0**:
if η₁, η₂ satisfy eigenspace 0, then η₁ · η₂ also satisfies eigenspace 0.
The new u is `u₁ * u₂`. -/
theorem eigenspaceCondition_mul_of_eigenspace_zero
    {η₁ η₂ : 𝓞 K}
    (h₁ : EigenspaceCondition (p := p) (K := K) η₁ 0)
    (h₂ : EigenspaceCondition (p := p) (K := K) η₂ 0) :
    EigenspaceCondition (p := p) (K := K) (η₁ * η₂) 0 := by
  intro a
  obtain ⟨u₁, hu₁⟩ := h₁ a
  obtain ⟨u₂, hu₂⟩ := h₂ a
  refine ⟨u₁ * u₂, ?_⟩
  simp only [pow_zero, pow_one] at hu₁ hu₂ ⊢
  rw [map_mul, map_mul, map_mul, hu₁, hu₂, mul_pow]
  ring

/-- **EigenspaceCondition closure under negation for eigenspace 0**:
if η satisfies eigenspace 0, then -η also satisfies eigenspace 0. -/
theorem eigenspaceCondition_neg_of_eigenspace_zero
    {η : 𝓞 K} (h : EigenspaceCondition (p := p) (K := K) η 0) :
    EigenspaceCondition (p := p) (K := K) (-η) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u, ?_⟩
  simp only [pow_zero, pow_one] at hu ⊢
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (-η) =
    -cyclotomicRingOfIntegersEquiv (p := p) K a η from map_neg _ _,
    map_neg, map_neg, hu]
  ring

/-- **`(-1 : 𝓞 K)` satisfies eigenspace-0 for odd p**: σ_a fixes -1, so
`EigenspaceCondition (-1) 0` holds via `eigenspaceCondition_zero_of_fixed`. -/
theorem eigenspaceCondition_neg_one_of_odd (_hp_odd : Odd p) :
    EigenspaceCondition (p := p) (K := K) (-1 : 𝓞 K) 0 := by
  apply eigenspaceCondition_zero_of_fixed
  intro a
  simp [map_neg, map_one]

/-- **`(-β)^p = -β^p` satisfies eigenspace-0 for odd p**: combined
closure of negation (in ZMod p with p odd) and pow_p. -/
theorem eigenspaceCondition_neg_pow_p_zero_of_odd
    (hp_odd : Odd p) (β : 𝓞 K) (hβ : β ≠ 0) :
    EigenspaceCondition (p := p) (K := K) (-β ^ p) 0 := by
  have h_eq : -β ^ p = (-β) ^ p := (Odd.neg_pow hp_odd β).symm
  rw [h_eq]
  exact eigenspaceCondition_pow_p_zero (-β) (neg_ne_zero.mpr hβ)

end Furtwaengler

end BernoulliRegular

end
