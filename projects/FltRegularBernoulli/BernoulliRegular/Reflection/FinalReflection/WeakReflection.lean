module

public import BernoulliRegular.Reflection.FinalReflection.ClassGroupBridge

/-!
# Weak reflection

This file proves the weak reflection theorems for the cyclotomic field
`K = Q(zeta_p)`.  The component form `weakReflection_componentNontrivial` shows
that nontriviality of the even `i`-th character component of `Cl(O_K)/p` forces
nontriviality of the reflected component; the class-number consequence
`weakReflection_dvd_hMinus_of_dvd_hPlus` deduces `p ∣ hMinus K` from
`p ∣ hPlus K`, the form consumed by Kummer's criterion.  The supporting
ingredients proved here are the singular-pair extraction with denominator
clearing, the vanishing of the zero and odd eigenspaces, and the triviality of
the full cyclotomic conjugate product in the class group.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

open Reflection.SingularKummer
open Reflection.SingularKummer.FiniteLevelCharacterLift.FinitePrimaryBridge
open Reflection.SingularKummer.SingularPair
open Reflection.Kummer

universe u

/-- The `ZMod p`-scalar action on the additive singular group corresponds, on the
multiplicative side, to raising to the `c.val`-th power. -/
theorem zmod_smul_toMul_singularGroup
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K]
    (c : ZMod p)
    (x : Additive (SingularGroup (R := 𝓞 K) (K := K) p)) :
    (c • x).toMul = x.toMul ^ c.val := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]

/-- The singular-pair generator is compatible with natural powers. -/
theorem singularPair_generator_pow
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (t : SingularPair (𝓞 K) K p) (n : ℕ) :
    generator (t ^ n) = generator t ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ, generator_mul, ih]

/-- A singular-group eigenspace relation gives the denominator-cleared
integral relation needed by the residue-symbol Galois covariance theorem. -/
theorem exists_integral_clear_denominators_of_singularGroup_eigen
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {i : ℕ} (η : 𝓞 K) (t : SingularPair (𝓞 K) K p)
    (hη_cast : algebraMap (𝓞 K) K η = (generator t : K))
    (ht_eigen :
      ∀ b : Reflection.SingularKummer.CharacterProjection.Delta p,
        Additive.ofMul
            (cyclotomicSingularGroupAction K p b
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p)) =
          ((b : ZMod p) ^ i) •
            Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p))
    (a : CyclotomicUnitDelta p) :
    ∃ n : ℕ, ∃ z w : 𝓞 K,
      (n : ZMod p) = (a : ZMod p) ^ i ∧
      0 < n ∧ z ≠ 0 ∧ w ≠ 0 ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
        η ^ n * z ^ p := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let c : ZMod p := (a : ZMod p) ^ i
  let n : ℕ := c.val
  have hn : (n : ZMod p) = (a : ZMod p) ^ i := by
    simp [n, c]
  have hn_pos : 0 < n := by
    dsimp [n, c]
    exact ZMod.val_pos.mpr (pow_ne_zero i (Units.ne_zero a))
  let σt : SingularPair (𝓞 K) K p :=
    (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).singularPairEquiv p t
  have hmul :
      cyclotomicSingularGroupAction K p a
          (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) =
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ^ n := by
    have h := congrArg Additive.toMul (ht_eigen a)
    change
      cyclotomicSingularGroupAction K p a
          (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) =
        (((a : ZMod p) ^ i) •
            Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p)).toMul at h
    rw [zmod_smul_toMul_singularGroup (p := p) (K := K)] at h
    simpa [n, c] using h
  have hmk :
      (QuotientGroup.mk σt :
          SingularGroup (R := 𝓞 K) (K := K) p) =
        QuotientGroup.mk (t ^ n) := by
    rw [← QuotientGroup.mk_pow] at hmul
    simpa [σt, cyclotomicSingularGroupAction] using hmul
  have hmem :
      ((t ^ n)⁻¹ * σt) ∈
        principalPairSubgroup (R := 𝓞 K) (K := K) p :=
    (QuotientGroup.eq).1 hmk.symm
  obtain ⟨γ, hγ⟩ := hmem
  have hgen := congrArg (fun s : SingularPair (𝓞 K) K p ↦ generator s) hγ
  change generator (principalPair (R := 𝓞 K) (K := K) p γ) =
      generator ((t ^ n)⁻¹ * σt) at hgen
  change γ ^ p = generator ((t ^ n)⁻¹ * σt) at hgen
  have hunit :
      generator σt = generator t ^ n * γ ^ p := by
    have htmp := congrArg (fun x : Kˣ ↦ generator (t ^ n) * x) hgen
    simp only [SingularPair.generator] at htmp
    simpa [SingularPair.generator] using htmp.symm
  have hK :
      algebraMap (𝓞 K) K (cyclotomicRingOfIntegersEquiv (p := p) K a η) =
        algebraMap (𝓞 K) K (η ^ n) * (γ : K) ^ p := by
    have h := congrArg (fun u : Kˣ ↦ (u : K)) hunit
    change
      (generator σt : K) = (generator t : K) ^ n * (γ : K) ^ p at h
    have hσ_cast :
        (generator σt : K) =
          algebraMap (𝓞 K) K (cyclotomicRingOfIntegersEquiv (p := p) K a η) := by
      change
        ((cyclotomicFieldUnitEquiv K p a (generator t) : Kˣ) : K) =
          algebraMap (𝓞 K) K (cyclotomicRingOfIntegersEquiv (p := p) K a η)
      change
        cyclotomicSigmaOfUnit (p := p) K a (generator t : K) =
          algebraMap (𝓞 K) K (cyclotomicRingOfIntegersEquiv (p := p) K a η)
      rw [← hη_cast]
      change
        cyclotomicSigmaOfUnit (p := p) K a (algebraMap (𝓞 K) K η) =
          algebraMap (𝓞 K) K (cyclotomicSigmaOfUnit (p := p) K a • η)
      rfl
    rw [hσ_cast, ← hη_cast, ← map_pow] at h
    simpa using h
  obtain ⟨⟨z, w₀⟩, hzw⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) (γ : K)
  let w : 𝓞 K := w₀
  have hw_ne : w ≠ 0 := nonZeroDivisors.ne_zero w₀.2
  have hwK_ne : algebraMap (𝓞 K) K w ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hw_ne
  have hz_ne : z ≠ 0 := by
    intro hz
    apply γ.ne_zero
    rw [hz, map_zero] at hzw
    exact (mul_eq_zero.mp hzw).resolve_right hwK_ne
  have hγw_pow :
      (γ : K) ^ p * algebraMap (𝓞 K) K w ^ p =
        algebraMap (𝓞 K) K z ^ p := by
    rw [← mul_pow]
    exact congrArg (fun x : K ↦ x ^ p) hzw
  refine ⟨n, z, w, hn, hn_pos, hz_ne, hw_ne, ?_⟩
  apply (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  push_cast
  calc
    algebraMap (𝓞 K) K (cyclotomicRingOfIntegersEquiv (p := p) K a η) *
        algebraMap (𝓞 K) K w ^ p
        = (algebraMap (𝓞 K) K (η ^ n) * (γ : K) ^ p) *
            algebraMap (𝓞 K) K w ^ p := by rw [hK]
    _ = algebraMap (𝓞 K) K (η ^ n) *
          ((γ : K) ^ p * algebraMap (𝓞 K) K w ^ p) := by ring
    _ = algebraMap (𝓞 K) K (η ^ n) * algebraMap (𝓞 K) K z ^ p := by
          rw [hγw_pow]

/-- Reflected-component support for the concrete WR-05 residue-symbol
character.

The only Galois-weight input is the explicit elementwise equation
`σ_a η = η^(a^i) * u_a^p`.  The residue-symbol covariance itself is supplied
by `locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i`, whose
representative avoidance is built from the concrete Kummer bad set. -/
theorem reflectedComponentNontrivial_of_locallyPrimaryKummerBadSet_galoisWeight
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    {i : ℕ} (hi : i ≤ p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η)
    (hη_span : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (hη_galois :
      ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K,
        cyclotomicRingOfIntegersEquiv (p := p) K a η =
          η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) := by
  let φ :=
    Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear
      (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
      hη_prime_to_p hη_local hη_span
  have hφ_nontrivial : ∃ v : Additive (ClassGroupModP K p), φ v ≠ 0 := by
    simpa [φ] using
      Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear_nontrivial_of_not_isPow
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hη_span
  have hφ_galois : ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      φ (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ reflectedComponentIndex p i) * φ v := by
    intro a v
    obtain ⟨u, hu⟩ := hη_galois a
    have hcov :=
      Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hη_span hi a u hu v
    simpa [φ, reflectedComponentIndex] using hcov
  exact eigenspaceComponentNontrivial_of_nontrivial_linear_character
    p K (reflectedComponentIndex p i) φ hφ_galois hφ_nontrivial

/-- Reflected-component support for the concrete WR-05 residue-symbol
character from denominator-cleared Galois-weight data.

This is the form supplied directly by the singular-group eigenspace relation:
for every `a`, the quotient between `σ_a η` and the expected `i`-power is a
field pth power, cleared here as `σ_a η * w^p = η^n * z^p`. -/
theorem reflectedComponentNontrivial_of_locallyPrimaryKummerBadSet_galoisWeight_clear_denominators
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_ne_two : p ≠ 2) (hp_odd : Odd p)
    {i : ℕ} (hi : i ≤ p)
    (η : 𝓞 K) (hη_ne : η ≠ 0)
    (hη_not_pow : ¬ ∃ β : K, β ^ p = (η : K))
    (B : Ideal (𝓞 K))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : Furtwaengler.IsLambdaLocalPthPower (p := p) (K := K) η)
    (hη_span : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (hη_galois :
      ∀ a : CyclotomicUnitDelta p, ∃ n : ℕ, ∃ z w : 𝓞 K,
        (n : ZMod p) = (a : ZMod p) ^ i ∧
        0 < n ∧ z ≠ 0 ∧ w ≠ 0 ∧
        cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
          η ^ n * z ^ p) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) := by
  let φ :=
    Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear
      (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
      hη_prime_to_p hη_local hη_span
  have hφ_nontrivial : ∃ v : Additive (ClassGroupModP K p), φ v ≠ 0 := by
    simpa [φ] using
      Reflection.Kummer.locallyPrimaryKummerBadSetClassGroupModPLinear_nontrivial_of_not_isPow
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hη_span
  have hφ_galois : ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      φ (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ reflectedComponentIndex p i) * φ v := by
    intro a v
    obtain ⟨n, z, w, hn, hn_pos, hz_ne, hw_ne, hclear⟩ := hη_galois a
    have hcov :=
      locallyPrimaryKummerBadSetClassGroupModPLinear_galois_pow_p_sub_i_clear_denominators
        (p := p) (K := K) hp_ne_two hp_odd η hη_ne hη_not_pow B
        hη_prime_to_p hη_local hη_span hi a z w hn hn_pos hz_ne hw_ne hclear v
    simpa [φ, reflectedComponentIndex] using hcov
  exact eigenspaceComponentNontrivial_of_nontrivial_linear_character
    p K (reflectedComponentIndex p i) φ hφ_galois hφ_nontrivial

/-- Assembly of the primary-kernel strategy after the concrete
residue-symbol character family has been constructed.

The hypotheses here are exactly the two remaining outputs of the Kummer
pairing part of weak reflection:

* injectivity/nondegeneracy of the character family on the completed
  localization kernel;
* Galois covariance with reflected weight.

The nontriviality of the primary kernel itself is supplied by the proved
localization-kernel dimension estimate. -/
theorem weakReflection_componentNontrivial_of_classPTorsion_component_and_kernel_character_family
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent
          (K := K) (p := p) i (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥)
    (characterFamily :
      LinearMap.ker
          (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i)) →ₗ[ZMod p]
        (Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p))
    (h_injective : Function.Injective characterFamily)
    (h_galois : ∀
        (x :
          LinearMap.ker
            (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i)))
        (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      characterFamily x
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ reflectedComponentIndex p i) * characterFamily x v) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) := by
  let Primary :=
    LinearMap.ker
      (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i))
  haveI : Nontrivial Primary :=
    completedLocalizationKernel_nontrivial_of_classPTorsion_component
      p K hp_gt_two hi_even hi_low hi_high hA_ne_bot
  exact weakReflection_componentNontrivial_of_injective_reflected_character_family
    p K (i := i) Primary characterFamily h_injective h_galois

/-- Interior weak-reflection assembly from the public hypothesis, after the
explicit residue-symbol character family has been constructed.

This is the no-hidden-input form left for WR-04--WR-06: starting from
`hcomp : eigenspaceComponentNontrivial p K i`, the finite bridge and
local-primary lower bound are now internal to this theorem.  The only remaining
parameters are the concrete character family on the completed localization
kernel and its two explicit properties, injectivity and reflected Galois
covariance. -/
theorem weakReflection_componentNontrivial_interior_of_kernel_character_family
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    (hcomp : eigenspaceComponentNontrivial p K i)
    (characterFamily :
      LinearMap.ker
          (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i)) →ₗ[ZMod p]
        (Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p))
    (h_injective : Function.Injective characterFamily)
    (h_galois : ∀
        (x :
          LinearMap.ker
            (singularGroupCompletedLocalizationComponentMap (K := K) (p := p) (i := i)))
        (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      characterFamily x
          (cyclotomicGalActionInstance (p := p) (K := K) a v) =
        ((a : ZMod p) ^ reflectedComponentIndex p i) * characterFamily x v) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) :=
  weakReflection_componentNontrivial_of_classPTorsion_component_and_kernel_character_family
    p K hp_gt_two hi_even hi_low hi_high
    (classGroupPTorsionCharacterProjectionComponent_ne_bot_of_eigenspaceComponentNontrivial
      p K i hcomp)
    characterFamily h_injective h_galois

/-- If `p` divides the class number, then `Cl(O_K)/p` has a nontrivial class. -/
theorem exists_ne_one_classGroupModP_of_dvd_classNumber
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K]
    (hdvd : p ∣ Fintype.card (ClassGroup (𝓞 K))) :
    ∃ x : ClassGroupModP K p, x ≠ 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hsub : Subsingleton (ClassGroupModP K p) :=
    ⟨fun x y ↦ by rw [hnone x, hnone y]⟩
  let G := ClassGroup (𝓞 K)
  have htop : (powMonoidHom p : G →* G).range = ⊤ :=
    QuotientGroup.subgroup_eq_top_of_subsingleton
      ((powMonoidHom p : G →* G).range) hsub
  have hsurj : Function.Surjective (powMonoidHom p : G →* G) := by
    intro y
    have hy : y ∈ (powMonoidHom p : G →* G).range := by
      rw [htop]
      exact Subgroup.mem_top y
    simpa [MonoidHom.mem_range] using hy
  have hinj : Function.Injective (powMonoidHom p : G →* G) :=
    (Finite.injective_iff_surjective).mpr hsurj
  obtain ⟨g, hg_order⟩ :=
    exists_prime_orderOf_dvd_card (G := G) p hdvd
  have hg_pow : g ^ p = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hg_order])
  have hg_ne : g ≠ 1 := by
    intro hg
    have : orderOf g = 1 := orderOf_eq_one_iff.mpr hg
    rw [this] at hg_order
    exact (Fact.out : Nat.Prime p).ne_one hg_order.symm
  apply hg_ne
  apply hinj
  change g ^ p = (1 : G) ^ p
  simpa using hg_pow

/-- Additive form of `exists_ne_one_classGroupModP_of_dvd_classNumber`. -/
theorem exists_ne_zero_additive_classGroupModP_of_dvd_classNumber
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K]
    (hdvd : p ∣ Fintype.card (ClassGroup (𝓞 K))) :
    ∃ v : Additive (ClassGroupModP K p), v ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne_one_classGroupModP_of_dvd_classNumber p K hdvd
  refine ⟨Additive.ofMul x, ?_⟩
  intro hv
  apply hx
  simpa using congrArg Additive.toMul hv

/-- The image of `Cl(O_{K⁺})` has index `hMinus K` in `Cl(O_K)`. -/
theorem plusClassGroupImage_index_eq_hMinus
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] :
    (classGroupMap K).range.index = hMinus K := by
  classical
  let H : Subgroup (ClassGroup (𝓞 K)) := (classGroupMap K).range
  have hcardH : Nat.card H = hPlus K := by
    rw [Nat.card_eq_fintype_card, hPlus]
    exact Fintype.card_coeSort_range (classGroupMap_injective p hp_odd K)
  have hmul : hPlus K * H.index = h K := by
    have h := H.card_mul_index
    rw [hcardH] at h
    simpa [BernoulliRegular.h] using h
  have hhmul : h K = hPlus K * hMinus K :=
    h_eq_hPlus_mul_hMinus p hp_odd K
  have hpos : 0 < hPlus K := by
    unfold hPlus
    exact Fintype.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by
    rw [hmul, hhmul])

/-- If `p ∤ hMinus K`, every class in `Cl(O_K)/p` is fixed by complex conjugation. -/
theorem cyclotomicGalActionInstance_neg_one_fixed_of_not_dvd_hMinus
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    (hnot : ¬ (p : ℕ) ∣ hMinus K)
    (v : Additive (ClassGroupModP K p)) :
    cyclotomicGalActionInstance (p := p) (K := K) (-1) v = v := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x : ClassGroupModP K p, Additive.ofMul x = v :=
    ⟨v.toMul, rfl⟩
  refine QuotientGroup.induction_on x ?_
  intro c
  let G := ClassGroup (𝓞 K)
  let H : Subgroup G := (classGroupMap K).range
  let m : ℕ := hMinus K
  have hindex : H.index = m := by
    simpa [H, m] using plusClassGroupImage_index_eq_hMinus p hp_odd K
  have hc_pow_mem : c ^ m ∈ H := by
    have hq : ((QuotientGroup.mk c : G ⧸ H) ^ H.index) = 1 :=
      pow_card_eq_one' (x := (QuotientGroup.mk c : G ⧸ H))
    have hmem_index : c ^ H.index ∈ H := by
      rw [← QuotientGroup.mk_pow] at hq
      exact (QuotientGroup.eq_one_iff (N := H) (c ^ H.index)).mp hq
    simpa [hindex, m] using hmem_index
  obtain ⟨cPlus, hcPlus⟩ : ∃ cPlus, classGroupMap K cPlus = c ^ m := by
    simpa [H, MonoidHom.mem_range] using hc_pow_mem
  let x : ClassGroupModP K p := QuotientGroup.mk c
  have hfix_pow :
      cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1) (x ^ m) = x ^ m := by
    change cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1)
        (QuotientGroup.mk (c ^ m) : ClassGroupModP K p) =
      (QuotientGroup.mk (c ^ m) : ClassGroupModP K p)
    rw [← hcPlus]
    exact cyclotomicGalActionMonoidHomModP_neg_one_classGroupMap hp_odd cPlus
  have hm_coprime_p : m.Coprime p :=
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by simpa [m] using hnot)).symm
  have horder_dvd : orderOf x ∣ p :=
    orderOf_dvd_of_pow_eq_one (classGroupModP_pow_p_eq_one x)
  have hm_coprime_order : m.Coprime (orderOf x) :=
    hm_coprime_p.coprime_dvd_right horder_dvd
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime (x := x) hm_coprime_order
  change Additive.ofMul
      (cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1) x) =
    Additive.ofMul x
  congr 1
  calc
    cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1) x
        = cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1) ((x ^ m) ^ r) := by
          rw [hr]
    _ = (cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1) (x ^ m)) ^ r := by
          rw [map_pow]
    _ = (x ^ m) ^ r := by rw [hfix_pow]
    _ = x := hr

/-- Odd eigenspaces vanish when every class is fixed by `σ_{-1}`. -/
theorem not_eigenspaceComponentNontrivial_odd_of_neg_one_fixed
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    (hfix : ∀ v : Additive (ClassGroupModP K p),
      cyclotomicGalActionInstance (p := p) (K := K) (-1) v = v)
    {j : ℕ} (hj_odd : Odd j) :
    ¬ eigenspaceComponentNontrivial p K j := by
  rintro ⟨v, hv_mem, hv_ne⟩
  have hneg_pow : ((-1 : ZMod p) ^ j) = -1 := by
    simpa using (Odd.neg_one_pow hj_odd : (-1 : ZMod p) ^ j = -1)
  have hv_eq_neg : v = -v := by
    have h := hv_mem (-1)
    rw [hfix v] at h
    simpa [hneg_pow] using h
  have htwo_unit : IsUnit (2 : ZMod p) := by
    refine (ZMod.isUnit_iff_coprime 2 p).2 ?_
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
      intro hdiv
      have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
      have htwo_le_p : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      exact hp_odd (le_antisymm hp_le_two htwo_le_p))).symm
  have htwo_smul : (2 : ZMod p) • v = 0 := by
    rw [two_smul]
    nth_rw 1 [hv_eq_neg]
    exact neg_add_cancel v
  exact hv_ne ((IsUnit.smul_eq_zero htwo_unit).mp htwo_smul)

/-- The `0`-indexed eigenspace is the same as the `(p - 1)`-indexed eigenspace. -/
theorem eigenspaceComponentNontrivial_pred_of_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcomp : eigenspaceComponentNontrivial p K 0) :
    eigenspaceComponentNontrivial p K (p - 1) := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hcomp
  refine ⟨v, ?_, hv_ne⟩
  intro a
  have hpow : ((a : ZMod p) ^ (p - 1)) = 1 := by
    rw [show ((a : ZMod p) ^ (p - 1)) = ((a ^ (p - 1) : (ZMod p)ˣ) : ZMod p) by
      push_cast
      rfl]
    rw [ZMod.units_pow_card_sub_one_eq_one p a]
    simp
  simpa [hpow] using hv_mem a

/-- The `(p - 1)`-indexed eigenspace is the same as the `0`-indexed
eigenspace. -/
theorem eigenspaceComponentNontrivial_zero_of_pred
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcomp : eigenspaceComponentNontrivial p K (p - 1)) :
    eigenspaceComponentNontrivial p K 0 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hcomp
  refine ⟨v, ?_, hv_ne⟩
  intro a
  have hpow : ((a : ZMod p) ^ (p - 1)) = 1 := by
    rw [show ((a : ZMod p) ^ (p - 1)) = ((a ^ (p - 1) : (ZMod p)ˣ) : ZMod p) by
      push_cast
      rfl]
    rw [ZMod.units_pow_card_sub_one_eq_one p a]
    simp
  have h := hv_mem a
  simpa [hpow] using h

/-- Product over all cyclotomic Galois conjugates is trivial in the class group.

This is the class-group form of
`Furtwaengler.cyclotomicConjugateProductIdeal_eq_absNorm_span`: the product of
all conjugates of an integral ideal is the extension of its norm from `ℤ`, hence
principal. -/
theorem cyclotomicGalActionMonoidHom_prod_eq_one
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (c : ClassGroup (𝓞 K)) :
    (∏ a : CyclotomicUnitDelta p,
        cyclotomicGalActionMonoidHom (p := p) (K := K) a c) = 1 := by
  classical
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective (R := 𝓞 K) c
  rw [← hI]
  have hI_ne : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hnorm :
      Furtwaengler.cyclotomicConjugateProductIdeal (p := p) (K := K) (I : Ideal (𝓞 K)) =
        Ideal.span
          ({algebraMap ℤ (𝓞 K) (((I : Ideal (𝓞 K)).absNorm : ℤ))} :
            Set (𝓞 K)) :=
    Furtwaengler.cyclotomicConjugateProductIdeal_eq_absNorm_span
      (p := p) (K := K) hI_ne
  have hspan_ne :
      Ideal.span
          ({algebraMap ℤ (𝓞 K) (((I : Ideal (𝓞 K)).absNorm : ℤ))} :
            Set (𝓞 K)) ≠ ⊥ := by
    intro hbot
    rw [Ideal.span_singleton_eq_bot] at hbot
    exact (Int.cast_ne_zero.mpr (by
      exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors I)) hbot
  calc
    (∏ a : CyclotomicUnitDelta p,
        cyclotomicGalActionMonoidHom (p := p) (K := K) a (ClassGroup.mk0 I))
        =
      ∏ a : CyclotomicUnitDelta p,
        ClassGroup.mk0
          (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) := by
        refine Finset.prod_congr rfl ?_
        intro a _
        exact cyclotomicGalActionOnClassGroup_mk0 (p := p) (K := K) a I
    _ =
      ClassGroup.mk0
        (∏ a : CyclotomicUnitDelta p,
          cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) := by
        rw [map_prod]
    _ =
      ClassGroup.mk0
        ⟨Furtwaengler.cyclotomicConjugateProductIdeal
            (p := p) (K := K) (I : Ideal (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by
              rw [hnorm]
              exact hspan_ne)⟩ := by
        congr 1
        apply Subtype.ext
        simp [Furtwaengler.cyclotomicConjugateProductIdeal,
          cyclotomicGaloisConjugateNonZeroDivisors]
    _ =
      ClassGroup.mk0
        ⟨Ideal.span
            ({algebraMap ℤ (𝓞 K) (((I : Ideal (𝓞 K)).absNorm : ℤ))} :
              Set (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr hspan_ne⟩ := by
        congr 1
        exact Subtype.ext <| hnorm
    _ = 1 :=
        (ClassGroup.mk0_eq_one_iff
            (mem_nonZeroDivisors_iff_ne_zero.mpr hspan_ne)).mpr
            ⟨algebraMap ℤ (𝓞 K) (((I : Ideal (𝓞 K)).absNorm : ℤ)), rfl⟩

/-- Product over all cyclotomic Galois conjugates is trivial in
`ClassGroupModP`. -/
theorem cyclotomicGalActionMonoidHomModP_prod_eq_one
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x : ClassGroupModP K p) :
    (∏ a : CyclotomicUnitDelta p,
        cyclotomicGalActionMonoidHomModP (p := p) (K := K) a x) = 1 := by
  classical
  refine QuotientGroup.induction_on x ?_
  intro c
  let H : Subgroup (ClassGroup (𝓞 K)) :=
    (powMonoidHom p : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range
  calc
    (∏ a : CyclotomicUnitDelta p,
        QuotientGroup.mk'
          H (cyclotomicGalActionMonoidHom (p := p) (K := K) a c))
        =
      QuotientGroup.mk' H
        (∏ a : CyclotomicUnitDelta p,
          cyclotomicGalActionMonoidHom (p := p) (K := K) a c) := by
        rw [map_prod]
    _ = 1 := by
        rw [cyclotomicGalActionMonoidHom_prod_eq_one (p := p) (K := K) c, map_one]

/-- The zero-character component of `Cl(O_K)/p` is trivial.

If a class is fixed by every cyclotomic Galois element, then its full conjugate
product is both `x^(p-1)` and `1`.  Since every element of `ClassGroupModP` has
order dividing `p`, coprimality of `p` and `p-1` forces the class to be zero. -/
theorem not_eigenspaceComponentNontrivial_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    ¬ eigenspaceComponentNontrivial p K 0 := by
  classical
  rintro ⟨v, hv_mem, hv_ne⟩
  obtain ⟨x, rfl⟩ : ∃ x : ClassGroupModP K p, Additive.ofMul x = v :=
    ⟨v.toMul, rfl⟩
  have hfixed :
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicGalActionMonoidHomModP (p := p) (K := K) a x = x := by
    intro a
    have h := hv_mem a
    change
      Additive.ofMul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a x) =
        ((a : ZMod p) ^ 0) • Additive.ofMul x at h
    simpa using congrArg Additive.toMul h
  have hprod_fixed :
      (∏ a : CyclotomicUnitDelta p,
          cyclotomicGalActionMonoidHomModP (p := p) (K := K) a x) =
        x ^ (p - 1) := by
    rw [Finset.prod_congr rfl (fun a _ ↦ hfixed a)]
    rw [Finset.prod_const, Finset.card_univ]
    change x ^ Fintype.card (CyclotomicUnitDelta p) = x ^ (p - 1)
    rw [show Fintype.card (CyclotomicUnitDelta p) = Fintype.card (ZMod p)ˣ from rfl,
      ZMod.card_units]
  have hx_pow_pred : x ^ (p - 1) = 1 := by
    rw [← hprod_fixed]
    exact cyclotomicGalActionMonoidHomModP_prod_eq_one (p := p) (K := K) x
  have hx_order_dvd_p : orderOf x ∣ p :=
    orderOf_dvd_of_pow_eq_one (classGroupModP_pow_p_eq_one x)
  have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
    intro hdiv
    have hpred_pos : 0 < p - 1 :=
      Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hle : p ≤ p - 1 := Nat.le_of_dvd hpred_pos hdiv
    omega
  have hp_coprime_pred : p.Coprime (p - 1) :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_not_dvd_pred
  have hpred_coprime_order : (p - 1).Coprime (orderOf x) :=
    hp_coprime_pred.symm.coprime_dvd_right hx_order_dvd_p
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime (x := x) hpred_coprime_order
  have hx_one : x = 1 := by
    rw [← hr, hx_pow_pred, one_pow]
  exact hv_ne (by simp [hx_one])

/-- **Weak reflection, component form.**

For the cyclotomic field `K = Q(zeta_p)`, if the even `i`-th character
component of `Cl(O_K) / p` is nontrivial, then the reflected component
`p - i`, equivalently `1 - i mod p - 1`, is nontrivial.

The proof uses the primary singular-pair extraction in the interior range and
the zero-character contradiction for the endpoint `i = p - 1`.  The only
remaining hard reciprocity input in this chain is
`oneSidedKummerPrincipalReciprocity_canonical`, through the WR-05
nontriviality theorem for the concrete Kummer bad-set character. -/
theorem weakReflection_componentNontrivial
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    {i : ℕ} (hi : IsReflectionComponentIndex p i) (hi_even : Even i)
    (hcomp : eigenspaceComponentNontrivial p K i) :
    eigenspaceComponentNontrivial p K (reflectedComponentIndex p i) := by
  classical
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    rcases hp_odd with ⟨k, hk⟩
    omega
  have hp_gt_two : 2 < p :=
    lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp_ne_two)
  by_cases hend : i = p - 1
  · subst i
    exact False.elim
      ((not_eigenspaceComponentNontrivial_zero p K)
        (eigenspaceComponentNontrivial_zero_of_pred p K hcomp))
  · have hi_low : 2 ≤ i := by
      have hi_pos : 0 < i := hi.1
      rcases hi_even with ⟨m, hm⟩
      omega
    have hi_high : i ≤ p - 3 := by
      by_contra hle
      have hi_lt : i < p := hi.2
      have hp_three : 3 ≤ p := by omega
      have hcases : i = p - 2 ∨ i = p - 1 := by omega
      rcases hcases with hcase | hcase
      · rcases hp_odd with ⟨m, hm⟩
        rcases hi_even with ⟨n, hn⟩
        omega
      · exact hend hcase
    have hi_le : i ≤ p := le_of_lt hi.2
    obtain ⟨η, t, J, hη_ne, hη_local, hη_prime_to_p, hη_not_pow, hη_cast,
      hη_span, _ht_ideal, _ht_ne, _ht_loc, ht_eigen⟩ :=
      exists_integral_numerator_primarySingularPair_of_eigenspaceComponentNontrivial
        (p := p) (K := K) hp_gt_two hi_even hi_low hi_high hcomp
    have hη_galois :
        ∀ a : CyclotomicUnitDelta p, ∃ n : ℕ, ∃ z w : 𝓞 K,
          (n : ZMod p) = (a : ZMod p) ^ i ∧
          0 < n ∧ z ≠ 0 ∧ w ≠ 0 ∧
          cyclotomicRingOfIntegersEquiv (p := p) K a η * w ^ p =
            η ^ n * z ^ p := fun a ↦
      exists_integral_clear_denominators_of_singularGroup_eigen
        (p := p) (K := K) (i := i) η t hη_cast ht_eigen a
    exact
      reflectedComponentNontrivial_of_locallyPrimaryKummerBadSet_galoisWeight_clear_denominators
        (p := p) (K := K) hp_ne_two hp_odd (i := i) hi_le
        η hη_ne hη_not_pow (J : Ideal (𝓞 K))
        hη_prime_to_p hη_local hη_span hη_galois

/-- **Weak reflection, class-number consequence.**

For the cyclotomic field `K = Q(zeta_p)`, divisibility of the plus relative
class number by `p` forces divisibility of the minus relative class number by
`p`. This is the form consumed by Kummer's criterion.
The only reflection input is `weakReflection_componentNontrivial`. -/
theorem weakReflection_dvd_hMinus_of_dvd_hPlus
    (p : ℕ) [Fact p.Prime] (hp_odd : p ≠ 2)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    (hplus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ hMinus K := by
  have hp_odd_nat : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
  by_contra hminus_not
  have hfix : ∀ v : Additive (ClassGroupModP K p),
      cyclotomicGalActionInstance (p := p) (K := K) (-1) v = v :=
    cyclotomicGalActionInstance_neg_one_fixed_of_not_dvd_hMinus p hp_odd K hminus_not
  have hdvd_h : (p : ℕ) ∣ h K := by
    rw [h_eq_hPlus_mul_hMinus p hp_odd K]
    exact dvd_mul_of_dvd_left hplus _
  have hdvd_card : (p : ℕ) ∣ Fintype.card (ClassGroup (𝓞 K)) := by
    simpa [BernoulliRegular.h] using hdvd_h
  obtain ⟨v, hv_ne⟩ :=
    exists_ne_zero_additive_classGroupModP_of_dvd_classNumber p K hdvd_card
  obtain ⟨k, hk_lt, hcomp_k⟩ :=
    exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial_unconditional
      p K (finalReflection_card_zMod_units_isUnit p) ⟨v, hv_ne⟩
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · by_cases hk_zero : k = 0
    · subst hk_zero
      exact (not_eigenspaceComponentNontrivial_zero p K) hcomp_k
    · have hi : IsReflectionComponentIndex p k := by
        constructor
        · exact Nat.pos_of_ne_zero hk_zero
        · omega
      have hcomp_reflected :
          eigenspaceComponentNontrivial p K (reflectedComponentIndex p k) :=
        weakReflection_componentNontrivial p hp_odd_nat K hi hk_even hcomp_k
      have hodd_reflected : Odd (reflectedComponentIndex p k) :=
        reflectedComponentIndex_odd_of_even hp_odd_nat hi hk_even
      exact (not_eigenspaceComponentNontrivial_odd_of_neg_one_fixed
        p hp_odd K hfix hodd_reflected) hcomp_reflected
  · exact (not_eigenspaceComponentNontrivial_odd_of_neg_one_fixed
      p hp_odd K hfix hk_odd) hcomp_k

end BernoulliRegular

end
