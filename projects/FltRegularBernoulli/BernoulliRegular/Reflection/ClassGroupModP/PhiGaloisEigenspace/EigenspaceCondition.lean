module

public import BernoulliRegular.Reflection.ClassGroupModP.PhiGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerPrincipalGen

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

/-- **Eigenspace condition on η**: `σ_a η = η^{a^i} · u^p` for some `u ∈ K`.
This is the Galois-eigenspace condition `[η] ∈ V_i` modulo `K^{×p}`,
expressed at the element level.

Note: this is the relation in `K^×`, not just at the level of `(η)`. -/
def EigenspaceCondition (η : 𝓞 K) (i : ℕ) : Prop :=
  ∀ a : CyclotomicUnitDelta p, ∃ u : K,
    (algebraMap (𝓞 K) K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) =
      ((algebraMap (𝓞 K) K η) ^ ((a : ZMod p).val ^ i : ℕ)) * u ^ p

/-- **`σ-fixed η satisfies eigenspace condition with i = 0`**: trivial
case linking the existing weight-1 phi-Galois infrastructure to the
generalised eigenspace API. -/
theorem eigenspaceCondition_zero_of_fixed
    {η : 𝓞 K}
    (hη_fixed : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a η = η) :
    EigenspaceCondition (p := p) (K := K) η 0 := by
  intro a
  refine ⟨1, ?_⟩
  rw [hη_fixed a, pow_zero, pow_one, one_pow, mul_one]

/-- **`(0 : 𝓞 K)` satisfies every eigenspace condition trivially**: with
`u = 0`, the equation `0 = 0^? · 0^p` holds (both sides are 0). -/
theorem eigenspaceCondition_zero (i : ℕ) (_hi : 0 < i) :
    EigenspaceCondition (p := p) (K := K) (0 : 𝓞 K) i := by
  intro a
  refine ⟨0, ?_⟩
  rw [map_zero, map_zero]
  -- 0 = 0^{(a.val^i)} * 0^p. RHS: 0^pos = 0 (when pos > 0), 0^p = 0.
  have hi_pow : 0 < (a : ZMod p).val ^ i := by
    have ha_val_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr (Units.ne_zero a)
    exact pow_pos ha_val_pos i
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hi_pow), zero_pow (Nat.pos_iff_ne_zero.mp hp_pos),
    zero_mul]

/-- **`(1 : 𝓞 K)` satisfies every eigenspace condition trivially**: σ_a fixes
1, and `1 = 1^{anything} · 1^p` with `u = 1`. -/
theorem eigenspaceCondition_one (i : ℕ) :
    EigenspaceCondition (p := p) (K := K) (1 : 𝓞 K) i := by
  intro a
  refine ⟨1, ?_⟩
  rw [map_one, map_one, one_pow, one_pow, mul_one]

/-- **EigenspaceCondition closure under multiplication by α^p**: if η
satisfies eigenspace i, then η * α^p satisfies eigenspace i too (for α ≠ 0).
The new u is `u * (algebraMap σ_a α) / (algebraMap α)^{a^i}`. -/
theorem eigenspaceCondition_mul_pow_p
    {η : 𝓞 K} {i : ℕ} (h : EigenspaceCondition (p := p) (K := K) η i)
    (α : 𝓞 K) (hα : α ≠ 0) :
    EigenspaceCondition (p := p) (K := K) (η * α ^ p) i := by
  intro a
  obtain ⟨u, hu⟩ := h a
  set α' := cyclotomicRingOfIntegersEquiv (p := p) K a α with hα'_def
  have hα'_ne : α' ≠ 0 := by
    rw [hα'_def]
    intro h
    apply hα
    have hinj : Function.Injective (cyclotomicRingOfIntegersEquiv (p := p) K a) :=
      (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
    exact hinj (h.trans (map_zero _).symm)
  have hα_K : (algebraMap (𝓞 K) K) α ≠ 0 := fun h ↦
    hα <| (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (h.trans (map_zero _).symm)
  refine ⟨u * (algebraMap (𝓞 K) K) α' /
    ((algebraMap (𝓞 K) K) α) ^ ((a : ZMod p).val ^ i : ℕ), ?_⟩
  show (algebraMap (𝓞 K) K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a (η * α ^ p)) =
    ((algebraMap (𝓞 K) K) (η * α ^ p)) ^ ((a : ZMod p).val ^ i : ℕ) *
      (u * (algebraMap (𝓞 K) K) α' /
        ((algebraMap (𝓞 K) K) α) ^ ((a : ZMod p).val ^ i : ℕ)) ^ p
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η * α ^ p) =
    cyclotomicRingOfIntegersEquiv (p := p) K a η * α' ^ p from by
      rw [hα'_def, map_mul, map_pow]]
  rw [map_mul, map_pow, hu]
  rw [map_mul, map_pow, mul_pow, div_pow]
  have hα_K_pow : ((algebraMap (𝓞 K) K) α) ^ ((a : ZMod p).val ^ i : ℕ) ≠ 0 :=
    pow_ne_zero _ hα_K
  field_simp
  ring

/-- **`β^p` satisfies eigenspace-0 condition for β = 0** (vacuous): η = 0,
already discharged by `eigenspaceCondition_zero`-style argument with i = 0
extended via map_zero. -/
theorem eigenspaceCondition_pow_p_zero_of_zero_β :
    EigenspaceCondition (p := p) (K := K) ((0 : 𝓞 K) ^ p) 0 := by
  intro a
  refine ⟨0, ?_⟩
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hp_pos)]
  rw [map_zero, map_zero, zero_pow (Nat.pos_iff_ne_zero.mp hp_pos), mul_zero]

/-- **`β^p` satisfies the eigenspace-0 condition trivially**: for any β
nonzero in 𝓞 K, σ_a (β^p) = (σ_a β)^p, and we factor as
`(β^p)^1 · ((σ_a β)/β)^p` with `u = (σ_a β)/β`. -/
theorem eigenspaceCondition_pow_p_zero (β : 𝓞 K) (hβ : β ≠ 0) :
    EigenspaceCondition (p := p) (K := K) (β ^ p) 0 := by
  intro a
  set α := cyclotomicRingOfIntegersEquiv (p := p) K a β with hα_def
  have hα_ne : α ≠ 0 := by
    rw [hα_def]
    intro h
    apply hβ
    have : cyclotomicRingOfIntegersEquiv (p := p) K a β = 0 := h
    have := (cyclotomicRingOfIntegersEquiv (p := p) K a).injective
      (this.trans (map_zero _).symm)
    exact this
  have hβ_K : (algebraMap (𝓞 K) K) β ≠ 0 := fun h ↦
    hβ <| (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (h.trans (map_zero _).symm)
  refine ⟨(algebraMap (𝓞 K) K) α / (algebraMap (𝓞 K) K) β, ?_⟩
  -- Goal: algebraMap (cyclotomic_iso a (β^p)) =
  --   ((algebraMap (β^p))^{(a.val^0 : ℕ)}) * ((algebraMap α / algebraMap β)^p)
  show (algebraMap (𝓞 K) K)
    (cyclotomicRingOfIntegersEquiv (p := p) K a (β ^ p)) =
      ((algebraMap (𝓞 K) K) (β ^ p)) ^ ((a : ZMod p).val ^ 0 : ℕ) *
      ((algebraMap (𝓞 K) K) α / (algebraMap (𝓞 K) K) β) ^ p
  rw [pow_zero, pow_one]
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (β ^ p) = α ^ p from by
    rw [hα_def]; exact map_pow _ _ _]
  rw [map_pow, map_pow, div_pow]
  field_simp


/-- **Stronger eigenspace condition (𝓞 K-level)**: `σ_a η = η^{a^i} · u^p`
with u ∈ 𝓞 K (not just K). Stronger than `EigenspaceCondition` (which
allows u : K) and easier to manipulate at the 𝓞 K level. -/
def StrongEigenspaceCondition (η : 𝓞 K) (i : ℕ) : Prop :=
  ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K,
    cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p

/-- **Strong eigenspace condition implies the standard eigenspace condition**:
if u ∈ 𝓞 K satisfies the strong condition, its algebra-map image gives
the K-level condition. -/
theorem eigenspaceCondition_of_strong
    {η : 𝓞 K} {i : ℕ}
    (h : StrongEigenspaceCondition (p := p) (K := K) η i) :
    EigenspaceCondition (p := p) (K := K) η i := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨algebraMap (𝓞 K) K u, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a η =
      η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p from hu]
  rw [map_mul, map_pow, map_pow]

/-- **`StrongEigenspaceCondition` for `(1 : 𝓞 K)`**: holds for any i with u = 1. -/
theorem strongEigenspaceCondition_one (i : ℕ) :
    StrongEigenspaceCondition (p := p) (K := K) (1 : 𝓞 K) i := by
  intro a
  refine ⟨1, ?_⟩
  rw [map_one, one_pow, one_pow, mul_one]

/-- **σ_a-fixed at 𝓞 K-level implies StrongEigenspaceCondition 0**: with u = 1. -/
theorem strongEigenspaceCondition_zero_of_fixed
    {η : 𝓞 K}
    (hη_fixed : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a η = η) :
    StrongEigenspaceCondition (p := p) (K := K) η 0 := by
  intro a
  refine ⟨1, ?_⟩
  rw [hη_fixed a, pow_zero, pow_one, one_pow, mul_one]

/-- **`StrongEigenspaceCondition` for ℕ-cast (eigenspace 0)**: any
ℕ-cast is σ_a-fixed at the 𝓞 K level (since cyclotomicRingOfIntegersEquiv
is a ring hom). -/
theorem strongEigenspaceCondition_natCast (n : ℕ) :
    StrongEigenspaceCondition (p := p) (K := K) (n : 𝓞 K) 0 := by
  apply strongEigenspaceCondition_zero_of_fixed
  intro a
  exact map_natCast _ _

/-- **`StrongEigenspaceCondition` for ℤ-cast (eigenspace 0)**: any
ℤ-cast is σ_a-fixed at the 𝓞 K level. -/
theorem strongEigenspaceCondition_intCast (z : ℤ) :
    StrongEigenspaceCondition (p := p) (K := K) (z : 𝓞 K) 0 := by
  apply strongEigenspaceCondition_zero_of_fixed
  intro a
  exact map_intCast _ _

/-- **`StrongEigenspaceCondition` for `β^p` with β a unit (eigenspace 0)**:
σ_a β is also a unit, so we can take u = σ_a β · β⁻¹ ∈ 𝓞 K. -/
theorem strongEigenspaceCondition_pow_p_of_isUnit {β : 𝓞 K} (hβ : IsUnit β) :
    StrongEigenspaceCondition (p := p) (K := K) (β ^ p) 0 := by
  intro a
  set α := cyclotomicRingOfIntegersEquiv (p := p) K a β with hα_def
  obtain ⟨β_inv, hβ_inv_left, hβ_inv_right⟩ : ∃ b : 𝓞 K, β * b = 1 ∧ b * β = 1 := by
    obtain ⟨u, hu⟩ := hβ
    exact ⟨u.inv, hu ▸ u.val_inv, hu ▸ u.inv_val⟩
  refine ⟨α * β_inv, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (β ^ p) = α ^ p from
    map_pow _ _ _]
  rw [pow_zero, pow_one, mul_pow]
  -- Goal: α^p = β^p * (α^p * β_inv^p).
  -- β^p * β_inv^p = (β * β_inv)^p = 1^p = 1.
  have hβp_inv : β ^ p * β_inv ^ p = 1 := by
    rw [← mul_pow, hβ_inv_left, one_pow]
  calc α ^ p
      = α ^ p * (β ^ p * β_inv ^ p) := by rw [hβp_inv, mul_one]
    _ = β ^ p * (α ^ p * β_inv ^ p) := by ring

/-- **`StrongEigenspaceCondition` for `(-1)` (eigenspace 0)**: σ_a fixes -1. -/
theorem strongEigenspaceCondition_neg_one :
    StrongEigenspaceCondition (p := p) (K := K) (-1 : 𝓞 K) 0 := by
  apply strongEigenspaceCondition_zero_of_fixed
  intro a
  simp [map_neg, map_one]

/-- **`StrongEigenspaceCondition` closure under σ-action**: if η satisfies
strong eigenspace i, then so does σ_b η for any b ∈ (ZMod p)ˣ. The new u
at index a is σ_b u (the σ_b-image of the original u). -/
theorem strongEigenspaceCondition_galois_image
    {η : 𝓞 K} {i : ℕ}
    (h : StrongEigenspaceCondition (p := p) (K := K) η i)
    (b : CyclotomicUnitDelta p) :
    StrongEigenspaceCondition (p := p) (K := K)
      (cyclotomicRingOfIntegersEquiv (p := p) K b η) i := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨cyclotomicRingOfIntegersEquiv (p := p) K b u, ?_⟩
  -- σ_a (σ_b η) = σ_b (σ_a η) = σ_b (η^{a^i} · u^p) = (σ_b η)^{a^i} · (σ_b u)^p.
  have h_comm :
      cyclotomicRingOfIntegersEquiv (p := p) K a
        (cyclotomicRingOfIntegersEquiv (p := p) K b η) =
      cyclotomicRingOfIntegersEquiv (p := p) K b
        (cyclotomicRingOfIntegersEquiv (p := p) K a η) := by
    rw [← cyclotomicRingOfIntegersEquiv_mul_apply,
      ← cyclotomicRingOfIntegersEquiv_mul_apply, mul_comm]
  rw [h_comm, hu, map_mul, map_pow, map_pow]

/-- **`StrongEigenspaceCondition` closure under negation at eigenspace 0**:
if η satisfies strong eigenspace 0, then -η also does, with same u. -/
theorem strongEigenspaceCondition_neg_of_eigenspace_zero
    {η : 𝓞 K} (h : StrongEigenspaceCondition (p := p) (K := K) η 0) :
    StrongEigenspaceCondition (p := p) (K := K) (-η) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (-η) =
    -cyclotomicRingOfIntegersEquiv (p := p) K a η from map_neg _ _]
  simp only [pow_zero, pow_one] at hu ⊢
  rw [hu]
  ring

/-- **`EigenspaceCondition` closure under multiplication by σ-fixed (eigenspace 0)**:
if η satisfies eigenspace 0 and ε is strictly σ-fixed, then η · ε
satisfies eigenspace 0 (with same u). -/
theorem eigenspaceCondition_mul_fixed_of_eigenspace_zero
    {η ε : 𝓞 K}
    (h : EigenspaceCondition (p := p) (K := K) η 0)
    (hε_fixed : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a ε = ε) :
    EigenspaceCondition (p := p) (K := K) (η * ε) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η * ε) =
    cyclotomicRingOfIntegersEquiv (p := p) K a η *
      cyclotomicRingOfIntegersEquiv (p := p) K a ε from map_mul _ _ _]
  rw [hε_fixed a]
  simp only [pow_zero, pow_one] at hu ⊢
  rw [map_mul, map_mul, hu]
  ring

/-- **σ_a-fixedness of `(-1)^n`**: trivial via pow_of_fixed and neg_one fixedness. -/
theorem cyclotomicRingOfIntegersEquiv_neg_one_pow_fixed
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    cyclotomicRingOfIntegersEquiv (p := p) K a ((-1 : 𝓞 K) ^ n) = (-1) ^ n := by
  rw [map_pow, map_neg, map_one]

/-- **`EigenspaceCondition` closure under multiplication by ℕ-cast (eigenspace 0)**:
trivial corollary of `_mul_fixed_of_eigenspace_zero` with ε = (n : 𝓞 K). -/
theorem eigenspaceCondition_mul_natCast_of_eigenspace_zero
    {η : 𝓞 K} (h : EigenspaceCondition (p := p) (K := K) η 0) (n : ℕ) :
    EigenspaceCondition (p := p) (K := K) ((n : 𝓞 K) * η) 0 := by
  rw [mul_comm]
  apply eigenspaceCondition_mul_fixed_of_eigenspace_zero h
  intro a
  exact map_natCast _ _

/-- **`StrongEigenspaceCondition` closure under multiplication by σ-fixed (eigenspace 0)**:
if η satisfies strong eigenspace 0 and ε is σ-fixed, then η · ε does. -/
theorem strongEigenspaceCondition_mul_fixed_of_eigenspace_zero
    {η ε : 𝓞 K}
    (h : StrongEigenspaceCondition (p := p) (K := K) η 0)
    (hε_fixed : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a ε = ε) :
    StrongEigenspaceCondition (p := p) (K := K) (η * ε) 0 := by
  intro a
  obtain ⟨u, hu⟩ := h a
  refine ⟨u, ?_⟩
  rw [show cyclotomicRingOfIntegersEquiv (p := p) K a (η * ε) =
    cyclotomicRingOfIntegersEquiv (p := p) K a η *
      cyclotomicRingOfIntegersEquiv (p := p) K a ε from map_mul _ _ _]
  rw [hε_fixed a, hu]
  ring

/-- **Ideal-level σ-fixedness from element-level σ-fixedness**: if η is
σ_a-fixed at the 𝓞 K-level (cyclotomicRingOfIntegersEquiv a η = η),
then `Ideal.span {η}` is also σ_a-fixed. -/
theorem cyclotomicGaloisConjugate_span_singleton_of_fixed
    {η : 𝓞 K} (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η) :
    cyclotomicGaloisConjugate (p := p) (K := K) a
        (Ideal.span ({η} : Set (𝓞 K))) =
      Ideal.span ({η} : Set (𝓞 K)) := by
  rw [cyclotomicGaloisConjugate_span_singleton, hη_fixed]

/-- **σ_a-fixed-pow identity**: for η σ_a-fixed at 𝓞 K-level,
σ_a (η^n) = η^n (since σ_a is a ring hom). -/
theorem cyclotomicRingOfIntegersEquiv_pow_of_fixed
    {η : 𝓞 K} (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η) (n : ℕ) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (η ^ n) = η ^ n := by
  rw [map_pow, hη_fixed]

/-- **σ_a-fixed-mul identity**: σ_a-fixedness is closed under multiplication. -/
theorem cyclotomicRingOfIntegersEquiv_mul_of_fixed
    {η₁ η₂ : 𝓞 K} (a : CyclotomicUnitDelta p)
    (hη₁_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η₁ = η₁)
    (hη₂_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η₂ = η₂) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (η₁ * η₂) = η₁ * η₂ := by
  rw [map_mul, hη₁_fixed, hη₂_fixed]

/-- **σ_a-fixed-neg identity**: σ_a-fixedness is closed under negation. -/
theorem cyclotomicRingOfIntegersEquiv_neg_of_fixed
    {η : 𝓞 K} (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (-η) = -η := by
  rw [map_neg, hη_fixed]

/-- **Ideal-level eigenspace identity from StrongEigenspaceCondition**:
for η satisfying strong eigenspace i with witness u,
`Ideal.span {σ_a η} = (Ideal.span {η})^{a^i} · (Ideal.span {u})^p`
as integral ideals of 𝓞 K. -/
theorem strongEigenspaceCondition_ideal_form
    {η : 𝓞 K} {i : ℕ}
    (h : StrongEigenspaceCondition (p := p) (K := K) η i)
    (a : CyclotomicUnitDelta p) :
    ∃ u : 𝓞 K,
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) =
        Ideal.span ({η} : Set (𝓞 K)) ^ ((a : ZMod p).val ^ i : ℕ) *
          Ideal.span ({u} : Set (𝓞 K)) ^ p := by
  obtain ⟨u, hu⟩ := h a
  refine ⟨u, ?_⟩
  rw [hu, ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow]

set_option backward.isDefEq.respectTransparency false in
/-- Ideal p-th-root cancellation for nonzero integral ideals in `𝓞 K`. -/
theorem ideal_pow_left_inj_of_ne_bot
    {n : ℕ} (hn : n ≠ 0) {A B : Ideal (𝓞 K)}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (h : A ^ n = B ^ n) :
    A = B := by
  have hfact : UniqueFactorizationMonoid.normalizedFactors (A ^ n) =
      UniqueFactorizationMonoid.normalizedFactors (B ^ n) := by
    rw [h]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow] at hfact
  have hfact' : UniqueFactorizationMonoid.normalizedFactors A =
      UniqueFactorizationMonoid.normalizedFactors B :=
    IsAddTorsionFree.nsmul_right_injective hn hfact
  have hassoc : Associated A B :=
    (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
      hA hB).mpr hfact'
  obtain ⟨u, hu⟩ := hassoc
  have h_top : (u : Ideal (𝓞 K)) = ⊤ := Ideal.isUnit_iff.mp u.isUnit
  rw [← hu, h_top, Ideal.mul_top]

/-- Taking p-th roots in the ideal form of `StrongEigenspaceCondition`.

If `(η)=b^p` and `σ_a η = η^{a^i} · u^p`, then the conjugate ideal
`σ_a b` differs from `b^{a^i}` by a principal factor. This is the
ideal-level bridge needed before the Stickelberger quotient of a singular
ideal can be made principal. -/
theorem strongEigenspaceCondition_ideal_pth_root_form
    {η : 𝓞 K} {i : ℕ} {b : Ideal (𝓞 K)}
    (h : StrongEigenspaceCondition (p := p) (K := K) η i)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) (a : CyclotomicUnitDelta p) :
    ∃ u : 𝓞 K,
      cyclotomicGaloisConjugate (p := p) (K := K) a b =
        b ^ ((a : ZMod p).val ^ i : ℕ) * Ideal.span ({u} : Set (𝓞 K)) := by
  obtain ⟨u, hu⟩ := strongEigenspaceCondition_ideal_form
    (p := p) (K := K) h a
  refine ⟨u, ?_⟩
  set e : ℕ := (a : ZMod p).val ^ i with he
  have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hσ_span :
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) =
        (cyclotomicGaloisConjugate (p := p) (K := K) a b) ^ p := by
    rw [← cyclotomicGaloisConjugate_span_singleton, hη,
      cyclotomicGaloisConjugate_pow_ideal]
  have hroot_pow :
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) =
        (b ^ e * Ideal.span ({u} : Set (𝓞 K))) ^ p := by
    rw [hu, hη]
    calc
      (b ^ p) ^ e * Ideal.span ({u} : Set (𝓞 K)) ^ p =
          (b ^ e) ^ p * Ideal.span ({u} : Set (𝓞 K)) ^ p := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm p e]
      _ = (b ^ e * Ideal.span ({u} : Set (𝓞 K))) ^ p := by
        rw [mul_pow]
  have hσb_ne :
      cyclotomicGaloisConjugate (p := p) (K := K) a b ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hb_ne
  have hright_ne : b ^ e * Ideal.span ({u} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨pow_ne_zero e hb_ne, ?_⟩
    intro hspanu_bot
    have hu_zero : u = 0 := by
      rw [Ideal.span_singleton_eq_bot] at hspanu_bot
      exact hspanu_bot
    have hσ_span_ne :
        Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) ≠
          ⊥ := by
      rw [hσ_span]
      exact pow_ne_zero p hσb_ne
    apply hσ_span_ne
    rw [hroot_pow, hu_zero]
    simp [hp_ne]
  exact ideal_pow_left_inj_of_ne_bot hp_ne hσb_ne hright_ne (hσ_span.symm.trans hroot_pow)

/-- The integer exponent with which a strong eigenspace-`i` singular ideal
class contributes to the Stickelberger ideal. -/
def strongEigenspaceStickelbergerExponent (i : ℕ) : ℕ :=
  ∑ a : CyclotomicUnitDelta p,
    (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) * ((a : ZMod p).val)

/-- Exact Stickelberger-ideal action forced by a strong eigenspace condition.

If `(η)=b^p`, then the p-th-root relation for every conjugate of `b`
computes `b^Θ` as the displayed power of `b`, times a principal ideal.
This theorem deliberately keeps the exponent explicit; reducing it to a
quotient such as `b · (β)` is a separate arithmetic statement about that
integer exponent modulo `p`. -/
theorem strongEigenspaceCondition_stickelbergerIdeal_eq_pow_mul_principal
    {η : 𝓞 K} {i : ℕ} {b : Ideal (𝓞 K)}
    (h : StrongEigenspaceCondition (p := p) (K := K) η i)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) :
    ∃ β : 𝓞 K,
      stickelbergerIdeal (p := p) (K := K) b =
        b ^ strongEigenspaceStickelbergerExponent (p := p) i *
          Ideal.span ({β} : Set (𝓞 K)) := by
  classical
  have hroot : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ b =
        b ^ (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
          Ideal.span ({u} : Set (𝓞 K)) := fun a ↦
    strongEigenspaceCondition_ideal_pth_root_form
      (p := p) (K := K) h hη hb_ne a⁻¹
  choose u hu using hroot
  refine ⟨∏ a : CyclotomicUnitDelta p, u a ^ ((a : ZMod p).val), ?_⟩
  unfold stickelbergerIdeal
  calc
    (∏ a : CyclotomicUnitDelta p,
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ b ^
          ((a : ZMod p).val))
        = ∏ a : CyclotomicUnitDelta p,
            (b ^ (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
              Ideal.span ({u a} : Set (𝓞 K))) ^ ((a : ZMod p).val) := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [hu a]
    _ = ∏ a : CyclotomicUnitDelta p,
          (b ^
              ((((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
                ((a : ZMod p).val)) *
            Ideal.span ({u a} : Set (𝓞 K)) ^ ((a : ZMod p).val)) := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [mul_pow, ← pow_mul]
    _ = (∏ a : CyclotomicUnitDelta p,
          b ^ ((((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
            ((a : ZMod p).val))) *
          ∏ a : CyclotomicUnitDelta p,
            Ideal.span ({u a} : Set (𝓞 K)) ^ ((a : ZMod p).val) := by
          rw [Finset.prod_mul_distrib]
    _ = b ^ (∑ a : CyclotomicUnitDelta p,
          (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
            ((a : ZMod p).val)) *
          ∏ a : CyclotomicUnitDelta p,
            Ideal.span ({u a} : Set (𝓞 K)) ^ ((a : ZMod p).val) := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ = b ^ (∑ a : CyclotomicUnitDelta p,
          (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
            ((a : ZMod p).val)) *
          Ideal.span ({∏ a : CyclotomicUnitDelta p, u a ^ ((a : ZMod p).val)} :
            Set (𝓞 K)) := by
          congr 1
          rw [← Ideal.prod_span_singleton
            (Finset.univ : Finset (CyclotomicUnitDelta p))
            (fun a ↦ u a ^ ((a : ZMod p).val))]
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [Ideal.span_singleton_pow]

/-- Taking p-th roots in the ideal form when the strong eigenspace witnesses
are units. In this case the principal factor disappears. -/
theorem strongEigenspaceCondition_ideal_pth_root_form_of_unit_witness
    {η : 𝓞 K} {i : ℕ} {b : Ideal (𝓞 K)}
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a b =
      b ^ ((a : ZMod p).val ^ i : ℕ) := by
  obtain ⟨u, hu_unit, hu⟩ := h a
  set e : ℕ := (a : ZMod p).val ^ i with he
  have hp_ne : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hσ_span :
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) =
        (cyclotomicGaloisConjugate (p := p) (K := K) a b) ^ p := by
    rw [← cyclotomicGaloisConjugate_span_singleton, hη,
      cyclotomicGaloisConjugate_pow_ideal]
  have hroot_pow :
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a η} : Set (𝓞 K)) =
        (b ^ e) ^ p := by
    rw [hu, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      ← Ideal.span_singleton_pow, Ideal.span_singleton_eq_top.mpr hu_unit,
      Ideal.top_pow, Ideal.mul_top, hη]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm p e]
  have hσb_ne :
      cyclotomicGaloisConjugate (p := p) (K := K) a b ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hb_ne
  exact ideal_pow_left_inj_of_ne_bot hp_ne hσb_ne (pow_ne_zero e hb_ne)
    (hσ_span.symm.trans hroot_pow)

/-- Exact Stickelberger-ideal action when the strong eigenspace witnesses are
units: no extra principal factor appears. -/
theorem strongEigenspaceCondition_stickelbergerIdeal_eq_pow_of_unit_witness
    {η : 𝓞 K} {i : ℕ} {b : Ideal (𝓞 K)}
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) :
    stickelbergerIdeal (p := p) (K := K) b =
      b ^ strongEigenspaceStickelbergerExponent (p := p) i := by
  classical
  have hroot : ∀ a : CyclotomicUnitDelta p,
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ b =
        b ^ (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) := fun a ↦
    strongEigenspaceCondition_ideal_pth_root_form_of_unit_witness
      (p := p) (K := K) h hη hb_ne a⁻¹
  unfold stickelbergerIdeal
  calc
    (∏ a : CyclotomicUnitDelta p,
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ b ^
          ((a : ZMod p).val))
        = ∏ a : CyclotomicUnitDelta p,
            (b ^ (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i)) ^
              ((a : ZMod p).val) := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [hroot a]
    _ = ∏ a : CyclotomicUnitDelta p,
          b ^ ((((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
            ((a : ZMod p).val)) := by
          refine Finset.prod_congr rfl fun a _ ↦ ?_
          rw [← pow_mul]
    _ = b ^ (∑ a : CyclotomicUnitDelta p,
          (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
            ((a : ZMod p).val)) := by
          rw [Finset.prod_pow_eq_pow_sum]

/-- The strong eigenspace Stickelberger exponent is positive: the unit
`a = 1` contributes `1`. -/
theorem strongEigenspaceStickelbergerExponent_pos (i : ℕ) :
    0 < strongEigenspaceStickelbergerExponent (p := p) i := by
  classical
  have hval_one : (((1 : CyclotomicUnitDelta p) : ZMod p).val) = 1 := by
    change ((1 : ZMod p).val) = 1
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.one_mod_eq_one.mpr (Fact.out : Nat.Prime p).one_lt.ne'
  have hterm_one :
      ((((1⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
        (((1 : CyclotomicUnitDelta p) : ZMod p).val)) = 1 := by
    rw [show (1⁻¹ : CyclotomicUnitDelta p) = 1 from inv_one]
    rw [hval_one, one_pow, one_mul]
  have hle :
      ((((1⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) *
        (((1 : CyclotomicUnitDelta p) : ZMod p).val)) ≤
        strongEigenspaceStickelbergerExponent (p := p) i := by
    rw [strongEigenspaceStickelbergerExponent]
    exact Finset.single_le_sum
      (f := fun a : CyclotomicUnitDelta p ↦
        (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p).val ^ i) * ((a : ZMod p).val))
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ (1 : CyclotomicUnitDelta p))
  exact lt_of_lt_of_le (by rw [hterm_one]; exact Nat.zero_lt_one) hle

omit [NumberField K] in
/-- If a power of an ideal lies in a prime ideal, then the ideal itself lies
in that prime. -/
theorem ideal_le_prime_of_pow_le
    {I P : Ideal (𝓞 K)} (hP : P.IsPrime) {n : ℕ}
    (hpow : I ^ n ≤ P) :
    I ≤ P := by
  intro x hx
  exact hP.mem_of_pow_mem n (hpow (Ideal.pow_mem_pow hx n))

/-- A Stickelberger-ideal pure-power computation gives the support inclusion
needed by product-form Ref19 transfer. -/
theorem principalGen_support_subset_eta_of_stickelbergerIdeal_eq_pow
    {η : 𝓞 K} {b : Ideal (𝓞 K)} {n : ℕ}
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hstick : stickelbergerIdeal (p := p) (K := K) b = b ^ n) :
    ∀ P : Ideal (𝓞 K), P.IsPrime →
      stickelbergerPrincipalGen (p := p) (K := K) η ∈ P → η ∈ P := by
  intro P hP_prime hξ_mem
  have hspan_le :
      Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
        Set (𝓞 K)) ≤ P :=
    (Ideal.span_singleton_le_iff_mem (I := P)).mpr hξ_mem
  have hbp_le : b ^ (n * p) ≤ P := by
    have hspan_eq :
        Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
            Set (𝓞 K)) =
          b ^ (n * p) := by
      calc
        Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
            Set (𝓞 K))
            = (stickelbergerIdeal (p := p) (K := K) b) ^ p :=
                span_stickelbergerPrincipalGen_of_span_eq_pow hη
        _ = (b ^ n) ^ p := by rw [hstick]
        _ = b ^ (n * p) := by rw [pow_mul]
    rw [← hspan_eq]
    exact hspan_le
  have hb_le : b ≤ P := ideal_le_prime_of_pow_le hP_prime hbp_le
  have hη_mem_pow : η ∈ b ^ p := by
    rw [← hη]
    exact Ideal.mem_span_singleton_self η
  exact hb_le (Ideal.pow_le_self (Fact.out : Nat.Prime p).ne_zero hη_mem_pow)

/-- Unit witnesses for strong eigenspace imply the product-transfer support
condition for `η^Θ`. -/
theorem strongEigenspaceCondition_principalGen_support_subset_eta_of_unit_witness
    {η : 𝓞 K} {i : ℕ} {b : Ideal (𝓞 K)}
    (h : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) :
    ∀ P : Ideal (𝓞 K), P.IsPrime →
      stickelbergerPrincipalGen (p := p) (K := K) η ∈ P → η ∈ P :=
  principalGen_support_subset_eta_of_stickelbergerIdeal_eq_pow hη
    (strongEigenspaceCondition_stickelbergerIdeal_eq_pow_of_unit_witness
      (p := p) (K := K) h hη hb_ne)

/-- Modulo `p`, the exact Stickelberger eigenspace exponent is the expected
weighted unit sum. -/
theorem strongEigenspaceStickelbergerExponent_cast_zmod (i : ℕ) :
    ((strongEigenspaceStickelbergerExponent (p := p) i : ℕ) : ZMod p) =
      ∑ a : CyclotomicUnitDelta p,
        (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p) ^ i) * (a : ZMod p) := by
  rw [strongEigenspaceStickelbergerExponent, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

/-- In eigenspace `1`, the Stickelberger eigenspace exponent is `-1`
modulo `p`. This records the arithmetic obstruction to replacing the exact
power in `strongEigenspaceCondition_stickelbergerIdeal_eq_pow_mul_principal`
by a `b · (β)` quotient without additional input. -/
theorem strongEigenspaceStickelbergerExponent_one_cast_zmod :
    ((strongEigenspaceStickelbergerExponent (p := p) 1 : ℕ) : ZMod p) = -1 := by
  rw [strongEigenspaceStickelbergerExponent_cast_zmod (p := p) 1]
  have hsum :
      (∑ a : CyclotomicUnitDelta p,
        (((a⁻¹ : CyclotomicUnitDelta p) : ZMod p) ^ 1) * (a : ZMod p)) =
        ∑ _a : CyclotomicUnitDelta p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [pow_one, ← Units.val_mul]
    exact congrArg (fun x : CyclotomicUnitDelta p ↦ (x : ZMod p)) (inv_mul_cancel a)
  rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units, nsmul_eq_mul, mul_one]
  have hp_one_le : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  rw [Nat.cast_sub hp_one_le, ZMod.natCast_self]
  simp

/-- The eigenspace-`1` Stickelberger exponent satisfies `S + 1 ≡ 0 mod p`. -/
theorem p_dvd_succ_strongEigenspaceStickelbergerExponent_one :
    p ∣ strongEigenspaceStickelbergerExponent (p := p) 1 + 1 := by
  rw [← ZMod.natCast_eq_zero_iff
    (strongEigenspaceStickelbergerExponent (p := p) 1 + 1) p]
  rw [Nat.cast_add, strongEigenspaceStickelbergerExponent_one_cast_zmod]
  simp

/-- In eigenspace `1`, the exact Stickelberger action gives a principal
product `b^Θ · b`. This is the honest product form corresponding to the
mod-`p` exponent `-1`. -/
theorem strongEigenspaceCondition_stickelbergerIdeal_mul_self_eq_principal
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h : StrongEigenspaceCondition (p := p) (K := K) η 1)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) :
    ∃ β : 𝓞 K,
      stickelbergerIdeal (p := p) (K := K) b * b =
        Ideal.span ({β} : Set (𝓞 K)) := by
  obtain ⟨β, hβ⟩ :=
    strongEigenspaceCondition_stickelbergerIdeal_eq_pow_mul_principal
      (p := p) (K := K) h hη hb_ne
  obtain ⟨n, hn⟩ := p_dvd_succ_strongEigenspaceStickelbergerExponent_one (p := p)
  refine ⟨η ^ n * β, ?_⟩
  calc
    stickelbergerIdeal (p := p) (K := K) b * b =
        (b ^ strongEigenspaceStickelbergerExponent (p := p) 1 *
          Ideal.span ({β} : Set (𝓞 K))) * b := by
          rw [hβ]
    _ = (b ^ strongEigenspaceStickelbergerExponent (p := p) 1 * b) *
          Ideal.span ({β} : Set (𝓞 K)) := by
          ac_rfl
    _ = b ^ (strongEigenspaceStickelbergerExponent (p := p) 1 + 1) *
          Ideal.span ({β} : Set (𝓞 K)) := by
          rw [pow_succ]
    _ = (b ^ p) ^ n * Ideal.span ({β} : Set (𝓞 K)) := by
          rw [hn, pow_mul]
    _ = Ideal.span ({η} : Set (𝓞 K)) ^ n *
          Ideal.span ({β} : Set (𝓞 K)) := by
          rw [← hη]
    _ = Ideal.span ({η ^ n} : Set (𝓞 K)) *
          Ideal.span ({β} : Set (𝓞 K)) := by
          rw [Ideal.span_singleton_pow]
    _ = Ideal.span ({η ^ n * β} : Set (𝓞 K)) := by
          rw [Ideal.span_singleton_mul_span_singleton]

/-- Element-level product comparison from the eigenspace-`1` ideal quotient:
`η^Θ · η` is a unit times a `p`-th power. -/
theorem exists_unit_principalGen_mul_eta_eq_pow_of_strongEigenspace_one
    {η : 𝓞 K} {b : Ideal (𝓞 K)}
    (h : StrongEigenspaceCondition (p := p) (K := K) η 1)
    (hη : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hb_ne : b ≠ ⊥) :
    ∃ u : (𝓞 K)ˣ, ∃ β : 𝓞 K,
      stickelbergerPrincipalGen (p := p) (K := K) η * η = (u : 𝓞 K) * β ^ p := by
  obtain ⟨β, hβ⟩ :=
    strongEigenspaceCondition_stickelbergerIdeal_mul_self_eq_principal
      (p := p) (K := K) h hη hb_ne
  have hspan :
      Ideal.span
          ({stickelbergerPrincipalGen (p := p) (K := K) η * η} : Set (𝓞 K)) =
        Ideal.span ({β ^ p} : Set (𝓞 K)) := by
    calc
      Ideal.span
          ({stickelbergerPrincipalGen (p := p) (K := K) η * η} : Set (𝓞 K)) =
          Ideal.span ({stickelbergerPrincipalGen (p := p) (K := K) η} :
              Set (𝓞 K)) *
            Ideal.span ({η} : Set (𝓞 K)) := by
            rw [Ideal.span_singleton_mul_span_singleton]
      _ = (stickelbergerIdeal (p := p) (K := K) b) ^ p * b ^ p := by
            rw [span_stickelbergerPrincipalGen_of_span_eq_pow hη, hη]
      _ = (stickelbergerIdeal (p := p) (K := K) b * b) ^ p := by
            rw [mul_pow]
      _ = Ideal.span ({β} : Set (𝓞 K)) ^ p := by
            rw [hβ]
      _ = Ideal.span ({β ^ p} : Set (𝓞 K)) := by
            rw [Ideal.span_singleton_pow]
  have h_assoc : Associated (stickelbergerPrincipalGen (p := p) (K := K) η * η)
      (β ^ p) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨u, hu⟩ := h_assoc
  refine ⟨u⁻¹, β, ?_⟩
  have h_inv_mul : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by
    rw [← Units.val_mul]
    simp
  have h_unit_left : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * β ^ p =
      stickelbergerPrincipalGen (p := p) (K := K) η * η := by
    rw [← hu]
    rw [show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
        ((stickelbergerPrincipalGen (p := p) (K := K) η * η) * (u : 𝓞 K)) =
        (stickelbergerPrincipalGen (p := p) (K := K) η * η) *
          (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) by ring]
    rw [h_inv_mul, mul_one]
  exact h_unit_left.symm

/-- **`StrongEigenspaceCondition` closure under multiplication by ℕ-cast (eigenspace 0)**:
trivial corollary of `_mul_fixed_of_eigenspace_zero` with ε = (n : 𝓞 K). -/
theorem strongEigenspaceCondition_mul_natCast_of_eigenspace_zero
    {η : 𝓞 K} (h : StrongEigenspaceCondition (p := p) (K := K) η 0) (n : ℕ) :
    StrongEigenspaceCondition (p := p) (K := K) ((n : 𝓞 K) * η) 0 := by
  rw [mul_comm]
  apply strongEigenspaceCondition_mul_fixed_of_eigenspace_zero h
  intro a
  exact map_natCast _ _

end Furtwaengler

end BernoulliRegular

end
