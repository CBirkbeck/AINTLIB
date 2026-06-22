module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Primary units of `𝓞 K⁺` (ticket FLT37c, scaffold)

For Vandiver Lemma 2 (primary unit decomposition), an element
`γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a rational integer
modulo `𝔭⁺^p`, where `𝔭⁺` is the unique prime of `𝓞 K⁺` above `(p)`.
Equivalently (since `𝔭⁺·𝓞 K = 𝔭² = (ζ-1)^2`), this is
`γ ≡ a (mod (ζ-1)^{2p})` viewed in `𝓞 K`.

This file isolates the K⁺-side primary definition with basic API.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
  Cyclotomic Class Number*.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- An element `γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a
rational integer modulo `𝔭⁺^p`. -/
def IsPrimaryPlus [IsCMField K] (γ : 𝓞 (K⁺)) : Prop :=
  ∃ a : ℤ, γ - (a : 𝓞 (K⁺)) ∈ zetaPrimePlus p K ^ p

namespace IsPrimaryPlus

variable {p K}

/-- Every rational integer is K⁺-primary. -/
theorem of_intCast [IsCMField K] (a : ℤ) :
    IsPrimaryPlus p K (a : 𝓞 (K⁺)) :=
  ⟨a, by simp⟩

/-- Every natural number cast to `𝓞 K⁺` is K⁺-primary. -/
theorem of_natCast [IsCMField K] (a : ℕ) :
    IsPrimaryPlus p K (a : 𝓞 (K⁺)) := by
  have : ((a : ℤ) : 𝓞 (NumberField.maximalRealSubfield K)) = (a : 𝓞 (K⁺)) := by
    push_cast; rfl
  exact this ▸ of_intCast (a : ℤ)

/-- Zero is K⁺-primary. -/
theorem zero [IsCMField K] : IsPrimaryPlus p K 0 :=
  ⟨0, by simp⟩

/-- One is K⁺-primary. -/
theorem one [IsCMField K] : IsPrimaryPlus p K 1 :=
  ⟨1, by simp⟩

/-- The negation of a K⁺-primary element is K⁺-primary. -/
theorem neg [IsCMField K] {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) :
    IsPrimaryPlus p K (-γ) := by
  obtain ⟨a, ha⟩ := hγ
  refine ⟨-a, ?_⟩
  have : -γ - ((-a : ℤ) : 𝓞 (K⁺)) = -(γ - (a : 𝓞 (K⁺))) := by push_cast; ring
  rw [this]
  exact (zetaPrimePlus p K ^ p).neg_mem ha

/-- `IsPrimaryPlus` is preserved by `Neg.neg` in both directions. -/
@[simp]
theorem neg_iff [IsCMField K] {γ : 𝓞 (K⁺)} :
    IsPrimaryPlus p K (-γ) ↔ IsPrimaryPlus p K γ :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩

/-- The sum of two K⁺-primary elements is K⁺-primary. -/
theorem add [IsCMField K] {γ δ : 𝓞 (K⁺)}
    (hγ : IsPrimaryPlus p K γ) (hδ : IsPrimaryPlus p K δ) :
    IsPrimaryPlus p K (γ + δ) := by
  obtain ⟨a, ha⟩ := hγ
  obtain ⟨b, hb⟩ := hδ
  refine ⟨a + b, ?_⟩
  have : (γ + δ) - ((a + b : ℤ) : 𝓞 (K⁺)) =
      (γ - (a : 𝓞 (K⁺))) + (δ - (b : 𝓞 (K⁺))) := by push_cast; ring
  rw [this]
  exact (zetaPrimePlus p K ^ p).add_mem ha hb

/-- The difference of two K⁺-primary elements is K⁺-primary. -/
theorem sub [IsCMField K] {γ δ : 𝓞 (K⁺)}
    (hγ : IsPrimaryPlus p K γ) (hδ : IsPrimaryPlus p K δ) :
    IsPrimaryPlus p K (γ - δ) := by
  rw [sub_eq_add_neg]
  exact hγ.add hδ.neg

/-- The product of two K⁺-primary elements is K⁺-primary. -/
theorem mul [IsCMField K] {γ δ : 𝓞 (K⁺)}
    (hγ : IsPrimaryPlus p K γ) (hδ : IsPrimaryPlus p K δ) :
    IsPrimaryPlus p K (γ * δ) := by
  obtain ⟨a, ha⟩ := hγ
  obtain ⟨b, hb⟩ := hδ
  refine ⟨a * b, ?_⟩
  have heq : γ * δ - ((a * b : ℤ) : 𝓞 (K⁺)) =
      (γ - (a : 𝓞 (K⁺))) * δ + (a : 𝓞 (K⁺)) * (δ - (b : 𝓞 (K⁺))) := by
    push_cast; ring
  rw [heq]
  exact (zetaPrimePlus p K ^ p).add_mem
    ((zetaPrimePlus p K ^ p).mul_mem_right _ ha)
    ((zetaPrimePlus p K ^ p).mul_mem_left _ hb)

/-- A K⁺-primary element raised to a natural-number power is K⁺-primary. -/
theorem pow [IsCMField K] {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) (n : ℕ) :
    IsPrimaryPlus p K (γ ^ n) := by
  induction n with
  | zero => simpa using IsPrimaryPlus.one
  | succ n ih => rw [pow_succ]; exact IsPrimaryPlus.mul ih hγ

/-- The product of a K⁺-primary element and an integer cast is K⁺-primary. -/
theorem int_mul [IsCMField K] {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) (a : ℤ) :
    IsPrimaryPlus p K ((a : 𝓞 (K⁺)) * γ) :=
  (of_intCast a).mul hγ

/-- The product of an integer cast and a K⁺-primary element is K⁺-primary. -/
theorem mul_int [IsCMField K] {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) (a : ℤ) :
    IsPrimaryPlus p K (γ * (a : 𝓞 (K⁺))) :=
  hγ.mul (of_intCast a)

end IsPrimaryPlus

/-- A primary unit of `(𝓞 K⁺)ˣ`. -/
def IsPrimaryUnit [IsCMField K] (u : (𝓞 (K⁺))ˣ) : Prop :=
  IsPrimaryPlus p K (u : 𝓞 (K⁺))

/-- **K⁺ → K bridge for primary elements.**
If `γ ∈ 𝓞 K⁺` is K⁺-primary (`γ ≡ a (mod 𝔭⁺^p)`), then
`algebraMap γ ∈ 𝓞 K` is K-primary (`algebraMap γ ≡ a (mod (ζ-1)^{2p})`).

Uses the ramification fact `𝔭⁺ · 𝓞 K = 𝔭² = ((ζ-1))²`. -/
theorem isPrimary_algebraMap_of_isPrimaryPlus [IsCMField K] (hp_odd : p ≠ 2)
    {γ : 𝓞 (K⁺)} (hγ : IsPrimaryPlus p K γ) :
    IsPrimary p (K := K)
      (algebraMap (𝓞 (K⁺)) (𝓞 K) γ) := by
  obtain ⟨a, ha⟩ := hγ
  refine ⟨a, ?_⟩
  have hmap : algebraMap (𝓞 (K⁺)) (𝓞 K) γ - (a : 𝓞 K) =
      algebraMap (𝓞 (K⁺)) (𝓞 K) (γ - (a : 𝓞 (K⁺))) := by
    rw [map_sub]
    rfl
  rw [hmap]
  have hmem : algebraMap (𝓞 (K⁺)) (𝓞 K) (γ - (a : 𝓞 (K⁺))) ∈
      ((zetaPrimePlus p K) ^ p).map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :=
    Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow, zetaPrimePlus_map_eq p hp_odd K, ← pow_mul] at hmem
  have hpow_eq : (zetaPrime p K) ^ (2 * p) =
      Ideal.span {((zetaSubOne p K : 𝓞 K)) ^ (2 * p)} := by
    rw [zetaPrime, Ideal.span_singleton_pow]
    rfl
  rw [hpow_eq, Ideal.mem_span_singleton] at hmem
  exact hmem

namespace IsPrimaryUnit

variable {p K}

/-- The unit `1` is primary. -/
theorem one [IsCMField K] : IsPrimaryUnit p K (1 : (𝓞 (K⁺))ˣ) :=
  IsPrimaryPlus.one

/-- The product of two primary units is primary. -/
theorem mul [IsCMField K] {u v : (𝓞 (K⁺))ˣ}
    (hu : IsPrimaryUnit p K u) (hv : IsPrimaryUnit p K v) :
    IsPrimaryUnit p K (u * v) := by
  change IsPrimaryPlus p K ((u * v : (𝓞 (K⁺))ˣ) : 𝓞 (K⁺))
  rw [Units.val_mul]
  exact IsPrimaryPlus.mul hu hv

/-- The negation of a primary unit is primary. -/
theorem neg [IsCMField K] {u : (𝓞 (K⁺))ˣ} (hu : IsPrimaryUnit p K u) :
    IsPrimaryUnit p K (-u) := by
  change IsPrimaryPlus p K ((-u : (𝓞 (K⁺))ˣ) : 𝓞 (K⁺))
  rw [Units.val_neg]
  exact IsPrimaryPlus.neg hu

/-- A primary unit raised to a natural-number power is primary. -/
theorem pow [IsCMField K] {u : (𝓞 (K⁺))ˣ} (hu : IsPrimaryUnit p K u)
    (n : ℕ) : IsPrimaryUnit p K (u ^ n) := by
  induction n with
  | zero => simpa using IsPrimaryUnit.one
  | succ n ih => rw [pow_succ]; exact mul ih hu

/-- A primary unit of `𝓞 K⁺`, viewed in `𝓞 K`, is K-primary. -/
theorem isPrimary_algebraMap [IsCMField K] (hp_odd : p ≠ 2)
    {u : (𝓞 (K⁺))ˣ} (hu : IsPrimaryUnit p K u) :
    IsPrimary p (K := K) (algebraMap (𝓞 (K⁺)) (𝓞 K) (u : 𝓞 (K⁺))) :=
  isPrimary_algebraMap_of_isPrimaryPlus p K hp_odd hu

/-- The image of a K⁺-primary unit under algebraMap is σ-fixed in 𝓞 K. -/
theorem complexConj_algebraMap_eq [IsCMField K] (u : (𝓞 (K⁺))ˣ) :
    ringOfIntegersComplexConj K
        (algebraMap (𝓞 (K⁺)) (𝓞 K) (u : 𝓞 (K⁺))) =
      algebraMap (𝓞 (K⁺)) (𝓞 K) (u : 𝓞 (K⁺)) := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj]
  rw [RingOfIntegers.complexConj_eq_self_iff]
  exact ⟨_, rfl⟩

end IsPrimaryUnit

/-- General version: any element of `𝓞 K⁺` viewed in `𝓞 K` is σ-fixed.
The proof is identical to `IsPrimaryUnit.complexConj_algebraMap_eq` but
parameterised over all `𝓞 K⁺` elements. -/
theorem ringOfIntegersComplexConj_algebraMap_eq [IsCMField K] (γ : 𝓞 (K⁺)) :
    ringOfIntegersComplexConj K (algebraMap (𝓞 (K⁺)) (𝓞 K) γ) =
      algebraMap (𝓞 (K⁺)) (𝓞 K) γ := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, RingOfIntegers.complexConj_eq_self_iff]
  exact ⟨γ, rfl⟩

/-- The submonoid of `(𝓞 K⁺)ˣ` consisting of primary units. -/
@[simps!]
noncomputable def primaryUnitsSubmonoid [IsCMField K] : Submonoid (𝓞 (K⁺))ˣ where
  carrier := { u | IsPrimaryUnit p K u }
  one_mem' := IsPrimaryUnit.one
  mul_mem' := IsPrimaryUnit.mul

/-- Membership in `primaryUnitsSubmonoid` is exactly being a primary unit. -/
theorem mem_primaryUnitsSubmonoid_iff [IsCMField K] (u : (𝓞 (K⁺))ˣ) :
    u ∈ primaryUnitsSubmonoid p K ↔ IsPrimaryUnit p K u :=
  Iff.rfl

/-- `u^n` is in the primary units submonoid for any `n : ℕ` if `u` is. -/
theorem pow_mem_primaryUnitsSubmonoid [IsCMField K] {u : (𝓞 (K⁺))ˣ}
    (hu : u ∈ primaryUnitsSubmonoid p K) (n : ℕ) :
    u ^ n ∈ primaryUnitsSubmonoid p K :=
  IsPrimaryUnit.pow hu n

/-! ## Cyclotomic units `(1 - ζ^k)/(1 - ζ)` in `𝓞 K`

For `k` coprime to `p` (so `1 ≤ k ≤ p-1`), the element
`(1 - ζ^k)/(1 - ζ)` is a unit in `𝓞 K`. These are the building blocks
for Pollaczek's primary units in K⁺. -/

section CyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic unit `(1 - ζ^k)/(1 - ζ) ∈ 𝓞 K` for `k` coprime to
`p`. Equivalently `1 + ζ + ζ^2 + ... + ζ^{k-1}`. -/
noncomputable def cyclotomicUnit (k : ℕ) : 𝓞 K :=
  ∑ j ∈ Finset.range k, (zeta_spec p ℚ K).toInteger ^ j

/-- For `k = 1`, the cyclotomic unit is `1`. -/
theorem cyclotomicUnit_one : cyclotomicUnit p K 1 = 1 := by
  unfold cyclotomicUnit
  rw [Finset.sum_range_one, pow_zero]

/-- For `k = 0`, the cyclotomic unit is `0`. -/
theorem cyclotomicUnit_zero : cyclotomicUnit p K 0 = 0 := by
  unfold cyclotomicUnit
  rw [Finset.sum_range_zero]

/-- Recursive identity: `cyclotomicUnit (k+1) = cyclotomicUnit k + ζ^k`. -/
theorem cyclotomicUnit_succ (k : ℕ) :
    cyclotomicUnit p K (k + 1) =
      cyclotomicUnit p K k + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k := by
  unfold cyclotomicUnit
  rw [Finset.sum_range_succ]

/-- For `k = 2`, the cyclotomic unit is `1 + ζ`. -/
theorem cyclotomicUnit_two :
    cyclotomicUnit p K 2 = 1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cyclotomicUnit_succ, cyclotomicUnit_one, pow_one]

/-- For `k = 3`, the cyclotomic unit is `1 + ζ + ζ²`. -/
theorem cyclotomicUnit_three :
    cyclotomicUnit p K 3 = 1 + ((zeta_spec p ℚ K).toInteger : 𝓞 K) +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cyclotomicUnit_succ, cyclotomicUnit_two]

/-- The cyclotomic-unit additive telescope:
`cyclotomicUnit (a + b) = cyclotomicUnit a + ζ^a · cyclotomicUnit b`. -/
theorem cyclotomicUnit_add (a b : ℕ) :
    cyclotomicUnit p K (a + b) =
      cyclotomicUnit p K a +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ a * cyclotomicUnit p K b := by
  unfold cyclotomicUnit
  rw [Finset.sum_range_add]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← pow_add, Nat.add_comm]

/-- Symmetric form: `cyclotomicUnit (a + b) = cyclotomicUnit b + ζ^b · cyclotomicUnit a`. -/
theorem cyclotomicUnit_add_comm (a b : ℕ) :
    cyclotomicUnit p K (a + b) =
      cyclotomicUnit p K b +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ b * cyclotomicUnit p K a := by
  rw [Nat.add_comm, cyclotomicUnit_add]

/-- The cyclotomic-unit telescoping identity:
`(1 - ζ) · cyclotomicUnit k = 1 - ζ^k` in `𝓞 K`. -/
theorem one_sub_zeta_mul_cyclotomicUnit (k : ℕ) :
    (1 - (zeta_spec p ℚ K).toInteger) * cyclotomicUnit p K k =
      1 - ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k := by
  unfold cyclotomicUnit
  rw [Finset.mul_sum]
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Reversed sign form: `(ζ - 1) · cyclotomicUnit k = ζ^k - 1`. -/
theorem zeta_sub_one_mul_cyclotomicUnit (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1 := by
  have h := one_sub_zeta_mul_cyclotomicUnit p K k
  linear_combination -h

/-- **`(ζ - 1) ∣ y - 1` for any `p`-th root of unity `y` in `𝓞 K`.**

If `y ∈ 𝓞 K` satisfies `y^p = 1`, then `y` is a power `ζ^k` of the primitive
`p`-th root of unity. Combined with the cyclotomic identity
`ζ^k - 1 = (ζ - 1) · cyclotomicUnit_k`, this gives `(ζ - 1) ∣ y - 1`. -/
theorem zetaSubOne_dvd_sub_one_of_pow_eq_one {y : 𝓞 K} (hy : y ^ p = 1) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ (y - 1) := by
  have hp_pos : 0 < p := hp.1.pos
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  have hζ_int : IsPrimitiveRoot ((zeta_spec p ℚ K).toInteger) p :=
    (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨k, _, hyk⟩ := hζ_int.eq_pow_of_pow_eq_one hy
  refine ⟨cyclotomicUnit p K k, ?_⟩
  rw [← hyk]
  change ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1 =
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K k
  exact (zeta_sub_one_mul_cyclotomicUnit p K k).symm

/-- **σ acts trivially on `𝓞 K / (ζ-1)`.** For any `x ∈ 𝓞 K` and complex
conjugation `σ`, `(ζ - 1) ∣ x - σ(x)`. Equivalently, `σ(x) ≡ x (mod ζ - 1)`.

Proof: every element of `𝓞 K` is in the ℤ-algebra generated by `p`-th roots
of unity (via `IsCyclotomicExtension.adjoin_roots`). For `y` a `p`-th root,
both `y` and `σ(y)` are `p`-th roots, so `(ζ-1) ∣ y - 1` and `(ζ-1) ∣ σ(y) - 1`,
giving `(ζ-1) ∣ y - σ(y)`. The property extends to ℤ-algebra elements by
additivity and the multiplicative formula
`xy - σ(xy) = (x - σ(x))·y + σ(x)·(y - σ(y))`. -/
theorem zetaSubOne_dvd_sub_complexConj_general [IsCMField K] (x : 𝓞 K) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ (x - ringOfIntegersComplexConj K x) := by
  haveI : IsCyclotomicExtension {p} ℤ (𝓞 K) := IsCyclotomicExtension.ringOfIntegers
  have hx := ‹IsCyclotomicExtension {p} ℤ (𝓞 K)›.adjoin_roots x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, hn, _, hpow⟩ := hy
    rw [Set.mem_singleton_iff] at hn
    -- y^n = 1 with n = p
    have hpow' : y ^ p = 1 := hn ▸ hpow
    have hy1 : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ (y - 1) :=
      zetaSubOne_dvd_sub_one_of_pow_eq_one (p := p) (K := K) hpow'
    have hσy_pow : (ringOfIntegersComplexConj K y) ^ p = 1 := by
      rw [← map_pow, hpow', map_one]
    have hσy1 : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        (ringOfIntegersComplexConj K y - 1) :=
      zetaSubOne_dvd_sub_one_of_pow_eq_one (p := p) (K := K) hσy_pow
    have h_id : y - ringOfIntegersComplexConj K y =
        (y - 1) - (ringOfIntegersComplexConj K y - 1) := by ring
    rw [h_id]
    exact dvd_sub hy1 hσy1
  | algebraMap r =>
    have h_real : ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) r) =
        (algebraMap ℤ (𝓞 K)) r := by
      change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) r) =
        (algebraMap ℤ (𝓞 K)) r
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
        AlgEquiv.commutes]
    rw [h_real, sub_self]
    exact dvd_zero _
  | add x y _ _ ihx ihy =>
    have h_id : x + y - ringOfIntegersComplexConj K (x + y) =
        (x - ringOfIntegersComplexConj K x) + (y - ringOfIntegersComplexConj K y) := by
      rw [map_add]; ring
    rw [h_id]
    exact dvd_add ihx ihy
  | mul x y _ _ ihx ihy =>
    have h_id : x * y - ringOfIntegersComplexConj K (x * y) =
        (x - ringOfIntegersComplexConj K x) * y +
          ringOfIntegersComplexConj K x * (y - ringOfIntegersComplexConj K y) := by
      rw [map_mul]; ring
    rw [h_id]
    exact dvd_add (ihx.mul_right y) (ihy.mul_left _)

/-- **Every element of `𝓞 K` has an integer representative modulo `(ζ-1)`.**

For any `x ∈ 𝓞 K`, there exists `a ∈ ℤ` such that `(ζ - 1) ∣ x - a`. This
expresses the fact that the residue field `𝓞 K / (ζ - 1) ≅ ZMod p` is a
quotient of `ℤ`. -/
theorem exists_int_zetaSubOne_dvd_sub (x : 𝓞 K) :
    ∃ a : ℤ, (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ (x - (a : 𝓞 K)) := by
  haveI : IsCyclotomicExtension {p} ℤ (𝓞 K) := IsCyclotomicExtension.ringOfIntegers
  have hx := ‹IsCyclotomicExtension {p} ℤ (𝓞 K)›.adjoin_roots x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, hn, _, hpow⟩ := hy
    rw [Set.mem_singleton_iff] at hn
    have hpow' : y ^ p = 1 := hn ▸ hpow
    refine ⟨1, ?_⟩
    push_cast
    exact zetaSubOne_dvd_sub_one_of_pow_eq_one (p := p) (K := K) hpow'
  | algebraMap r =>
    refine ⟨r, ?_⟩
    have : (algebraMap ℤ (𝓞 K)) r - ((r : ℤ) : 𝓞 K) = 0 := by
      change (algebraMap ℤ (𝓞 K)) r - (algebraMap ℤ (𝓞 K)) r = 0
      ring
    rw [this]
    exact dvd_zero _
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a + b, ?_⟩
    have h_id : x + y - ((a + b : ℤ) : 𝓞 K) =
        (x - (a : 𝓞 K)) + (y - (b : 𝓞 K)) := by
      push_cast; ring
    rw [h_id]
    exact dvd_add ha hb
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a * b, ?_⟩
    have h_id : x * y - ((a * b : ℤ) : 𝓞 K) =
        (x - (a : 𝓞 K)) * y + (a : 𝓞 K) * (y - (b : 𝓞 K)) := by
      push_cast; ring
    rw [h_id]
    exact dvd_add (ha.mul_right y) (hb.mul_left _)

/-- **Conjugation unit value: `u = -ζ^{p-1}` in `𝓞 K`.** -/
private theorem zetaSubOneConjUnit_val_eq [IsCMField K] :
    ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) =
      -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
  unfold zetaSubOneConjUnit
  push_cast
  rw [IsUnit.unit_spec]
  ring

/-- **`(ζ-1)² ∣ v - V₀` for real `v` in `𝓞 K`.**

For `v ∈ 𝓞 K` with `σ(v) = v` (where `σ` is complex conjugation) and `p`
odd, there exists an integer `V₀` such that `(ζ - 1)² ∣ v - V₀`.

Proof outline:
1. Find `V₀ ∈ ℤ` with `v - V₀ = (ζ-1) · w` (by `exists_int_zetaSubOne_dvd_sub`).
2. Apply `σ`: since `v - V₀` is real, `(ζ-1) · w = σ(ζ-1) · σ(w) = u·(ζ-1)·σ(w)`
   where `u = -ζ^{p-1}`. Cancel `(ζ-1)` to get `w = u · σ(w)`.
3. By `zetaSubOne_dvd_sub_complexConj_general`, `(ζ-1) ∣ σ(w) - w`. Write
   `σ(w) - w = (ζ-1) · q`.
4. Substitute: `w = u·(w + (ζ-1)·q)`, giving `(1 - u)·w = u·(ζ-1)·q`.
5. Compute `1 - u = 1 + ζ^{p-1} = 2 + (ζ-1)·cyclotomicUnit_{p-1}`.
6. Hence `2w = (ζ-1) · (u·q - cyclotomicUnit_{p-1}·w)`, so `(ζ-1) ∣ 2w`.
7. For `p ≠ 2`, `(ζ-1) ∤ 2`, and `(ζ-1)` is prime, so `(ζ-1) ∣ w`.
8. Therefore `(ζ-1)² ∣ (ζ-1)·w = v - V₀`. -/
theorem exists_int_zetaSubOne_sq_dvd_sub_of_real [IsCMField K]
    (hp_odd : p ≠ 2) {v : 𝓞 K}
    (hv_real : ringOfIntegersComplexConj K v = v) :
    ∃ V₀ : ℤ, (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ (v - (V₀ : 𝓞 K)) := by
  obtain ⟨V₀, w, hw⟩ : ∃ V₀ : ℤ, ∃ w : 𝓞 K,
      v - (V₀ : 𝓞 K) = (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * w := by
    obtain ⟨V₀, hV₀⟩ := exists_int_zetaSubOne_dvd_sub (p := p) (K := K) v
    obtain ⟨w, hw⟩ := hV₀
    exact ⟨V₀, w, hw⟩
  refine ⟨V₀, ?_⟩
  rw [hw, sq]
  refine mul_dvd_mul_left _ ?_
  -- Goal: (ζ-1) ∣ w. Use σ(v - V₀) = v - V₀ and complexConj_zetaSubOne_eq.
  have hv_sub_real : ringOfIntegersComplexConj K (v - (V₀ : 𝓞 K)) = v - (V₀ : 𝓞 K) := by
    have hV₀_real : ringOfIntegersComplexConj K ((V₀ : 𝓞 K)) = (V₀ : 𝓞 K) := by
      change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) V₀) =
        (algebraMap ℤ (𝓞 K)) V₀
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
        AlgEquiv.commutes]
    rw [map_sub, hv_real, hV₀_real]
  -- Compute σ((ζ-1) · w) = σ(ζ-1) · σ(w) = u · (ζ-1) · σ(w).
  have h_zsubOne_eq : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) = zetaSubOne p K := rfl
  have h_sigma_zsubOne :
      ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) =
        ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) := by
    rw [h_zsubOne_eq]
    exact complexConj_zetaSubOne_eq (p := p) (K := K)
  -- σ(v - V₀) = σ(ζ-1) · σ(w) = u · (ζ-1) · σ(w). And σ(v - V₀) = v - V₀ = (ζ-1)·w.
  -- Cancel (ζ-1) to get w = u · σ(w).
  have h_w_eq_u_sigma : w =
      ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K w := by
    have h_sigma_w_eq :
        ringOfIntegersComplexConj K (v - (V₀ : 𝓞 K)) =
          ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
              ringOfIntegersComplexConj K w := by
      rw [hw, map_mul, h_sigma_zsubOne]
    rw [hv_sub_real, hw] at h_sigma_w_eq
    have h_zSubOne_ne : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ≠ 0 :=
      zetaSubOne_ne_zero p K
    have h_factor : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * w =
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
          (((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) *
            ringOfIntegersComplexConj K w) := by
      linear_combination h_sigma_w_eq
    exact mul_left_cancel₀ h_zSubOne_ne h_factor
  -- (ζ-1) ∣ σ(w) - w (general fact).
  have h_sigma_w_dvd :
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
        (ringOfIntegersComplexConj K w - w) := by
    have h := zetaSubOne_dvd_sub_complexConj_general (p := p) (K := K) w
    -- h : (ζ-1) ∣ w - σ(w). We want σ(w) - w.
    rcases h with ⟨q, hq⟩
    exact ⟨-q, by linear_combination -hq⟩
  obtain ⟨q, hq⟩ := h_sigma_w_dvd
  -- hq : σ(w) - w = (ζ-1) · q
  -- Now we have w = u·σ(w) and σ(w) = w + (ζ-1)·q. Substituting:
  -- w = u·(w + (ζ-1)·q) = u·w + u·(ζ-1)·q.
  -- So (1 - u)·w = u·(ζ-1)·q.
  -- Compute u value: u = -ζ^{p-1}.
  have h_u_val := zetaSubOneConjUnit_val_eq (p := p) (K := K)
  -- h_u_val : u = -ζ^{p-1}
  have h_zeta_pow_pred : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - 1) :=
    (zeta_sub_one_mul_cyclotomicUnit p K (p - 1)).symm
  -- 1 + ζ^{p-1} = 2 + (ζ^{p-1} - 1) = 2 + (ζ-1)·cyclotomicUnit_{p-1}
  -- So 1 - u = 1 + ζ^{p-1} = 2 + (ζ-1)·cyclotomicUnit_{p-1}.
  -- Hence 2w + (ζ-1)·cycl_{p-1}·w = u·(ζ-1)·q.
  -- So 2w = u·(ζ-1)·q - (ζ-1)·cycl_{p-1}·w = (ζ-1)·(u·q - cycl_{p-1}·w).
  set u : 𝓞 K := ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) with hu_def
  set z : 𝓞 K := (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) with hz_def
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K) with hζ_def
  set c : 𝓞 K := cyclotomicUnit p K (p - 1) with hc_def
  -- h_w_eq_u_sigma: w = u · σ(w)
  -- hq: σ(w) - w = z · q
  -- h_u_val: u = -ζ^{p-1}
  -- h_zeta_pow_pred: ζ^{p-1} - 1 = z · c
  -- Want: 2*w = z * (u*q - c*w)
  -- From w = u·σ(w) and σ(w) = w + z·q:
  --   w = u·(w + z·q) = u·w + u·z·q
  --   (1 - u)·w = u·z·q
  --   1 - u = 1 + ζ^{p-1} = 2 + (ζ^{p-1} - 1) = 2 + z·c
  --   (2 + z·c)·w = u·z·q
  --   2·w = u·z·q - z·c·w = z·(u·q - c·w)
  have h_2w : (2 : 𝓞 K) * w = z * (u * q - c * w) := by
    have h1 : ringOfIntegersComplexConj K w = w + z * q := by linear_combination hq
    rw [h1] at h_w_eq_u_sigma
    -- h_w_eq_u_sigma : w = u · (w + z · q)
    -- Use h_u_val (u = -ζ^{p-1}) and h_zeta_pow_pred (ζ^{p-1} - 1 = z·c)
    -- Goal residual: 2w - z·u·q + z·c·w
    -- = h_w_eq_u_sigma residual + w · (h_u_val residual - h_zeta_pow_pred residual)
    linear_combination h_w_eq_u_sigma + w * (h_u_val - h_zeta_pow_pred)
  -- (ζ-1) | 2w. For p odd, (ζ-1) ∤ 2. Hence (ζ-1) | w.
  have h_zSubOne_dvd_2w : z ∣ ((2 : 𝓞 K) * w) := ⟨_, h_2w⟩
  have h_dvd_2 : ¬ z ∣ (2 : 𝓞 K) := by
    change ¬ (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ (2 : 𝓞 K)
    have h_2_cast : ((2 : ℤ) : 𝓞 K) = (2 : 𝓞 K) := by push_cast; rfl
    rw [← h_2_cast, zeta_sub_one_dvd_Int_iff]
    intro h_p_dvd_2
    have hp_pos : 0 < p := hp.1.pos
    have hp_le_2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast h_p_dvd_2)
    have hp_eq_2 : p = 2 := by
      have hp_ge_2 : 2 ≤ p := hp.1.two_le
      omega
    exact hp_odd hp_eq_2
  have h_prime : Prime z := by
    change Prime (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)
    exact zetaSubOne_prime p K
  rcases h_prime.dvd_mul.mp h_zSubOne_dvd_2w with h | h
  · exact absurd h h_dvd_2
  · exact h

/-- **Real units have an integer representative modulo `(ζ-1)²`.**
For `v_plus : (𝓞 K⁺)ˣ` a real unit, the image `(algebraMap v_plus : 𝓞 K)` is
σ-fixed, so by `exists_int_zetaSubOne_sq_dvd_sub_of_real` there's an integer
`V₀` with `(ζ-1)² ∣ algebraMap v_plus - V₀`. -/
theorem exists_int_zetaSubOne_sq_dvd_algebraMap_real_unit_sub
    [IsCMField K] (hp_odd : p ≠ 2)
    (v_plus : (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
    ∃ V₀ : ℤ, (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (v_plus : 𝓞 (NumberField.maximalRealSubfield K))) - (V₀ : 𝓞 K)) := by
  apply exists_int_zetaSubOne_sq_dvd_sub_of_real (p := p) (K := K) hp_odd
  -- Show algebraMap v_plus is σ-fixed (real).
  change ringOfIntegersComplexConj K
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
        (v_plus : 𝓞 (NumberField.maximalRealSubfield K))) = _
  rw [IsScalarTower.algebraMap_apply
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
    AlgEquiv.commutes]


/-- `cyclotomicUnit k ≡ k (mod ζ - 1)` in `𝓞 K`: the difference
`cyclotomicUnit k - k` is divisible by `ζ - 1`. -/
theorem zetaSubOne_dvd_cyclotomicUnit_sub_natCast (k : ℕ) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      cyclotomicUnit p K k - (k : 𝓞 K) := by
  unfold cyclotomicUnit
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : 𝓞 K) = (n : 𝓞 K) + 1 := by push_cast; rfl
    rw [hcast]
    have hsplit : ∑ j ∈ Finset.range n, ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ j +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n - ((n : 𝓞 K) + 1) =
        (∑ j ∈ Finset.range n, ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ j - (n : 𝓞 K)) +
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n - 1) := by ring
    rw [hsplit]
    refine dvd_add ih ?_
    -- ζ - 1 ∣ ζ^n - 1
    have htel : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
        cyclotomicUnit p K n =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ n - 1 := by
      have h := one_sub_zeta_mul_cyclotomicUnit p K n
      linear_combination -h
    exact ⟨cyclotomicUnit p K n, htel.symm⟩

/-- Equivalent form via `zetaSubOne`. -/
theorem zetaSubOne_dvd_cyclotomicUnit_sub_natCast' (k : ℕ) :
    (zetaSubOne p K : 𝓞 K) ∣ cyclotomicUnit p K k - (k : 𝓞 K) :=
  zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k

/-- The complex conjugate of `cyclotomicUnit k` is also congruent to `k`
modulo `ζ - 1`. -/
theorem zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast [IsCMField K]
    (k : ℕ) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      ringOfIntegersComplexConj K (cyclotomicUnit p K k) - (k : 𝓞 K) := by
  have h := zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k
  have h_apply :
      ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      ringOfIntegersComplexConj K (cyclotomicUnit p K k - (k : 𝓞 K)) :=
    map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h
  rw [map_sub, map_sub (a := cyclotomicUnit p K k), map_one,
    map_natCast] at h_apply
  -- σ(ζ - 1) is associated to ζ - 1
  have hassoc :
      Associated (ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K)) - 1)
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) := by
    have h_orig := associated_complexConj_zetaSubOne p K
    change Associated (ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K)) - 1)
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)
    have h_eq : ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K)) - 1 =
        ringOfIntegersComplexConj K (zetaSubOne p K) := by
      rw [show (zetaSubOne p K : 𝓞 K) = ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 from rfl,
        map_sub, map_one]
    rw [h_eq]
    exact h_orig.symm
  exact hassoc.symm.dvd.trans h_apply

/-- The cyclotomic unit `(1 - ζ^k)/(1 - ζ)` is a unit in `𝓞 K` when
`k` is coprime to `p`. Proven via mathlib's `geom_sum_isUnit`. -/
theorem isUnit_cyclotomicUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (cyclotomicUnit p K k) := by
  unfold cyclotomicUnit
  exact (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_isUnit hp_two hk

/-- The cyclotomic unit packaged as `(𝓞 K)ˣ` when `k` is coprime to `p`. -/
noncomputable def cyclotomicUnitUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 K)ˣ :=
  (isUnit_cyclotomicUnit p K k hk hp_two).unit

@[simp]
theorem cyclotomicUnitUnit_val (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (cyclotomicUnitUnit p K k hk hp_two : 𝓞 K) = cyclotomicUnit p K k :=
  IsUnit.unit_spec _

/-- For `k` coprime to `p`, `(ζ - 1)` is associated to `(ζ^k - 1)` in `𝓞 K`,
with witness `cyclotomicUnitUnit k` (since `(ζ - 1) · cyclotomicUnit k = ζ^k - 1`). -/
theorem associated_zeta_sub_one_zeta_pow_sub_one (k : ℕ) (hk : k.Coprime p)
    (hp_two : 2 ≤ p) :
    Associated (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) :=
  ⟨cyclotomicUnitUnit p K k hk hp_two, by
    rw [cyclotomicUnitUnit_val]
    exact zeta_sub_one_mul_cyclotomicUnit p K k⟩

/-- For `k` coprime to `p`, `(ζ^k - 1)` is prime in `𝓞 K` (being associated
to the prime `(ζ - 1)`). -/
theorem prime_zeta_pow_sub_one (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    Prime (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) :=
  (associated_zeta_sub_one_zeta_pow_sub_one p K k hk hp_two).prime
    (zeta_spec p ℚ K).zeta_sub_one_prime'

/-- The principal ideal generated by `(ζ^k - 1)` for `k` coprime to `p`
equals `zetaPrime p K`. -/
theorem span_zeta_pow_sub_one_eq_zetaPrime (k : ℕ) (hk : k.Coprime p)
    (hp_two : 2 ≤ p) :
    Ideal.span ({((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1} : Set (𝓞 K)) =
      BernoulliRegular.zetaPrime p K := by
  rw [← Ideal.span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_zeta_pow_sub_one p K k hk hp_two)]
  rfl

/-- `(ζ - 1) ∣ (ζ^k - 1)` in `𝓞 K` for any natural `k`. -/
theorem zetaSubOne_dvd_zeta_pow_sub_one (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) :=
  ⟨cyclotomicUnit p K k, (zeta_sub_one_mul_cyclotomicUnit p K k).symm⟩

/-- For integers `a, b` and any natural `k`, `(ζ - 1) ∣ (a + ζ^k · b - (a + b))`
in `𝓞 K`. The key residue-modulo-(ζ-1) computation for FLT case I. -/
theorem zetaSubOne_dvd_factor_sub_sum (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K)) := by
  have h := zetaSubOne_dvd_zeta_pow_sub_one p K k
  have heq :
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((a + b : ℤ) : 𝓞 K) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) * (b : 𝓞 K) := by
    push_cast
    ring
  rw [heq]
  exact h.mul_right _

/-- **First-order Taylor expansion modulo `(ζ - 1)^2`.** For integers `a, b`
and any natural `k`, the cyclotomic factor `a + ζ^k · b` is congruent to
`(a + b) + b·k·(ζ - 1)` modulo `(ζ - 1)^2`. Concretely:
`(ζ - 1)^2 ∣ (a + ζ^k · b) - ((a + b) + b·k·(ζ - 1))`. -/
theorem zetaSubOne_sq_dvd_factor_sub_taylor (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (((a + b : ℤ) : 𝓞 K) +
          (b : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) := by
  -- ζ^k - 1 = (ζ - 1) * cyclotomicUnit_k, and cyclotomicUnit_k - k is divisible by (ζ - 1).
  have htel : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K k
    linear_combination -h
  obtain ⟨w, hw⟩ : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      cyclotomicUnit p K k - (k : 𝓞 K) :=
    zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k
  refine ⟨(b : 𝓞 K) * w, ?_⟩
  -- The difference equals (ζ - 1)^2 · b · w by direct expansion.
  have hcast : ((a + b : ℤ) : 𝓞 K) = (a : 𝓞 K) + (b : 𝓞 K) := by push_cast; rfl
  rw [hcast]
  linear_combination -(b : 𝓞 K) * htel + (b : 𝓞 K) *
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * hw

/-- **`(ζ - 1)^{p-1} ∣ p` in `𝓞 K`.** Cyclotomic ramification: `(p)·𝓞 K`
factors with `zetaPrime` to multiplicity `p - 1`. We use the project's
`primesOver_ramificationIdx_eq_prime_sub_one_at_p` and mathlib's
`Ideal.le_pow_ramificationIdx`. -/
theorem zetaSubOne_pow_p_sub_one_dvd_p :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ (p - 1) ∣ ((p : ℕ) : 𝓞 K) := by
  -- ramificationIdx (rationalPrimeIdeal p) (zetaPrime p K) = p - 1.
  have hram : (rationalPrimeIdeal p).ramificationIdx (zetaPrime p K) = p - 1 :=
    primesOver_ramificationIdx_eq_prime_sub_one_at_p (p := p) (K := K) (zetaPrime p K)
      (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  -- map (algebraMap ℤ (𝓞 K)) (rationalPrimeIdeal p) ≤ (zetaPrime p K) ^ (p - 1).
  have h_le := Ideal.le_pow_ramificationIdx
    (R := ℤ) (S := 𝓞 K)
    (p := rationalPrimeIdeal p) (P := zetaPrime p K)
  rw [hram] at h_le
  -- Cast (p : 𝓞 K) ∈ map ... rationalPrimeIdeal p:
  have hp_mem : ((p : ℕ) : 𝓞 K) ∈
      (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 K)) := by
    have h_int : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by
      push_cast; rfl
    rw [h_int]
    refine Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 K)) ?_
    rw [rationalPrimeIdeal]
    exact Ideal.subset_span (Set.mem_singleton _)
  -- so (p : 𝓞 K) ∈ (zetaPrime)^{p-1}, which is the span of (ζ-1)^{p-1}.
  have hp_in_pow : ((p : ℕ) : 𝓞 K) ∈ (zetaPrime p K) ^ (p - 1) := h_le hp_mem
  rw [show zetaPrime p K =
    Ideal.span {((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)} from rfl,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hp_in_pow
  exact hp_in_pow

/-- **`(ζ-1)^2 ∣ p` for `p ≥ 3`** in `𝓞 K`. Direct corollary of
`zetaSubOne_pow_p_sub_one_dvd_p`: `(ζ-1)^2 ∣ (ζ-1)^{p-1} ∣ p` when
`p - 1 ≥ 2`, i.e., `p ≥ 3`. -/
theorem zetaSubOne_sq_dvd_p (hp_three : 3 ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ ((p : ℕ) : 𝓞 K) :=
  (pow_dvd_pow _ (by omega : 2 ≤ p - 1)).trans
    (zetaSubOne_pow_p_sub_one_dvd_p (p := p) (K := K))

/-- **`γ^p` is congruent to an integer modulo `(ζ-1)^2`** for `p ≥ 3`.
`exists_int_sub_pow_prime_dvd` gives `m ∈ ℤ` with `γ^p ≡ m (mod p)`,
and `(ζ-1)^2 ∣ p` lifts the congruence to `(ζ-1)^2`. -/
theorem exists_int_zetaSubOne_sq_dvd_pow_sub
    (hp_three : 3 ≤ p) (γ : 𝓞 K) :
    ∃ m : ℤ, (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ (γ ^ p - (m : 𝓞 K)) := by
  obtain ⟨m, hm⟩ := exists_int_sub_pow_prime_dvd p γ
  refine ⟨m, ?_⟩
  rw [Ideal.mem_span_singleton] at hm
  have h_p_dvd : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ ((p : ℕ) : 𝓞 K) :=
    zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
  have hp_cast : ((p : ℕ) : 𝓞 K) = (p : 𝓞 K) := by rfl
  rw [hp_cast] at h_p_dvd
  exact h_p_dvd.trans hm

/-- **Second-order Taylor expansion of `ζ^m`:**
`(ζ - 1)^2 ∣ ζ^m - 1 - m·(ζ - 1)` in `𝓞 K`. The proof uses
`ζ^m - 1 = (ζ - 1) · cyclotomicUnit_m` and
`cyclotomicUnit_m - m ∈ (ζ - 1)`. -/
theorem zetaSubOne_sq_dvd_zeta_pow_sub_one_sub_natCast_mul (m : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m - 1) -
        (m : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by
  have htel : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K m =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ m - 1 := by
    have h := one_sub_zeta_mul_cyclotomicUnit p K m
    linear_combination -h
  obtain ⟨w, hw⟩ : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      cyclotomicUnit p K m - (m : 𝓞 K) :=
    zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K m
  refine ⟨w, ?_⟩
  -- (ζ^m - 1) - m(ζ-1) = (ζ-1)·cycl_m - m(ζ-1) = (ζ-1)(cycl_m - m) = (ζ-1)·(ζ-1)·w = (ζ-1)^2·w.
  linear_combination -htel + (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * hw

end CyclotomicUnits
end PrimaryPlus
end FLT37

end BernoulliRegular

end
