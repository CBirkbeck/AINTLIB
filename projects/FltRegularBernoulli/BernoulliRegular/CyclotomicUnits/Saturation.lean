module

public import BernoulliRegular.CyclotomicUnits.Subgroup
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Exact p-saturation for the real cyclotomic-unit subgroup

This file isolates the group-theoretic part of the saturation argument.  The
`p`th-power subgroup is the exact image of the `p`th-power map on a subgroup,
not the closure of that image.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The full real-unit subgroup on the plus side. -/
def EPlus : Subgroup (𝓞 K⁺)ˣ :=
  ⊤

/-- Exact image of the `p`th-power map on a subgroup.  This is not a closure. -/
def pPowerSubgroup {G : Type*} [CommGroup G] (H : Subgroup G) (p : ℕ) : Subgroup G where
  carrier := {x | ∃ y : G, y ∈ H ∧ y ^ p = x}
  one_mem' := by
    refine ⟨1, H.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, haH, rfl⟩ ⟨b, hbH, rfl⟩
    refine ⟨a * b, H.mul_mem haH hbH, ?_⟩
    simp [mul_pow]
  inv_mem' := by
    rintro x ⟨a, haH, rfl⟩
    refine ⟨a⁻¹, H.inv_mem haH, ?_⟩
    simp [inv_pow]

theorem mem_pPowerSubgroup_iff {G : Type*} [CommGroup G] {H : Subgroup G}
    {p : ℕ} {x : G} :
    x ∈ pPowerSubgroup H p ↔ ∃ y : G, y ∈ H ∧ y ^ p = x :=
  Iff.rfl

theorem pow_mem_pPowerSubgroup {G : Type*} [CommGroup G] {H : Subgroup G}
    {p : ℕ} {x : G} (hx : x ∈ H) :
    x ^ p ∈ pPowerSubgroup H p :=
  ⟨x, hx, rfl⟩

/-- `H` is `p`-saturated in `E` if an element of `H` that is a `p`th power in
`E` is already a `p`th power in `H`. -/
def pSaturated {G : Type*} [CommGroup G] (H E : Subgroup G) (p : ℕ) : Prop :=
  H ≤ E ∧ H ⊓ pPowerSubgroup E p ≤ pPowerSubgroup H p

theorem pSaturated.le {G : Type*} [CommGroup G] {H E : Subgroup G} {p : ℕ}
    (h : pSaturated H E p) :
    H ≤ E :=
  h.1

theorem pSaturated.mem_pPowerSubgroup_of_mem {G : Type*} [CommGroup G]
    {H E : Subgroup G} {p : ℕ} (h : pSaturated H E p) {x : G}
    (hxH : x ∈ H) (hxEpow : x ∈ pPowerSubgroup E p) :
    x ∈ pPowerSubgroup H p :=
  h.2 ⟨hxH, hxEpow⟩

theorem CPlus_le_EPlus (hp_three : 3 ≤ p) :
    CPlus (p := p) (K := K) hp_three ≤ EPlus (K := K) := by
  intro x hx
  trivial

/-- Integer-exponent product of the sign and the finite `CPlus` generators. -/
noncomputable def CPlusExponentProduct (hp_three : 3 ≤ p) (s : ℤ)
    (e : Fin ((p - 3) / 2) → ℤ) : (𝓞 K⁺)ˣ :=
  (-1 : (𝓞 K⁺)ˣ) ^ s *
    ∏ a : Fin ((p - 3) / 2),
      CPlusGenerator (p := p) (K := K) hp_three a ^ e a

theorem CPlusExponentProduct_mul (hp_three : 3 ≤ p) (s t : ℤ)
    (e f : Fin ((p - 3) / 2) → ℤ) :
    CPlusExponentProduct (p := p) (K := K) hp_three s e *
        CPlusExponentProduct (p := p) (K := K) hp_three t f =
      CPlusExponentProduct (p := p) (K := K) hp_three (s + t) (e + f) := by
  classical
  simp [CPlusExponentProduct, zpow_add, Finset.prod_mul_distrib, mul_assoc, mul_left_comm]

theorem CPlusExponentProduct_inv (hp_three : 3 ≤ p) (s : ℤ)
    (e : Fin ((p - 3) / 2) → ℤ) :
    (CPlusExponentProduct (p := p) (K := K) hp_three s e)⁻¹ =
      CPlusExponentProduct (p := p) (K := K) hp_three (-s) (-e) := by
  classical
  simp [CPlusExponentProduct, Finset.prod_inv_distrib, mul_comm]

theorem CPlusExponentProduct_single (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    CPlusExponentProduct (p := p) (K := K) hp_three 0
        (fun j => if j = i then 1 else 0) =
      CPlusGenerator (p := p) (K := K) hp_three i := by
  classical
  unfold CPlusExponentProduct
  simp only [zpow_zero, one_mul]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem CPlusExponentProduct_mem_CPlus (hp_three : 3 ≤ p) (s : ℤ)
    (e : Fin ((p - 3) / 2) → ℤ) :
    CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
      CPlus (p := p) (K := K) hp_three := by
  classical
  unfold CPlusExponentProduct
  exact (CPlus (p := p) (K := K) hp_three).mul_mem
    ((CPlus (p := p) (K := K) hp_three).zpow_mem
      (neg_one_mem_CPlus (p := p) (K := K) hp_three) s)
    ((CPlus (p := p) (K := K) hp_three).prod_mem fun a _ =>
      (CPlus (p := p) (K := K) hp_three).zpow_mem
        (CPlusGenerator_mem (p := p) (K := K) hp_three a) (e a))

/-- Every element of `CPlus` has an integer-exponent expression in the sign and
the finite cyclotomic-unit generators. -/
theorem exists_CPlusExponentProduct_of_mem_CPlus (hp_three : 3 ≤ p)
    {x : (𝓞 K⁺)ˣ} (hx : x ∈ CPlus (p := p) (K := K) hp_three) :
    ∃ (s : ℤ) (e : Fin ((p - 3) / 2) → ℤ),
      CPlusExponentProduct (p := p) (K := K) hp_three s e = x := by
  classical
  unfold CPlus at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rcases hx with rfl
        refine ⟨1, 0, ?_⟩
        simp [CPlusExponentProduct]
      · rcases hx with ⟨i, rfl⟩
        refine ⟨0, (fun j => if j = i then 1 else 0), ?_⟩
        exact CPlusExponentProduct_single (p := p) (K := K) hp_three i
  | one =>
      refine ⟨0, 0, ?_⟩
      simp [CPlusExponentProduct]
  | mul x y _ _ hx hy =>
      rcases hx with ⟨s, e, hx⟩
      rcases hy with ⟨t, f, hy⟩
      refine ⟨s + t, e + f, ?_⟩
      rw [← hx, ← hy, CPlusExponentProduct_mul]
  | inv x _ hx =>
      rcases hx with ⟨s, e, hx⟩
      refine ⟨-s, -e, ?_⟩
      rw [← hx, ← CPlusExponentProduct_inv]

theorem zpow_pow_eq_self_of_sq_eq_one_of_odd {G : Type*} [CommGroup G] {x : G}
    (hx_sq : x ^ 2 = 1) {n : ℕ} (hn_odd : n % 2 = 1) (s : ℤ) :
    (x ^ s) ^ n = x ^ s := by
  have hn_split : n = 2 * (n / 2) + 1 := by omega
  have hxs_sq : (x ^ s) ^ 2 = 1 := by
    calc
      (x ^ s) ^ 2 = (x ^ s) ^ (2 : ℤ) :=
        (zpow_natCast (x ^ s) 2).symm
      _ = x ^ (s * (2 : ℤ)) := by rw [zpow_mul]
      _ = x ^ ((2 : ℤ) * s) := by rw [mul_comm]
      _ = (x ^ (2 : ℤ)) ^ s := by rw [zpow_mul]
      _ = (x ^ 2) ^ s :=
        congrArg (fun y : G => y ^ s) (zpow_natCast x 2)
      _ = 1 := by rw [hx_sq, one_zpow]
  calc
    (x ^ s) ^ n = (x ^ s) ^ (2 * (n / 2) + 1) :=
      congrArg (fun m : ℕ => (x ^ s) ^ m) hn_split
    _ = (x ^ s) ^ (2 * (n / 2)) * x ^ s := by rw [pow_add, pow_one]
    _ = ((x ^ s) ^ 2) ^ (n / 2) * x ^ s := by rw [pow_mul]
    _ = x ^ s := by rw [hxs_sq]; simp

set_option linter.unusedSectionVars false in
theorem neg_one_zpow_pow_eq_self (hp_odd : p ≠ 2) (s : ℤ) :
    ((-1 : (𝓞 K⁺)ˣ) ^ s) ^ p = (-1 : (𝓞 K⁺)ˣ) ^ s := by
  have hp_mod : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd)
  have hneg_sq : ((-1 : (𝓞 K⁺)ˣ) ^ 2) = 1 := by
    ext
    simp
  exact zpow_pow_eq_self_of_sq_eq_one_of_odd hneg_sq hp_mod s

theorem neg_one_zpow_mem_pPowerSubgroup_CPlus (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (s : ℤ) :
    (-1 : (𝓞 K⁺)ˣ) ^ s ∈
      pPowerSubgroup (CPlus (p := p) (K := K) hp_three) p := by
  refine ⟨(-1 : (𝓞 K⁺)ˣ) ^ s,
    (CPlus (p := p) (K := K) hp_three).zpow_mem
      (neg_one_mem_CPlus (p := p) (K := K) hp_three) s, ?_⟩
  exact neg_one_zpow_pow_eq_self (p := p) (K := K) hp_odd s

theorem CPlusExponentProduct_pow_of_exponents_eq_mul (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) (s : ℤ) (e k : Fin ((p - 3) / 2) → ℤ)
    (hk : ∀ a, e a = (p : ℤ) * k a) :
    CPlusExponentProduct (p := p) (K := K) hp_three s k ^ p =
      CPlusExponentProduct (p := p) (K := K) hp_three s e := by
  classical
  unfold CPlusExponentProduct
  rw [mul_pow, neg_one_zpow_pow_eq_self (p := p) (K := K) hp_odd s,
    ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro a _
  calc
    (CPlusGenerator (p := p) (K := K) hp_three a ^ k a) ^ p =
        CPlusGenerator (p := p) (K := K) hp_three a ^ (k a * (p : ℤ)) := by
          rw [← zpow_natCast, zpow_mul]
    _ = CPlusGenerator (p := p) (K := K) hp_three a ^ ((p : ℤ) * k a) := by
          rw [mul_comm]
    _ = CPlusGenerator (p := p) (K := K) hp_three a ^ e a := by
          rw [hk a]

/-- Concrete group-theoretic saturation criterion for `CPlus`.  CU-14e is
intended to provide the exponent-vanishing hypothesis from the logarithm
determinant; this theorem contains no p-adic logarithm input. -/
theorem CPlus_pSaturated_of_generator_exponents_modP_zero (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p)
    (h : ∀ (s : ℤ) (e : Fin ((p - 3) / 2) → ℤ),
      CPlusExponentProduct (p := p) (K := K) hp_three s e ∈
          pPowerSubgroup (EPlus (K := K)) p →
        ∀ a, (e a : ZMod p) = 0) :
    pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p := by
  classical
  refine ⟨CPlus_le_EPlus (p := p) (K := K) hp_three, ?_⟩
  intro x hx
  rcases hx with ⟨hxC, hxEpow⟩
  rcases exists_CPlusExponentProduct_of_mem_CPlus
      (p := p) (K := K) hp_three hxC with
    ⟨s, e, hxe⟩
  have hzero : ∀ a, (e a : ZMod p) = 0 := by
    refine h s e ?_
    simpa [hxe] using hxEpow
  have hdiv : ∀ a, (p : ℤ) ∣ e a := fun a =>
    (CharP.intCast_eq_zero_iff (ZMod p) p (e a)).mp (hzero a)
  choose k hk using hdiv
  refine ⟨CPlusExponentProduct (p := p) (K := K) hp_three s k,
    CPlusExponentProduct_mem_CPlus (p := p) (K := K) hp_three s k, ?_⟩
  calc
    CPlusExponentProduct (p := p) (K := K) hp_three s k ^ p =
        CPlusExponentProduct (p := p) (K := K) hp_three s e :=
          CPlusExponentProduct_pow_of_exponents_eq_mul
            (p := p) (K := K) hp_odd hp_three s e k hk
    _ = x := hxe

end BernoulliRegular

end
