module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import BernoulliRegular.Reflection.Local.GradedAction
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent
public import BernoulliRegular.Reflection.Local.ComponentDimension.Part1

/-!
# Local unit component dimensions

This file starts the REF-11d assembly layer.  It packages the completed local
principal-unit quotient `completed U_1 / completed U_1^p` with its additive
`ZMod p` character projectors, using the `Delta` action constructed in
`Local.DeltaAction`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- The submodule structure repeatedly synthesizes the quotient's `ZMod p`
-- module instance through additive/multiplicative wrappers.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem exists_delta_zmod_pow_ne_one
    {k : ℕ} (hk_pos : 0 < k) (hk_lt : k < p - 1) :
    ∃ a : CyclotomicUnitDelta p, (a : ZMod p) ^ k ≠ 1 := by
  classical
  letI : IsCyclic (CyclotomicUnitDelta p) := by
    dsimp [CyclotomicUnitDelta]
    exact ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := CyclotomicUnitDelta p)
  refine ⟨g, ?_⟩
  intro hgval
  have hgpow : g ^ k = 1 := by
    apply Units.ext
    change (g : ZMod p) ^ k = 1
    exact hgval
  have hdiv : p - 1 ∣ k := by
    have hdiv' := orderOf_dvd_of_pow_eq_one hgpow
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units] at hdiv'
  exact Nat.not_dvd_of_pos_of_lt hk_pos hk_lt hdiv

theorem exists_delta_zmod_pow_ne_of_lt
    {n j : ℕ} (hnj : n < j) (hdiff_lt : j - n < p - 1) :
    ∃ a : CyclotomicUnitDelta p, (a : ZMod p) ^ n ≠ (a : ZMod p) ^ j := by
  rcases exists_delta_zmod_pow_ne_one (p := p)
      (by omega : 0 < j - n) hdiff_lt with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro hpow
  have hpow_units : a ^ n = a ^ j := by
    apply Units.ext
    change (a : ZMod p) ^ n = (a : ZMod p) ^ j
    exact hpow
  have hdiff_units : a ^ (j - n) = 1 := by
    have hnj_eq : j = n + (j - n) := by omega
    rw [← mul_eq_left (a := a ^ n), ← pow_add, ← hnj_eq, hpow_units]
  exact ha (by
    change ((a ^ (j - n) : CyclotomicUnitDelta p) : ZMod p) = 1
    rw [hdiff_units]
    rfl)

theorem exists_delta_zmod_pow_ne_of_gt
    {n j : ℕ} (hjn : j < n) (hdiff_lt : n - j < p - 1) :
    ∃ a : CyclotomicUnitDelta p, (a : ZMod p) ^ n ≠ (a : ZMod p) ^ j := by
  rcases exists_delta_zmod_pow_ne_one (p := p)
      (by omega : 0 < n - j) hdiff_lt with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro hpow
  have hpow_units : a ^ n = a ^ j := by
    apply Units.ext
    change (a : ZMod p) ^ n = (a : ZMod p) ^ j
    exact hpow
  have hdiff_units : a ^ (n - j) = 1 := by
    have hnj_eq : n = j + (n - j) := by omega
    rw [← mul_eq_left (a := a ^ j), ← pow_add, ← hnj_eq, hpow_units]
  exact ha (by
    change ((a ^ (n - j) : CyclotomicUnitDelta p) : ZMod p) = 1
    rw [hdiff_units]
    rfl)

theorem completedPrincipalUnitSubgroupToOne_equiv
    (n : ℕ) (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitSubgroupToOne (p := p) (K := K) n hn
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) =
      completedPrincipalUnitSubgroupEquiv (p := p) K a 1
        (completedPrincipalUnitSubgroupToOne (p := p) (K := K) n hn u) :=
  rfl

-- This proof crosses between quotient representatives, additive scalar
-- notation, and the graded multiplicative quotient.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem completedPrincipalUnitModPEigenspace_mem_filtration_succ_of_exists_pow_ne
    (n j : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p)
    (hne : ∃ a : CyclotomicUnitDelta p, (a : ZMod p) ^ n ≠ (a : ZMod p) ^ j)
    {x : Additive (completedPrincipalUnitModPQuotient p K)}
    (hxE : x ∈ completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j)
    (hxF : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) n (Fact.out : 1 ≤ n)) :
    x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (n + 1)
      (Nat.le_succ_of_le (Fact.out : 1 ≤ n)) := by
  rcases hne with ⟨a, ha_ne⟩
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n
    (Fact.out : 1 ≤ n)] at hxF
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) (n + 1)
    (Nat.le_succ_of_le (Fact.out : 1 ≤ n))]
  rcases hxF with ⟨u, rfl⟩
  let cn : ZMod p := (a : ZMod p) ^ n
  let cj : ZMod p := (a : ZMod p) ^ j
  let y : Additive (completedPrincipalUnitGradedQuotient p K n) :=
    Additive.ofMul (completedPrincipalUnitGradedClass p K n u)
  have hmod_eq :
      completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n (Fact.out : 1 ≤ n)
          (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) =
        completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n (Fact.out : 1 ≤ n)
          (u ^ cj.val) := by
    have hact := congrArg Additive.toMul (hxE a)
    change completedPrincipalUnitModPDeltaAction (p := p) K a
        (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
          (Fact.out : 1 ≤ n) u) =
      (cj • Additive.ofMul
        (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
          (Fact.out : 1 ≤ n) u)).toMul at hact
    rw [zmod_smul_toMul_completedPrincipalUnitModP (p := p) (K := K)] at hact
    change completedPrincipalUnitModPDeltaAction (p := p) K a
        (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
          (Fact.out : 1 ≤ n) u) =
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
        (Fact.out : 1 ≤ n) u) ^ cj.val at hact
    rw [← map_pow
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
        (Fact.out : 1 ≤ n)) u cj.val] at hact
    rw [completedPrincipalUnitModPClassOfLevel_apply,
      completedPrincipalUnitModPDeltaAction_apply_class] at hact
    rw [completedPrincipalUnitModPClassOfLevel_apply,
      completedPrincipalUnitModPClassOfLevel_apply,
      completedPrincipalUnitSubgroupToOne_equiv]
    exact hact
  have hgraded_eq :
      completedPrincipalUnitGradedClass p K n
          (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) =
        completedPrincipalUnitGradedClass p K n (u ^ cj.val) :=
    completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
      (p := p) (K := K) n hnp hmod_eq
  have hglobal :
      completedPrincipalUnitGradedDeltaActionZMod (p := p) K n a y = cj • y := by
    apply Additive.ext
    change completedPrincipalUnitGradedDeltaAction (p := p) K n a
        (completedPrincipalUnitGradedClass p K n u) =
      (cj • y).toMul
    rw [completedPrincipalUnitGradedDeltaAction_apply_class,
      zmod_smul_toMul_completedPrincipalUnitGraded (p := p) (K := K)]
    change completedPrincipalUnitGradedClass p K n
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) =
      (completedPrincipalUnitGradedClass p K n u) ^ cj.val
    rw [← map_pow (completedPrincipalUnitGradedClass p K n) u cj.val]
    exact hgraded_eq
  have hscalar : cn • y = cj • y := by
    calc
      cn • y =
          completedPrincipalUnitGradedDeltaActionZMod (p := p) K n a y :=
            (completedPrincipalUnitGradedDeltaActionZMod_apply_eq_smul
              (p := p) (K := K) n a y).symm
      _ = cj • y := hglobal
  have hdiff : (cn - cj) • y = 0 := by
    rw [sub_smul, hscalar, sub_self]
  have hdiff_ne : cn - cj ≠ 0 :=
    sub_ne_zero.mpr (by simpa [cn, cj] using ha_ne)
  have hy_zero : y = 0 :=
    (smul_eq_zero.mp hdiff).resolve_left hdiff_ne
  have hclass_one :
      completedPrincipalUnitGradedClass p K n u = 1 := by
    change y.toMul = 1
    rw [hy_zero]
    rfl
  have hu_succ : (u : completedLocalCyclotomicUnitGroup p K) ∈
      completedPrincipalUnitSubgroup p K (n + 1) := by
    have hker : u ∈ completedPrincipalUnitGradedSubgroup p K n :=
      (QuotientGroup.eq_one_iff
        (N := completedPrincipalUnitGradedSubgroup p K n) u).1 hclass_one
    rw [mem_completedPrincipalUnitGradedSubgroup_iff] at hker
    exact hker
  let uSucc : completedPrincipalUnitSubgroup p K (n + 1) :=
    ⟨(u : completedLocalCyclotomicUnitGroup p K), hu_succ⟩
  refine ⟨uSucc, ?_⟩
  apply Additive.ext
  rfl

theorem completedPrincipalUnitModPDeltaAction_mem_filtration
    (n : ℕ) (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    {x : Additive (completedPrincipalUnitModPQuotient p K)}
    (hx : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) :
    completedPrincipalUnitModPDeltaActionZMod (p := p) K a x ∈
      completedPrincipalUnitModPFiltration (p := p) (K := K) n hn := by
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n hn] at hx ⊢
  rcases hx with ⟨u, rfl⟩
  refine ⟨completedPrincipalUnitSubgroupEquiv (p := p) K a n u, ?_⟩
  apply Additive.ext
  change completedPrincipalUnitModPDeltaAction (p := p) K a
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn u) =
    completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn
      (completedPrincipalUnitSubgroupEquiv (p := p) K a n u)
  rw [completedPrincipalUnitModPClassOfLevel_apply,
    completedPrincipalUnitModPDeltaAction_apply_class,
    completedPrincipalUnitModPClassOfLevel_apply,
    completedPrincipalUnitSubgroupToOne_equiv]

/-- The `Delta` action restricted to one filtration step. -/
noncomputable def completedPrincipalUnitModPFiltrationLinearEquivZMod
    (n : ℕ) (hn : 1 ≤ n) (a : CyclotomicUnitDelta p) :
    completedPrincipalUnitModPFiltration (p := p) (K := K) n hn ≃ₗ[ZMod p]
      completedPrincipalUnitModPFiltration (p := p) (K := K) n hn where
  toFun x :=
    ⟨completedPrincipalUnitModPDeltaActionZMod (p := p) K a x.1,
      completedPrincipalUnitModPDeltaAction_mem_filtration (p := p) (K := K) n hn a x.2⟩
  invFun x :=
    ⟨(completedPrincipalUnitModPDeltaActionZMod (p := p) K a).symm x.1, by
      have hx :=
        completedPrincipalUnitModPDeltaAction_mem_filtration
          (p := p) (K := K) n hn a⁻¹ x.2
      simpa using hx⟩
  left_inv x := by
    ext
    exact (completedPrincipalUnitModPDeltaActionZMod (p := p) K a).left_inv x.1
  right_inv x := by
    ext
    exact (completedPrincipalUnitModPDeltaActionZMod (p := p) K a).right_inv x.1
  map_add' x y := by
    ext
    exact map_add (completedPrincipalUnitModPDeltaActionZMod (p := p) K a) x.1 y.1
  map_smul' c x := by
    ext
    exact map_smul (completedPrincipalUnitModPDeltaActionZMod (p := p) K a) c x.1

@[simp]
theorem completedPrincipalUnitModPFiltrationLinearEquivZMod_apply
    (n : ℕ) (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    (x : completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) :
    (completedPrincipalUnitModPFiltrationLinearEquivZMod
      (p := p) (K := K) n hn a x).1 =
      completedPrincipalUnitModPDeltaActionZMod (p := p) K a x.1 :=
  rfl

/-- The restricted `Delta` action on one filtration step. -/
noncomputable def completedPrincipalUnitModPFiltrationDeltaActionZMod
    (n : ℕ) (hn : 1 ≤ n) :
    CyclotomicUnitDelta p →*
      (completedPrincipalUnitModPFiltration (p := p) (K := K) n hn ≃ₗ[ZMod p]
        completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) where
  toFun := completedPrincipalUnitModPFiltrationLinearEquivZMod (p := p) (K := K) n hn
  map_one' := by
    ext x
    change Additive.toMul (completedPrincipalUnitModPDeltaActionZMod (p := p) K 1 x.1) =
      Additive.toMul x.1
    simp
  map_mul' a b := by
    ext x
    change Additive.toMul (completedPrincipalUnitModPDeltaActionZMod (p := p) K (a * b) x.1) =
      Additive.toMul (completedPrincipalUnitModPDeltaActionZMod (p := p) K a
        (completedPrincipalUnitModPDeltaActionZMod (p := p) K b x.1))
    rw [map_mul]
    rfl

/-- A noncomputable representative in `completed U_n` for an element of the
`n`-th filtration step. -/
noncomputable def completedPrincipalUnitModPFiltrationRep
    (n : ℕ) (hn : 1 ≤ n)
    (x : completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) :
    completedPrincipalUnitSubgroup p K n :=
  Classical.choose
    ((mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n hn).mp x.2)

theorem completedPrincipalUnitModPFiltrationRep_spec
    (n : ℕ) (hn : 1 ≤ n)
    (x : completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) :
    x.1 = Additive.ofMul
      (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n hn
        (completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n hn x)) :=
  Classical.choose_spec
    ((mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n hn).mp x.2)

-- The representative-defined linear map needs extra heartbeats for repeated
-- `ZMod p` scalar and quotient-instance synthesis.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- The quotient map from a filtration step to the corresponding completed
graded quotient. -/
noncomputable def completedPrincipalUnitModPFiltrationToGraded
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p) :
    completedPrincipalUnitModPFiltration (p := p) (K := K) n (Fact.out : 1 ≤ n) →ₗ[ZMod p]
      Additive (completedPrincipalUnitGradedQuotient p K n) where
  toFun x :=
    Additive.ofMul
      (completedPrincipalUnitGradedClass p K n
        (completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
          (Fact.out : 1 ≤ n) x))
  map_add' x y := by
    let rx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    let ry := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) y
    let rxy := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) (x + y)
    have hx := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    have hy := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) y
    have hxy := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) (x + y)
    have hclass :
        completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) rxy =
          completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) (rx * ry) := by
      apply Additive.ofMul.injective
      calc
        Additive.ofMul
            (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
              (Fact.out : 1 ≤ n) rxy) = (x + y).1 := hxy.symm
        _ = x.1 + y.1 := rfl
        _ = Additive.ofMul
              (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) rx) +
            Additive.ofMul
              (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) ry) := by rw [hx, hy]
        _ = Additive.ofMul
              (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) (rx * ry)) := by
              apply Additive.ext
              simp
    apply Additive.ext
    change completedPrincipalUnitGradedClass p K n rxy =
      completedPrincipalUnitGradedClass p K n rx *
        completedPrincipalUnitGradedClass p K n ry
    rw [← map_mul]
    exact completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
      (p := p) (K := K) n hnp hclass
  map_smul' c x := by
    let rx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    let rcx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) (c • x)
    have hx := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    have hcx := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) (c • x)
    have hclass :
        completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) rcx =
          completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) (rx ^ c.val) := by
      apply Additive.ofMul.injective
      calc
        Additive.ofMul
            (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
              (Fact.out : 1 ≤ n) rcx) = (c • x).1 := hcx.symm
        _ = c • x.1 := rfl
        _ = Additive.ofMul
              ((completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) rx) ^ c.val) := by
              rw [hx]
              apply Additive.ext
              change (c • Additive.ofMul
                  (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                    (Fact.out : 1 ≤ n) rx)).toMul =
                (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                  (Fact.out : 1 ≤ n) rx) ^ c.val
              rw [zmod_smul_toMul_completedPrincipalUnitModP (p := p) (K := K)]
              rfl
        _ = Additive.ofMul
              (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) (rx ^ c.val)) := by
              apply Additive.ext
              change (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                  (Fact.out : 1 ≤ n) rx) ^ c.val =
                completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                  (Fact.out : 1 ≤ n) (rx ^ c.val)
              rw [map_pow]
    apply Additive.ext
    change completedPrincipalUnitGradedClass p K n rcx =
      (c • Additive.ofMul (completedPrincipalUnitGradedClass p K n rx)).toMul
    rw [zmod_smul_toMul_completedPrincipalUnitGraded (p := p) (K := K)]
    change completedPrincipalUnitGradedClass p K n rcx =
      (completedPrincipalUnitGradedClass p K n rx) ^ c.val
    rw [← map_pow]
    exact completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
      (p := p) (K := K) n hnp hclass

theorem completedPrincipalUnitModPFiltrationToGraded_eq_zero_mem_succ
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p)
    (x : completedPrincipalUnitModPFiltration (p := p) (K := K) n (Fact.out : 1 ≤ n))
    (hx : completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp x = 0) :
    x.1 ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (n + 1)
      (Nat.le_succ_of_le (Fact.out : 1 ≤ n)) := by
  let rx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
    (Fact.out : 1 ≤ n) x
  have hxspec := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
    (Fact.out : 1 ≤ n) x
  have hclass_one : completedPrincipalUnitGradedClass p K n rx = 1 := by
    change (Additive.ofMul (completedPrincipalUnitGradedClass p K n rx) :
        Additive (completedPrincipalUnitGradedQuotient p K n)) = 0 at hx
    exact congrArg Additive.toMul hx
  have hrx_succ : (rx : completedLocalCyclotomicUnitGroup p K) ∈
      completedPrincipalUnitSubgroup p K (n + 1) := by
    have hker : rx ∈ completedPrincipalUnitGradedSubgroup p K n :=
      (QuotientGroup.eq_one_iff
        (N := completedPrincipalUnitGradedSubgroup p K n) rx).1 hclass_one
    rw [mem_completedPrincipalUnitGradedSubgroup_iff] at hker
    exact hker
  rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) (n + 1)
    (Nat.le_succ_of_le (Fact.out : 1 ≤ n))]
  let rxSucc : completedPrincipalUnitSubgroup p K (n + 1) :=
    ⟨(rx : completedLocalCyclotomicUnitGroup p K), hrx_succ⟩
  refine ⟨rxSucc, ?_⟩
  rw [hxspec]
  apply Additive.ext
  rfl

theorem completedPrincipalUnitModPFiltrationToGraded_surjective
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p) :
    Function.Surjective
      (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp) := by
  intro y
  cases y with
  | ofMul q =>
    refine QuotientGroup.induction_on q ?_
    intro u
    let x : completedPrincipalUnitModPFiltration (p := p) (K := K) n
        (Fact.out : 1 ≤ n) :=
      ⟨Additive.ofMul
          (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) u), by
        rw [mem_completedPrincipalUnitModPFiltration_iff (p := p) (K := K) n
          (Fact.out : 1 ≤ n)]
        exact ⟨u, rfl⟩⟩
    refine ⟨x, ?_⟩
    let rx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    have hxspec := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
      (Fact.out : 1 ≤ n) x
    have hclass :
        completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) rx =
          completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) u := by
      apply Additive.ofMul.injective
      exact hxspec.symm
    apply Additive.ext
    change completedPrincipalUnitGradedClass p K n rx =
      completedPrincipalUnitGradedClass p K n u
    exact completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
      (p := p) (K := K) n hnp hclass

theorem completedPrincipalUnitModPFiltrationToGraded_equivariant
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p)
    (a : CyclotomicUnitDelta p)
    (x : completedPrincipalUnitModPFiltration (p := p) (K := K) n (Fact.out : 1 ≤ n)) :
    completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp
        (completedPrincipalUnitModPFiltrationDeltaActionZMod
          (p := p) (K := K) n (Fact.out : 1 ≤ n) a x) =
      completedPrincipalUnitGradedDeltaActionZMod (p := p) K n a
        (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp x) := by
  let rx := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
    (Fact.out : 1 ≤ n) x
  let rax := completedPrincipalUnitModPFiltrationRep (p := p) (K := K) n
    (Fact.out : 1 ≤ n)
    (completedPrincipalUnitModPFiltrationDeltaActionZMod
      (p := p) (K := K) n (Fact.out : 1 ≤ n) a x)
  have hxspec := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
    (Fact.out : 1 ≤ n) x
  have haxspec := completedPrincipalUnitModPFiltrationRep_spec (p := p) (K := K) n
    (Fact.out : 1 ≤ n)
    (completedPrincipalUnitModPFiltrationDeltaActionZMod
      (p := p) (K := K) n (Fact.out : 1 ≤ n) a x)
  have hclass :
      completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
          (Fact.out : 1 ≤ n) rax =
        completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
          (Fact.out : 1 ≤ n)
          (completedPrincipalUnitSubgroupEquiv (p := p) K a n rx) := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul
          (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
            (Fact.out : 1 ≤ n) rax) =
          (completedPrincipalUnitModPFiltrationDeltaActionZMod
            (p := p) (K := K) n (Fact.out : 1 ≤ n) a x).1 := haxspec.symm
      _ = completedPrincipalUnitModPDeltaActionZMod (p := p) K a x.1 := rfl
      _ = completedPrincipalUnitModPDeltaActionZMod (p := p) K a
            (Additive.ofMul
              (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n) rx)) := by rw [hxspec]
      _ = Additive.ofMul
            (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
              (Fact.out : 1 ≤ n)
              (completedPrincipalUnitSubgroupEquiv (p := p) K a n rx)) := by
            apply Additive.ext
            change completedPrincipalUnitModPDeltaAction (p := p) K a
                (completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                  (Fact.out : 1 ≤ n) rx) =
              completedPrincipalUnitModPClassOfLevel (p := p) (K := K) n
                (Fact.out : 1 ≤ n)
                (completedPrincipalUnitSubgroupEquiv (p := p) K a n rx)
            rw [completedPrincipalUnitModPClassOfLevel_apply,
              completedPrincipalUnitModPDeltaAction_apply_class,
              completedPrincipalUnitModPClassOfLevel_apply,
              completedPrincipalUnitSubgroupToOne_equiv]
  apply Additive.ext
  change completedPrincipalUnitGradedClass p K n rax =
    completedPrincipalUnitGradedDeltaAction (p := p) K n a
      (completedPrincipalUnitGradedClass p K n rx)
  rw [completedPrincipalUnitGradedDeltaAction_apply_class]
  exact completedPrincipalUnitGradedClass_eq_of_modPClassOfLevel_eq
    (p := p) (K := K) n hnp hclass

-- The induction repeatedly instantiates filtration submodules at varying
-- indices and transports through proof-irrelevant index bounds.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem completedPrincipalUnitModPEigenspace_le_filtration
    {j : ℕ} (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2) :
    completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j ≤
      completedPrincipalUnitModPFiltration (p := p) (K := K) j (by omega : 1 ≤ j) := by
  intro x hxE
  have hmem : ∀ m, (hm : 1 ≤ m) → m ≤ j →
      x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) m hm := by
    intro m hm hmj
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        rw [completedPrincipalUnitModPFiltration_one_eq_top (p := p) (K := K)]
        exact Submodule.mem_top
      · have hmpos : 1 ≤ m := by omega
        have hmle : m ≤ j := by omega
        have hprev : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) m hmpos :=
          ih hmpos hmle
        have hmlt : m < j := by omega
        have hne : ∃ a : CyclotomicUnitDelta p,
            (a : ZMod p) ^ m ≠ (a : ZMod p) ^ j :=
          exists_delta_zmod_pow_ne_of_lt (p := p) hmlt (by omega)
        haveI : Fact (1 ≤ m) := ⟨hmpos⟩
        have hstep :=
          completedPrincipalUnitModPEigenspace_mem_filtration_succ_of_exists_pow_ne
            (p := p) (K := K) m j (by omega : m ≤ p) hne hxE hprev
        convert hstep using 1
  simpa using hmem j (by omega : 1 ≤ j) le_rfl

-- The descending-filtration induction has the same varying-index submodule
-- synthesis as the preceding containment theorem.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem completedPrincipalUnitModPEigenspace_eq_zero_of_mem_filtration_succ
    {j : ℕ} (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2)
    {x : Additive (completedPrincipalUnitModPQuotient p K)}
    (hxE : x ∈ completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j)
    (hxF : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (j + 1)
      (by omega : 1 ≤ j + 1)) :
    x = 0 := by
  have hmem_t : ∀ t, t ≤ p - j →
      x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (j + 1 + t)
        (by omega : 1 ≤ j + 1 + t) := by
    intro t ht
    induction t with
    | zero =>
      simpa using hxF
    | succ t ih =>
      have ht' : t ≤ p - j := by omega
      have hprev : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K)
          (j + 1 + t) (by omega : 1 ≤ j + 1 + t) :=
        ih ht'
      let n := j + 1 + t
      have hnpos : 1 ≤ n := by omega
      have hnp : n ≤ p := by omega
      have hngt : j < n := by omega
      have hne : ∃ a : CyclotomicUnitDelta p,
          (a : ZMod p) ^ n ≠ (a : ZMod p) ^ j :=
        exists_delta_zmod_pow_ne_of_gt (p := p) hngt (by omega)
      haveI : Fact (1 ≤ n) := ⟨hnpos⟩
      have hstep :=
        completedPrincipalUnitModPEigenspace_mem_filtration_succ_of_exists_pow_ne
          (p := p) (K := K) n j hnp hne hxE hprev
      convert hstep using 2
      omega
  have hbot_mem : x ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (p + 1)
      (by omega : 1 ≤ p + 1) := by
    have h := hmem_t (p - j) (by omega : p - j ≤ p - j)
    have hjp : j ≤ p := by omega
    have hsum0 : j + (p - j) = p := Nat.add_sub_of_le hjp
    have hsum : j + 1 + (p - j) = p + 1 := by omega
    simpa [hsum] using h
  rw [completedPrincipalUnitModPFiltration_p_add_one_eq_bot (p := p) (K := K)] at hbot_mem
  exact hbot_mem

/-- The `i`-th character projection on one filtration step. -/
noncomputable def completedPrincipalUnitModPFiltrationCharacterProjection
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    completedPrincipalUnitModPFiltration (p := p) (K := K) n hn →ₗ[ZMod p]
      completedPrincipalUnitModPFiltration (p := p) (K := K) n hn := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact SingularKummer.CharacterProjection.characterProjection (p := p) i
    (completedPrincipalUnitModPFiltrationDeltaActionZMod (p := p) (K := K) n hn)

/-- The range of the `i`-th character projection on one filtration step. -/
noncomputable def completedPrincipalUnitModPFiltrationCharacterProjectionRange
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    Submodule (ZMod p)
      (completedPrincipalUnitModPFiltration (p := p) (K := K) n hn) :=
  LinearMap.range
    (completedPrincipalUnitModPFiltrationCharacterProjection (p := p) (K := K) n hn i)

theorem completedPrincipalUnitModPFiltrationToGraded_map_characterProjectionRange
    (n : ℕ) [Fact (1 ≤ n)] (hnp : n ≤ p) (i : ℕ) :
    Submodule.map (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp)
        (completedPrincipalUnitModPFiltrationCharacterProjectionRange
          (p := p) (K := K) n (Fact.out : 1 ≤ n) i) =
      completedPrincipalUnitGradedCharacterProjectionRange (p := p) K n i := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact
    SingularKummer.CharacterProjection.map_characterProjection_range_eq_range_of_surjective
      (p := p) i
      (completedPrincipalUnitModPFiltrationDeltaActionZMod
        (p := p) (K := K) n (Fact.out : 1 ≤ n))
      (completedPrincipalUnitGradedDeltaActionZMod (p := p) K n)
      (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) n hnp)
      (completedPrincipalUnitModPFiltrationToGraded_surjective (p := p) (K := K) n hnp)
      (completedPrincipalUnitModPFiltrationToGraded_equivariant (p := p) (K := K) n hnp)

theorem completedPrincipalUnitModPFiltrationCharacterProjection_mem_globalRange
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ)
    {z : completedPrincipalUnitModPFiltration (p := p) (K := K) n hn}
    (hz : z ∈ completedPrincipalUnitModPFiltrationCharacterProjectionRange
      (p := p) (K := K) n hn i) :
    z.1 ∈ completedPrincipalUnitModPCharacterProjectionRange (p := p) K i := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases hz with ⟨w, rfl⟩
  refine ⟨w.1, ?_⟩
  have hcomm :=
    SingularKummer.CharacterProjection.map_projection_apply
      (p := p)
      (completedPrincipalUnitModPFiltrationDeltaActionZMod
        (p := p) (K := K) n hn)
      (completedPrincipalUnitModPDeltaActionZMod (p := p) K)
      (Submodule.subtype (completedPrincipalUnitModPFiltration (p := p) (K := K) n hn))
      (by
        intro a x
        rfl)
      (SingularKummer.CharacterProjection.characterProjectionCoefficient (p := p) i)
      w
  exact hcomm.symm

-- The final comparison map composes projected submodules with the
-- representative-defined filtration-to-graded map.
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
noncomputable def completedPrincipalUnitModPCharacterProjectionRangeToGraded
    (hp_gt_two : 2 < p) {j : ℕ} [Fact (1 ≤ j)]
    (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2) :
    completedPrincipalUnitModPCharacterProjectionRange (p := p) K j →ₗ[ZMod p]
      Additive (completedPrincipalUnitGradedQuotient p K j) := by
  have hj_one : 1 ≤ j := by omega
  have hjp : j ≤ p := by omega
  let toFiltration :
      completedPrincipalUnitModPCharacterProjectionRange (p := p) K j →ₗ[ZMod p]
        completedPrincipalUnitModPFiltration (p := p) (K := K) j hj_one :=
    {
      toFun z :=
        ⟨z.1, by
          have hzE : z.1 ∈ completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j := by
            rw [← completedPrincipalUnitModPCharacterProjectionRange_eq_eigenspace
              (p := p) (K := K) hp_gt_two j]
            exact z.2
          exact completedPrincipalUnitModPEigenspace_le_filtration (p := p) (K := K)
            hj_low hj_high hzE⟩
      map_add' z w := by
        ext
        rfl
      map_smul' c z := by
        ext
        rfl
    }
  exact (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp).comp
    toFiltration

theorem completedPrincipalUnitModPCharacterProjectionRangeToGraded_surjective
    (hp_gt_two : 2 < p) {j : ℕ} [Fact (1 ≤ j)]
    (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2) :
    Function.Surjective
      (completedPrincipalUnitModPCharacterProjectionRangeToGraded
        (p := p) (K := K) hp_gt_two hj_low hj_high) := by
  intro y
  have hj_one : 1 ≤ j := by omega
  have hjp : j ≤ p := by omega
  have hyRange : y ∈ completedPrincipalUnitGradedCharacterProjectionRange (p := p) K j j := by
    rw [completedPrincipalUnitGradedCharacterProjectionRange_eq_top_self
      (p := p) (K := K) hp_gt_two j]
    exact Submodule.mem_top
  have hmap :=
    completedPrincipalUnitModPFiltrationToGraded_map_characterProjectionRange
      (p := p) (K := K) j hjp j
  have hyMap : y ∈ Submodule.map
      (completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp)
      (completedPrincipalUnitModPFiltrationCharacterProjectionRange
        (p := p) (K := K) j hj_one j) := by
    rw [hmap]
    exact hyRange
  rcases hyMap with ⟨z, hzRange, hzmap⟩
  have hzGlobal :
      z.1 ∈ completedPrincipalUnitModPCharacterProjectionRange (p := p) K j :=
    completedPrincipalUnitModPFiltrationCharacterProjection_mem_globalRange
      (p := p) (K := K) j hj_one j hzRange
  refine ⟨⟨z.1, hzGlobal⟩, ?_⟩
  rw [← hzmap]
  change completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp
      (⟨z.1, _⟩ : completedPrincipalUnitModPFiltration (p := p) (K := K) j hj_one) =
    completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp z
  congr 1

theorem completedPrincipalUnitModPCharacterProjectionRangeToGraded_injective
    (hp_gt_two : 2 < p) {j : ℕ} [Fact (1 ≤ j)]
    (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2) :
    Function.Injective
      (completedPrincipalUnitModPCharacterProjectionRangeToGraded
        (p := p) (K := K) hp_gt_two hj_low hj_high) := by
  intro z w hzw
  apply Subtype.ext
  have hj_one : 1 ≤ j := by omega
  have hjp : j ≤ p := by omega
  let f :=
    completedPrincipalUnitModPCharacterProjectionRangeToGraded
      (p := p) (K := K) hp_gt_two hj_low hj_high
  have hdiff : f (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  let zwF : completedPrincipalUnitModPFiltration (p := p) (K := K) j hj_one :=
    ⟨(z - w).1,
      completedPrincipalUnitModPEigenspace_le_filtration (p := p) (K := K)
        hj_low hj_high (by
          have hzwRange : (z - w).1 ∈
              completedPrincipalUnitModPCharacterProjectionRange (p := p) K j := (z - w).2
          rw [← completedPrincipalUnitModPCharacterProjectionRange_eq_eigenspace
            (p := p) (K := K) hp_gt_two j]
          exact hzwRange)⟩
  have hgraded_zero :
      completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp zwF = 0 := by
    change completedPrincipalUnitModPFiltrationToGraded (p := p) (K := K) j hjp
        (⟨(z - w).1, _⟩ :
          completedPrincipalUnitModPFiltration (p := p) (K := K) j hj_one) = 0 at hdiff
    convert hdiff using 1
  have hsucc :
      (z - w).1 ∈ completedPrincipalUnitModPFiltration (p := p) (K := K) (j + 1)
        (by omega : 1 ≤ j + 1) :=
    completedPrincipalUnitModPFiltrationToGraded_eq_zero_mem_succ
      (p := p) (K := K) j hjp zwF hgraded_zero
  have hE : (z - w).1 ∈ completedPrincipalUnitModPDeltaPowerEigenspace (p := p) K j := by
    have hzwRange : (z - w).1 ∈
        completedPrincipalUnitModPCharacterProjectionRange (p := p) K j := (z - w).2
    rw [← completedPrincipalUnitModPCharacterProjectionRange_eq_eigenspace
      (p := p) (K := K) hp_gt_two j]
    exact hzwRange
  have hzero : (z - w).1 = 0 :=
    completedPrincipalUnitModPEigenspace_eq_zero_of_mem_filtration_succ
      (p := p) (K := K) hj_low hj_high hE hsucc
  exact sub_eq_zero.mp hzero

theorem completedPrincipalUnitModPCharacterProjectionRange_finrank_one
    (hp_gt_two : 2 < p) {j : ℕ} (hj_low : 2 ≤ j) (hj_high : j ≤ p - 2) :
    Module.finrank (ZMod p)
        (completedPrincipalUnitModPCharacterProjectionRange (p := p) K j) = 1 := by
  haveI : Fact (1 ≤ j) := ⟨by omega⟩
  let e : completedPrincipalUnitModPCharacterProjectionRange (p := p) K j ≃ₗ[ZMod p]
      Additive (completedPrincipalUnitGradedQuotient p K j) :=
    LinearEquiv.ofBijective
      (completedPrincipalUnitModPCharacterProjectionRangeToGraded
        (p := p) (K := K) hp_gt_two hj_low hj_high)
      ⟨completedPrincipalUnitModPCharacterProjectionRangeToGraded_injective
        (p := p) (K := K) hp_gt_two hj_low hj_high,
       completedPrincipalUnitModPCharacterProjectionRangeToGraded_surjective
        (p := p) (K := K) hp_gt_two hj_low hj_high⟩
  rw [LinearEquiv.finrank_eq e]
  exact completedPrincipalUnitGradedQuotient_finrank_one (p := p) (K := K) j

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular

end
