/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Finsupp.LSum
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# The tuple-chain homotopy for alternating Cech cochains

This file formalizes the support-preserving free-chain construction in Conrad,
*Cech Cohomology and Alternating Cochains*. It is the combinatorial core of the
homotopy in Stacks Project, Lemma 20.23.6 (Tag 01FM).
-/

open Set

namespace ModularCurves

noncomputable section

universe u

/-- The free integral module on tuples of length `n + 1`. -/
abbrev CechTupleChain (ι : Type u) (n : ℕ) :=
  (Fin (n + 1) → ι) →₀ ℤ

/-- Delete one entry from a tuple. -/
def cechTupleDelete {ι : Type u} {n : ℕ}
    (i : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    Fin (n + 1) → ι :=
  i ∘ k.succAbove

/-- Extend a function on tuple generators linearly. -/
def cechTupleLinearExtension {ι : Type u} {n m : ℕ}
    (f : (Fin (n + 1) → ι) → CechTupleChain ι m) :
    CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m :=
  Finsupp.lsum ℤ fun i =>
    LinearMap.toSpanSingleton ℤ (CechTupleChain ι m) (f i)

@[simp]
theorem cechTupleLinearExtension_single {ι : Type u} {n m : ℕ}
    (f : (Fin (n + 1) → ι) → CechTupleChain ι m)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTupleLinearExtension f (Finsupp.single i a) = a • f i := by
  simp [cechTupleLinearExtension]

/-- The alternating deletion boundary of a tuple generator. -/
def cechTupleBoundaryBasis {ι : Type u} (n : ℕ)
    (i : Fin (n + 2) → ι) : CechTupleChain ι n :=
  ∑ k : Fin (n + 2),
    Finsupp.single (cechTupleDelete i k) ((-1 : ℤ) ^ (k : ℕ))

/-- The alternating deletion boundary on free tuple chains. -/
def cechTupleBoundary {ι : Type u} (n : ℕ) :
    CechTupleChain ι (n + 1) →ₗ[ℤ] CechTupleChain ι n :=
  cechTupleLinearExtension (cechTupleBoundaryBasis n)

@[simp]
theorem cechTupleBoundary_single {ι : Type u} (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    cechTupleBoundary n (Finsupp.single i a) =
      a • cechTupleBoundaryBasis n i := by
  simp [cechTupleBoundary]

/-- Prepend one entry to a tuple. -/
def cechTuplePrepend {ι : Type u} {n : ℕ}
    (i₀ : ι) (i : Fin (n + 1) → ι) : Fin (n + 2) → ι :=
  Fin.cases i₀ i

/-- Prepending a fixed entry, extended to free tuple chains. -/
def cechTuplePrependChain {ι : Type u} (i₀ : ι) (n : ℕ) :
    CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι (n + 1) :=
  cechTupleLinearExtension fun i => Finsupp.single (cechTuplePrepend i₀ i) 1

@[simp]
theorem cechTuplePrependChain_single {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTuplePrependChain i₀ n (Finsupp.single i a) =
      Finsupp.single (cechTuplePrepend i₀ i) a := by
  simp [cechTuplePrependChain]

@[simp]
theorem cechTupleDelete_prepend_zero {ι : Type u} {n : ℕ} (i₀ : ι)
    (i : Fin (n + 1) → ι) :
    cechTupleDelete (cechTuplePrepend i₀ i) 0 = i := by
  funext k
  rfl

@[simp]
theorem cechTupleDelete_prepend_succ {ι : Type u} {n : ℕ} (i₀ : ι)
    (i : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    cechTupleDelete (cechTuplePrepend i₀ i) k.succ =
      cechTuplePrepend i₀ (cechTupleDelete i k) := by
  funext l
  refine Fin.cases ?_ (fun m => ?_) l
  · rfl
  · simp [cechTupleDelete, cechTuplePrepend, Function.comp_apply]

theorem cechTupleDelete_delete {ι : Type u} {n : ℕ}
    (i : Fin (n + 3) → ι) {k : Fin (n + 3)} {l : Fin (n + 2)}
    (hkl : k ≤ l.castSucc) :
    cechTupleDelete (cechTupleDelete i l.succ)
        (k.castLT (lt_of_le_of_lt hkl l.is_lt)) =
      cechTupleDelete (cechTupleDelete i k) l := by
  funext m
  have hδ := CategoryTheory.ConcreteCategory.congr_hom
    (SimplexCategory.δ_comp_δ'' hkl)
  exact congrArg i (hδ m)

private theorem cechTuplePrepend_contraction_single {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 2) → ι) :
    cechTupleBoundary (n + 1)
          (cechTuplePrependChain i₀ (n + 1) (Finsupp.single i 1)) +
        cechTuplePrependChain i₀ n
          (cechTupleBoundary n (Finsupp.single i 1)) =
      Finsupp.single i 1 := by
  simp only [cechTuplePrependChain_single, cechTupleBoundary_single, one_smul]
  unfold cechTupleBoundaryBasis
  rw [Fin.sum_univ_succ, map_sum]
  simp only [Fin.val_zero, pow_zero, cechTupleDelete_prepend_zero,
    cechTuplePrependChain_single, Fin.val_succ, pow_succ,
    cechTupleDelete_prepend_succ, mul_neg, mul_one, Finsupp.single_neg]
  rw [Finset.sum_neg_distrib]
  abel

private theorem cechTuplePrepend_contraction_single_smul {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    cechTupleBoundary (n + 1)
          (cechTuplePrependChain i₀ (n + 1) (Finsupp.single i a)) +
        cechTuplePrependChain i₀ n
          (cechTupleBoundary n (Finsupp.single i a)) =
      Finsupp.single i a := by
  have h := congrArg (fun x => a • x) (cechTuplePrepend_contraction_single i₀ n i)
  simpa using h

/-- Prepending a fixed entry contracts the free tuple-chain complex in positive degrees. -/
theorem cechTuplePrepend_contraction {ι : Type u} (i₀ : ι) (n : ℕ)
    (x : CechTupleChain ι (n + 1)) :
    cechTupleBoundary (n + 1) (cechTuplePrependChain i₀ (n + 1) x) +
        cechTuplePrependChain i₀ n (cechTupleBoundary n x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      calc
        _ =
            (cechTupleBoundary (n + 1) (cechTuplePrependChain i₀ (n + 1) x) +
              cechTuplePrependChain i₀ n (cechTupleBoundary n x)) +
            (cechTupleBoundary (n + 1) (cechTuplePrependChain i₀ (n + 1) y) +
              cechTuplePrependChain i₀ n (cechTupleBoundary n y)) := by
                abel
        _ = x + y := by rw [hx, hy]
  | single i a => exact cechTuplePrepend_contraction_single_smul i₀ n i a

private theorem cechTupleBoundary_boundary_single {ι : Type u} (n : ℕ)
    (i : Fin (n + 3) → ι) :
    cechTupleBoundary n
        (cechTupleBoundary (n + 1) (Finsupp.single i 1)) = 0 := by
  simp only [cechTupleBoundary_single, one_smul]
  unfold cechTupleBoundaryBasis
  rw [map_sum]
  simp only [cechTupleBoundary_single]
  unfold cechTupleBoundaryBasis
  simp only [Finset.smul_sum]
  rw [← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {kl : P | (kl.1 : ℕ) ≤ (kl.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ kl : P, kl ∈ T → P := fun kl hkl =>
    (kl.2.succ, Fin.castLT kl.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hkl).right (Fin.is_lt kl.2)))
  apply Finset.sum_bij φ
  · intro kl hkl
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hkl ⊢
    omega
  · rintro ⟨k, l⟩ hkl ⟨k', l'⟩ hkl' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨k', l'⟩ hkl'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hkl'
    refine ⟨(Fin.castSucc l', k'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hkl')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hkl'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨k, l⟩ hkl
    dsimp
    rw [cechTupleDelete_delete i]
    · simp [φ, pow_succ, Finsupp.smul_single, mul_comm]
    · simpa [T] using! hkl

private theorem cechTupleBoundary_boundary_single_smul {ι : Type u} (n : ℕ)
    (i : Fin (n + 3) → ι) (a : ℤ) :
    cechTupleBoundary n
        (cechTupleBoundary (n + 1) (Finsupp.single i a)) = 0 := by
  have h := congrArg (fun x => a • x) (cechTupleBoundary_boundary_single n i)
  simpa using h

/-- Consecutive free tuple-chain boundaries compose to zero. -/
theorem cechTupleBoundary_boundary {ι : Type u} (n : ℕ)
    (x : CechTupleChain ι (n + 2)) :
    cechTupleBoundary n (cechTupleBoundary (n + 1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a => exact cechTupleBoundary_boundary_single_smul n i a

/-- Sort an injective tuple with the sign of the sorting permutation, and kill tuples
with repeated entries. -/
def cechTupleAlternatingProjectionBasis {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) : CechTupleChain ι n :=
  if Function.Injective i then
    Finsupp.single (i ∘ Tuple.sort i)
      (Equiv.Perm.sign (Tuple.sort i) : ℤ)
  else
    0

/-- The signed sorting projection on free tuple chains. -/
def cechTupleAlternatingProjection {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι n :=
  cechTupleLinearExtension (cechTupleAlternatingProjectionBasis n)

@[simp]
theorem cechTupleAlternatingProjection_single {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTupleAlternatingProjection n (Finsupp.single i a) =
      a • cechTupleAlternatingProjectionBasis n i := by
  simp [cechTupleAlternatingProjection]

theorem cechTupleAlternatingProjectionBasis_of_injective
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    cechTupleAlternatingProjectionBasis n i =
      Finsupp.single (i ∘ Tuple.sort i)
        (Equiv.Perm.sign (Tuple.sort i) : ℤ) := by
  simp [cechTupleAlternatingProjectionBasis, hi]

theorem cechTupleAlternatingProjectionBasis_of_not_injective
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : ¬Function.Injective i) :
    cechTupleAlternatingProjectionBasis n i = 0 := by
  simp [cechTupleAlternatingProjectionBasis, hi]

theorem cechTupleAlternatingProjectionBasis_comp_perm
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    cechTupleAlternatingProjectionBasis n (i ∘ σ) =
      (Equiv.Perm.sign σ : ℤ) •
        cechTupleAlternatingProjectionBasis n i := by
  by_cases hi : Function.Injective i
  · have hiσ : Function.Injective (i ∘ σ) :=
      (Function.Injective.of_comp_iff' i σ.bijective).2 hi
    rw [cechTupleAlternatingProjectionBasis_of_injective (i ∘ σ) hiσ,
      cechTupleAlternatingProjectionBasis_of_injective i hi,
      Finsupp.smul_single]
    have htuple :
        (i ∘ σ) ∘ Tuple.sort (i ∘ σ) = i ∘ Tuple.sort i :=
      Tuple.comp_perm_comp_sort_eq_comp_sort
    rw [htuple]
    have hperm :
        σ * Tuple.sort (i ∘ σ) = Tuple.sort i := by
      ext k
      exact congrArg Fin.val (hi (congrFun htuple k))
    have hsign := congrArg
      (fun τ : Equiv.Perm (Fin (n + 1)) =>
        (Equiv.Perm.sign τ : ℤ)) hperm
    simp only [Equiv.Perm.sign_mul, Units.val_mul] at hsign
    have hs : (Equiv.Perm.sign σ : ℤ) *
        (Equiv.Perm.sign σ : ℤ) = 1 :=
      Int.units_coe_mul_self (Equiv.Perm.sign σ)
    congr 1
    calc
      (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) =
          1 * (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) := by rw [one_mul]
      _ = ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) *
          (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) := by rw [hs]
      _ = (Equiv.Perm.sign σ : ℤ) *
          ((Equiv.Perm.sign σ : ℤ) *
            (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ)) := by
              rw [mul_assoc]
      _ = (Equiv.Perm.sign σ : ℤ) *
          (Equiv.Perm.sign (Tuple.sort i) : ℤ) := by rw [hsign]
  · have hiσ : ¬Function.Injective (i ∘ σ) := by
      simpa only [Function.Injective.of_comp_iff' i σ.bijective] using hi
    rw [cechTupleAlternatingProjectionBasis_of_not_injective (i ∘ σ) hiσ,
      cechTupleAlternatingProjectionBasis_of_not_injective i hi, smul_zero]

theorem cechTupleAlternatingProjectionBasis_of_strictMono
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    cechTupleAlternatingProjectionBasis n i = Finsupp.single i 1 := by
  rw [cechTupleAlternatingProjectionBasis_of_injective i hi.injective]
  have hsort : Tuple.sort i = 1 :=
    Tuple.sort_eq_refl_iff_monotone.2 hi.monotone
  simp [hsort]

private theorem cechTupleAlternatingProjection_boundary_single_of_strictMono
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    cechTupleBoundary n
        (cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      cechTupleAlternatingProjection n
        (cechTupleBoundary n (Finsupp.single i 1)) := by
  rw [cechTupleAlternatingProjection_single,
    cechTupleAlternatingProjectionBasis_of_strictMono i hi, one_smul]
  simp only [cechTupleBoundary_single, one_smul]
  unfold cechTupleBoundaryBasis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cechTupleAlternatingProjection_single,
    cechTupleAlternatingProjectionBasis_of_strictMono]
  · simp
  · exact hi.comp (Fin.strictMono_succAbove k)

private theorem cechTupleDelete_comp_cechPermDelete
    {ι : Type u} {n : ℕ} (i : Fin (n + 2) → ι)
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechTupleDelete i (σ r) ∘
        AlgebraicGeometry.Scheme.Modules.cechPermDelete σ r =
      cechTupleDelete (i ∘ σ) r := by
  funext x
  exact congrArg i
    (AlgebraicGeometry.Scheme.Modules.succAbove_cechPermDelete σ r x)

private theorem cechTupleAlternatingProjectionBasis_delete_perm
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (σ : Equiv.Perm (Fin (n + 2)))
    (hiσ : StrictMono (i ∘ σ)) (r : Fin (n + 2)) :
    cechTupleAlternatingProjectionBasis n (cechTupleDelete i (σ r)) =
      (Equiv.Perm.sign
          (AlgebraicGeometry.Scheme.Modules.cechPermDelete σ r) : ℤ) •
        Finsupp.single (cechTupleDelete (i ∘ σ) r) 1 := by
  let ρ := AlgebraicGeometry.Scheme.Modules.cechPermDelete σ r
  have htuple :
      cechTupleDelete i (σ r) ∘ ρ =
        cechTupleDelete (i ∘ σ) r :=
    cechTupleDelete_comp_cechPermDelete i σ r
  have hperm :=
    cechTupleAlternatingProjectionBasis_comp_perm
      (cechTupleDelete i (σ r)) ρ
  rw [htuple, cechTupleAlternatingProjectionBasis_of_strictMono
    (cechTupleDelete (i ∘ σ) r)
    (hiσ.comp (Fin.strictMono_succAbove r))] at hperm
  have hs :
      (Equiv.Perm.sign ρ : ℤ) * (Equiv.Perm.sign ρ : ℤ) = 1 :=
    Int.units_coe_mul_self (Equiv.Perm.sign ρ)
  calc
    cechTupleAlternatingProjectionBasis n (cechTupleDelete i (σ r)) =
        1 • cechTupleAlternatingProjectionBasis n
          (cechTupleDelete i (σ r)) := by rw [one_smul]
    _ = ((Equiv.Perm.sign ρ : ℤ) * (Equiv.Perm.sign ρ : ℤ)) •
        cechTupleAlternatingProjectionBasis n
          (cechTupleDelete i (σ r)) :=
      congrArg (fun a : ℤ => a •
        cechTupleAlternatingProjectionBasis n
          (cechTupleDelete i (σ r))) hs.symm
    _ = (Equiv.Perm.sign ρ : ℤ) •
        ((Equiv.Perm.sign ρ : ℤ) •
          cechTupleAlternatingProjectionBasis n
            (cechTupleDelete i (σ r))) := by rw [smul_smul]
    _ = (Equiv.Perm.sign ρ : ℤ) •
        Finsupp.single (cechTupleDelete (i ∘ σ) r) 1 :=
      congrArg ((Equiv.Perm.sign ρ : ℤ) • ·) hperm.symm

private theorem cechTupleAlternatingProjection_boundary_single_of_injective
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : Function.Injective i) :
    cechTupleBoundary n
        (cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      cechTupleAlternatingProjection n
        (cechTupleBoundary n (Finsupp.single i 1)) := by
  let σ := Tuple.sort i
  let j := i ∘ σ
  have hj : StrictMono j :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp σ.injective)
  rw [cechTupleAlternatingProjection_single,
    cechTupleAlternatingProjectionBasis_of_injective i hi, one_smul,
    cechTupleBoundary_single]
  rw [cechTupleBoundary_single, one_smul]
  change (Equiv.Perm.sign σ : ℤ) • cechTupleBoundaryBasis n j =
    cechTupleAlternatingProjection n (cechTupleBoundaryBasis n i)
  unfold cechTupleBoundaryBasis
  rw [map_sum, Finset.smul_sum]
  simp only [cechTupleAlternatingProjection_single]
  refine Fintype.sum_equiv σ _ _ fun r => ?_
  rw [cechTupleAlternatingProjectionBasis_delete_perm i σ hj r]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1
  rw [AlgebraicGeometry.Scheme.Modules.cechPermDelete_sign]
  have hsquare :
      (-1 : ℤ) ^ (σ r : ℕ) * (-1 : ℤ) ^ (σ r : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (σ r : ℕ)).neg_one_pow]
  calc
    (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (r : ℕ) =
        (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) := mul_comm _ _
    _ = (-1 : ℤ) ^ (σ r : ℕ) *
        (((-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ)) *
          (-1 : ℤ) ^ (σ r : ℕ)) := by
      symm
      calc
        (-1 : ℤ) ^ (σ r : ℕ) *
            (((-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ)) *
              (-1 : ℤ) ^ (σ r : ℕ)) =
            (((-1 : ℤ) ^ (σ r : ℕ)) *
              (-1 : ℤ) ^ (σ r : ℕ)) *
              (((-1 : ℤ) ^ (r : ℕ)) *
                (Equiv.Perm.sign σ : ℤ)) := by ring
        _ = (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) := by
          rw [hsquare, one_mul]

private theorem cechTupleAlternatingProjectionBasis_delete_pair
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hkl : i k = i l) :
    cechTupleAlternatingProjectionBasis n (cechTupleDelete i k) =
      (Equiv.Perm.sign
          (AlgebraicGeometry.Scheme.Modules.cechDeleteSwapPerm k l) : ℤ) •
        cechTupleAlternatingProjectionBasis n (cechTupleDelete i l) := by
  let ρ := AlgebraicGeometry.Scheme.Modules.cechDeleteSwapPerm k l
  have htuple :
      cechTupleDelete i l ∘ ρ = cechTupleDelete i k :=
    AlgebraicGeometry.Scheme.Modules.comp_succAbove_cechDeleteSwapPerm_of_eq
      i k l hkl
  have hperm :=
    cechTupleAlternatingProjectionBasis_comp_perm
      (cechTupleDelete i l) ρ
  rwa [htuple] at hperm

private theorem cechTupleAlternatingProjectionBasis_delete_pair_cancel
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) (hkl : k ≠ l) :
    (-1 : ℤ) ^ (k : ℕ) •
        cechTupleAlternatingProjectionBasis n (cechTupleDelete i k) +
      (-1 : ℤ) ^ (l : ℕ) •
        cechTupleAlternatingProjectionBasis n (cechTupleDelete i l) = 0 := by
  let t := cechTupleAlternatingProjectionBasis n (cechTupleDelete i l)
  have hpair :=
    cechTupleAlternatingProjectionBasis_delete_pair i k l hki
  change (-1 : ℤ) ^ (k : ℕ) • _ + (-1 : ℤ) ^ (l : ℕ) • t = 0
  rw [hpair, smul_smul,
    AlgebraicGeometry.Scheme.Modules.cechDeleteSwapPerm_sign k l hkl]
  have hcoef :
      (-1 : ℤ) ^ (k : ℕ) *
          -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) =
        -((-1 : ℤ) ^ (l : ℕ)) := by
    rw [mul_neg, ← mul_assoc, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_mul]
  rw [hcoef, neg_smul, neg_add_cancel]

private theorem cechTupleAlternatingProjection_boundary_single_of_not_injective
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : ¬Function.Injective i) :
    cechTupleBoundary n
        (cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      cechTupleAlternatingProjection n
        (cechTupleBoundary n (Finsupp.single i 1)) := by
  rw [cechTupleAlternatingProjection_single,
    cechTupleAlternatingProjectionBasis_of_not_injective i hi, one_smul,
    map_zero, cechTupleBoundary_single, one_smul]
  unfold cechTupleBoundaryBasis
  rw [map_sum]
  simp only [cechTupleAlternatingProjection_single]
  symm
  let F : Fin (n + 2) → CechTupleChain ι n := fun k =>
    (-1 : ℤ) ^ (k : ℕ) •
      cechTupleAlternatingProjectionBasis n (cechTupleDelete i k)
  change ∑ k, F k = 0
  by_cases hall : ∀ k : Fin (n + 2),
      ¬Function.Injective (cechTupleDelete i k)
  · apply Finset.sum_eq_zero
    intro k _
    dsimp only [F]
    rw [cechTupleAlternatingProjectionBasis_of_not_injective _ (hall k),
      smul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (cechTupleDelete i k) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hil⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_partner_of_delete_injective
        i hi k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        F m = 0 := by
      have hm :=
        AlgebraicGeometry.Scheme.Modules.delete_not_injective_of_ne
          i k l m hkl hmk.symm hml.symm hil
      have hm' : ¬Function.Injective (cechTupleDelete i m) := by
        simpa [cechTupleDelete] using hm
      dsimp only [F]
      rw [cechTupleAlternatingProjectionBasis_of_not_injective _ hm',
        smul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum F = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, F m = (Finset.univ.erase l).sum F + F l :=
        (Finset.sum_erase_add Finset.univ F (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum F + F k) + F l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) F hk_mem]
      _ = F k + F l := by rw [hrem, zero_add]
      _ = 0 := by
        dsimp only [F]
        exact cechTupleAlternatingProjectionBasis_delete_pair_cancel
          i k l hil.symm hkl

private theorem cechTupleAlternatingProjection_boundary_single
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) :
    cechTupleBoundary n
        (cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      cechTupleAlternatingProjection n
        (cechTupleBoundary n (Finsupp.single i 1)) := by
  by_cases hi : Function.Injective i
  · exact cechTupleAlternatingProjection_boundary_single_of_injective n i hi
  · exact cechTupleAlternatingProjection_boundary_single_of_not_injective n i hi

private theorem cechTupleAlternatingProjection_boundary_single_smul
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    cechTupleBoundary n
        (cechTupleAlternatingProjection (n + 1) (Finsupp.single i a)) =
      cechTupleAlternatingProjection n
        (cechTupleBoundary n (Finsupp.single i a)) := by
  have h := congrArg (fun x => a • x)
    (cechTupleAlternatingProjection_boundary_single n i)
  simpa using h

/-- Signed sorting is a chain map on free tuple chains. -/
theorem cechTupleAlternatingProjection_boundary
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : CechTupleChain ι (n + 1)) :
    cechTupleBoundary n (cechTupleAlternatingProjection (n + 1) x) =
      cechTupleAlternatingProjection n (cechTupleBoundary n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a =>
      exact cechTupleAlternatingProjection_boundary_single_smul n i a

/-- Conrad's recursive chain homotopy from the identity to signed sorting. -/
def cechTupleAlternatingHomotopy {ι : Type u} [LinearOrder ι] :
    (n : ℕ) → CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι (n + 1)
  | 0 => 0
  | n + 1 =>
      cechTupleLinearExtension fun i =>
        cechTuplePrependChain (i 0) (n + 1)
          (cechTupleAlternatingProjectionBasis (n + 1) i -
            Finsupp.single i 1 -
            cechTupleAlternatingHomotopy n
              (cechTupleBoundaryBasis n i))

@[simp]
theorem cechTupleAlternatingHomotopy_zero
    {ι : Type u} [LinearOrder ι] :
    cechTupleAlternatingHomotopy (ι := ι) 0 = 0 :=
  rfl

@[simp]
theorem cechTupleAlternatingHomotopy_succ_single
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    cechTupleAlternatingHomotopy (n + 1) (Finsupp.single i a) =
      a • cechTuplePrependChain (i 0) (n + 1)
        (cechTupleAlternatingProjectionBasis (n + 1) i -
          Finsupp.single i 1 -
          cechTupleAlternatingHomotopy n
            (cechTupleBoundaryBasis n i)) := by
  simp [cechTupleAlternatingHomotopy, cechTupleLinearExtension]

/-- The lower-degree term `h∂` in the tuple-chain homotopy identity. -/
def cechTupleAlternatingHomotopyPrevious
    {ι : Type u} [LinearOrder ι] :
    (n : ℕ) → CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι n
  | 0 => 0
  | n + 1 =>
      (cechTupleAlternatingHomotopy n).comp (cechTupleBoundary n)

@[simp]
theorem cechTupleAlternatingHomotopyPrevious_zero
    {ι : Type u} [LinearOrder ι] :
    cechTupleAlternatingHomotopyPrevious (ι := ι) 0 = 0 :=
  rfl

@[simp]
theorem cechTupleAlternatingHomotopyPrevious_succ_apply
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : CechTupleChain ι (n + 1)) :
    cechTupleAlternatingHomotopyPrevious (n + 1) x =
      cechTupleAlternatingHomotopy n (cechTupleBoundary n x) :=
  rfl

theorem cechTupleAlternatingProjection_zero
    {ι : Type u} [LinearOrder ι] (x : CechTupleChain ι 0) :
    cechTupleAlternatingProjection 0 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a =>
      have hi : StrictMono i := by
        intro k l hkl
        omega
      rw [cechTupleAlternatingProjection_single,
        cechTupleAlternatingProjectionBasis_of_strictMono i hi]
      simp

private theorem cechTupleAlternatingHomotopyPrevious_boundaryBasis
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) :
    cechTupleAlternatingHomotopyPrevious n
        (cechTupleBoundaryBasis n i) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      change cechTupleAlternatingHomotopy n
        (cechTupleBoundary n (cechTupleBoundaryBasis (n + 1) i)) = 0
      have hsq := cechTupleBoundary_boundary (ι := ι) n
        (Finsupp.single i 1)
      simp only [cechTupleBoundary_single, one_smul] at hsq
      rw [hsq, map_zero]

/-- Conrad's recursive homotopy satisfies `∂h + h∂ = p - 1`. -/
theorem cechTupleAlternatingHomotopy_identity
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : CechTupleChain ι n) :
    cechTupleBoundary n (cechTupleAlternatingHomotopy n x) +
        cechTupleAlternatingHomotopyPrevious n x =
      cechTupleAlternatingProjection n x - x := by
  induction n with
  | zero =>
      simp [cechTupleAlternatingProjection_zero]
  | succ n ih =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy =>
          simp only [map_add]
          calc
            (cechTupleBoundary (n + 1))
                  (cechTupleAlternatingHomotopy (n + 1) x) +
                (cechTupleBoundary (n + 1))
                  (cechTupleAlternatingHomotopy (n + 1) y) +
              (cechTupleAlternatingHomotopyPrevious (n + 1) x +
                cechTupleAlternatingHomotopyPrevious (n + 1) y) =
                ((cechTupleBoundary (n + 1))
                    (cechTupleAlternatingHomotopy (n + 1) x) +
                  cechTupleAlternatingHomotopyPrevious (n + 1) x) +
                ((cechTupleBoundary (n + 1))
                    (cechTupleAlternatingHomotopy (n + 1) y) +
                  cechTupleAlternatingHomotopyPrevious (n + 1) y) := by
                    abel
            _ = (cechTupleAlternatingProjection (n + 1) x - x) +
                (cechTupleAlternatingProjection (n + 1) y - y) := by
                  rw [hx, hy]
            _ = cechTupleAlternatingProjection (n + 1) x +
                  cechTupleAlternatingProjection (n + 1) y -
                (x + y) := by
                  abel
      | single i a =>
          let ω :=
            cechTupleAlternatingProjectionBasis (n + 1) i -
              Finsupp.single i 1 -
              cechTupleAlternatingHomotopy n
                (cechTupleBoundaryBasis n i)
          have hp := cechTupleAlternatingProjection_boundary
            (ι := ι) n (Finsupp.single i 1)
          simp only [cechTupleAlternatingProjection_single,
            cechTupleBoundary_single, one_smul] at hp
          have hih := ih (cechTupleBoundaryBasis n i)
          rw [cechTupleAlternatingHomotopyPrevious_boundaryBasis,
            add_zero] at hih
          have hcycle : cechTupleBoundary n ω = 0 := by
            dsimp only [ω]
            rw [map_sub, map_sub, hp, hih]
            simp only [cechTupleBoundary_single, one_smul]
            abel
          have hcon := cechTuplePrepend_contraction (i 0) n ω
          rw [hcycle, map_zero, add_zero] at hcon
          have hunit :
              cechTupleBoundary (n + 1)
                    (cechTupleAlternatingHomotopy (n + 1)
                      (Finsupp.single i 1)) +
                  cechTupleAlternatingHomotopyPrevious (n + 1)
                    (Finsupp.single i 1) =
                cechTupleAlternatingProjection (n + 1)
                    (Finsupp.single i 1) -
                  Finsupp.single i 1 := by
            rw [cechTupleAlternatingHomotopy_succ_single, one_smul,
              cechTupleAlternatingHomotopyPrevious_succ_apply,
              cechTupleBoundary_single, one_smul,
              cechTupleAlternatingProjection_single, one_smul]
            change cechTupleBoundary (n + 1)
                (cechTuplePrependChain (i 0) (n + 1) ω) +
                cechTupleAlternatingHomotopy n
                  (cechTupleBoundaryBasis n i) =
              cechTupleAlternatingProjectionBasis (n + 1) i -
                Finsupp.single i 1
            rw [hcon]
            dsimp only [ω]
            abel
          have h := congrArg (fun y => a • y) hunit
          simpa [smul_sub, Finsupp.smul_single] using h

namespace CechTupleChain

/-- Every tuple occurring in a chain uses indices from `N`. -/
def SupportedBy {ι : Type u} {n : ℕ}
    (x : CechTupleChain ι n) (N : Set ι) : Prop :=
  ∀ ⦃i⦄, i ∈ x.support → Set.range i ⊆ N

theorem supportedBy_zero {ι : Type u} {n : ℕ} {N : Set ι} :
    SupportedBy (0 : CechTupleChain ι n) N := by
  intro i hi
  simp at hi

theorem SupportedBy.add {ι : Type u} {n : ℕ} {N : Set ι}
    {x y : CechTupleChain ι n} (hx : SupportedBy x N)
    (hy : SupportedBy y N) :
    SupportedBy (x + y) N := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
  · exact hx hi
  · exact hy hi

theorem SupportedBy.sub {ι : Type u} {n : ℕ} {N : Set ι}
    {x y : CechTupleChain ι n} (hx : SupportedBy x N)
    (hy : SupportedBy y N) :
    SupportedBy (x - y) N := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_sub hi) with hi | hi
  · exact hx hi
  · exact hy hi

theorem SupportedBy.smul {ι : Type u} {n : ℕ} {N : Set ι}
    {x : CechTupleChain ι n} (hx : SupportedBy x N) (a : ℤ) :
    SupportedBy (a • x) N := by
  intro i hi
  exact hx (Finsupp.support_smul hi)

theorem SupportedBy.mono {ι : Type u} {n : ℕ} {N N' : Set ι}
    {x : CechTupleChain ι n} (hx : SupportedBy x N)
    (hNN' : N ⊆ N') :
    SupportedBy x N' := by
  intro i hi
  exact (hx hi).trans hNN'

theorem supportedBy_single {ι : Type u} {n : ℕ} {N : Set ι}
    (i : Fin (n + 1) → ι) (a : ℤ) (hi : Set.range i ⊆ N) :
    SupportedBy (Finsupp.single i a) N := by
  intro j hj
  have hji := Finsupp.support_single_subset hj
  simp only [Finset.mem_singleton] at hji
  subst j
  exact hi

theorem supportedBy_sum {ι : Type u} {n : ℕ} {N : Set ι}
    {κ : Type*} (s : Finset κ) (f : κ → CechTupleChain ι n)
    (hf : ∀ k ∈ s, SupportedBy (f k) N) :
    SupportedBy (∑ k ∈ s, f k) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supportedBy_zero]
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (hf k (Finset.mem_insert_self k s)).add
        (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

theorem supportedBy_linearExtension
    {ι : Type u} {n m : ℕ} {N : Set ι}
    (f : (Fin (n + 1) → ι) → CechTupleChain ι m)
    (x : CechTupleChain ι n)
    (hf : ∀ i ∈ x.support, SupportedBy (f i) N) :
    SupportedBy (cechTupleLinearExtension f x) N := by
  classical
  intro j hj
  rw [cechTupleLinearExtension, Finsupp.lsum_apply] at hj
  change j ∈ (x.sum fun i a => a • f i).support at hj
  obtain ⟨i, hi, hj⟩ :=
    Finset.mem_biUnion.mp (Finsupp.support_sum hj)
  exact hf i hi (Finsupp.support_smul hj)

end CechTupleChain

theorem cechTupleBoundaryBasis_supportedBy
    {ι : Type u} (n : ℕ) (i : Fin (n + 2) → ι) :
    CechTupleChain.SupportedBy (cechTupleBoundaryBasis n i)
      (Set.range i) := by
  unfold cechTupleBoundaryBasis
  refine CechTupleChain.supportedBy_sum Finset.univ _ ?_
  intro k _
  apply CechTupleChain.supportedBy_single
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

theorem cechTupleAlternatingProjectionBasis_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) :
    CechTupleChain.SupportedBy
      (cechTupleAlternatingProjectionBasis n i) (Set.range i) := by
  by_cases hi : Function.Injective i
  · rw [cechTupleAlternatingProjectionBasis_of_injective i hi]
    apply CechTupleChain.supportedBy_single
    rintro x ⟨k, rfl⟩
    exact ⟨Tuple.sort i k, rfl⟩
  · rw [cechTupleAlternatingProjectionBasis_of_not_injective i hi]
    exact CechTupleChain.supportedBy_zero

theorem cechTuplePrependChain_supportedBy
    {ι : Type u} (i₀ : ι) (n : ℕ)
    (x : CechTupleChain ι n) (N : Set ι)
    (hi₀ : i₀ ∈ N) (hx : CechTupleChain.SupportedBy x N) :
    CechTupleChain.SupportedBy (cechTuplePrependChain i₀ n x) N := by
  rw [cechTuplePrependChain]
  apply CechTupleChain.supportedBy_linearExtension
  intro i hi
  apply CechTupleChain.supportedBy_single
  rintro y ⟨k, rfl⟩
  induction k using Fin.cases with
  | zero => exact hi₀
  | succ l => exact hx hi ⟨l, rfl⟩

theorem cechTupleBoundary_supportedBy
    {ι : Type u} (n : ℕ) (x : CechTupleChain ι (n + 1))
    (N : Set ι) (hx : CechTupleChain.SupportedBy x N) :
    CechTupleChain.SupportedBy (cechTupleBoundary n x) N := by
  rw [cechTupleBoundary]
  apply CechTupleChain.supportedBy_linearExtension
  intro i hi
  exact (cechTupleBoundaryBasis_supportedBy n i).mono (hx hi)

theorem cechTupleAlternatingProjection_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : CechTupleChain ι n) (N : Set ι)
    (hx : CechTupleChain.SupportedBy x N) :
    CechTupleChain.SupportedBy
      (cechTupleAlternatingProjection n x) N := by
  rw [cechTupleAlternatingProjection]
  apply CechTupleChain.supportedBy_linearExtension
  intro i hi
  exact (cechTupleAlternatingProjectionBasis_supportedBy n i).mono (hx hi)

theorem cechTupleAlternatingHomotopy_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : CechTupleChain ι n) (N : Set ι)
    (hx : CechTupleChain.SupportedBy x N) :
    CechTupleChain.SupportedBy
      (cechTupleAlternatingHomotopy n x) N := by
  induction n generalizing N with
  | zero =>
      change CechTupleChain.SupportedBy 0 N
      exact CechTupleChain.supportedBy_zero
  | succ n ih =>
      rw [cechTupleAlternatingHomotopy]
      apply CechTupleChain.supportedBy_linearExtension
      intro i hi
      have hiN : Set.range i ⊆ N := hx hi
      have hp :=
        (cechTupleAlternatingProjectionBasis_supportedBy (n + 1) i).mono hiN
      have hsingle :=
        (CechTupleChain.supportedBy_single i 1 (Subset.rfl)).mono hiN
      have hboundary :=
        (cechTupleBoundaryBasis_supportedBy n i).mono hiN
      have hh := ih _ _ hboundary
      apply cechTuplePrependChain_supportedBy
      · exact hiN ⟨0, rfl⟩
      · exact (hp.sub hsingle).sub hh

/-- A free tuple-chain map does not introduce new tuple indices. -/
def CechTupleSupportNonincreasing
    {ι : Type u} {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m) : Prop :=
  ∀ i : Fin (n + 1) → ι,
    CechTupleChain.SupportedBy (f (Finsupp.single i 1)) (Set.range i)

theorem cechTupleAlternatingHomotopy_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleSupportNonincreasing
      (cechTupleAlternatingHomotopy (ι := ι) n) := by
  intro i
  apply cechTupleAlternatingHomotopy_supportedBy
  exact CechTupleChain.supportedBy_single i 1 Subset.rfl

end

end ModularCurves
