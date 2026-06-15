/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic Convergence — Series and Limits in I-adically Complete Rings

This file provides reusable API for constructing elements of I-adically complete
rings via convergent series and Cauchy sequences.

## Main results

* `IsAdicComplete.exists_limit` : Every I-adic Cauchy sequence has a limit.
* `IsAdicComplete.series_convergent` : A series `Σ aₙ` with `aₙ ∈ I^n • ⊤` converges.
-/

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### Limits in I-adically complete rings -/

/-- In an I-adically complete module, every I-adic Cauchy sequence has a limit. -/
theorem IsAdicComplete.exists_limit {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] {f : ℕ → M}
    (hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec inferInstance hf

/-- In an I-adically complete module, a series `Σ aₙ` with `aₙ ∈ I^n • ⊤` converges:
the partial sums form a Cauchy sequence, hence have a limit. -/
theorem IsAdicComplete.series_convergent {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] {a : ℕ → M}
    (ha : ∀ n, a n ∈ (I ^ n • ⊤ : Submodule R M)) :
    ∃ S : M, ∀ n, (∑ i ∈ Finset.range n, a i) ≡ S
      [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  apply IsAdicComplete.exists_limit I
  intro m n hmn
  rw [SModEq.sub_mem]
  -- The difference of partial sums: Σ_{range m} a - Σ_{range n} a = -Σ_{Ico m n} a
  -- Each term aᵢ ∈ I^i • ⊤ ⊆ I^m • ⊤ for i ≥ m.
  suffices h : ∑ i ∈ Finset.Ico m n, a i ∈ (I ^ m • ⊤ : Submodule R M) by
    have heq := Finset.sum_range_add_sum_Ico a hmn
    -- range m + Ico m n = range n, so range m - range n = -(Ico m n)
    have : ∑ i ∈ Finset.range m, a i - ∑ i ∈ Finset.range n, a i =
        -(∑ i ∈ Finset.Ico m n, a i) := by
      rw [← heq]; abel
    rw [this]; exact neg_mem h
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hi).1) (ha i)

/-- In an I-adically Hausdorff module, if `x ≡ 0 (mod I^n • ⊤)` for all n, then `x = 0`. -/
theorem IsHausdorff.eq_zero_of_forall_smodEq {M : Type*} [AddCommGroup M] [Module R M]
    [h : IsHausdorff I M] {x : M}
    (hx : ∀ n, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) : x = 0 :=
  h.haus' x hx
