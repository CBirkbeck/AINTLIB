/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Maximal ideals of a polynomial ring over an algebraically closed field have full height
(T-SMOOTH-REG brick 2)

Mathlib knows `dim k[x_i : i ∈ ι] = #ι` (`MvPolynomial.ringKrullDim_of_isNoetherianRing`),
but the smoothness argument needs the **local** statement at a closed point:

> every maximal ideal `𝔮` of `MvPolynomial ι k`, `k` algebraically closed and `ι` finite,
> has `height 𝔮 = #ι`.

The lower bound is the substance. By the Nullstellensatz `𝔮 = ker (eval a)` for a point
`a : ι → k`, and we exhibit the chain of primes

    ⊥ = 𝔭_∅ ⊊ 𝔭_{S₁} ⊊ ⋯ ⊊ 𝔭_ι = 𝔮,    𝔭_S := ker (X i ↦ if i ∈ S then a i else X i),

each prime because it is the kernel of a map into the domain `MvPolynomial ι k`, and each
inclusion strict because `X j - C (a j)` lies in `𝔭_S` exactly when `j ∈ S`.

The upper bound is `Ideal.height_le_ringKrullDim_of_isPrime` plus mathlib's dimension
formula.
-/

universe u v

open MvPolynomial

namespace ModularCurves

variable {k : Type u} [Field k] {ι : Type v} [DecidableEq ι] (a : ι → k)

/-- The `k`-algebra endomorphism of `MvPolynomial ι k` that substitutes `a i` for `X i` at
the indices `i ∈ S` and leaves the other variables alone. -/
noncomputable def substHom (S : Finset ι) : MvPolynomial ι k →ₐ[k] MvPolynomial ι k :=
  aeval (fun i => if i ∈ S then C (a i) else X i)

@[simp] theorem substHom_X (S : Finset ι) (i : ι) :
    substHom a S (X i) = if i ∈ S then C (a i) else X i := by
  simp [substHom]

/-- Substituting on `S` and then on a larger `T` is the same as substituting on `T`. -/
theorem substHom_comp {S T : Finset ι} (h : S ⊆ T) :
    (substHom a T).comp (substHom a S) = substHom a T := by
  refine algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, substHom_X]
  by_cases hi : i ∈ S
  · simp only [hi, if_true, h hi, substHom, aeval_C, algebraMap_eq]
  · simp [hi]

/-- The kernel of `substHom`: the prime ideal cutting out the coordinate subspace where the
variables indexed by `S` take the values prescribed by `a`. -/
noncomputable def substKer (S : Finset ι) : Ideal (MvPolynomial ι k) :=
  RingHom.ker (substHom a S).toRingHom

instance substKer_isPrime (S : Finset ι) : (substKer a S).IsPrime :=
  RingHom.ker_isPrime _

theorem substKer_mono {S T : Finset ι} (h : S ⊆ T) : substKer a S ≤ substKer a T := by
  intro p hp
  have hp0 : substHom a S p = 0 := hp
  show substHom a T p = 0
  rw [← substHom_comp a h]
  simp only [AlgHom.comp_apply, hp0, map_zero]

theorem X_sub_C_mem_substKer {S : Finset ι} {j : ι} (hj : j ∈ S) :
    X j - C (a j) ∈ substKer a S := by
  show substHom a S (X j - C (a j)) = 0
  simp [substHom, hj]

theorem X_sub_C_notMem_substKer {S : Finset ι} {j : ι} (hj : j ∉ S) :
    X j - C (a j) ∉ substKer a S := by
  intro hmem
  have h0 : substHom a S (X j - C (a j)) = 0 := hmem
  rw [map_sub, substHom_X, if_neg hj] at h0
  simp only [substHom, aeval_C, algebraMap_eq, sub_eq_zero] at h0
  have hcoeff := congrArg (fun q : MvPolynomial ι k => coeff (Finsupp.single j 1) q) h0
  simp [coeff_X, coeff_C, eq_comm (a := (0 : ι →₀ ℕ)), Finsupp.single_eq_zero] at hcoeff

theorem substKer_lt {S T : Finset ι} (h : S ⊆ T) {j : ι} (hjT : j ∈ T) (hjS : j ∉ S) :
    substKer a S < substKer a T :=
  lt_of_le_of_ne (substKer_mono a h) fun heq =>
    X_sub_C_notMem_substKer a hjS (heq ▸ X_sub_C_mem_substKer a hjT)

theorem substKer_empty : substKer a (∅ : Finset ι) = ⊥ := by
  have hid : substHom a (∅ : Finset ι) = AlgHom.id k (MvPolynomial ι k) :=
    algHom_ext fun i => by simp
  ext p
  simp only [substKer, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hid,
    AlgHom.coe_id, id_eq, Ideal.mem_bot]

variable [Fintype ι]

/-- Substituting *all* the variables lands in the constants: the kernel is the kernel of
evaluation at `a`. -/
theorem substKer_univ : substKer a (Finset.univ : Finset ι) = RingHom.ker (eval a) := by
  have hcomp : substHom a (Finset.univ : Finset ι) =
      (Algebra.ofId k (MvPolynomial ι k)).comp (aeval a) :=
    algHom_ext fun i => by simp [Algebra.ofId_apply, algebraMap_eq]
  ext p
  simp only [substKer, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hcomp,
    AlgHom.comp_apply, Algebra.ofId_apply, algebraMap_eq]
  constructor
  · intro h
    have : (aeval a) p = 0 := by
      have := congrArg (fun q => MvPolynomial.constantCoeff q) h
      simpa using this
    simpa [aeval_eq_eval] using this
  · intro h
    have : (aeval a) p = 0 := by simpa [aeval_eq_eval] using h
    rw [this, map_zero]

/-- The increasing family of coordinate subspaces cutting `𝔮` out one variable at a time,
indexed through a bijection `ι ≃ Fin (card ι)`. -/
private noncomputable def substStage (e : ι ≃ Fin (Fintype.card ι)) (m : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => (e i).val < m)

omit [DecidableEq ι] in
private theorem substStage_mono (e : ι ≃ Fin (Fintype.card ι)) {m n : ℕ} (h : m ≤ n) :
    substStage e m ⊆ substStage e n := by
  intro i hi
  simp only [substStage, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

omit [DecidableEq ι] in
private theorem substStage_zero (e : ι ≃ Fin (Fintype.card ι)) :
    substStage e 0 = (∅ : Finset ι) := by
  ext i
  simp [substStage]

omit [DecidableEq ι] in
private theorem substStage_card (e : ι ≃ Fin (Fintype.card ι)) :
    substStage e (Fintype.card ι) = (Finset.univ : Finset ι) := by
  ext i
  simp only [substStage, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact (e i).isLt

/-- **(brick 2, the chain)** Each stage of the substitution chain has height at least its
index. -/
private theorem le_height_substKer_substStage (e : ι ≃ Fin (Fintype.card ι)) :
    ∀ m : ℕ, m ≤ Fintype.card ι → (m : ℕ∞) ≤ (substKer a (substStage e m)).height := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hstep := ih (by omega)
    have hlt : substKer a (substStage e m) < substKer a (substStage e (m + 1)) := by
      refine substKer_lt a (substStage_mono e (by omega))
        (j := e.symm ⟨m, by omega⟩) ?_ ?_
      · simp only [substStage, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply]
        omega
      · simp only [substStage, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply, not_lt]
        omega
    calc ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; ring
      _ ≤ (substKer a (substStage e m)).height + 1 := by gcongr
      _ ≤ (substKer a (substStage e (m + 1))).height :=
          Ideal.height_add_one_le_of_lt_of_isPrime hlt

/-- **(T-SMOOTH-REG brick 2a ★)** The kernel of evaluation at a point of `kⁿ` has height
at least `n`. -/
theorem card_le_height_ker_eval :
    (Fintype.card ι : ℕ∞) ≤ (RingHom.ker (eval a : MvPolynomial ι k →+* k)).height := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have h := le_height_substKer_substStage a e (Fintype.card ι) le_rfl
  rwa [substStage_card, substKer_univ] at h

/-- **(T-SMOOTH-REG brick 2 ★★)** Every maximal ideal of `MvPolynomial ι k`, for `k`
algebraically closed and `ι` finite, has height at least `#ι`. (With the mathlib bound
`height ≤ dim = #ι` this is an equality; only `≥` is used downstream.) -/
theorem card_le_height_of_isMaximal [IsAlgClosed k] {𝔮 : Ideal (MvPolynomial ι k)}
    (h𝔮 : 𝔮.IsMaximal) : (Fintype.card ι : ℕ∞) ≤ 𝔮.height := by
  classical
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (K := k) h𝔮
  have hker : 𝔮 = RingHom.ker (eval x : MvPolynomial ι k →+* k) := by
    rw [hx]
    ext p
    simp only [RingHom.mem_ker, eval]
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff x p
  rw [hker]
  exact card_le_height_ker_eval x

end ModularCurves
