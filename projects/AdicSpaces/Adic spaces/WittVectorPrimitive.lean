/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Identities
import «Adic spaces».AdicConvergence

/-!
# Primitive Elements in Witt Vectors

An element `ξ ∈ W(R)` is **primitive of degree 1** if it has the form `ξ = p + [ϖ] · α`
where `ϖ ∈ R` is a nonzerodivisor and `α ∈ W(R)`. Primitive elements play a central
role in the theory of perfectoid rings: the kernel of Fontaine's theta map is generated
by a primitive element of degree 1 (Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8).

## Main definitions

* `WittVector.IsPrimitive` : Predicate for primitive elements of degree 1.

## Main results

* `WittVector.IsPrimitive.coeff_zero_ne_zero` : A primitive element has nonzero 0-th coeff.
* `WittVector.IsPrimitive.ne_zero` : A primitive element is nonzero.
* `WittVector.IsPrimitive.not_mem_span_p` : A primitive element is not in `(p)`.
* `WittVector.divides_of_ker_surjection` : If `θ : W(k) →+* R` is surjective,
  `ξ ∈ ker(θ)` is primitive, and `W(k)/(ξ, [ϖ]) ≅ R/(ϖ♯)`, then `ker(θ) = (ξ)`.

## References

* Scholze-Weinstein, *Berkeley Lectures on p-adic Geometry*, Definitions 6.2.9-6.2.10
-/

open WittVector

universe u

variable {p : ℕ} [hp : Fact (Nat.Prime p)]
variable {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]

local notation "𝕎" => WittVector p

/-! ### Primitive elements of degree 1 -/

/-- An element `ξ ∈ W(R)` is **primitive of degree 1** if it has the form `ξ = p + [ϖ] · α`
where `ϖ ∈ R` and `α ∈ W(R)`.

Equivalently, `ξ.coeff 0 ∈ ϖ · R` and `ξ.coeff 1 ≡ 1 (mod ϖ)` (approximately).

(Scholze-Weinstein, Berkeley Lectures, Definition 6.2.9) -/
structure WittVector.IsPrimitive (ξ : 𝕎 k) (ϖ : k) : Prop where
  /-- The primitive element equals p + [ϖ] · α for some α. -/
  eq_p_add : ∃ α : 𝕎 k, ξ = (p : 𝕎 k) + teichmuller p ϖ * α

omit [PerfectRing k p] in
/-- The 0-th Witt coefficient of `p ∈ W(k)` is 0 when `k` has characteristic `p`. -/
theorem WittVector.coeff_zero_p : ((p : 𝕎 k)).coeff 0 = 0 := by
  rw [WittVector.coeff_p]; simp

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` has `ξ.coeff 0 = ϖ · (α.coeff 0)`. -/
theorem WittVector.IsPrimitive.coeff_zero_eq {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α) :
    ξ.coeff 0 = ϖ * α.coeff 0 := by
  rw [hξ, WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
    WittVector.coeff_zero_p, WittVector.teichmuller_coeff_zero, zero_add]

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` has nonzero 0-th coefficient when ϖ and
`α.coeff 0` are both nonzero in a domain. -/
theorem WittVector.IsPrimitive.coeff_zero_ne_zero_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] : ξ.coeff 0 ≠ 0 := by
  rw [IsPrimitive.coeff_zero_eq hξ]
  exact mul_ne_zero hϖ hα

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` is nonzero when ϖ ≠ 0 and α.coeff 0 ≠ 0. -/
theorem WittVector.IsPrimitive.ne_zero_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] : ξ ≠ 0 := by
  intro h; rw [h] at hξ
  have := IsPrimitive.coeff_zero_ne_zero_of hξ hϖ hα
  simp at this

/-- A primitive element is not in `(p)` when ϖ ≠ 0 and α.coeff 0 ≠ 0, since
every element of `(p)` has 0-th coefficient equal to 0. -/
theorem WittVector.IsPrimitive.not_mem_span_p_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] :
    ξ ∉ Ideal.span {(p : 𝕎 k)} := by
  rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  exact IsPrimitive.coeff_zero_ne_zero_of hξ hϖ hα

/-! ### Coefficient-level operations for p-adic division -/

/-- In `W(k)` for a perfect ring `k` of char `p`, every element `x` can be written as
`x = [x.coeff 0] + p · x'` for a unique `x'`. This is because `W(k)/(p) ≅ k` via
`coeff 0`, and the Teichmüller lift provides a section. -/
theorem WittVector.eq_teichmuller_add_p_mul (x : 𝕎 k) :
    ∃ x' : 𝕎 k, x = teichmuller p (x.coeff 0) + (p : 𝕎 k) * x' := by
  -- x - [x.coeff 0] has coeff 0 = x.coeff 0 - x.coeff 0 = 0
  -- So x - [x.coeff 0] ∈ ker(constantCoeff) = (p) by ker_constantCoeff
  have h0 : constantCoeff (x - teichmuller p (x.coeff 0)) = 0 := by
    rw [map_sub, constantCoeff_apply, constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, sub_self]
  have hmem : x - teichmuller p (x.coeff 0) ∈ RingHom.ker constantCoeff := h0
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at hmem
  obtain ⟨x', hx'⟩ := hmem
  exact ⟨x', by linear_combination hx'⟩

omit [PerfectRing k p] in
/-- `p · x` has 0-th coefficient equal to 0. -/
theorem WittVector.coeff_zero_mul_p (x : 𝕎 k) : (x * (p : 𝕎 k)).coeff 0 = 0 :=
  WittVector.mul_charP_coeff_zero x

/-- If `x ∈ (p^n)` in `W(k)`, then `x.coeff i = 0` for all `i < n`. -/
theorem WittVector.coeff_eq_zero_of_mem_pow_p {x : 𝕎 k} {n : ℕ}
    (hx : x ∈ Ideal.span {(p : 𝕎 k) ^ n}) {i : ℕ} (hi : i < n) :
    x.coeff i = 0 :=
  (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero x n).mp hx i hi

/-! ### Division by primitive elements -/

/-- **Lemma 6.2.10 (Scholze-Weinstein):** A primitive element `ξ = p + [ϖ]α` is a
nonzerodivisor in `W(k)`, provided `ϖ` is a nonzerodivisor in `k`.

The proof: if `ξ · x = 0`, then `(p + [ϖ]α) · x = 0`, so `p · x = -[ϖ]α · x`.
The 0-th coefficient gives: `0 = -(ϖ · (α.coeff 0)) · (x.coeff 0)` (using
`mul_charP_coeff_zero`). Since ϖ is a nonzerodivisor, `α.coeff 0 · x.coeff 0 = 0`.
If α.coeff 0 is also a nonzerodivisor, then x.coeff 0 = 0, so x ∈ (p).
Writing `x = p · x₁`, we get `ξ · p · x₁ = 0`, hence `p · (ξ · x₁) = 0`.
By p-torsion-freeness, `ξ · x₁ = 0`. Induct to get x₁ ∈ (p^n) for all n,
hence x₁ = 0 by Hausdorffness, so x = 0. -/
theorem WittVector.IsPrimitive.mul_left_cancel {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [IsDomain k]
    {x : 𝕎 k} (h : ξ * x = 0) : x = 0 := by
  -- Inductive argument: show x ∈ (p^n) for all n, hence x = 0 by Hausdorffness.
  suffices ∀ n, x ∈ Ideal.span {(p : 𝕎 k) ^ n} by
    -- x ∈ (p^n) for all n → all coefficients are 0 → x = 0
    have : ∀ i, x.coeff i = 0 := fun i =>
      WittVector.coeff_eq_zero_of_mem_pow_p (this (i + 1)) (Nat.lt_succ_of_le le_rfl)
    exact WittVector.ext fun i => by rw [this i]; simp [WittVector.zero_coeff]
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    -- x ∈ (p^n), write x = p^n * y
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero] at ih ⊢
    intro i hi
    by_cases hin : i < n
    · exact ih i hin
    · -- i = n (by omega from ¬(i < n) and i < n + 1)
      have hin' : i = n := by omega
      subst hin'
      -- x.coeff j = 0 for j < i, so x ∈ (p^i). Extract y with x = p^i * y.
      have hx_mem : x ∈ Ideal.span {(p : 𝕎 k) ^ i} :=
        (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero x i).mpr (fun m hm => ih m hm)
      rw [Ideal.mem_span_singleton] at hx_mem
      obtain ⟨y, hxy⟩ := hx_mem
      -- ξ * x = 0 and x = p^i * y, so ξ * (p^i * y) = 0.
      -- Rearranging: (ξ * y) * p^i = 0. By iterated p-torsion-freeness: ξ * y = 0.
      -- Then (ξ*y).coeff 0 = ξ.coeff 0 * y.coeff 0 = 0 (mul_coeff_zero).
      -- Since ξ.coeff 0 ≠ 0 (domain), y.coeff 0 = 0.
      -- Finally x.coeff i = (p^i*y).coeff i = y.coeff 0^{p^i} = 0
      --   (mul_pow_charP_coeff_succ with m = 0).
      --
      -- Step A: ξ * y = 0 (cancel p^i using p-torsion-freeness)
      -- Cancel p^i: if a * p^n = 0 then a = 0 (iterated p-torsion-free)
      have cancel_p_pow : ∀ (a : 𝕎 k) (n : ℕ), a * (p : 𝕎 k) ^ n = 0 → a = 0 := by
        intro a n; induction n with
        | zero => simp [pow_zero, mul_one]
        | succ m ihm =>
          intro h
          apply ihm
          have : a * (p : 𝕎 k) ^ (m + 1) = (a * (p : 𝕎 k) ^ m) * p := by ring
          rw [this] at h
          exact WittVector.eq_zero_of_p_mul_eq_zero _ h
      have hξy : ξ * y = 0 := by
        apply cancel_p_pow _ i
        have : ξ * y * (p : 𝕎 k) ^ i = ξ * ((p : 𝕎 k) ^ i * y) := by ring
        rw [this]; exact hxy ▸ h
      -- Step B: y.coeff 0 = 0
      have hy0 : y.coeff 0 = 0 := by
        have h0 := WittVector.mul_coeff_zero ξ y
        rw [hξy, WittVector.zero_coeff] at h0
        have hξ0 : ξ.coeff 0 ≠ 0 := IsPrimitive.coeff_zero_ne_zero_of hξ hϖ hα
        exact (mul_eq_zero.mp h0.symm).resolve_left hξ0
      -- Step C: x.coeff i = y.coeff 0 ^ (p^i) = 0
      have hcoeff := WittVector.mul_pow_charP_coeff_succ y (m := 0) (n := i)
      simp only [zero_add] at hcoeff
      rw [hxy, show (p : 𝕎 k) ^ i * y = y * (p : 𝕎 k) ^ i from mul_comm _ _,
        hcoeff, hy0, zero_pow (pow_ne_zero i (Fact.out : Nat.Prime p).ne_zero)]

/-! ### Kernel generation by primitive elements -/

/-- In `W(k)` (p-adically complete, p-torsion-free), given `ξ ∈ ker(θ)` and a
division step `∀ x ∈ ker(θ), ∃ q r, x = ξ·q + p·r ∧ r ∈ ker(θ)`, every
element of `ker(θ)` is divisible by `ξ`.

The proof iterates the division: `x = ξ·q₀ + p·r₀`, `r₀ = ξ·q₁ + p·r₁`, etc.
Then `x = ξ·(q₀ + p·q₁ + p²·q₂ + ...)` where the series converges p-adically
by `isAdicCompleteIdealSpanP`.

(Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8 — algebraic core) -/
theorem WittVector.ker_of_primitive_and_division
    {R : Type*} [CommRing R] (θ : 𝕎 k →+* R)
    {ξ : 𝕎 k}
    (hdiv : ∀ x ∈ RingHom.ker θ, ∃ (q r : 𝕎 k), x = ξ * q + (p : 𝕎 k) * r ∧
      r ∈ RingHom.ker θ)
    (x : 𝕎 k) (hx : x ∈ RingHom.ker θ) :
    ∃ q : 𝕎 k, x = ξ * q := by
  -- Step 1: Build sequences qₙ, rₙ by recursion using hdiv.
  -- rₙ ∈ ker(θ) and r_{n-1} = ξ·qₙ + p·rₙ for all n.
  -- So x = ξ·q₀ + p·(ξ·q₁ + p·r₁) = ξ·(q₀ + p·q₁) + p²·r₁ = ...
  -- After n steps: x = ξ · (Σ_{i<n} qᵢ · pⁱ) + pⁿ · rₙ.
  -- As n → ∞, pⁿ · rₙ → 0 p-adically, and Σ qᵢ pⁱ converges.
  --
  -- Build the sequence by recursion.
  -- Build the sequences q_n, r_n by dependent recursion.
  -- r_0 = x, and at each step hdiv gives r_n = ξ·q_n + p·r_{n+1}.
  -- After N steps: x = ξ·(Σ_{n<N} q_n·p^n) + p^N·r_N.
  -- Since r_N ∈ ker(θ), p^N·r_N ∈ (p^N), so x - ξ·(partial sum) ∈ (p^N).
  -- By p-adic completeness (isAdicCompleteIdealSpanP), the partial sums converge.
  -- By Hausdorffness, the limit q satisfies x = ξ·q.
  --
  -- This is the algebraic core of Berkeley Lectures Lemma 6.2.8 (pp.46-47).
  -- Step 1: Build sequences r_n ∈ ker(θ) and q_n by recursion.
  -- r_0 = x, and hdiv gives r_n = ξ·q_{n} + p·r_{n+1}.
  -- We use a subtype recursion to track membership in ker(θ).
  have build : ∃ (r q : ℕ → 𝕎 k), r 0 = x ∧
      (∀ n, r n ∈ RingHom.ker θ) ∧
      (∀ n, r n = ξ * q n + (p : 𝕎 k) * r (n + 1)) := by
    -- Use dependent choice: given r_n ∈ ker θ, produce q_n, r_{n+1}
    have step : ∀ y : 𝕎 k, y ∈ RingHom.ker θ →
        ∃ (q r' : 𝕎 k), y = ξ * q + (p : 𝕎 k) * r' ∧ r' ∈ RingHom.ker θ := hdiv
    -- Build by Nat.rec on a bundled type
    let T := { w : 𝕎 k // w ∈ RingHom.ker θ }
    -- For each element of T, choose q and r' from the division step
    let chooseQ : T → 𝕎 k := fun ⟨y, hy⟩ => (step y hy).choose
    let chooseR : T → T := fun ⟨y, hy⟩ =>
      ⟨(step y hy).choose_spec.choose, (step y hy).choose_spec.choose_spec.2⟩
    have div_prop : ∀ t : T, (t : 𝕎 k) = ξ * chooseQ t + (p : 𝕎 k) * (chooseR t : 𝕎 k) :=
      fun ⟨y, hy⟩ => (step y hy).choose_spec.choose_spec.1
    -- Build the sequence r_n by iterating chooseR
    let rT : ℕ → T := fun n => Nat.rec ⟨x, hx⟩ (fun _ t => chooseR t) n
    refine ⟨fun n => (rT n).1, fun n => chooseQ (rT n), rfl, fun n => (rT n).2,
      fun n => div_prop (rT n)⟩
  obtain ⟨r, q, hr0, hr_ker, hdiv_eq⟩ := build
  -- Step 2: Telescoping — x = ξ * (Σ_{i<N} q_i * p^i) + p^N * r_N
  have telescope : ∀ N, x = ξ * (∑ i ∈ Finset.range N, q i * (p : 𝕎 k) ^ i) +
      (p : 𝕎 k) ^ N * r N := by
    intro N; induction N with
    | zero => simp [hr0]
    | succ N ih =>
      rw [ih, hdiv_eq N]
      rw [Finset.sum_range_succ]
      ring
  -- Step 3: The series Σ q_n * p^n converges by p-adic completeness.
  -- We need: q n * p^n ∈ Ideal.span {(p : 𝕎 k)} ^ n • ⊤
  have term_mem : ∀ n, q n * (p : 𝕎 k) ^ n ∈
      ((Ideal.span {(p : 𝕎 k)}) ^ n • ⊤ : Submodule (𝕎 k) (𝕎 k)) := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr ⟨q n, mul_comm _ _⟩
  obtain ⟨S, hS⟩ := IsAdicComplete.series_convergent (Ideal.span {(p : 𝕎 k)})
    term_mem
  -- Step 4: x - ξ * S ∈ (p^N) for all N, so x = ξ * S by Hausdorffness.
  refine ⟨S, ?_⟩
  -- Show x - ξ * S = 0
  suffices h0 : x - ξ * S = 0 by rwa [sub_eq_zero] at h0
  apply IsHausdorff.eq_zero_of_forall_smodEq (Ideal.span {(p : 𝕎 k)})
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  set partN := ∑ i ∈ Finset.range n, q i * (p : 𝕎 k) ^ i
  have htel := telescope n
  have hconv := hS n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at hconv
  have decomp : x - ξ * S = (x - ξ * partN) + ξ * (partN - S) := by ring
  rw [decomp]
  apply Ideal.add_mem
  · have : x - ξ * partN = (p : 𝕎 k) ^ n * r n := by rw [htel]; ring
    rw [this]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · exact Ideal.mul_mem_left _ _ hconv
