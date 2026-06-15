module

public import BernoulliRegular.Reflection.WeakSplitting.Factorization
public import BernoulliRegular.Reflection.WeakSplitting.PartialZeta

/-!
# Pole-order assembly: forcing [L:K] = 1

From the global Kummer comparison identity (REF-21c2c)
$$
\zeta_L(s) \cdot \prod_{Q \in F_L}(1 - N(Q)^{-s})
  = \Bigl(\zeta_K(s) \cdot \prod_{P \in S}(1 - N(P)^{-s})\Bigr)^{[L:K]}
$$
together with the simple-pole behaviour at `s = 1` of each side
(REF-21a), comparing pole orders forces `[L:K] = 1`.

The argument: the LHS has a simple pole at `s = 1` (from `ζ_L`), but the
RHS, being the `[L:K]`-th power of a function with a simple pole, has a
pole of order `[L:K]`. For these to be equal, `[L:K] = 1`.

This file is REF-21d. It uses the global identity from REF-21c2c, plus
REF-21a's pole-preservation results.

## Main results

* `BernoulliRegular.WeakSplitting.tendsto_sub_one_mul_unfolded_partial`:
  the unfolded partial zeta `ζ_L · ∏(1-N(Q)^{-s})` has a simple pole at
  `s = 1`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (L : Type*) [Field L] [NumberField L]

/--
The unfolded partial Dedekind zeta `ζ_L(s) · ∏ Q ∈ F (1 - N(Q)^{-s})` has
a simple pole at `s = 1`, with residue `dedekindZeta_residue L · ∏ Q ∈ F
(1 - N(Q)⁻¹)`. This mirrors `tendsto_sub_one_mul_dedekindZetaPartial_nhdsGT`
from `PartialZeta.lean`, but for a `Finset (Ideal (𝓞 L))` instead of a
`Finset (HeightOneSpectrum (𝓞 L))`.
-/
theorem tendsto_sub_one_mul_unfolded_partial (F : Finset (Ideal (𝓞 L)))
    (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥) :
    Tendsto (fun s : ℝ => (s - 1) *
        (dedekindZeta L s * ∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ)))))
      (𝓝[>] 1)
      (𝓝 ((dedekindZeta_residue L : ℂ) *
        ∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ)⁻¹))) := by
  have h₂ : Tendsto (fun s : ℝ =>
      ∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ))))
      (𝓝[>] 1)
      (𝓝 (∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ)⁻¹))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine tendsto_finsetProd F fun Q hQ => ?_
    have hQ_ne : Q ≠ ⊥ := (hF Q hQ).2
    have hN_ne : (Ideal.absNorm Q : ℂ) ≠ 0 := by
      haveI : NeZero Q := ⟨hQ_ne⟩
      exact_mod_cast (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
        (mem_nonZeroDivisors_of_ne_zero hQ_ne)
    have h_sub : Continuous (fun s : ℝ =>
        (1 : ℂ) - ((Ideal.absNorm Q : ℂ)) ^ (-((s : ℂ)))) :=
      continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (.inl hN_ne))
    convert h_sub.tendsto 1 using 2
    push_cast
    rw [Complex.cpow_neg, Complex.cpow_one]
  convert (tendsto_sub_one_mul_dedekindZeta_nhdsGT L).mul h₂ using 1
  ext s; ring

variable (K : Type*) [Field K] [NumberField K] [Algebra K L]

/--
**REF-21d: The pole-order argument forcing `[L:K] = 1`.**

If we have the global Kummer comparison identity
$$
\zeta_L(s) \cdot \prod_{Q \in F_L}(1 - N(Q)^{-s})
  = \Bigl(\zeta_K(s) \cdot \prod_{P \in S}(1 - N(P)^{-s})\Bigr)^{[L:K]}
$$
on the half-plane `Re(s) > 1`, then `[L:K] = 1`.

The argument: multiply both sides by `(s - 1) ^ [L:K]` and take the limit
as `s → 1⁺` along the reals. The LHS becomes `(s - 1)^([L:K] - 1)` times
`((s - 1) · LHS)`, which by the simple pole at `s = 1` of `ζ_L · ∏ ...`
tends to `0` for `[L:K] > 1` (since `(s - 1)^(positive integer) → 0`).
The RHS becomes `((s - 1) · ζ_K · ∏)^[L:K]`, which tends to a positive
power of a positive limit, hence positive. Equal limits would force `0 =
(positive)`, a contradiction. So `[L:K] ≤ 1`, and since `[L:K] ≥ 1`,
`[L:K] = 1`.
-/
theorem finrank_eq_one_of_global_identity
    (F_L : Finset (Ideal (𝓞 L))) (S : Finset (Ideal (𝓞 K)))
    (hF_L : ∀ Q ∈ F_L, Q.IsPrime ∧ Q ≠ ⊥)
    (hS : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥)
    (h_global : ∀ s : ℝ, 1 < s →
      dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ))) =
        (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
          ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ Module.finrank K L)
    [Module.Finite K L] [Module.Free K L] (h_finrank_pos : 0 < Module.finrank K L) :
    Module.finrank K L = 1 := by
  by_contra h_ne
  set n := Module.finrank K L
  have hn_ne : n ≠ 0 := by omega
  have hn_sub_pos : 0 < n - 1 := by omega
  have hL_to_zero :
      Tendsto (fun s : ℝ => ((s : ℂ) - 1) ^ n *
          (dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L,
            ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ)))))
        (𝓝[>] 1) (𝓝 0) := by
    have h_factor : (fun s : ℝ => ((s : ℂ) - 1) ^ n *
          (dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L,
            ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ))))) =
        (fun s : ℝ => ((s : ℂ) - 1) ^ (n - 1) *
          (((s : ℂ) - 1) * (dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L,
            ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ)))))) := by
      ext s
      rw [show ((s : ℂ) - 1) ^ n = ((s : ℂ) - 1) ^ ((n - 1) + 1) by
        congr 1; omega, pow_succ]
      ring
    rw [h_factor]
    have h_first : Tendsto (fun s : ℝ => ((s : ℂ) - 1) ^ (n - 1)) (𝓝[>] 1) (𝓝 0) := by
      have h_real : Tendsto (fun s : ℝ => ((s : ℂ) - 1)) (𝓝[>] 1) (𝓝 0) := by
        simpa using ((Complex.continuous_ofReal.tendsto 1).mono_left
          nhdsWithin_le_nhds).sub_const (1 : ℂ)
      simpa [zero_pow hn_sub_pos.ne'] using h_real.pow (n - 1)
    simpa using h_first.mul (tendsto_sub_one_mul_unfolded_partial L F_L hF_L)
  have hK_to_pow :
      Tendsto (fun s : ℝ => ((s : ℂ) - 1) ^ n *
          (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
            ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ n)
        (𝓝[>] 1)
        (𝓝 (((dedekindZeta_residue K : ℂ) *
          ∏ P ∈ S, ((1 : ℂ) - (Ideal.absNorm P : ℂ)⁻¹)) ^ n)) := by
    have h_eq : (fun s : ℝ => ((s : ℂ) - 1) ^ n *
          (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
            ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ n) =
        (fun s : ℝ => (((s : ℂ) - 1) *
          (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
            ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ))))) ^ n) := by
      ext s; rw [← mul_pow]
    rw [h_eq]
    exact (tendsto_sub_one_mul_unfolded_partial K S hS).pow n
  have h_funeq : (fun s : ℝ => ((s : ℂ) - 1) ^ n *
        (dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L,
          ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ))))) =ᶠ[𝓝[>] 1]
      (fun s : ℝ => ((s : ℂ) - 1) ^ n *
        (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
          ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ n) := by
    refine eventually_nhdsWithin_of_forall ?_
    intro s hs
    change ((s : ℂ) - 1) ^ n *
        (dedekindZeta L (s : ℂ) * ∏ Q ∈ F_L,
          ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-(s : ℂ)))) =
      ((s : ℂ) - 1) ^ n *
        (dedekindZeta K (s : ℂ) * ∏ P ∈ S,
          ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-(s : ℂ)))) ^ n
    rw [h_global s hs]
  have hL_to_pow := hK_to_pow.congr' h_funeq.symm
  have h_limits_eq : (0 : ℂ) =
      ((dedekindZeta_residue K : ℂ) *
        ∏ P ∈ S, ((1 : ℂ) - (Ideal.absNorm P : ℂ)⁻¹)) ^ n :=
    tendsto_nhds_unique hL_to_zero hL_to_pow
  have hcK_ne : ((dedekindZeta_residue K : ℂ) *
      ∏ P ∈ S, ((1 : ℂ) - (Ideal.absNorm P : ℂ)⁻¹)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (dedekindZeta_residue_pos K).ne'
    · refine Finset.prod_ne_zero_iff.mpr fun P hP => ?_
      intro h_zero
      have hN_eq_one : (Ideal.absNorm P : ℂ)⁻¹ = 1 := by linear_combination -h_zero
      have hN_eq_one' : (Ideal.absNorm P : ℂ) = 1 := by
        rw [← inv_inv ((Ideal.absNorm P : ℂ)), hN_eq_one, inv_one]
      exact (hS P hP).1.ne_top (Ideal.absNorm_eq_one_iff.mp (by exact_mod_cast hN_eq_one'))
  exact hcK_ne (pow_eq_zero_iff hn_ne |>.mp h_limits_eq.symm)

end WeakSplitting

end BernoulliRegular
