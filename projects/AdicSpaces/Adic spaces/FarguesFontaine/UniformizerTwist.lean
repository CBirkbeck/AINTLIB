/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.WittF

/-!
# Twisted pseudo-uniformizers (ID3a)

Powers and Frobenius roots of a pseudo-uniformizer of the perfectoid base
field `F`:

* `FarguesFontaine.isTopologicallyNilpotent_of_pow` : root-detection of
  topological nilpotency in any topological ring;
* `FarguesFontaine.PseudoUniformizer.pPow` : `ϖ^m` (`m > 0`);
* `FarguesFontaine.PseudoUniformizer.frobRoot` : `ϖ^{1/p^s}` via perfectness;
* value identities `perfectoidValuation_frobRoot_pow` / `perfectoidValuation_pPow`.

These supply the attainable exact left endpoints `|ϖ|^{p^{±n}}` for the
Big-window covering of the curve (board: ID3, 2026-07-27).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

/-- **Root-detection of topological nilpotency**: if some positive power of `r`
is topologically nilpotent, so is `r` (split `r^m = (r^N)^{m/N}·r^{m%N}`; the
finitely many remainder cofactors each tend to zero under multiplication). -/
theorem isTopologicallyNilpotent_of_pow {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {r : R} {N : ℕ} (hN : 0 < N)
    (h : IsTopologicallyNilpotent (r ^ N)) : IsTopologicallyNilpotent r := by
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  have hj : ∀ j : ℕ, Filter.Tendsto (fun k => (r ^ N) ^ k * r ^ j)
      Filter.atTop (nhds 0) := by
    intro j
    have hmul := h.mul_const (r ^ j)
    rwa [zero_mul] at hmul
  have hev : ∀ j, ∃ K, ∀ k ≥ K, (r ^ N) ^ k * r ^ j ∈ U :=
    fun j => Filter.eventually_atTop.mp ((hj j).eventually_mem hU)
  choose Kf hKf using hev
  set K : ℕ := (Finset.range N).sup Kf with hKdef
  refine ⟨N * (K + 1), fun m hm => ?_⟩
  have hsplit : r ^ m = (r ^ N) ^ (m / N) * r ^ (m % N) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hKle : K ≤ m / N := by
    have h1' : (K + 1) * N ≤ m := by
      rw [Nat.mul_comm]
      exact hm
    have h2 : K + 1 ≤ m / N := (Nat.le_div_iff_mul_le hN).mpr h1'
    omega
  have hmodK : Kf (m % N) ≤ K :=
    Finset.le_sup (Finset.mem_range.mpr (Nat.mod_lt m hN))
  show r ^ m ∈ U
  rw [hsplit]
  exact hKf (m % N) (m / N) (le_trans hmodK hKle)

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- **Positive powers of a pseudo-uniformizer** are pseudo-uniformizers. -/
noncomputable def PseudoUniformizer.pPow (ϖ : PseudoUniformizer F) (m : ℕ)
    (hm : 0 < m) : PseudoUniformizer F :=
  ⟨(ϖ : Fˣ) ^ m, by
    have h := PseudoUniformizer.isTopologicallyNilpotent ϖ
    show IsTopologicallyNilpotent (((ϖ : Fˣ) ^ m : Fˣ) : F)
    rw [Units.val_pow_eq_pow_val]
    rw [IsTopologicallyNilpotent]
    have hcomp : (fun k => (((ϖ : Fˣ) : F) ^ m) ^ k)
        = (fun n => ((ϖ : Fˣ) : F) ^ n) ∘ (fun k => m * k) := by
      funext k
      simp [pow_mul]
    rw [hcomp]
    exact h.comp (Filter.tendsto_atTop_atTop.mpr
      (fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hm)⟩))⟩

@[simp]
theorem PseudoUniformizer.toOF_pPow (ϖ : PseudoUniformizer F) (m : ℕ)
    (hm : 0 < m) :
    PseudoUniformizer.toOF F (PseudoUniformizer.pPow F ϖ m hm)
      = PseudoUniformizer.toOF F ϖ ^ m := by
  apply Subtype.ext
  show (((ϖ : Fˣ) ^ m : Fˣ) : F) = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ m
  rw [Units.val_pow_eq_pow_val]
  rfl

/-- The `O_F`-side `p^s`-th Frobenius root of the pseudo-uniformizer. -/
noncomputable def frobRootOF (ϖ : PseudoUniformizer F) (s : ℕ) : OF F :=
  ((_root_.frobeniusEquiv (OF F) p).symm ^ s : RingAut (OF F))
    (PseudoUniformizer.toOF F ϖ)

/-- The defining power identity of the Frobenius root. -/
theorem frobRootOF_pow (ϖ : PseudoUniformizer F) (s : ℕ) :
    frobRootOF p F ϖ s ^ p ^ s = PseudoUniformizer.toOF F ϖ := by
  refine (((_root_.frobeniusEquiv (OF F) p).symm ^ s
    : RingAut (OF F)).injective) ?_
  rw [show (((_root_.frobeniusEquiv (OF F) p).symm ^ s : RingAut (OF F)))
      (frobRootOF p F ϖ s ^ p ^ s) = frobRootOF p F ϖ s from
    frobeniusEquiv_symm_pow_pow_cancel p F (frobRootOF p F ϖ s) s]
  rfl

theorem frobRootOF_ne_zero (ϖ : PseudoUniformizer F) (s : ℕ) :
    ((frobRootOF p F ϖ s : OF F) : F) ≠ 0 := by
  intro hcon
  have h0 : frobRootOF p F ϖ s = 0 := Subtype.ext hcon
  have hϖ0 : PseudoUniformizer.toOF F ϖ = 0 := by
    rw [← frobRootOF_pow p F ϖ s, h0, zero_pow (pow_ne_zero s
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))]
  exact PseudoUniformizer.toOF_ne_zero F ϖ hϖ0

/-- **The `p^s`-th Frobenius root of a pseudo-uniformizer**: `F` is perfect, so
`ϖ^{1/p^s}` exists as an `O_F`-element; its unit is topologically nilpotent
since its `p^s`-th power is. -/
noncomputable def PseudoUniformizer.frobRoot (ϖ : PseudoUniformizer F) (s : ℕ) :
    PseudoUniformizer F :=
  ⟨Units.mk0 ((frobRootOF p F ϖ s : OF F) : F) (frobRootOF_ne_zero p F ϖ s), by
    show IsTopologicallyNilpotent ((frobRootOF p F ϖ s : OF F) : F)
    refine isTopologicallyNilpotent_of_pow
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) s) ?_
    have hp : ((frobRootOF p F ϖ s : OF F) : F) ^ p ^ s
        = (((ϖ : Fˣ) : F)) := by
      have h := congrArg (fun z : OF F => (z : F)) (frobRootOF_pow p F ϖ s)
      push_cast at h
      exact h
    rw [hp]
    exact PseudoUniformizer.isTopologicallyNilpotent ϖ⟩

@[simp]
theorem PseudoUniformizer.toOF_frobRoot (ϖ : PseudoUniformizer F) (s : ℕ) :
    PseudoUniformizer.toOF F (PseudoUniformizer.frobRoot p F ϖ s)
      = frobRootOF p F ϖ s :=
  Subtype.ext rfl

/-- The valuation identity of the Frobenius root:
`|ϖ^{1/p^s}|^{p^s} = |ϖ|`. -/
theorem perfectoidValuation_frobRoot_pow (ϖ : PseudoUniformizer F) (s : ℕ) :
    perfectoidValuation p F
        ((PseudoUniformizer.toOF F (PseudoUniformizer.frobRoot p F ϖ s) : OF F) : F)
        ^ p ^ s
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
  rw [PseudoUniformizer.toOF_frobRoot, ← Valuation.map_pow]
  congr 1
  have h := congrArg (fun z : OF F => (z : F)) (frobRootOF_pow p F ϖ s)
  push_cast at h
  exact h

omit [CharP F p] in
/-- The valuation identity of the power: `|ϖ^m| = |ϖ|^m`. -/
theorem perfectoidValuation_pPow (ϖ : PseudoUniformizer F) (m : ℕ) (hm : 0 < m) :
    perfectoidValuation p F
        ((PseudoUniformizer.toOF F (PseudoUniformizer.pPow F ϖ m hm) : OF F) : F)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ m := by
  rw [PseudoUniformizer.toOF_pPow, ← Valuation.map_pow]
  congr 1

end FarguesFontaine

end
