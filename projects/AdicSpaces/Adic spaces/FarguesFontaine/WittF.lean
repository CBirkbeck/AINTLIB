/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.RobbaLoc

/-!
# Coordinate continuity for the Gauss value (Hölder estimates)

The Teichmüller coordinate functionals are *uniformly* continuous for the Gauss
metrics, but not Lipschitz: the `k`-th digit is `p^k`-homogeneous, so differences obey
a Hölder bound with exponent `p^{-k}`. This file proves the elementary route recorded
in ticket T902(b):

* **diagonal divisibility** — for `k ≥ 1`, the `k`-th Witt coefficient of `[x] − [y]`
  is divisible by `x − y` (proved by naturality of Witt vectors along polynomial
  evaluation, no Witt-polynomial computations);
* the **twist bound** `v(teichCoeff ([x]−[y]) k) ^ (p^k) ≤ v (x−y)`;
* the **ε–δ continuity** of `a ↦ [a]`: for every `ε > 0` there is `δ > 0` with
  `v(a−b) ≤ δ → w_ρ([a]−[b]) ≤ ε`.

These are the inputs for the completion realization of `A^r` (T903, decision AD-3 of
`decomposition-laneB.md`).

## Sources

* [Kedlaya, *New methods for (φ,Γ)-modules*][kedlaya-new-methods], Remark 3.7 and the
  homogeneity discussion in the proof of Lemma 4.1 (the `p^j`-homogeneous digit
  polynomials); Theorem 4.5 (the continuity phenomenon).
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- **Diagonal divisibility**: every Witt coefficient of `[x] − [y]` is divisible by
`x − y`. (For `k = 0` this is the identity `x − y = (x−y)·1` since `constantCoeff` is
additive on Teichmüller lifts; the content is `k ≥ 1`.) Proof by naturality: in
`W((O_F)[T])` the coefficient `E_k` of `[C x] − [T]` is a polynomial with root `x`
(evaluate at `x` and use `[x] − [x] = 0`), hence divisible by `T − C x`; evaluate at
`y`. -/
theorem exists_teichmuller_sub_coeff_eq (x y : OF F) (k : ℕ) :
    ∃ r : OF F, (WittVector.teichmuller p x - WittVector.teichmuller p y).coeff k
      = (x - y) * r := by
  set E : Polynomial (OF F) :=
    (WittVector.teichmuller p (Polynomial.C x : Polynomial (OF F))
      - WittVector.teichmuller p (Polynomial.X : Polynomial (OF F))).coeff k with hE
  have hroot : E.IsRoot x := by
    have hmap := WittVector.map_coeff (Polynomial.evalRingHom x)
      (WittVector.teichmuller p (Polynomial.C x : Polynomial (OF F))
        - WittVector.teichmuller p (Polynomial.X : Polynomial (OF F))) k
    rw [map_sub, WittVector.map_teichmuller, WittVector.map_teichmuller] at hmap
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X,
      sub_self, WittVector.zero_coeff] at hmap
    exact hmap.symm
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨-(q.eval y), ?_⟩
  have hcoeff : (WittVector.teichmuller p x - WittVector.teichmuller p y).coeff k
      = E.eval y := by
    have hmap := WittVector.map_coeff (Polynomial.evalRingHom y)
      (WittVector.teichmuller p (Polynomial.C x : Polynomial (OF F))
        - WittVector.teichmuller p (Polynomial.X : Polynomial (OF F))) k
    rw [map_sub, WittVector.map_teichmuller, WittVector.map_teichmuller] at hmap
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X] at hmap
    rw [hE]
    exact hmap
  rw [hcoeff, hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  ring

/-- The **twist bound** (Hölder exponent through `θ^{-k}`, in `pow`-form):
`v(teichCoeff ([x]−[y]) k) ^ (p^k) ≤ v(x−y)`. -/
theorem valuation_teichCoeff_teichmuller_sub_pow_le (x y : OF F) (k : ℕ) :
    (perfectoidValuation p F ((teichCoeff p F
      (WittVector.teichmuller p x - WittVector.teichmuller p y) k : OF F) : F)) ^ (p ^ k)
      ≤ perfectoidValuation p F ((x - y : OF F) : F) := by
  obtain ⟨r, hr⟩ := exists_teichmuller_sub_coeff_eq p F x y k
  have hpoweq : ((teichCoeff p F
      (WittVector.teichmuller p x - WittVector.teichmuller p y) k : OF F)) ^ (p ^ k)
      = (x - y) * r := by
    rw [teichCoeff, ← map_pow, frobeniusEquiv_symm_pow_pow_cancel p F _ k, hr]
  have hcoe : (((teichCoeff p F
      (WittVector.teichmuller p x - WittVector.teichmuller p y) k : OF F)) ^ (p ^ k) :
        OF F) = ((x - y) * r : OF F) := hpoweq
  calc (perfectoidValuation p F ((teichCoeff p F
      (WittVector.teichmuller p x - WittVector.teichmuller p y) k : OF F) : F)) ^ (p ^ k)
      = perfectoidValuation p F ((((teichCoeff p F
          (WittVector.teichmuller p x - WittVector.teichmuller p y) k : OF F)) ^ (p ^ k)
            : OF F) : F) := by
        rw [show ((((teichCoeff p F (WittVector.teichmuller p x
          - WittVector.teichmuller p y) k : OF F)) ^ (p ^ k) : OF F) : F)
          = ((teichCoeff p F (WittVector.teichmuller p x
            - WittVector.teichmuller p y) k : OF F) : F) ^ (p ^ k) from rfl, map_pow]
    _ = perfectoidValuation p F (((x - y) * r : OF F) : F) := by rw [hcoe]
    _ = perfectoidValuation p F ((x - y : OF F) : F) *
          perfectoidValuation p F ((r : OF F) : F) := by
        rw [show (((x - y) * r : OF F) : F)
          = ((x - y : OF F) : F) * ((r : OF F) : F) from rfl, Valuation.map_mul]
    _ ≤ perfectoidValuation p F ((x - y : OF F) : F) :=
        mul_le_of_le_one_right zero_le (perfectoidValuation_le_one p F r)

/-- **ε–δ continuity of the Teichmüller section** for the Gauss value: given `ε > 0`
there is `δ > 0` such that `v(a−b) ≤ δ` forces `w_ρ([a]−[b]) ≤ ε`. Not Lipschitz —
the exponents `p^{-k}` appear via `valuation_teichCoeff_teichmuller_sub_pow_le`. -/
theorem gaussValue_teichmuller_sub_le_of_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ a b : OF F,
      perfectoidValuation p F ((a - b : OF F) : F) ≤ δ →
      gaussValue p F ρ (WittVector.teichmuller p a - WittVector.teichmuller p b) ≤ ε := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε0 hρ1
  refine ⟨ε ^ p ^ K, pow_pos hε0 _, fun a b hab => ?_⟩
  rw [gaussValue]
  refine ciSup_le fun k => ?_
  rcases le_or_gt k K with hkK | hkK
  · -- small indices: use the Hölder bound
    have hpow := valuation_teichCoeff_teichmuller_sub_pow_le p F a b k
    have hle : (perfectoidValuation p F ((teichCoeff p F
        (WittVector.teichmuller p a - WittVector.teichmuller p b) k : OF F) : F)) ^ (p ^ k)
        ≤ (ε ^ p ^ (K - k)) ^ p ^ k := by
      refine hpow.trans (hab.trans ?_)
      rw [← pow_mul]
      have harith : p ^ (K - k) * p ^ k = p ^ K := by
        rw [← pow_add]
        congr 1
        omega
      rw [harith]
    have hbase : perfectoidValuation p F ((teichCoeff p F
        (WittVector.teichmuller p a - WittVector.teichmuller p b) k : OF F) : F)
        ≤ ε ^ p ^ (K - k) := by
      have hpk : p ^ k ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)
      exact (pow_le_pow_iff_left₀ zero_le zero_le hpk).mp hle
    rw [gaussTerm]
    calc ρ ^ k * perfectoidValuation p F ((teichCoeff p F
        (WittVector.teichmuller p a - WittVector.teichmuller p b) k : OF F) : F)
        ≤ 1 * (ε ^ p ^ (K - k)) := by
          exact mul_le_mul (pow_le_one₀ zero_le hρ1.le) hbase zero_le zero_le
      _ = ε ^ p ^ (K - k) := one_mul _
      _ ≤ ε ^ 1 := pow_le_pow_of_le_one zero_le hε1 (Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)))
      _ = ε := pow_one ε
  · -- large indices: the raw ρ^k bound already wins
    refine (gaussTerm_le p F ρ _ k).trans ?_
    exact le_of_lt (lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le hρ1.le (by omega)) hK)

end FarguesFontaine

end
