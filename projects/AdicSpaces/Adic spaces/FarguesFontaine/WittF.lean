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
  [UniformSpace F] [NonarchimedeanRing F] [hPF : IsPerfectoidField p F] [CharP F p]

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

/-- **Per-coordinate uniform continuity** on `A_inf`: for each level `n` and `ε > 0`
there is `δ > 0` with `w_ρ(a−b) ≤ δ → v(aₙ − bₙ) ≤ ε`. Level 0 is exact
(`constantCoeff` is additive); level `n+1` recurses through head splits, feeding the
Teichmüller-difference continuity `gaussValue_teichmuller_sub_le_of_le`. -/
theorem exists_delta_teichCoeff_sub (n : ℕ) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ a b : Ainf p F, gaussValue p F ρ (a - b) ≤ δ →
      perfectoidValuation p F ((teichCoeff p F a n - teichCoeff p F b n : OF F) : F) ≤ ε := by
  induction n generalizing ε with
  | zero =>
    refine ⟨ε, hε0, fun a b hab => ?_⟩
    have h00 : teichCoeff p F a 0 - teichCoeff p F b 0 = teichCoeff p F (a - b) 0 := by
      rw [teichCoeff_zero_eq, teichCoeff_zero_eq, teichCoeff_zero_eq]
      exact (RingHom.map_sub WittVector.constantCoeff a b).symm
    rw [h00]
    have hterm : perfectoidValuation p F ((teichCoeff p F (a - b) 0 : OF F) : F)
        = gaussTerm p F ρ (a - b) 0 := by
      rw [gaussTerm, pow_zero, one_mul]
    rw [hterm]
    exact (gaussTerm_le_gaussValue p F hρ1.le (a - b) 0).trans hab
  | succ n ih =>
    obtain ⟨δn, hδn0, hδn⟩ := ih hε0 hε1
    obtain ⟨δT, hδT0, hδT⟩ := gaussValue_teichmuller_sub_le_of_le p F hρ0 hρ1
      (ε := min (ρ * δn) 1) (lt_min (mul_pos hρ0 hδn0) one_pos) (min_le_right _ _)
    refine ⟨min (min (ρ * δn) δT) 1, lt_min (lt_min (mul_pos hρ0 hδn0) hδT0) one_pos,
      fun a b hab => ?_⟩
    obtain ⟨x', hx'eq, hx'c⟩ := exists_head_split p F a
    obtain ⟨y', hy'eq, hy'c⟩ := exists_head_split p F b
    have hpx : (p : Ainf p F) * x' = a - WittVector.teichmuller p (teichCoeff p F a 0) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hx'eq.symm)
    have hpy : (p : Ainf p F) * y' = b - WittVector.teichmuller p (teichCoeff p F b 0) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hy'eq.symm)
    have hsub : (p : Ainf p F) * (x' - y')
        = (a - b) - (WittVector.teichmuller p (teichCoeff p F a 0)
          - WittVector.teichmuller p (teichCoeff p F b 0)) := by
      rw [mul_sub, hpx, hpy]
      ring
    have h0 : perfectoidValuation p F
        ((teichCoeff p F a 0 - teichCoeff p F b 0 : OF F) : F) ≤ δT := by
      have h00 : teichCoeff p F a 0 - teichCoeff p F b 0 = teichCoeff p F (a - b) 0 := by
        rw [teichCoeff_zero_eq, teichCoeff_zero_eq, teichCoeff_zero_eq]
        exact (RingHom.map_sub WittVector.constantCoeff a b).symm
      rw [h00]
      have hterm : perfectoidValuation p F ((teichCoeff p F (a - b) 0 : OF F) : F)
          = gaussTerm p F ρ (a - b) 0 := by
        rw [gaussTerm, pow_zero, one_mul]
      rw [hterm]
      exact (gaussTerm_le_gaussValue p F hρ1.le (a - b) 0).trans
        (hab.trans ((min_le_left _ _).trans (min_le_right _ _)))
    have hT : gaussValue p F ρ (WittVector.teichmuller p (teichCoeff p F a 0)
        - WittVector.teichmuller p (teichCoeff p F b 0)) ≤ min (ρ * δn) 1 :=
      hδT _ _ h0
    have hw : ρ * gaussValue p F ρ (x' - y') ≤ ρ * δn := by
      rw [← gaussValue_p_mul p F hρ1.le, hsub]
      exact (gaussValue_sub_le p F hρ1 _ _).trans (max_le
        (hab.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (hT.trans (min_le_left _ _)))
    have hxy' : gaussValue p F ρ (x' - y') ≤ δn :=
      le_of_mul_le_mul_left hw hρ0
    have hres := hδn x' y' hxy'
    rwa [hx'c n, hy'c n] at hres

include hPF in
/-- **Tate absorption**: every element of `F` lands in `O_F` after enough `ϖ`-scaling. -/
theorem exists_mul_pow_isPowerBounded (ϖ : PseudoUniformizer F) (x : F) :
    ∃ k : ℕ, IsPowerBounded (x * ((ϖ.val : Fˣ) : F) ^ k) := by
  obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := F)
  have hnil : Filter.Tendsto (fun k => ((ϖ.val : Fˣ) : F) ^ k) Filter.atTop (nhds 0) :=
    ϖ.isTopologicallyNilpotent
  have hcont : Filter.Tendsto (fun k => x * ((ϖ.val : Fˣ) : F) ^ k) Filter.atTop (nhds 0) := by
    have h := hnil.const_mul x
    rwa [mul_zero] at h
  have hmem : (powerBoundedSubring F : Set F) ∈ nhds (0 : F) :=
    P.isOpen_powerBoundedSubring.mem_nhds isPowerBounded_zero
  obtain ⟨k, hk⟩ := (hcont.eventually_mem hmem).exists
  exact ⟨k, hk⟩

/-- `F` itself is a perfect ring: Frobenius is surjective after Tate absorption
(clear `ϖ^{pk}`, take a `p`-th root in `O_F`, divide by `ϖ^k`). -/
instance instPerfectRingF : PerfectRing F p := by
  refine PerfectRing.ofSurjective _ p fun x => ?_
  set ϖ : PseudoUniformizer F := IsTateRing.pseudoUniformizer (A := F) with hϖ
  obtain ⟨k, hk⟩ := exists_mul_pow_isPowerBounded p F ϖ (x)
  have hϖpb : IsPowerBounded (((ϖ.val : Fˣ) : F)) :=
    ϖ.isTopologicallyNilpotent.isPowerBounded
  have hϖpow : ∀ m : ℕ, IsPowerBounded (((ϖ.val : Fˣ) : F) ^ m) := by
    intro m
    induction m with
    | zero => simpa using isPowerBounded_one
    | succ m' ihm => rw [pow_succ]; exact isPowerBounded_mul ihm hϖpb
  have hkp : IsPowerBounded (x * ((ϖ.val : Fˣ) : F) ^ (p * k)) := by
    have hp1 : 1 ≤ p := (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
    have hsplit : x * ((ϖ.val : Fˣ) : F) ^ (p * k)
        = (x * ((ϖ.val : Fˣ) : F) ^ k) * ((ϖ.val : Fˣ) : F) ^ ((p - 1) * k) := by
      rw [mul_assoc, ← pow_add]
      have hcancel : k + (p - 1) * k = p * k := by
        calc k + (p - 1) * k = (1 + (p - 1)) * k := by ring
          _ = p * k := by rw [show 1 + (p - 1) = p from by omega]
      rw [hcancel]
    rw [hsplit]
    exact isPowerBounded_mul hk (hϖpow _)
  obtain ⟨b, hb⟩ := frobenius_surjective_OF p F ⟨_, hkp⟩
  refine ⟨(b : F) * (((ϖ.val : Fˣ) : F) ^ k)⁻¹, ?_⟩
  have hbF : ((b : OF F) : F) ^ p = x * ((ϖ.val : Fˣ) : F) ^ (p * k) := by
    have h := congrArg (fun z : OF F => (z : F)) hb
    simpa [frobenius_def] using h
  have hϖne : ((ϖ.val : Fˣ) : F) ≠ 0 := (ϖ.val : Fˣ).ne_zero
  rw [frobenius_def, mul_pow, ← inv_pow, ← pow_mul, hbF, mul_assoc,
    show k * p = p * k from Nat.mul_comm k p, ← mul_pow,
    mul_inv_cancel₀ hϖne, one_pow, mul_one]

/-- The `n`-th Teichmüller coordinate of a Witt vector over the field `F`. -/
def teichCoeffF (x : WittVector p F) (n : ℕ) : F :=
  (((_root_.frobeniusEquiv F p).symm ^ n : RingAut F)) (x.coeff n)

theorem frobeniusEquivF_symm_pow_pow_cancel (b : F) (j : ℕ) :
    ((_root_.frobeniusEquiv F p).symm ^ j : RingAut F) (b ^ p ^ j) = b := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hσ : (_root_.frobeniusEquiv F p).symm ((b ^ p ^ k) ^ p) = b ^ p ^ k := by
      have hfe : _root_.frobeniusEquiv F p (b ^ p ^ k) = (b ^ p ^ k) ^ p := by
        rw [_root_.frobeniusEquiv_apply, frobenius_def]
      rw [← hfe, RingEquiv.symm_apply_apply]
    rw [pow_succ ((_root_.frobeniusEquiv F p).symm) k, RingAut.mul_apply,
      show (p : ℕ) ^ (k + 1) = p ^ k * p from pow_succ p k, pow_mul, hσ, ih]

/-- CORE-2 over `F`: every Witt vector over `F` is its length-`N` Teichmüller prefix
plus a `p^N`-tail. -/
theorem exists_eq_sum_teichCoeffF_add (x : WittVector p F) (N : ℕ) :
    ∃ z : WittVector p F, x = (∑ i ∈ Finset.range N,
      WittVector.teichmuller p (teichCoeffF p F x i) * (p : WittVector p F) ^ i) +
      (p : WittVector p F) ^ N * z := by
  rcases N with - | n
  · exact ⟨x, by simp⟩
  · obtain ⟨w, hw⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
    refine ⟨w, ?_⟩
    have hIic : Finset.Iic n = Finset.range (n + 1) := by
      ext m; simp [Nat.lt_succ_iff]
    have hsum : (∑ i ∈ Finset.range (n + 1),
        WittVector.teichmuller p (teichCoeffF p F x i) * (p : WittVector p F) ^ i)
        = ∑ i ≤ n, WittVector.teichmuller p
            (((_root_.frobeniusEquiv F p).symm ^ i) (x.coeff i)) * (p : WittVector p F) ^ i := by
      rw [← hIic]
      exact Finset.sum_congr rfl fun i _ => by rw [teichCoeffF]
    rw [hsum]
    exact sub_eq_iff_eq_add'.mp hw

/-- CORE-1 over `F`: uniqueness of Teichmüller expansions. -/
theorem teichCoeffF_sum_range_add {N : ℕ} (b : ℕ → F) (z : WittVector p F) {j : ℕ}
    (hj : j < N) :
    teichCoeffF p F ((∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i)
      + (p : WittVector p F) ^ N * z) j = b j := by
  have hcoeff_eq : ∀ i < N, ((∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i)
        + (p : WittVector p F) ^ N * z).coeff i
      = (∑ i ∈ Finset.range N,
          WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i).coeff i := by
    rw [WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    rw [add_sub_cancel_left, mul_comm]
    exact WittVector.mul_pow_charP_coeff_zero z hi
  have hsumcoeff : (∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i).coeff j
      = (b j) ^ p ^ j := by
    rw [WittVector.sum_coeff_eq_coeff_sum]
    · rw [Finset.sum_eq_single j]
      · exact WittVector.teichmuller_mul_pow_coeff j (b j)
      · intro i _ hne
        exact WittVector.teichmuller_mul_pow_coeff_of_ne _ hne.symm
      · intro hj'
        exact absurd (Finset.mem_range.mpr hj) hj'
    · refine fun m ↦ ⟨fun ⟨a, _, ha⟩ ⟨a', _, ha'⟩ ↦ ?_⟩
      ext
      dsimp only [ne_eq, Set.mem_setOf_eq]
      rw [← Not.imp_symm (WittVector.teichmuller_mul_pow_coeff_of_ne _) ha]
      exact Not.imp_symm (WittVector.teichmuller_mul_pow_coeff_of_ne _) ha'
  rw [teichCoeffF, hcoeff_eq j hj, hsumcoeff]
  exact frobeniusEquivF_symm_pow_pow_cancel p F (b j) j

/-- One-step commutation of the inverse Frobenius with the inclusion `O_F → F`. -/
theorem frobeniusEquivF_symm_subtype (z : OF F) :
    (_root_.frobeniusEquiv F p).symm ((z : OF F) : F)
      = (((_root_.frobeniusEquiv (OF F) p).symm z : OF F) : F) := by
  refine ((_root_.frobeniusEquiv F p).symm_apply_eq).mpr ?_
  rw [_root_.frobeniusEquiv_apply, frobenius_def]
  have h2 : ((((_root_.frobeniusEquiv (OF F) p).symm z) ^ p : OF F) : F)
      = ((z : OF F) : F) := by
    have h4 : (((_root_.frobeniusEquiv (OF F) p).symm z) ^ p : OF F) = z := by
      rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    rw [h4]
  rw [show ((((_root_.frobeniusEquiv (OF F) p).symm z : OF F) : F)) ^ p
    = ((((_root_.frobeniusEquiv (OF F) p).symm z) ^ p : OF F) : F) from rfl, h2]

/-- Iterated commutation of the inverse Frobenius with the inclusion `O_F → F`. -/
theorem frobeniusEquivF_symm_pow_subtype (z : OF F) (k : ℕ) :
    ((_root_.frobeniusEquiv F p).symm ^ k : RingAut F) ((z : OF F) : F)
      = ((((_root_.frobeniusEquiv (OF F) p).symm ^ k : RingAut (OF F)) z : OF F) : F) := by
  induction k generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, RingAut.mul_apply, RingAut.mul_apply,
      frobeniusEquivF_symm_subtype p F z, ih]

/-- Coordinate transport along the inclusion: coordinates of `W(O_F)`-elements viewed
in `W(F)` are the coercions of their `O_F`-coordinates. -/
theorem teichCoeffF_map (a : Ainf p F) (n : ℕ) :
    teichCoeffF p F (WittVector.map ((powerBoundedSubring.toSubring F).subtype) a) n
      = ((teichCoeff p F a n : OF F) : F) := by
  rw [teichCoeffF, teichCoeff, WittVector.map_coeff]
  exact frobeniusEquivF_symm_pow_subtype p F (a.coeff n) n


/-! ### The Gauss value over `W(F)` (boundedness-threaded)

Over `W(F)` coordinate valuations are unbounded in general, so the sup-based value
carries explicit `BddAbove` hypotheses instead of the global `≤ 1` of `GaussNorm.lean`.
These are the ports promised by T902(a)/T903(3). -/

/-- The `n`-th Gauss term of `x : W(F)`. -/
def gaussTermF (ρ : NNReal) (x : WittVector p F) (n : ℕ) : NNReal :=
  ρ ^ n * perfectoidValuation p F (teichCoeffF p F x n)

/-- The Gauss value of `x : W(F)` (junk `0` when the terms are unbounded — every lemma
carries the boundedness hypothesis it needs). -/
def gaussValueF (ρ : NNReal) (x : WittVector p F) : NNReal :=
  ⨆ n, gaussTermF p F ρ x n

theorem gaussTermF_le_gaussValueF {ρ : NNReal} {x : WittVector p F}
    (hB : BddAbove (Set.range (gaussTermF p F ρ x))) (n : ℕ) :
    gaussTermF p F ρ x n ≤ gaussValueF p F ρ x :=
  le_ciSup hB n

/-- Scaling (F-version): coordinates of `[w]·s` are `w`-multiples. -/
theorem teichCoeffF_teichmuller_mul (w : F) (s : WittVector p F) (j : ℕ) :
    teichCoeffF p F (WittVector.teichmuller p w * s) j = w * teichCoeffF p F s j := by
  obtain ⟨z, hz⟩ := exists_eq_sum_teichCoeffF_add p F s (j + 1)
  have hws : WittVector.teichmuller p w * s = (∑ i ∈ Finset.range (j + 1),
      WittVector.teichmuller p (w * teichCoeffF p F s i) * (p : WittVector p F) ^ i) +
      (p : WittVector p F) ^ (j + 1) * (WittVector.teichmuller p w * z) := by
    conv_lhs => rw [hz]
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (by ring)
    rw [map_mul]
    ring
  rw [hws, teichCoeffF_sum_range_add p F (N := j + 1) _ _ (Nat.lt_succ_self j)]

/-- Head split (F-version). -/
theorem exists_head_splitF (x : WittVector p F) :
    ∃ x' : WittVector p F,
      x = WittVector.teichmuller p (teichCoeffF p F x 0) + (p : WittVector p F) * x'
      ∧ ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1) := by
  obtain ⟨z, hz⟩ := exists_eq_sum_teichCoeffF_add p F x 1
  have h1 : x = WittVector.teichmuller p (teichCoeffF p F x 0) + (p : WittVector p F) * z := by
    simpa using hz
  refine ⟨z, h1, fun k => ?_⟩
  obtain ⟨w, hw⟩ := exists_eq_sum_teichCoeffF_add p F z (k + 1)
  have hmul : (p : WittVector p F) * z = (∑ i ∈ Finset.range (k + 1),
      WittVector.teichmuller p (teichCoeffF p F z i) * (p : WittVector p F) ^ (i + 1)) +
      (p : WittVector p F) ^ (k + 2) * w := by
    conv_lhs => rw [hw]
    rw [mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) (by ring)
  have hpeel : (∑ i ∈ Finset.range (k + 2),
      WittVector.teichmuller p
        (Nat.casesOn i (teichCoeffF p F x 0) fun i' => teichCoeffF p F z i') *
        (p : WittVector p F) ^ i)
      = (∑ i ∈ Finset.range (k + 1),
          WittVector.teichmuller p (teichCoeffF p F z i) * (p : WittVector p F) ^ (i + 1)) +
        WittVector.teichmuller p (teichCoeffF p F x 0) := by
    rw [Finset.sum_range_succ']
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => rfl)
      (by rw [pow_zero, mul_one]; rfl)
  have hx2 : x = (∑ i ∈ Finset.range (k + 2),
      WittVector.teichmuller p
        (Nat.casesOn i (teichCoeffF p F x 0) fun i' => teichCoeffF p F z i') *
        (p : WittVector p F) ^ i) + (p : WittVector p F) ^ (k + 2) * w := by
    conv_lhs => rw [h1, hmul]
    rw [hpeel]
    abel
  have hj := teichCoeffF_sum_range_add p F (N := k + 2)
    (fun i => Nat.casesOn i (teichCoeffF p F x 0) fun i' => teichCoeffF p F z i') w
    (j := k + 1) (by omega)
  rw [← hx2] at hj
  exact hj.symm

/-- Pair bound (F-version, one-sided): the `u = b/a` trick, coordinates of `1 + [u]`
transported from `W(O_F)`. -/
private theorem valuation_teichCoeffF_teichmuller_add_le_left {a b : F}
    (h : perfectoidValuation p F b ≤ perfectoidValuation p F a) (j : ℕ) :
    perfectoidValuation p F (teichCoeffF p F
      (WittVector.teichmuller p a + WittVector.teichmuller p b) j)
      ≤ perfectoidValuation p F a := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 0 := by
      have h0 : perfectoidValuation p F b = 0 := by
        refine le_antisymm ?_ zero_le
        simpa using h
      exact (Valuation.zero_iff _).mp h0
    subst hb
    simp [teichCoeffF]
  · have hva : perfectoidValuation p F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
    have hu1 : perfectoidValuation p F (b / a) ≤ 1 := by
      have hmul : perfectoidValuation p F (b / a) * perfectoidValuation p F a
          = perfectoidValuation p F b := by
        rw [← Valuation.map_mul, div_mul_cancel₀ _ ha]
      refine le_of_mul_le_mul_right ?_ (pos_iff_ne_zero.mpr hva)
      rw [one_mul]
      exact hmul.le.trans h
    obtain ⟨u, hu⟩ := (perfectoidValuation_integers p F).exists_of_le_one hu1
    have hab : a * ((u : OF F) : F) = b := by
      have hcoe : ((u : OF F) : F) = b / a := hu
      rw [hcoe, mul_comm, div_mul_cancel₀ _ ha]
    have hsplit : WittVector.teichmuller p a + WittVector.teichmuller p b
        = WittVector.teichmuller p a *
          (1 + WittVector.teichmuller p ((u : OF F) : F)) := by
      rw [mul_add, mul_one, ← map_mul, hab]
    rw [hsplit, teichCoeffF_teichmuller_mul, Valuation.map_mul]
    refine mul_le_of_le_one_right zero_le ?_
    -- coordinates of 1 + [↑u] come from W(O_F)
    have htrans : (1 + WittVector.teichmuller p ((u : OF F) : F))
        = WittVector.map ((powerBoundedSubring.toSubring F).subtype)
            (1 + WittVector.teichmuller p u) := by
      rw [map_add, map_one, WittVector.map_teichmuller]
      rfl
    rw [htrans, teichCoeffF_map]
    exact perfectoidValuation_le_one p F _

/-- Pair bound (F-version): every coordinate of `[a] + [b]` has valuation at most
`max |a| |b|`. -/
theorem valuation_teichCoeffF_teichmuller_add_le (a b : F) (j : ℕ) :
    perfectoidValuation p F (teichCoeffF p F
      (WittVector.teichmuller p a + WittVector.teichmuller p b) j)
      ≤ max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
  rcases le_total (perfectoidValuation p F b) (perfectoidValuation p F a) with h | h
  · exact le_max_of_le_left (valuation_teichCoeffF_teichmuller_add_le_left p F h j)
  · rw [add_comm]
    exact le_max_of_le_right (valuation_teichCoeffF_teichmuller_add_le_left p F h j)

/-- Boundedness propagates to head-split tails (coordinates shift). -/
theorem bddAbove_gaussTermF_of_tail {ρ : NNReal} (hρ0 : 0 < ρ) {x x' : WittVector p F}
    (hcoords : ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1))
    (hB : BddAbove (Set.range (gaussTermF p F ρ x))) :
    BddAbove (Set.range (gaussTermF p F ρ x')) := by
  obtain ⟨M, hM⟩ := hB
  refine ⟨M / ρ, ?_⟩
  rintro y ⟨k, rfl⟩
  have heq : ρ * gaussTermF p F ρ x' k = gaussTermF p F ρ x (k + 1) := by
    rw [gaussTermF, gaussTermF, hcoords k, pow_succ]
    ring
  have hle : ρ * gaussTermF p F ρ x' k ≤ M := heq.le.trans (hM ⟨k + 1, rfl⟩)
  rw [le_div_iff₀ hρ0, mul_comm]
  exact hle

/-- Tail bound (F-version): `ρ·wF(x') ≤ wF(x)` for a head-split tail. -/
theorem mul_gaussValueF_le_of_tail {ρ : NNReal} {x x' : WittVector p F}
    (hB : BddAbove (Set.range (gaussTermF p F ρ x)))
    (hcoords : ∀ k, teichCoeffF p F x' k = teichCoeffF p F x (k + 1)) :
    ρ * gaussValueF p F ρ x' ≤ gaussValueF p F ρ x := by
  rw [gaussValueF, NNReal.mul_iSup]
  refine ciSup_le fun k => ?_
  have heq : ρ * gaussTermF p F ρ x' k = gaussTermF p F ρ x (k + 1) := by
    rw [gaussTermF, gaussTermF, hcoords k, pow_succ]
    ring
  rw [heq]
  exact gaussTermF_le_gaussValueF p F hB (k + 1)

/-- The Gauss value of a two-Teichmüller sum (F-version). -/
theorem gaussValueF_teichmuller_add_le {ρ : NNReal} (hρ1 : ρ < 1) (a b : F) :
    gaussValueF p F ρ (WittVector.teichmuller p a + WittVector.teichmuller p b)
      ≤ max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
  rw [gaussValueF]
  refine ciSup_le fun j => ?_
  rw [gaussTermF]
  exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hρ1.le)).trans
    (valuation_teichCoeffF_teichmuller_add_le p F a b j)

/-- Boundedness for two-Teichmüller sums. -/
theorem bddAbove_gaussTermF_teichmuller_add {ρ : NNReal} (hρ1 : ρ < 1) (a b : F) :
    BddAbove (Set.range (gaussTermF p F ρ
      (WittVector.teichmuller p a + WittVector.teichmuller p b))) := by
  refine ⟨max (perfectoidValuation p F a) (perfectoidValuation p F b), ?_⟩
  rintro y ⟨j, rfl⟩
  rw [gaussTermF]
  exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hρ1.le)).trans
    (valuation_teichCoeffF_teichmuller_add_le p F a b j)

/-- List head-split (F-version), with boundedness threaded through the pools. -/
private theorem exists_list_head_splitF {ρ : NNReal} (hρ0 : 0 < ρ) (s B : NNReal)
    (L : List (WittVector p F))
    (hL : ∀ w ∈ L, BddAbove (Set.range (gaussTermF p F ρ w)) ∧
      s * gaussValueF p F ρ w ≤ B) :
    ∃ (hl : List F) (tl : List (WittVector p F)),
      L.sum = (hl.map fun h => WittVector.teichmuller p h).sum
        + (p : WittVector p F) * tl.sum
      ∧ (∀ h ∈ hl, s * perfectoidValuation p F h ≤ B)
      ∧ ∀ t ∈ tl, BddAbove (Set.range (gaussTermF p F ρ t)) ∧
          s * (ρ * gaussValueF p F ρ t) ≤ B := by
  induction L with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | cons w rest ih =>
    obtain ⟨hl, tl, hsum, hhl, htl⟩ := ih fun w' hw' => hL w' (by simp [hw'])
    obtain ⟨w', hw', hw'coords⟩ := exists_head_splitF p F w
    obtain ⟨hBw, hVw⟩ := hL w (by simp)
    refine ⟨teichCoeffF p F w 0 :: hl, w' :: tl, ?_, ?_, ?_⟩
    · rw [List.sum_cons, hsum, List.map_cons, List.sum_cons, List.sum_cons]
      conv_lhs => rw [hw']
      ring
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · have hv : perfectoidValuation p F (teichCoeffF p F w 0)
            ≤ gaussValueF p F ρ w := by
          have h0 := gaussTermF_le_gaussValueF p F hBw 0
          rwa [gaussTermF, pow_zero, one_mul] at h0
        exact le_trans (mul_le_mul_of_nonneg_left hv zero_le) hVw
      · exact hhl h hh'
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · refine ⟨bddAbove_gaussTermF_of_tail p F hρ0 hw'coords hBw, ?_⟩
        have htail := mul_gaussValueF_le_of_tail p F hBw hw'coords
        exact le_trans (mul_le_mul_of_nonneg_left htail zero_le) hVw
      · exact htl t ht'

/-- Fold of Teichmüller heads (F-version). -/
private theorem exists_fold_teichmuller_headsF {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (s B : NNReal) (l : List F)
    (hl : ∀ h ∈ l, s * perfectoidValuation p F h ≤ B) :
    ∃ (c : F) (P : List (WittVector p F)),
      (l.map fun h => WittVector.teichmuller p h).sum
        = WittVector.teichmuller p c + (p : WittVector p F) * P.sum
      ∧ s * perfectoidValuation p F c ≤ B
      ∧ ∀ w ∈ P, BddAbove (Set.range (gaussTermF p F ρ w)) ∧
          s * (ρ * gaussValueF p F ρ w) ≤ B := by
  induction l with
  | nil =>
    refine ⟨0, [], by simp [WittVector.teichmuller_zero], ?_, by simp⟩
    simp
  | cons h t ih =>
    obtain ⟨c, P, hsum, hc, hP⟩ := ih fun h' hh' => hl h' (by simp [hh'])
    obtain ⟨G', hG', hG'coords⟩ := exists_head_splitF p F
      (WittVector.teichmuller p h + WittVector.teichmuller p c)
    have hmax : s * max (perfectoidValuation p F h) (perfectoidValuation p F c) ≤ B := by
      rw [nnreal_mul_max]
      exact max_le (hl h (by simp)) hc
    have hBpair := bddAbove_gaussTermF_teichmuller_add p F hρ1 h c
    have hpairval := gaussValueF_teichmuller_add_le p F hρ1 h c
    refine ⟨teichCoeffF p F (WittVector.teichmuller p h + WittVector.teichmuller p c) 0,
      G' :: P, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hsum, List.sum_cons]
      conv_lhs => rw [show WittVector.teichmuller p h + (WittVector.teichmuller p c
        + (p : WittVector p F) * P.sum)
        = (WittVector.teichmuller p h + WittVector.teichmuller p c)
          + (p : WittVector p F) * P.sum from by ring, hG']
      ring
    · refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) hmax
      exact valuation_teichCoeffF_teichmuller_add_le p F h c 0
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · refine ⟨bddAbove_gaussTermF_of_tail p F hρ0 hG'coords hBpair, ?_⟩
        have h1 := (mul_gaussValueF_le_of_tail p F hBpair hG'coords).trans hpairval
        exact le_trans (mul_le_mul_of_nonneg_left h1 zero_le) hmax
      · exact hP w hw'

/-- Level representation (F-version). -/
private theorem exists_level_repF {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x y : WittVector p F}
    (hBx : BddAbove (Set.range (gaussTermF p F ρ x)))
    (hBy : BddAbove (Set.range (gaussTermF p F ρ y))) (n : ℕ) :
    ∃ (b : ℕ → F) (L : List (WittVector p F)),
      x + y = (∑ i ∈ Finset.range n,
          WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i)
        + (p : WittVector p F) ^ n * L.sum
      ∧ (∀ i < n, ρ ^ i * perfectoidValuation p F (b i)
          ≤ max (gaussValueF p F ρ x) (gaussValueF p F ρ y))
      ∧ ∀ w ∈ L, BddAbove (Set.range (gaussTermF p F ρ w)) ∧
          ρ ^ n * gaussValueF p F ρ w
            ≤ max (gaussValueF p F ρ x) (gaussValueF p F ρ y) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, [x, y], by simp, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro w hw
    rw [pow_zero, one_mul]
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact ⟨hBx, le_max_left _ _⟩
    · rcases List.mem_cons.mp hw' with rfl | hw''
      · exact ⟨hBy, le_max_right _ _⟩
      · exact absurd hw'' (List.not_mem_nil)
  | succ n ihn =>
    obtain ⟨b, L, hrep, hb, hL⟩ := ihn
    obtain ⟨hl, tl, hsplit, hhl, htl⟩ := exists_list_head_splitF p F hρ0 (ρ ^ n)
      (max (gaussValueF p F ρ x) (gaussValueF p F ρ y)) L hL
    obtain ⟨c, P, hfold, hcbound, hPbound⟩ := exists_fold_teichmuller_headsF p F hρ0 hρ1
      (ρ ^ n) (max (gaussValueF p F ρ x) (gaussValueF p F ρ y)) hl hhl
    refine ⟨Function.update b n c, P ++ tl, ?_, ?_, ?_⟩
    · have hpre : (∑ i ∈ Finset.range (n + 1),
          WittVector.teichmuller p (Function.update b n c i) * (p : WittVector p F) ^ i)
          = (∑ i ∈ Finset.range n,
              WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i)
            + WittVector.teichmuller p c * (p : WittVector p F) ^ n := by
        rw [Finset.sum_range_succ]
        refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) ?_
        · rw [Function.update_of_ne (Finset.mem_range.mp hi).ne]
        · rw [Function.update_self]
      rw [hpre, List.sum_append]
      conv_lhs => rw [hrep]
      rw [hsplit, hfold]
      ring
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne]
        exact hb i hi'
      · rw [Function.update_self]
        exact hcbound
    · intro w hw
      rcases List.mem_append.mp hw with hw' | hw'
      · obtain ⟨hBw, hVw⟩ := hPbound w hw'
        exact ⟨hBw, by rw [pow_succ, mul_assoc]; exact hVw⟩
      · obtain ⟨hBw, hVw⟩ := htl w hw'
        exact ⟨hBw, by rw [pow_succ, mul_assoc]; exact hVw⟩

/-- **Ultrametric inequality over `W(F)`** (boundedness-threaded). -/
theorem gaussValueF_add_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x y : WittVector p F}
    (hBx : BddAbove (Set.range (gaussTermF p F ρ x)))
    (hBy : BddAbove (Set.range (gaussTermF p F ρ y))) :
    gaussValueF p F ρ (x + y)
      ≤ max (gaussValueF p F ρ x) (gaussValueF p F ρ y) := by
  rw [gaussValueF]
  refine ciSup_le fun j => ?_
  obtain ⟨b, L, hrep, hb, -⟩ := exists_level_repF p F hρ0 hρ1 hBx hBy (j + 1)
  have hcoeff : teichCoeffF p F (x + y) j = b j := by
    rw [hrep, teichCoeffF_sum_range_add p F (N := j + 1) b _ (Nat.lt_succ_self j)]
  rw [gaussTermF, hcoeff]
  exact hb j (Nat.lt_succ_self j)

/-- Transport: term values of `W(O_F)`-elements agree in `W(F)`. -/
theorem gaussTermF_map {ρ : NNReal} (z : Ainf p F) (n : ℕ) :
    gaussTermF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) n
      = gaussTerm p F ρ z n := by
  rw [gaussTermF, gaussTerm, teichCoeffF_map]

theorem gaussValueF_map {ρ : NNReal} (z : Ainf p F) :
    gaussValueF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z)
      = gaussValue p F ρ z := by
  rw [gaussValueF, gaussValue]
  exact iSup_congr fun n => gaussTermF_map p F z n

/-- Term-value scaling under Teichmüller multiplication (F-version). -/
theorem gaussTermF_teichmuller_mul {ρ : NNReal} (w : F) (s : WittVector p F) (n : ℕ) :
    gaussTermF p F ρ (WittVector.teichmuller p w * s) n
      = perfectoidValuation p F w * gaussTermF p F ρ s n := by
  rw [gaussTermF, gaussTermF, teichCoeffF_teichmuller_mul, Valuation.map_mul]
  ring

theorem gaussValueF_teichmuller_mul {ρ : NNReal} (w : F) (s : WittVector p F) :
    gaussValueF p F ρ (WittVector.teichmuller p w * s)
      = perfectoidValuation p F w * gaussValueF p F ρ s := by
  rw [gaussValueF, gaussValueF, NNReal.mul_iSup]
  exact iSup_congr fun n => gaussTermF_teichmuller_mul p F w s n

/-- **Scaled Teichmüller-difference continuity**: for pairs with values at most
`(vϖ)⁻ᵐ`, scale down by `ϖ^m` into `O_F`, apply the `O_F`-continuity, transport back. -/
theorem gaussValueF_teichmuller_sub_le_of_le_scaled {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (ϖ : PseudoUniformizer F) (m : ℕ) {ε : NNReal} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ a b : F,
      perfectoidValuation p F a ≤ ((perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m →
      perfectoidValuation p F b ≤ ((perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m →
      perfectoidValuation p F (a - b) ≤ δ →
      gaussValueF p F ρ (WittVector.teichmuller p a - WittVector.teichmuller p b) ≤ ε := by
  set ϖF : F := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hϖF
  set c : NNReal := perfectoidValuation p F ϖF with hc
  have hϖne : ϖF ≠ 0 := fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hc1 : c ≤ 1 := perfectoidValuation_le_one p F _
  have hεc0 : 0 < ε * c ^ m := mul_pos hε0 (pow_pos hc0 m)
  have hεc1 : ε * c ^ m ≤ 1 :=
    mul_le_one₀ hε1 zero_le (pow_le_one₀ zero_le hc1)
  obtain ⟨δT, hδT0, hδT⟩ := gaussValue_teichmuller_sub_le_of_le p F hρ0 hρ1
    (ε := ε * c ^ m) hεc0 hεc1
  refine ⟨δT * (c⁻¹) ^ m, mul_pos hδT0 (pow_pos (inv_pos.mpr hc0) m),
    fun a b ha hb hab => ?_⟩
  have hscale : ∀ x : F, perfectoidValuation p F x ≤ (c⁻¹) ^ m →
      perfectoidValuation p F (x * ϖF ^ m) ≤ 1 := by
    intro x hx
    rw [Valuation.map_mul, map_pow]
    calc perfectoidValuation p F x * c ^ m
        ≤ (c⁻¹) ^ m * c ^ m := mul_le_mul_of_nonneg_right hx zero_le
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc0.ne', one_pow]
  obtain ⟨ahat, hahat⟩ := (perfectoidValuation_integers p F).exists_of_le_one
    (hscale a ha)
  obtain ⟨bhat, hbhat⟩ := (perfectoidValuation_integers p F).exists_of_le_one
    (hscale b hb)
  have hahat' : ((ahat : OF F) : F) = a * ϖF ^ m := hahat
  have hbhat' : ((bhat : OF F) : F) = b * ϖF ^ m := hbhat
  have hdiff : perfectoidValuation p F ((ahat - bhat : OF F) : F) ≤ δT := by
    have hcoe : ((ahat - bhat : OF F) : F) = (a - b) * ϖF ^ m := by
      rw [show ((ahat - bhat : OF F) : F)
        = ((ahat : OF F) : F) - ((bhat : OF F) : F) from rfl, hahat', hbhat']
      ring
    rw [hcoe, Valuation.map_mul, map_pow]
    calc perfectoidValuation p F (a - b) * c ^ m
        ≤ (δT * (c⁻¹) ^ m) * c ^ m := mul_le_mul_of_nonneg_right hab zero_le
      _ = δT := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0.ne', one_pow, mul_one]
  have hOF := hδT ahat bhat hdiff
  -- transport: [a] − [b] = [ϖF⁻¹]^m-scaled image of [ahat] − [bhat]
  have hsplit : WittVector.teichmuller p a - WittVector.teichmuller p b
      = WittVector.teichmuller p ((ϖF ^ m)⁻¹) *
        (WittVector.map ((powerBoundedSubring.toSubring F).subtype)
          (WittVector.teichmuller p ahat - WittVector.teichmuller p bhat)) := by
    rw [map_sub, WittVector.map_teichmuller, WittVector.map_teichmuller]
    rw [show ((powerBoundedSubring.toSubring F).subtype) ahat = ((ahat : OF F) : F) from rfl,
      show ((powerBoundedSubring.toSubring F).subtype) bhat = ((bhat : OF F) : F) from rfl,
      hahat', hbhat', mul_sub, ← map_mul, ← map_mul]
    have hϖpm : (ϖF ^ m) ≠ 0 := pow_ne_zero m hϖne
    rw [show (ϖF ^ m)⁻¹ * (a * ϖF ^ m) = a from by field_simp,
      show (ϖF ^ m)⁻¹ * (b * ϖF ^ m) = b from by field_simp]
  rw [hsplit, gaussValueF_teichmuller_mul, gaussValueF_map]
  have hvinv : perfectoidValuation p F ((ϖF ^ m)⁻¹) = (c⁻¹) ^ m := by
    rw [map_inv₀, map_pow, inv_pow]
  rw [hvinv]
  calc (c⁻¹) ^ m * (gaussValue p F ρ
        (WittVector.teichmuller p ahat - WittVector.teichmuller p bhat))
      ≤ (c⁻¹) ^ m * (ε * c ^ m) := mul_le_mul_of_nonneg_left hOF zero_le
    _ = ε := by
        rw [mul_comm ε (c ^ m), ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0.ne',
          one_pow, one_mul]

/-- Coordinates shift under multiplication by `p` (F-version). -/
theorem teichCoeffF_p_mul (x : WittVector p F) (n : ℕ) :
    teichCoeffF p F ((p : WittVector p F) * x) (n + 1) = teichCoeffF p F x n := by
  rw [teichCoeffF, teichCoeffF, show (p : WittVector p F) * x = x * (p : WittVector p F)
    from mul_comm _ _, show ((x * (p : WittVector p F)).coeff (n + 1)) = x.coeff n ^ p from
    WittVector.mul_charP_coeff_succ x n, pow_succ ((_root_.frobeniusEquiv F p).symm),
    RingAut.mul_apply]
  congr 1
  rw [show x.coeff n ^ p = _root_.frobenius F p (x.coeff n) from rfl,
    ← _root_.frobeniusEquiv_apply, RingEquiv.symm_apply_apply]

theorem teichCoeffF_p_mul_zero (x : WittVector p F) :
    teichCoeffF p F ((p : WittVector p F) * x) 0 = 0 := by
  rw [teichCoeffF]
  have h0 : ((p : WittVector p F) * x).coeff 0 = 0 := by
    rw [mul_comm]
    exact WittVector.mul_charP_coeff_zero x
  simp [h0]

/-- Term identities for the `p`-shift. -/
theorem gaussTermF_p_mul {ρ : NNReal} (x : WittVector p F) (n : ℕ) :
    gaussTermF p F ρ ((p : WittVector p F) * x) (n + 1) = ρ * gaussTermF p F ρ x n := by
  rw [gaussTermF, gaussTermF, teichCoeffF_p_mul, pow_succ]
  ring

theorem gaussTermF_p_mul_zero {ρ : NNReal} (x : WittVector p F) :
    gaussTermF p F ρ ((p : WittVector p F) * x) 0 = 0 := by
  rw [gaussTermF, teichCoeffF_p_mul_zero]
  simp

theorem bddAbove_gaussTermF_p_mul {ρ : NNReal} {x : WittVector p F}
    (hB : BddAbove (Set.range (gaussTermF p F ρ x))) :
    BddAbove (Set.range (gaussTermF p F ρ ((p : WittVector p F) * x))) := by
  obtain ⟨M, hM⟩ := hB
  refine ⟨ρ * M, ?_⟩
  rintro y ⟨k, rfl⟩
  rcases k with - | n
  · rw [gaussTermF_p_mul_zero]
    exact zero_le
  · rw [gaussTermF_p_mul]
    exact mul_le_mul_of_nonneg_left (hM ⟨n, rfl⟩) zero_le

/-- The `p`-shift for the F-value (boundedness-threaded). -/
theorem gaussValueF_p_mul {ρ : NNReal} {x : WittVector p F}
    (hB : BddAbove (Set.range (gaussTermF p F ρ x))) :
    gaussValueF p F ρ ((p : WittVector p F) * x) = ρ * gaussValueF p F ρ x := by
  rw [gaussValueF, gaussValueF, NNReal.mul_iSup]
  refine le_antisymm (ciSup_le fun n => ?_) (ciSup_le fun n => ?_)
  · rcases n with - | n
    · rw [gaussTermF_p_mul_zero]
      exact zero_le
    · rw [gaussTermF_p_mul]
      refine le_ciSup (⟨ρ * (gaussValueF p F ρ x), ?_⟩ :
        BddAbove (Set.range fun m => ρ * gaussTermF p F ρ x m)) n
      rintro y ⟨k, rfl⟩
      exact mul_le_mul_of_nonneg_left (gaussTermF_le_gaussValueF p F hB k) zero_le
  · rw [← gaussTermF_p_mul]
    exact le_ciSup (bddAbove_gaussTermF_p_mul p F hB) (n + 1)

/-- Sums of boundedly-termed vectors are boundedly termed (digits of the level
representation are uniformly controlled). -/
theorem bddAbove_gaussTermF_add {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x y : WittVector p F}
    (hBx : BddAbove (Set.range (gaussTermF p F ρ x)))
    (hBy : BddAbove (Set.range (gaussTermF p F ρ y))) :
    BddAbove (Set.range (gaussTermF p F ρ (x + y))) := by
  refine ⟨max (gaussValueF p F ρ x) (gaussValueF p F ρ y), ?_⟩
  rintro z ⟨j, rfl⟩
  obtain ⟨b, L, hrep, hb, -⟩ := exists_level_repF p F hρ0 hρ1 hBx hBy (j + 1)
  have hcoeff : teichCoeffF p F (x + y) j = b j := by
    rw [hrep, teichCoeffF_sum_range_add p F (N := j + 1) b _ (Nat.lt_succ_self j)]
  rw [gaussTermF, hcoeff]
  exact hb j (Nat.lt_succ_self j)

/-- Boundedness for Teichmüller differences (any pair, via `ϖ`-power scaling). -/
theorem bddAbove_gaussTermF_teichmuller_sub {ρ : NNReal} (hρ1 : ρ < 1)
    (ϖ : PseudoUniformizer F) (a b : F) :
    BddAbove (Set.range (gaussTermF p F ρ
      (WittVector.teichmuller p a - WittVector.teichmuller p b))) := by
  set ϖF : F := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hϖF
  set c : NNReal := perfectoidValuation p F ϖF with hc
  have hϖne : ϖF ≠ 0 := fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hclt : c < 1 := perfectoidValuation_toOF_lt_one p F ϖ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, max (perfectoidValuation p F a) (perfectoidValuation p F b)
      ≤ (c⁻¹) ^ m := by
    rcases eq_or_ne (max (perfectoidValuation p F a) (perfectoidValuation p F b)) 0
      with h0 | hpos
    · exact ⟨0, by rw [h0, pow_zero]; exact zero_le⟩
    · have hmaxpos : 0 < (max (perfectoidValuation p F a)
          (perfectoidValuation p F b))⁻¹ :=
        inv_pos.mpr (pos_iff_ne_zero.mpr hpos)
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hmaxpos hclt
      refine ⟨m, ?_⟩
      rw [inv_pow]
      have h1 : max (perfectoidValuation p F a) (perfectoidValuation p F b) * c ^ m
          < 1 := by
        have h2 := mul_lt_mul_of_pos_left hm (pos_iff_ne_zero.mpr hpos)
        rwa [mul_inv_cancel₀ hpos] at h2
      exact le_of_lt ((NNReal.lt_inv_iff_mul_lt (pow_ne_zero m hc0.ne')).mpr h1)
  have hscale : ∀ x : F, perfectoidValuation p F x ≤ (c⁻¹) ^ m →
      perfectoidValuation p F (x * ϖF ^ m) ≤ 1 := by
    intro x hx
    rw [Valuation.map_mul, map_pow]
    calc perfectoidValuation p F x * c ^ m
        ≤ (c⁻¹) ^ m * c ^ m := mul_le_mul_of_nonneg_right hx zero_le
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc0.ne', one_pow]
  obtain ⟨ahat, hahat⟩ := (perfectoidValuation_integers p F).exists_of_le_one
    (hscale a ((le_max_left _ _).trans hm))
  obtain ⟨bhat, hbhat⟩ := (perfectoidValuation_integers p F).exists_of_le_one
    (hscale b ((le_max_right _ _).trans hm))
  have hahat' : ((ahat : OF F) : F) = a * ϖF ^ m := hahat
  have hbhat' : ((bhat : OF F) : F) = b * ϖF ^ m := hbhat
  have hsplit : WittVector.teichmuller p a - WittVector.teichmuller p b
      = WittVector.teichmuller p ((ϖF ^ m)⁻¹) *
        (WittVector.map ((powerBoundedSubring.toSubring F).subtype)
          (WittVector.teichmuller p ahat - WittVector.teichmuller p bhat)) := by
    rw [map_sub, WittVector.map_teichmuller, WittVector.map_teichmuller]
    rw [show ((powerBoundedSubring.toSubring F).subtype) ahat = ((ahat : OF F) : F) from rfl,
      show ((powerBoundedSubring.toSubring F).subtype) bhat = ((bhat : OF F) : F) from rfl,
      hahat', hbhat', mul_sub, ← map_mul, ← map_mul]
    have hϖpm : (ϖF ^ m) ≠ 0 := pow_ne_zero m hϖne
    rw [show (ϖF ^ m)⁻¹ * (a * ϖF ^ m) = a from by field_simp,
      show (ϖF ^ m)⁻¹ * (b * ϖF ^ m) = b from by field_simp]
  refine ⟨(c⁻¹) ^ m, ?_⟩
  rintro z ⟨n, rfl⟩
  rw [hsplit, gaussTermF_teichmuller_mul, gaussTermF_map]
  have hvinv : perfectoidValuation p F ((ϖF ^ m)⁻¹) = (c⁻¹) ^ m := by
    rw [map_inv₀, map_pow, inv_pow]
  rw [hvinv]
  exact mul_le_of_le_one_right zero_le (gaussTerm_le_one p F hρ1.le _ n)

/-- **Per-coordinate uniform continuity over `W(F)`** on value-bounded sets: for each
level `n`, bound scale `m`, and `ε > 0` there is `δ > 0` such that any boundedly-termed
pair with values `≤ (vϖ)⁻ᵐ` and `w_ρ(x−y) ≤ δ` has `|xₙ − yₙ| ≤ ε`. This is the
engine behind coordinates on the completion `A^r` (T903 step 4). -/
theorem exists_delta_teichCoeffF_sub (ϖ : PseudoUniformizer F) (n : ℕ) {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ x y : WittVector p F,
      BddAbove (Set.range (gaussTermF p F ρ x)) →
      BddAbove (Set.range (gaussTermF p F ρ y)) →
      BddAbove (Set.range (gaussTermF p F ρ (x - y))) →
      gaussValueF p F ρ x ≤ ((perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m →
      gaussValueF p F ρ y ≤ ((perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ m →
      gaussValueF p F ρ (x - y) ≤ δ →
      perfectoidValuation p F (teichCoeffF p F x n - teichCoeffF p F y n) ≤ ε := by
  induction n generalizing m ε with
  | zero =>
    refine ⟨ε, hε0, fun x y hBx hBy hBxy hVx hVy hab => ?_⟩
    have h00 : teichCoeffF p F x 0 - teichCoeffF p F y 0 = teichCoeffF p F (x - y) 0 := by
      rw [teichCoeffF, teichCoeffF, teichCoeffF]
      simp only [pow_zero]
      exact (RingHom.map_sub WittVector.constantCoeff x y).symm
    rw [h00]
    have hterm : perfectoidValuation p F (teichCoeffF p F (x - y) 0)
        = gaussTermF p F ρ (x - y) 0 := by
      rw [gaussTermF, pow_zero, one_mul]
    rw [hterm]
    exact (gaussTermF_le_gaussValueF p F hBxy 0).trans hab
  | succ n ih =>
    set c : NNReal := perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hcdef
    have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
      fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
    have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
    have hclt : c < 1 := perfectoidValuation_toOF_lt_one p F ϖ
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hρ0 hclt
    obtain ⟨δn, hδn0, hδn⟩ := ih (m + K) hε0 hε1
    obtain ⟨δT, hδT0, hδT⟩ := gaussValueF_teichmuller_sub_le_of_le_scaled p F hρ0 hρ1 ϖ m
      (ε := min (ρ * δn) 1) (lt_min (mul_pos hρ0 hδn0) one_pos) (min_le_right _ _)
    refine ⟨min (min δT (ρ * δn)) 1,
      lt_min (lt_min hδT0 (mul_pos hρ0 hδn0)) one_pos,
      fun x y hBx hBy hBxy hVx hVy hab => ?_⟩
    obtain ⟨x', hx'eq, hx'c⟩ := exists_head_splitF p F x
    obtain ⟨y', hy'eq, hy'c⟩ := exists_head_splitF p F y
    have hpx : (p : WittVector p F) * x'
        = x - WittVector.teichmuller p (teichCoeffF p F x 0) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hx'eq.symm)
    have hpy : (p : WittVector p F) * y'
        = y - WittVector.teichmuller p (teichCoeffF p F y 0) :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hy'eq.symm)
    have hsub : (p : WittVector p F) * (x' - y')
        = (x - y) + (WittVector.teichmuller p (teichCoeffF p F y 0)
          - WittVector.teichmuller p (teichCoeffF p F x 0)) := by
      rw [mul_sub, hpx, hpy]
      ring
    -- head values are within the scale
    have hheadx : perfectoidValuation p F (teichCoeffF p F x 0) ≤ (c⁻¹) ^ m := by
      have h0 := gaussTermF_le_gaussValueF p F hBx 0
      rw [gaussTermF, pow_zero, one_mul] at h0
      exact h0.trans hVx
    have hheady : perfectoidValuation p F (teichCoeffF p F y 0) ≤ (c⁻¹) ^ m := by
      have h0 := gaussTermF_le_gaussValueF p F hBy 0
      rw [gaussTermF, pow_zero, one_mul] at h0
      exact h0.trans hVy
    -- head difference is small
    have hhead0 : perfectoidValuation p F
        (teichCoeffF p F y 0 - teichCoeffF p F x 0) ≤ δT := by
      have h00 : teichCoeffF p F y 0 - teichCoeffF p F x 0
          = teichCoeffF p F (y - x) 0 := by
        rw [teichCoeffF, teichCoeffF, teichCoeffF]
        simp only [pow_zero]
        exact (RingHom.map_sub WittVector.constantCoeff y x).symm
      have hyx : y - x = -(x - y) := by ring
      have hcoords : ∀ k, teichCoeffF p F (y - x) k = teichCoeffF p F (y - x) k :=
        fun _ => rfl
      -- |(y−x)₀| = |(x−y)₀| : digit-0 is additive so it is exact negation
      have hneg0 : teichCoeffF p F (y - x) 0 = -(teichCoeffF p F (x - y) 0) := by
        rw [teichCoeffF, teichCoeffF]
        simp only [pow_zero]
        have := RingHom.map_neg WittVector.constantCoeff (x - y)
        rw [show (-(x - y)) = y - x from by ring] at this
        exact this
      rw [h00, hneg0, Valuation.map_neg]
      have hterm : perfectoidValuation p F (teichCoeffF p F (x - y) 0)
          = gaussTermF p F ρ (x - y) 0 := by
        rw [gaussTermF, pow_zero, one_mul]
      rw [hterm]
      exact (gaussTermF_le_gaussValueF p F hBxy 0).trans
        (hab.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hT := hδT _ _ hheady hheadx hhead0
    -- the p-scaled tail difference
    have hBTsub := bddAbove_gaussTermF_teichmuller_sub p F hρ1 ϖ
      (teichCoeffF p F y 0) (teichCoeffF p F x 0)
    have hBS : BddAbove (Set.range (gaussTermF p F ρ ((x - y)
        + (WittVector.teichmuller p (teichCoeffF p F y 0)
          - WittVector.teichmuller p (teichCoeffF p F x 0))))) :=
      bddAbove_gaussTermF_add p F hρ0 hρ1 hBxy hBTsub
    have hBxy' : BddAbove (Set.range (gaussTermF p F ρ (x' - y'))) := by
      refine bddAbove_gaussTermF_of_tail p F hρ0 (x := (p : WittVector p F) * (x' - y'))
        (fun k => (teichCoeffF_p_mul p F (x' - y') k).symm) ?_
      rw [hsub]
      exact hBS
    have hw : ρ * gaussValueF p F ρ (x' - y') ≤ ρ * δn := by
      rw [← gaussValueF_p_mul p F hBxy', hsub]
      refine (gaussValueF_add_le p F hρ0 hρ1 hBxy hBTsub).trans (max_le
        (hab.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (hT.trans (min_le_left _ _)))
    have hxy' : gaussValueF p F ρ (x' - y') ≤ δn := le_of_mul_le_mul_left hw hρ0
    -- tail hypotheses for the inductive step
    have hBx' : BddAbove (Set.range (gaussTermF p F ρ x')) :=
      bddAbove_gaussTermF_of_tail p F hρ0 hx'c hBx
    have hBy' : BddAbove (Set.range (gaussTermF p F ρ y')) :=
      bddAbove_gaussTermF_of_tail p F hρ0 hy'c hBy
    have hscaleup : ∀ z' z : WittVector p F,
        (∀ k, teichCoeffF p F z' k = teichCoeffF p F z (k + 1)) →
        BddAbove (Set.range (gaussTermF p F ρ z)) →
        gaussValueF p F ρ z ≤ (c⁻¹) ^ m →
        gaussValueF p F ρ z' ≤ (c⁻¹) ^ (m + K) := by
      intro z' z hzc hBz hVz
      have h1 : ρ * gaussValueF p F ρ z' ≤ (c⁻¹) ^ m :=
        (mul_gaussValueF_le_of_tail p F hBz hzc).trans hVz
      have h2 : (c⁻¹) ^ m = (c⁻¹) ^ (m + K) * c ^ K := by
        rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0.ne', one_pow, mul_one]
      have h3 : ρ * gaussValueF p F ρ z' ≤ (c⁻¹) ^ (m + K) * ρ := by
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left hK.le zero_le)
      rw [mul_comm ((c⁻¹) ^ (m + K)) ρ] at h3
      exact le_of_mul_le_mul_left h3 hρ0
    have hres := hδn x' y' hBx' hBy' hBxy'
      (hscaleup x' x hx'c hBx hVx) (hscaleup y' y hy'c hBy hVy) hxy'
    rwa [hx'c n, hy'c n] at hres

end FarguesFontaine

end
