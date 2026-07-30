/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.AinfHuber

/-!
# The weighted Gauss value on A_inf

For a perfectoid field `F` of characteristic `p` with rank-1 valuation `v` (the class
field `IsPerfectoidField.exists_valuation`), and a weight `ρ ∈ (0,1)`, every
`x ∈ A_inf = W(O_F)` has Teichmüller coordinates `a_n = θ^{-n}(x_n)` (θ the Frobenius
of `O_F`), and we define the **weighted Gauss value**

`gaussValue ρ x = ⨆ n, ρ^n · v (a_n)`.

This is Kedlaya's `λ_t` from *Noetherian properties of Fargues–Fontaine curves*
(arXiv:1410.5160, formula (2.2.1)) in the untwisted normalization
`w_ρ = λ_t^{1/t}`, `ρ = p^{-1/t}` (an order- and multiplication-preserving
renormalization, so Lemma 2.3 transfers; convention validated by the 2026-07-26
external review). The campaign uses it to produce a point of `𝒴` (`Y_nonempty`) and,
downstream, the Banach structure on the Fargues–Fontaine interval rings.

## Main definitions

* `FarguesFontaine.perfectoidValuation` : the fixed rank-1 valuation of `F`.
* `FarguesFontaine.teichCoeff x n` : the `n`-th Teichmüller coordinate `θ^{-n}(x_n)`.
* `FarguesFontaine.gaussValue ρ x` : the weighted Gauss value.

## Main results (this file: T801 basics)

* `gaussValue_le_one`, `gaussValue_zero`, `gaussValue_one`,
  `gaussValue_teichmuller`, `gaussValue_p_mul` (`w(p·x) = ρ·w(x)`),
  `exists_gaussValue_eq_gaussTerm` (the sup is attained for `ρ < 1`).

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff]
  Definition 2.2, formula (2.2.1), Lemma 2.3.
* [Kedlaya, AWS 2017][kedlaya-aws], Definition 2.6.2 and Remark 2.6.3.
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- The fixed rank-1 valuation of the perfectoid field `F`, with integer ring `F°`
(Wedhorn Prop 6.1 packaged in the `IsPerfectoidField` class). -/
def perfectoidValuation : Valuation F NNReal :=
  (IsPerfectoidField.exists_valuation (p := p) (K := F)).choose

omit [CharP F p] in
theorem perfectoidValuation_integers :
    (perfectoidValuation p F).Integers ↥(powerBoundedSubring.toSubring F) :=
  (IsPerfectoidField.exists_valuation (p := p) (K := F)).choose_spec

omit [CharP F p] in
/-- The valuation is `≤ 1` on `O_F`. -/
theorem perfectoidValuation_le_one (a : OF F) :
    perfectoidValuation p F (a : F) ≤ 1 :=
  (perfectoidValuation_integers p F).map_le_one a

/-- The `n`-th **Teichmüller coordinate** of `x ∈ A_inf`: `a_n = θ^{-n}(x_n)`, so that
`x = Σ p^n [a_n]` (`p`-adically). -/
def teichCoeff (x : Ainf p F) (n : ℕ) : OF F :=
  (((_root_.frobeniusEquiv (OF F) p).symm ^ n : RingAut (OF F))) (x.coeff n)

@[simp]
theorem teichCoeff_zero_vector (n : ℕ) : teichCoeff p F (0 : Ainf p F) n = 0 := by
  rw [teichCoeff, WittVector.zero_coeff, map_zero]

theorem teichCoeff_eq_zero_iff {x : Ainf p F} {n : ℕ} :
    teichCoeff p F x n = 0 ↔ x.coeff n = 0 := by
  rw [teichCoeff, map_eq_zero_iff _ (RingEquiv.injective _)]

/-- The `n`-th term of the Gauss value. -/
def gaussTerm (ρ : NNReal) (x : Ainf p F) (n : ℕ) : NNReal :=
  ρ ^ n * perfectoidValuation p F ((teichCoeff p F x n : F))

/-- The **weighted Gauss value** `w_ρ(x) = sup_n ρ^n·|a_n|`
([Kedlaya-noetherian-ff, (2.2.1)], untwisted normalization). -/
def gaussValue (ρ : NNReal) (x : Ainf p F) : NNReal :=
  ⨆ n, gaussTerm p F ρ x n

theorem gaussTerm_le (ρ : NNReal) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F ρ x n ≤ ρ ^ n :=
  (mul_le_of_le_one_right zero_le (perfectoidValuation_le_one p F _))

theorem gaussTerm_le_one {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F ρ x n ≤ 1 :=
  (gaussTerm_le p F ρ x n).trans (pow_le_one₀ zero_le hρ1)

theorem gaussValue_le_one {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    gaussValue p F ρ x ≤ 1 :=
  ciSup_le fun n => gaussTerm_le_one p F hρ1 x n

theorem bddAbove_range_gaussTerm {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    BddAbove (Set.range (gaussTerm p F ρ x)) :=
  ⟨1, by rintro y ⟨n, rfl⟩; exact gaussTerm_le_one p F hρ1 x n⟩

@[simp]
theorem gaussValue_zero (ρ : NNReal) : gaussValue p F ρ (0 : Ainf p F) = 0 := by
  rw [gaussValue]
  refine le_antisymm (ciSup_le fun n => ?_) zero_le
  simp [gaussTerm]

@[simp]
theorem gaussValue_one {ρ : NNReal} (hρ1 : ρ ≤ 1) :
    gaussValue p F ρ (1 : Ainf p F) = 1 := by
  rw [gaussValue]
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [gaussTerm, teichCoeff, WittVector.one_coeff_zero]
    · have h1 : (1 : Ainf p F).coeff n = 0 :=
        WittVector.one_coeff_eq_of_pos (p := p) (R := OF F) (n := n) (hn := hn)
      simp [gaussTerm, teichCoeff, h1]
  · refine le_trans ?_ (le_ciSup (bddAbove_range_gaussTerm p F hρ1 1) 0)
    simp [gaussTerm, teichCoeff, WittVector.one_coeff_zero]

/-- On a Teichmüller lift, the Gauss value is the valuation of the coordinate. -/
theorem gaussValue_teichmuller {ρ : NNReal} (hρ1 : ρ ≤ 1) (a : OF F) :
    gaussValue p F ρ (WittVector.teichmuller p a) = perfectoidValuation p F (a : F) := by
  rw [gaussValue]
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [gaussTerm, teichCoeff, WittVector.teichmuller_coeff_zero]
    · simp [gaussTerm, teichCoeff, WittVector.teichmuller_coeff_pos p a n hn]
  · refine le_trans ?_ (le_ciSup (bddAbove_range_gaussTerm p F hρ1 _) 0)
    simp [gaussTerm, teichCoeff, WittVector.teichmuller_coeff_zero]

/-- The `p`-shift: `w_ρ(p·x) = ρ·w_ρ(x)`. The Witt coefficients of `x·p` are
`0, x_0^p, x_1^p, …` (characteristic-`p` base), so the Teichmüller coordinates shift
by one index. -/
theorem gaussValue_p_mul {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    gaussValue p F ρ ((p : Ainf p F) * x) = ρ * gaussValue p F ρ x := by
  have hcoeff : ∀ n : ℕ, teichCoeff p F ((p : Ainf p F) * x) (n + 1)
      = teichCoeff p F x n := by
    intro n
    rw [teichCoeff, teichCoeff, show (p : Ainf p F) * x = x * (p : Ainf p F) from
      mul_comm _ _, show ((x * (p : Ainf p F)).coeff (n + 1)) = x.coeff n ^ p from
      WittVector.mul_charP_coeff_succ x n, pow_succ ((_root_.frobeniusEquiv (OF F) p).symm),
      RingAut.mul_apply]
    congr 1
    rw [show x.coeff n ^ p = _root_.frobeniusEquiv (OF F) p (x.coeff n) from rfl,
      RingEquiv.symm_apply_apply]
  have hzero : gaussTerm p F ρ ((p : Ainf p F) * x) 0 = 0 := by
    have h0 : ((p : Ainf p F) * x).coeff 0 = 0 := by
      rw [mul_comm]
      exact WittVector.mul_charP_coeff_zero x
    simp [gaussTerm, teichCoeff, h0]
  have hterm : ∀ n : ℕ, gaussTerm p F ρ ((p : Ainf p F) * x) (n + 1)
      = ρ * gaussTerm p F ρ x n := by
    intro n
    rw [gaussTerm, gaussTerm, hcoeff, pow_succ]
    ring
  rw [gaussValue, gaussValue, NNReal.mul_iSup]
  refine le_antisymm (ciSup_le fun n => ?_) (ciSup_le fun n => ?_)
  · rcases n with - | n
    · rw [hzero]; exact zero_le
    · rw [hterm]
      exact le_ciSup (⟨ρ, by
        rintro y ⟨m, rfl⟩
        exact mul_le_of_le_one_right zero_le (gaussTerm_le_one p F hρ1 x m)⟩ :
          BddAbove (Set.range fun m => ρ * gaussTerm p F ρ x m)) n
  · rw [← hterm]
    exact le_ciSup (bddAbove_range_gaussTerm p F hρ1 _) (n + 1)

/-- For `ρ < 1` and `x ≠ 0`, the Gauss value is attained at some index
([Kedlaya-aws, Rem. 2.6.3]: "the supremum becomes a maximum as soon as ρ < 1"). -/
theorem exists_gaussValue_eq_gaussTerm {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x : Ainf p F} (hx : x ≠ 0) :
    ∃ n : ℕ, gaussValue p F ρ x = gaussTerm p F ρ x n := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x.coeff m ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (WittVector.ext fun n => by rw [hall n, WittVector.zero_coeff])
  have hpos : 0 < gaussTerm p F ρ x m := by
    rw [gaussTerm]
    refine mul_pos (pow_pos hρ0 m) (pos_iff_ne_zero.mpr fun h0 => hm ?_)
    have hcoe : (teichCoeff p F x m : F) = 0 :=
      (Valuation.zero_iff (perfectoidValuation p F)).mp h0
    exact (teichCoeff_eq_zero_iff p F).mp (Subtype.ext hcoe)
  set t := gaussTerm p F ρ x m with ht
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ρ ^ n < t := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hρ1
    exact ⟨N, fun n hn =>
      lt_of_le_of_lt (pow_le_pow_of_le_one zero_le hρ1.le hn) hN⟩
  have hbig : ∀ n ≥ N, gaussTerm p F ρ x n < t :=
    fun n hn => lt_of_le_of_lt (gaussTerm_le p F ρ x n) (hN n hn)
  obtain ⟨n₀, hn₀mem, hn₀max⟩ := (Finset.range (N + 1)).exists_max_image
    (gaussTerm p F ρ x) ⟨m, Finset.mem_range.mpr (by
      by_contra hmN
      push Not at hmN
      exact absurd (hbig m (by omega)) (lt_irrefl t))⟩
  refine ⟨n₀, le_antisymm (ciSup_le fun n => ?_)
    (le_ciSup (bddAbove_range_gaussTerm p F hρ1.le x) n₀)⟩
  rcases lt_or_ge n (N + 1) with hn | hn
  · exact hn₀max n (Finset.mem_range.mpr hn)
  · refine le_trans (hbig n (by omega)).le ?_
    exact hn₀max m (Finset.mem_range.mpr (by
      by_contra hmN
      push Not at hmN
      exact absurd (hbig m (by omega)) (lt_irrefl t)))

/-!
Expansion-uniqueness layer (toolkit for the ultrametric inequality, after
[Kedlaya, *New methods for (φ,Γ)-modules*, arXiv:1004.0466] §3–4): `A_inf`-elements
have unique `p`-adic Teichmüller expansions, read off by `teichCoeff`.
-/

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] in
theorem coe_p_ne_zero : (p : Ainf p F) ≠ 0 := by
  intro h
  have h1 : ((p : Ainf p F)).coeff 1 = 1 := by
    have h2 := WittVector.teichmuller_mul_pow_coeff (p := p) (R := OF F) 1 1
    simpa using h2
  rw [h] at h1
  simp at h1

theorem frobeniusEquiv_symm_pow_pow_cancel (b : OF F) (j : ℕ) :
    ((_root_.frobeniusEquiv (OF F) p).symm ^ j : RingAut (OF F)) (b ^ p ^ j) = b := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hσ : (_root_.frobeniusEquiv (OF F) p).symm ((b ^ p ^ k) ^ p) = b ^ p ^ k := by
      have hfe : _root_.frobeniusEquiv (OF F) p (b ^ p ^ k) = (b ^ p ^ k) ^ p := by
        rw [_root_.frobeniusEquiv_apply, frobenius_def]
      rw [← hfe, RingEquiv.symm_apply_apply]
    rw [pow_succ ((_root_.frobeniusEquiv (OF F) p).symm) k, RingAut.mul_apply,
      show (p : ℕ) ^ (k + 1) = p ^ k * p from pow_succ p k, pow_mul, hσ, ih]

/-- Every `x ∈ A_inf` is its length-`N` Teichmüller prefix plus a `p^N`-tail. -/
theorem exists_eq_sum_teichCoeff_add (x : Ainf p F) (N : ℕ) :
    ∃ z : Ainf p F, x = (∑ i ∈ Finset.range N,
      WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i) +
      (p : Ainf p F) ^ N * z := by
  rcases N with - | n
  · exact ⟨x, by simp⟩
  · obtain ⟨w, hw⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
    refine ⟨w, ?_⟩
    have hIic : Finset.Iic n = Finset.range (n + 1) := by
      ext m; simp
    have hsum : (∑ i ∈ Finset.range (n + 1),
        WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i)
        = ∑ i ≤ n, WittVector.teichmuller p
            (((_root_.frobeniusEquiv (OF F) p).symm ^ i) (x.coeff i)) * (p : Ainf p F) ^ i := by
      rw [← hIic]
      exact Finset.sum_congr rfl fun i _ => by rw [teichCoeff]
    rw [hsum]
    exact sub_eq_iff_eq_add'.mp hw

/-- **Uniqueness of Teichmüller expansions**: the first `N` Teichmüller coordinates of
`Σ_{i<N} [b_i]·p^i + p^N·z` are exactly `b_0, …, b_{N-1}`. -/
theorem teichCoeff_sum_range_add {N : ℕ} (b : ℕ → OF F) (z : Ainf p F) {j : ℕ} (hj : j < N) :
    teichCoeff p F ((∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i) + (p : Ainf p F) ^ N * z) j
      = b j := by
  have hcoeff_eq : ∀ i < N, ((∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i) + (p : Ainf p F) ^ N * z).coeff i
      = (∑ i ∈ Finset.range N, WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i).coeff i := by
    rw [WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    rw [add_sub_cancel_left, mul_comm]
    exact WittVector.mul_pow_charP_coeff_zero z hi
  have hsumcoeff : (∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i).coeff j = (b j) ^ p ^ j := by
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
  rw [teichCoeff, hcoeff_eq j hj, hsumcoeff]
  exact frobeniusEquiv_symm_pow_pow_cancel p F (b j) j

/-- **Head split**: `x = [x₀] + p·x'` where the tail `x'` has the shifted Teichmüller
coordinates of `x`. -/
theorem exists_head_split (x : Ainf p F) :
    ∃ x' : Ainf p F, x = WittVector.teichmuller p (teichCoeff p F x 0) + (p : Ainf p F) * x'
      ∧ ∀ k, teichCoeff p F x' k = teichCoeff p F x (k + 1) := by
  obtain ⟨z, hz⟩ := exists_eq_sum_teichCoeff_add p F x 1
  have h1 : x = WittVector.teichmuller p (teichCoeff p F x 0) + (p : Ainf p F) * z := by
    simpa using hz
  refine ⟨z, h1, fun k => ?_⟩
  obtain ⟨w, hw⟩ := exists_eq_sum_teichCoeff_add p F z (k + 1)
  have hmul : (p : Ainf p F) * z = (∑ i ∈ Finset.range (k + 1),
      WittVector.teichmuller p (teichCoeff p F z i) * (p : Ainf p F) ^ (i + 1)) +
      (p : Ainf p F) ^ (k + 2) * w := by
    conv_lhs => rw [hw]
    rw [mul_add, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) (by ring)
  have hpeel : (∑ i ∈ Finset.range (k + 2),
      WittVector.teichmuller p
        (Nat.casesOn i (teichCoeff p F x 0) fun i' => teichCoeff p F z i') *
        (p : Ainf p F) ^ i)
      = (∑ i ∈ Finset.range (k + 1),
          WittVector.teichmuller p (teichCoeff p F z i) * (p : Ainf p F) ^ (i + 1)) +
        WittVector.teichmuller p (teichCoeff p F x 0) := by
    rw [Finset.sum_range_succ']
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => rfl)
      (by rw [pow_zero, mul_one]; rfl)
  have hx2 : x = (∑ i ∈ Finset.range (k + 2),
      WittVector.teichmuller p
        (Nat.casesOn i (teichCoeff p F x 0) fun i' => teichCoeff p F z i') *
        (p : Ainf p F) ^ i) + (p : Ainf p F) ^ (k + 2) * w := by
    conv_lhs => rw [h1, hmul]
    rw [hpeel]
    abel
  have hj := teichCoeff_sum_range_add p F (N := k + 2)
    (fun i => Nat.casesOn i (teichCoeff p F x 0) fun i' => teichCoeff p F z i') w
    (j := k + 1) (by omega)
  rw [← hx2] at hj
  exact hj.symm

/-- **Scaling**: multiplying by a Teichmüller lift scales every Teichmüller coordinate. -/
theorem teichCoeff_teichmuller_mul (w : OF F) (s : Ainf p F) (j : ℕ) :
    teichCoeff p F (WittVector.teichmuller p w * s) j = w * teichCoeff p F s j := by
  obtain ⟨z, hz⟩ := exists_eq_sum_teichCoeff_add p F s (j + 1)
  have hws : WittVector.teichmuller p w * s = (∑ i ∈ Finset.range (j + 1),
      WittVector.teichmuller p (w * teichCoeff p F s i) * (p : Ainf p F) ^ i) +
      (p : Ainf p F) ^ (j + 1) * (WittVector.teichmuller p w * z) := by
    conv_lhs => rw [hz]
    rw [mul_add, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (by ring)
    rw [map_mul]
    ring
  rw [hws, teichCoeff_sum_range_add p F (N := j + 1) _ _ (Nat.lt_succ_self j)]

private theorem valuation_teichCoeff_teichmuller_add_le_left {a b : OF F}
    (h : perfectoidValuation p F (b : F) ≤ perfectoidValuation p F (a : F)) (j : ℕ) :
    perfectoidValuation p F ((teichCoeff p F
      (WittVector.teichmuller p a + WittVector.teichmuller p b) j : F)) ≤
      perfectoidValuation p F (a : F) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 0 := by
      have h0 : perfectoidValuation p F (b : F) = 0 := by
        refine le_antisymm ?_ zero_le
        simpa using h
      exact Subtype.ext ((Valuation.zero_iff _).mp h0)
    subst hb
    simp [teichCoeff]
  · have haF : (a : F) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have hva : perfectoidValuation p F (a : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr haF
    have hu1 : perfectoidValuation p F ((b : F) / (a : F)) ≤ 1 := by
      have hmul : perfectoidValuation p F ((b : F) / (a : F)) *
          perfectoidValuation p F (a : F) = perfectoidValuation p F (b : F) := by
        rw [← Valuation.map_mul, div_mul_cancel₀ _ haF]
      refine le_of_mul_le_mul_right ?_ (pos_iff_ne_zero.mpr hva)
      rw [one_mul]
      exact hmul.le.trans h
    obtain ⟨u, hu⟩ := (perfectoidValuation_integers p F).exists_of_le_one hu1
    have hab : a * u = b := by
      refine Subtype.ext ?_
      have hcoe : (u : F) = (b : F) / (a : F) := hu
      calc ((a * u : OF F) : F) = (a : F) * (u : F) := rfl
        _ = (a : F) * ((b : F) / (a : F)) := by rw [hcoe]
        _ = (b : F) := by rw [mul_comm, div_mul_cancel₀ _ haF]
    have hsplit : WittVector.teichmuller p a + WittVector.teichmuller p b
        = WittVector.teichmuller p a * (1 + WittVector.teichmuller p u) := by
      rw [mul_add, mul_one, ← map_mul, hab]
    rw [hsplit, teichCoeff_teichmuller_mul]
    have hcoe2 : ((a * teichCoeff p F (1 + WittVector.teichmuller p u) j : OF F) : F)
        = (a : F) * (teichCoeff p F (1 + WittVector.teichmuller p u) j : F) := rfl
    rw [hcoe2, Valuation.map_mul]
    exact mul_le_of_le_one_right zero_le (perfectoidValuation_le_one p F _)

/-- **Pair bound** (the `u = b/a` scaling trick — no Witt-polynomial homogeneity needed):
every Teichmüller coordinate of `[a] + [b]` has valuation at most `max (v a) (v b)`. -/
theorem valuation_teichCoeff_teichmuller_add_le (a b : OF F) (j : ℕ) :
    perfectoidValuation p F ((teichCoeff p F
      (WittVector.teichmuller p a + WittVector.teichmuller p b) j : F)) ≤
      max (perfectoidValuation p F (a : F)) (perfectoidValuation p F (b : F)) := by
  rcases le_total (perfectoidValuation p F (b : F)) (perfectoidValuation p F (a : F)) with h | h
  · exact le_max_of_le_left (valuation_teichCoeff_teichmuller_add_le_left p F h j)
  · rw [add_comm]
    exact le_max_of_le_right (valuation_teichCoeff_teichmuller_add_le_left p F h j)

theorem gaussTerm_le_gaussValue {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F ρ x n ≤ gaussValue p F ρ x :=
  le_ciSup (bddAbove_range_gaussTerm p F hρ1 x) n

/-- Tail bound: if `x'` carries the shifted coordinates of `x` (head split), then
`ρ·w(x') ≤ w(x)`. -/
theorem mul_gaussValue_le_of_tail {ρ : NNReal} (hρ1 : ρ ≤ 1) {x x' : Ainf p F}
    (hcoords : ∀ k, teichCoeff p F x' k = teichCoeff p F x (k + 1)) :
    ρ * gaussValue p F ρ x' ≤ gaussValue p F ρ x := by
  rw [gaussValue, NNReal.mul_iSup]
  refine ciSup_le fun k => ?_
  have heq : ρ * gaussTerm p F ρ x' k = gaussTerm p F ρ x (k + 1) := by
    rw [gaussTerm, gaussTerm, hcoords k, pow_succ]
    ring
  rw [heq]
  exact gaussTerm_le_gaussValue p F hρ1 x (k + 1)

theorem nnreal_mul_max (s a b : NNReal) : s * max a b = max (s * a) (s * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h zero_le)]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h zero_le)]

/-- The Gauss value of a two-Teichmüller sum is at most the max of the coordinate
valuations (all its coordinates are, by the pair bound). -/
theorem gaussValue_teichmuller_add_le {ρ : NNReal} (hρ1 : ρ ≤ 1) (a b : OF F) :
    gaussValue p F ρ (WittVector.teichmuller p a + WittVector.teichmuller p b)
      ≤ max (perfectoidValuation p F (a : F)) (perfectoidValuation p F (b : F)) := by
  rw [gaussValue]
  refine ciSup_le fun j => ?_
  rw [gaussTerm]
  exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hρ1)).trans
    (valuation_teichCoeff_teichmuller_add_le p F a b j)

/-- Split every member of a list at its head coordinate: the sum becomes a sum of
Teichmüller lifts plus `p` times a controlled remainder ([Kedlaya-1004.0466],
proof of Lemma 4.1, operation 1). -/
private theorem exists_list_head_split {ρ : NNReal} (hρ1 : ρ ≤ 1) (s B : NNReal)
    (L : List (Ainf p F)) (hL : ∀ w ∈ L, s * gaussValue p F ρ w ≤ B) :
    ∃ (hl : List (OF F)) (tl : List (Ainf p F)),
      L.sum = (hl.map fun h => WittVector.teichmuller p h).sum + (p : Ainf p F) * tl.sum
      ∧ (∀ h ∈ hl, s * perfectoidValuation p F (h : F) ≤ B)
      ∧ ∀ t ∈ tl, s * (ρ * gaussValue p F ρ t) ≤ B := by
  induction L with
  | nil => exact ⟨[], [], by simp, by simp, by simp⟩
  | cons w rest ih =>
    obtain ⟨hl, tl, hsum, hhl, htl⟩ := ih fun w' hw' => hL w' (by simp [hw'])
    obtain ⟨w', hw', hw'coords⟩ := exists_head_split p F w
    refine ⟨teichCoeff p F w 0 :: hl, w' :: tl, ?_, ?_, ?_⟩
    · rw [List.sum_cons, hsum, List.map_cons, List.sum_cons, List.sum_cons]
      conv_lhs => rw [hw']
      ring
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · have hv : perfectoidValuation p F ((teichCoeff p F w 0 : OF F) : F)
            ≤ gaussValue p F ρ w := by
          have h0 := gaussTerm_le_gaussValue p F hρ1 w 0
          rwa [gaussTerm, pow_zero, one_mul] at h0
        exact le_trans (mul_le_mul_of_nonneg_left hv zero_le) (hL w (by simp))
      · exact hhl h hh'
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · have htail := mul_gaussValue_le_of_tail p F hρ1 hw'coords
        exact le_trans (mul_le_mul_of_nonneg_left htail zero_le) (hL w (by simp))
      · exact htl t ht'

/-- Fold a list of Teichmüller lifts into one Teichmüller head plus `p` times a
controlled remainder ([Kedlaya-1004.0466], proof of Lemma 4.1, operation 2 iterated). -/
private theorem exists_fold_teichmuller_heads {ρ : NNReal} (hρ1 : ρ ≤ 1) (s B : NNReal)
    (l : List (OF F)) (hl : ∀ h ∈ l, s * perfectoidValuation p F (h : F) ≤ B) :
    ∃ (c : OF F) (P : List (Ainf p F)),
      (l.map fun h => WittVector.teichmuller p h).sum
        = WittVector.teichmuller p c + (p : Ainf p F) * P.sum
      ∧ s * perfectoidValuation p F (c : F) ≤ B
      ∧ ∀ w ∈ P, s * (ρ * gaussValue p F ρ w) ≤ B := by
  induction l with
  | nil =>
    refine ⟨0, [], by simp [WittVector.teichmuller_zero], ?_, by simp⟩
    simp
  | cons h t ih =>
    obtain ⟨c, P, hsum, hc, hP⟩ := ih fun h' hh' => hl h' (by simp [hh'])
    obtain ⟨G', hG', hG'coords⟩ := exists_head_split p F
      (WittVector.teichmuller p h + WittVector.teichmuller p c)
    have hmax : s * max (perfectoidValuation p F (h : F)) (perfectoidValuation p F (c : F))
        ≤ B := by
      rw [nnreal_mul_max]
      exact max_le (hl h (by simp)) hc
    have hpairval : gaussValue p F ρ
        (WittVector.teichmuller p h + WittVector.teichmuller p c)
        ≤ max (perfectoidValuation p F (h : F)) (perfectoidValuation p F (c : F)) :=
      gaussValue_teichmuller_add_le p F hρ1 h c
    refine ⟨teichCoeff p F (WittVector.teichmuller p h + WittVector.teichmuller p c) 0,
      G' :: P, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hsum, List.sum_cons]
      conv_lhs => rw [show WittVector.teichmuller p h + (WittVector.teichmuller p c
        + (p : Ainf p F) * P.sum) = (WittVector.teichmuller p h + WittVector.teichmuller p c)
        + (p : Ainf p F) * P.sum from by ring, hG']
      ring
    · refine le_trans (mul_le_mul_of_nonneg_left ?_ zero_le) hmax
      exact valuation_teichCoeff_teichmuller_add_le p F h c 0
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · have h1 := (mul_gaussValue_le_of_tail p F hρ1 hG'coords).trans hpairval
        exact le_trans (mul_le_mul_of_nonneg_left h1 zero_le) hmax
      · exact hP w hw'

/-- The level-`n` representation in the proof of the ultrametric inequality
([Kedlaya-1004.0466], (4.1.1)/(4.1.2)): `x + y` is a Teichmüller prefix whose digit
terms are bounded by `max (w x) (w y)`, plus `p^n` times a sum of controlled elements. -/
private theorem exists_level_rep {ρ : NNReal} (hρ1 : ρ ≤ 1) (x y : Ainf p F) (n : ℕ) :
    ∃ (b : ℕ → OF F) (L : List (Ainf p F)),
      x + y = (∑ i ∈ Finset.range n,
          WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i) + (p : Ainf p F) ^ n * L.sum
      ∧ (∀ i < n, ρ ^ i * perfectoidValuation p F (b i : F)
          ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y))
      ∧ ∀ w ∈ L, ρ ^ n * gaussValue p F ρ w
          ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, [x, y], by simp, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro w hw
    rw [pow_zero, one_mul]
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact le_max_left _ _
    · rcases List.mem_cons.mp hw' with rfl | hw''
      · exact le_max_right _ _
      · exact absurd hw'' (List.not_mem_nil)
  | succ n ihn =>
    obtain ⟨b, L, hrep, hb, hL⟩ := ihn
    obtain ⟨hl, tl, hsplit, hhl, htl⟩ := exists_list_head_split p F hρ1 (ρ ^ n)
      (max (gaussValue p F ρ x) (gaussValue p F ρ y)) L hL
    obtain ⟨c, P, hfold, hcbound, hPbound⟩ := exists_fold_teichmuller_heads p F hρ1 (ρ ^ n)
      (max (gaussValue p F ρ x) (gaussValue p F ρ y)) hl hhl
    refine ⟨Function.update b n c, P ++ tl, ?_, ?_, ?_⟩
    · have hpre : (∑ i ∈ Finset.range (n + 1),
          WittVector.teichmuller p (Function.update b n c i) * (p : Ainf p F) ^ i)
          = (∑ i ∈ Finset.range n,
              WittVector.teichmuller p (b i) * (p : Ainf p F) ^ i)
            + WittVector.teichmuller p c * (p : Ainf p F) ^ n := by
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
      rw [pow_succ, mul_assoc]
      rcases List.mem_append.mp hw with hw' | hw'
      · exact hPbound w hw'
      · exact htl w hw'

/-- **The ultrametric inequality** for the weighted Gauss value
([Kedlaya-1004.0466, Lemma 4.1]; [Kedlaya-noetherian-ff, Lemma 2.3(a)]):
`w(x + y) ≤ max (w x) (w y)`. -/
theorem gaussValue_add_le {ρ : NNReal} (hρ1 : ρ ≤ 1) (x y : Ainf p F) :
    gaussValue p F ρ (x + y) ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y) := by
  rw [gaussValue]
  refine ciSup_le fun j => ?_
  obtain ⟨b, L, hrep, hb, -⟩ := exists_level_rep p F hρ1 x y (j + 1)
  have hcoeff : teichCoeff p F (x + y) j = b j := by
    rw [hrep, teichCoeff_sum_range_add p F (N := j + 1) b _ (Nat.lt_succ_self j)]
  rw [gaussTerm, hcoeff]
  exact hb j (Nat.lt_succ_self j)

theorem teichCoeff_p_pow_mul (x : Ainf p F) (n k : ℕ) :
    teichCoeff p F ((p : Ainf p F) ^ n * x) (n + k) = teichCoeff p F x k := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
    have hcoeff : ∀ y : Ainf p F, ∀ j : ℕ,
        teichCoeff p F ((p : Ainf p F) * y) (j + 1) = teichCoeff p F y j := by
      intro y j
      rw [teichCoeff, teichCoeff, show (p : Ainf p F) * y = y * (p : Ainf p F) from
        mul_comm _ _, show ((y * (p : Ainf p F)).coeff (j + 1)) = y.coeff j ^ p from
        WittVector.mul_charP_coeff_succ y j, pow_succ ((_root_.frobeniusEquiv (OF F) p).symm),
        RingAut.mul_apply]
      congr 1
      rw [show y.coeff j ^ p = _root_.frobeniusEquiv (OF F) p (y.coeff j) from rfl,
        RingEquiv.symm_apply_apply]
    have hsplit : (p : Ainf p F) ^ (m + 1) * x = (p : Ainf p F) * ((p : Ainf p F) ^ m * x) := by
      ring
    have harith : m + 1 + k = (m + k) + 1 := by omega
    rw [hsplit, harith, hcoeff ((p : Ainf p F) ^ m * x) (m + k), ih]

theorem gaussValue_p_pow_mul {ρ : NNReal} (hρ1 : ρ ≤ 1) (n : ℕ) (x : Ainf p F) :
    gaussValue p F ρ ((p : Ainf p F) ^ n * x) = ρ ^ n * gaussValue p F ρ x := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : (p : Ainf p F) ^ (m + 1) * x = (p : Ainf p F) * ((p : Ainf p F) ^ m * x) := by
      ring
    rw [hsplit, gaussValue_p_mul p F hρ1, ih, pow_succ]
    ring

/-- Ultrametric bound for list sums. -/
theorem gaussValue_list_sum_le {ρ : NNReal} (hρ1 : ρ ≤ 1) (B : NNReal)
    (L : List (Ainf p F)) (hL : ∀ w ∈ L, gaussValue p F ρ w ≤ B) :
    gaussValue p F ρ L.sum ≤ B := by
  induction L with
  | nil => simp
  | cons w rest ih =>
    rw [List.sum_cons]
    refine (gaussValue_add_le p F hρ1 w rest.sum).trans (max_le (hL w (by simp)) ?_)
    exact ih fun w' hw' => hL w' (by simp [hw'])

/-- Iterated head split: `x = (length-n prefix) + p^n·X` where `X` carries the
`n`-shifted Teichmüller coordinates of `x`. -/
theorem exists_iter_split (x : Ainf p F) (n : ℕ) :
    ∃ X : Ainf p F, x = (∑ i ∈ Finset.range n,
      WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i) +
      (p : Ainf p F) ^ n * X
      ∧ ∀ k, teichCoeff p F X k = teichCoeff p F x (n + k) := by
  obtain ⟨X, hX⟩ := exists_eq_sum_teichCoeff_add p F x n
  refine ⟨X, hX, fun k => ?_⟩
  have h2 : x = (∑ i ∈ Finset.range (n + (k + 1)),
      WittVector.teichmuller p
        (if h : i < n then teichCoeff p F x i else teichCoeff p F X (i - n)) *
      (p : Ainf p F) ^ i) + (p : Ainf p F) ^ (n + (k + 1)) *
      (exists_eq_sum_teichCoeff_add p F X (k + 1)).choose := by
    obtain hXk := (exists_eq_sum_teichCoeff_add p F X (k + 1)).choose_spec
    set W := (exists_eq_sum_teichCoeff_add p F X (k + 1)).choose
    have hbig : (∑ i ∈ Finset.range (n + (k + 1)),
        WittVector.teichmuller p
          (if h : i < n then teichCoeff p F x i else teichCoeff p F X (i - n)) *
        (p : Ainf p F) ^ i)
        = (∑ i ∈ Finset.range n,
            WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i)
          + (p : Ainf p F) ^ n * (∑ i ∈ Finset.range (k + 1),
            WittVector.teichmuller p (teichCoeff p F X i) * (p : Ainf p F) ^ i) := by
      rw [Finset.sum_range_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
        (Finset.sum_congr rfl fun i _ => ?_)
      · rw [dif_pos (Finset.mem_range.mp hi)]
      · rw [dif_neg (by omega)]
        have : n + i - n = i := by omega
        rw [this, pow_add]
        ring
    rw [hbig]
    conv_lhs => rw [hX]
    conv_lhs => rw [show X = (∑ i ∈ Finset.range (k + 1),
      WittVector.teichmuller p (teichCoeff p F X i) * (p : Ainf p F) ^ i) +
      (p : Ainf p F) ^ (k + 1) * W from hXk]
    rw [pow_add]
    ring
  have hj := teichCoeff_sum_range_add p F (N := n + (k + 1))
    (fun i => if h : i < n then teichCoeff p F x i else teichCoeff p F X (i - n))
    ((exists_eq_sum_teichCoeff_add p F X (k + 1)).choose) (j := n + k) (by omega)
  rw [← h2] at hj
  have hred : (if h : n + k < n then teichCoeff p F x (n + k)
      else teichCoeff p F X (n + k - n)) = teichCoeff p F X k := by
    rw [dif_neg (by omega)]
    congr 1
    omega
  rw [hj]
  simp only [hred]

/-- Ultrametric bound for finite sums. -/
theorem gaussValue_finset_sum_le {ι : Type*} {ρ : NNReal} (hρ1 : ρ ≤ 1) (B : NNReal)
    (s : Finset ι) (f : ι → Ainf p F) (hf : ∀ i ∈ s, gaussValue p F ρ (f i) ≤ B) :
    gaussValue p F ρ (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (gaussValue_add_le p F hρ1 _ _).trans (max_le (hf a (by simp)) ?_)
    exact ih fun i hi => hf i (by simp [hi])

/-- Gauss value of a single expansion term. -/
theorem gaussValue_teichmuller_mul_p_pow {ρ : NNReal} (hρ1 : ρ ≤ 1) (a : OF F) (i : ℕ) :
    gaussValue p F ρ (WittVector.teichmuller p a * (p : Ainf p F) ^ i)
      = ρ ^ i * perfectoidValuation p F (a : F) := by
  rw [mul_comm, gaussValue_p_pow_mul p F hρ1, gaussValue_teichmuller p F hρ1]

/-- **The product of two Teichmüller prefixes is bounded by the product of the Gauss
values.** Expanding the double sum, each cross term `[xᵢ]pⁱ · [yⱼ]pʲ` collapses to
`[xᵢyⱼ]p^{i+j}`, whose value is `ρ^{i+j}·|xᵢ|·|yⱼ|`; regrouping gives
`(ρⁱ|xᵢ|)·(ρʲ|yⱼ|) ≤ w(x)·w(y)`. -/
private theorem gaussValue_prefix_mul_prefix_le {ρ : NNReal} (hρ1 : ρ < 1)
    (x y : Ainf p F) (n : ℕ) :
    gaussValue p F ρ
        ((∑ i ∈ Finset.range (n + 1),
            WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i) *
          (∑ i ∈ Finset.range (n + 1),
            WittVector.teichmuller p (teichCoeff p F y i) * (p : Ainf p F) ^ i))
      ≤ gaussValue p F ρ x * gaussValue p F ρ y := by
  rw [Finset.sum_mul_sum]
  refine gaussValue_finset_sum_le p F hρ1.le _ _ _ fun i hi => ?_
  refine gaussValue_finset_sum_le p F hρ1.le _ _ _ fun j hj => ?_
  have hterm : (WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i) *
      (WittVector.teichmuller p (teichCoeff p F y j) * (p : Ainf p F) ^ j)
      = WittVector.teichmuller p (teichCoeff p F x i * teichCoeff p F y j) *
        (p : Ainf p F) ^ (i + j) := by
    rw [map_mul, pow_add]
    ring
  rw [hterm, mul_comm, gaussValue_p_pow_mul p F hρ1.le,
    gaussValue_teichmuller p F hρ1.le]
  have hvv : perfectoidValuation p F
      ((teichCoeff p F x i * teichCoeff p F y j : OF F) : F)
      = perfectoidValuation p F ((teichCoeff p F x i : OF F) : F) *
        perfectoidValuation p F ((teichCoeff p F y j : OF F) : F) := by
    rw [show ((teichCoeff p F x i * teichCoeff p F y j : OF F) : F)
      = ((teichCoeff p F x i : OF F) : F) * ((teichCoeff p F y j : OF F) : F) from rfl,
      Valuation.map_mul]
  rw [hvv, pow_add]
  have h1 : ρ ^ i * perfectoidValuation p F ((teichCoeff p F x i : OF F) : F)
      ≤ gaussValue p F ρ x := gaussTerm_le_gaussValue p F hρ1.le x i
  have h2 : ρ ^ j * perfectoidValuation p F ((teichCoeff p F y j : OF F) : F)
      ≤ gaussValue p F ρ y := gaussTerm_le_gaussValue p F hρ1.le y j
  calc ρ ^ i * ρ ^ j * (perfectoidValuation p F ((teichCoeff p F x i : OF F) : F) *
          perfectoidValuation p F ((teichCoeff p F y j : OF F) : F))
      = (ρ ^ i * perfectoidValuation p F ((teichCoeff p F x i : OF F) : F)) *
        (ρ ^ j * perfectoidValuation p F ((teichCoeff p F y j : OF F) : F)) := by ring
    _ ≤ gaussValue p F ρ x * gaussValue p F ρ y :=
        mul_le_mul h1 h2 zero_le zero_le

/-- **Submultiplicativity** ([Kedlaya-1004.0466, Lemma 4.1]): `w(x·y) ≤ w(x)·w(y)`
for `ρ < 1`. -/
theorem gaussValue_mul_le {ρ : NNReal} (hρ1 : ρ < 1) (x y : Ainf p F) :
    gaussValue p F ρ (x * y) ≤ gaussValue p F ρ x * gaussValue p F ρ y := by
  have key : ∀ n : ℕ, gaussValue p F ρ (x * y)
      ≤ max (gaussValue p F ρ x * gaussValue p F ρ y) (ρ ^ (n + 1)) := by
    intro n
    obtain ⟨X, hX, -⟩ := exists_iter_split p F x (n + 1)
    obtain ⟨Y, hY, -⟩ := exists_iter_split p F y (n + 1)
    set Px := ∑ i ∈ Finset.range (n + 1),
      WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i with hPx
    set Py := ∑ i ∈ Finset.range (n + 1),
      WittVector.teichmuller p (teichCoeff p F y i) * (p : Ainf p F) ^ i with hPy
    have hxy : x * y = Px * Py + ((p : Ainf p F) ^ (n + 1) * (Px * Y)
        + ((p : Ainf p F) ^ (n + 1) * (X * Py)
          + (p : Ainf p F) ^ (n + 1) * ((p : Ainf p F) ^ (n + 1) * (X * Y)))) := by
      conv_lhs => rw [hX, hY]
      ring
    have hPP : gaussValue p F ρ (Px * Py)
        ≤ gaussValue p F ρ x * gaussValue p F ρ y := by
      rw [hPx, hPy]
      exact gaussValue_prefix_mul_prefix_le p F hρ1 x y n
    have htail : ∀ W : Ainf p F, gaussValue p F ρ ((p : Ainf p F) ^ (n + 1) * W)
        ≤ ρ ^ (n + 1) := by
      intro W
      rw [gaussValue_p_pow_mul p F hρ1.le]
      exact mul_le_of_le_one_right zero_le (gaussValue_le_one p F hρ1.le W)
    rw [hxy]
    refine (gaussValue_add_le p F hρ1.le _ _).trans (max_le (le_max_of_le_left hPP) ?_)
    refine le_max_of_le_right ?_
    refine (gaussValue_add_le p F hρ1.le _ _).trans (max_le (htail _) ?_)
    exact (gaussValue_add_le p F hρ1.le _ _).trans (max_le (htail _) (htail _))
  by_contra hlt
  push Not at hlt
  have hpos : 0 < gaussValue p F ρ (x * y) :=
    lt_of_le_of_lt zero_le hlt
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hρ1
  have hbound := key N
  have hmax : max (gaussValue p F ρ x * gaussValue p F ρ y) (ρ ^ (N + 1))
      < gaussValue p F ρ (x * y) := by
    refine max_lt hlt (lt_of_le_of_lt ?_ hN)
    exact pow_le_pow_of_le_one zero_le hρ1.le (by omega)
  exact absurd hbound (not_le.mpr hmax)

/-- `w(-x) = w(x)`. -/
theorem gaussValue_neg {ρ : NNReal} (hρ1 : ρ < 1) (x : Ainf p F) :
    gaussValue p F ρ (-x) = gaussValue p F ρ x := by
  have h : ∀ z : Ainf p F, gaussValue p F ρ (-z) ≤ gaussValue p F ρ z := by
    intro z
    have h1 : -z = (-1 : Ainf p F) * z := by ring
    rw [h1]
    refine (gaussValue_mul_le p F hρ1 (-1) z).trans ?_
    exact mul_le_of_le_one_left zero_le (gaussValue_le_one p F hρ1.le (-1))
  refine le_antisymm (h x) ?_
  have h2 := h (-x)
  rwa [neg_neg] at h2

/-- `w(x - y) ≤ max (w x) (w y)`. -/
theorem gaussValue_sub_le {ρ : NNReal} (hρ1 : ρ < 1) (x y : Ainf p F) :
    gaussValue p F ρ (x - y) ≤ max (gaussValue p F ρ x) (gaussValue p F ρ y) := by
  rw [sub_eq_add_neg]
  refine (gaussValue_add_le p F hρ1.le x (-y)).trans ?_
  rw [gaussValue_neg p F hρ1]

/-- The isosceles principle: adding a strictly smaller element preserves the value. -/
theorem gaussValue_add_eq_of_lt {ρ : NNReal} (hρ1 : ρ < 1) {A B : Ainf p F}
    (hAB : gaussValue p F ρ B < gaussValue p F ρ A) :
    gaussValue p F ρ (A + B) = gaussValue p F ρ A := by
  refine le_antisymm ((gaussValue_add_le p F hρ1.le A B).trans
    (max_le le_rfl hAB.le)) ?_
  have hA : A = (A + B) - B := by ring
  have h1 : gaussValue p F ρ A ≤ max (gaussValue p F ρ (A + B)) (gaussValue p F ρ B) := by
    conv_lhs => rw [hA]
    exact gaussValue_sub_le p F hρ1 (A + B) B
  rcases max_cases (gaussValue p F ρ (A + B)) (gaussValue p F ρ B) with ⟨heq, -⟩ | ⟨heq, -⟩
  · rwa [heq] at h1
  · rw [heq] at h1
    exact absurd (lt_of_le_of_lt h1 hAB) (lt_irrefl _)

/-- Positivity: `x ≠ 0` gives `w(x) > 0` (for `0 < ρ ≤ 1`). -/
theorem gaussValue_pos_of_ne_zero {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {x : Ainf p F} (hx : x ≠ 0) :
    0 < gaussValue p F ρ x := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x.coeff m ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (WittVector.ext fun n => by rw [hall n, WittVector.zero_coeff])
  have hpos : 0 < gaussTerm p F ρ x m := by
    rw [gaussTerm]
    refine mul_pos (pow_pos hρ0 m) (pos_iff_ne_zero.mpr fun h0 => hm ?_)
    have hcoe : (teichCoeff p F x m : F) = 0 :=
      (Valuation.zero_iff (perfectoidValuation p F)).mp h0
    exact (teichCoeff_eq_zero_iff p F).mp (Subtype.ext hcoe)
  exact lt_of_lt_of_le hpos (gaussTerm_le_gaussValue p F hρ1 x m)

theorem teichCoeff_zero_eq (W : Ainf p F) : teichCoeff p F W 0 = W.coeff 0 := by
  rw [teichCoeff]
  simp

/-- The value of an `n`-shifted tail is at most the value of the original. -/
private theorem gaussValue_shift_tail_le {ρ : NNReal} (hρ1 : ρ ≤ 1) {x X : Ainf p F} {n : ℕ}
    (hcoords : ∀ k, teichCoeff p F X k = teichCoeff p F x (n + k)) :
    gaussValue p F ρ ((p : Ainf p F) ^ n * X) ≤ gaussValue p F ρ x := by
  rw [gaussValue_p_pow_mul p F hρ1]
  conv_lhs => rw [gaussValue, NNReal.mul_iSup]
  refine ciSup_le fun i => ?_
  have heq : ρ ^ n * gaussTerm p F ρ X i = gaussTerm p F ρ x (n + i) := by
    rw [gaussTerm, gaussTerm, hcoords i, pow_add]
    ring
  rw [heq]
  exact gaussTerm_le_gaussValue p F hρ1 x (n + i)

/-- **Multiplicativity** of the Gauss value ([Kedlaya-1004.0466, Lemma 4.1];
[Kedlaya-noetherian-ff, Lemma 2.3(b)]): `w(x·y) = w(x)·w(y)` for `0 < ρ < 1`. -/
theorem gaussValue_mul {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x y : Ainf p F) :
    gaussValue p F ρ (x * y) = gaussValue p F ρ x * gaussValue p F ρ y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hxpos := gaussValue_pos_of_ne_zero p F hρ0 hρ1.le hx
  have hypos := gaussValue_pos_of_ne_zero p F hρ0 hρ1.le hy
  have hax := exists_gaussValue_eq_gaussTerm p F hρ0 hρ1 hx
  have hay := exists_gaussValue_eq_gaussTerm p F hρ0 hρ1 hy
  set j := Nat.find hax with hjdef
  set k := Nat.find hay with hkdef
  have hjspec : gaussValue p F ρ x = gaussTerm p F ρ x j := Nat.find_spec hax
  have hkspec : gaussValue p F ρ y = gaussTerm p F ρ y k := Nat.find_spec hay
  have hjmin : ∀ i < j, gaussTerm p F ρ x i < gaussValue p F ρ x := fun i hi =>
    lt_of_le_of_ne (gaussTerm_le_gaussValue p F hρ1.le x i)
      fun heq => Nat.find_min hax hi heq.symm
  have hkmin : ∀ i < k, gaussTerm p F ρ y i < gaussValue p F ρ y := fun i hi =>
    lt_of_le_of_ne (gaussTerm_le_gaussValue p F hρ1.le y i)
      fun heq => Nat.find_min hay hi heq.symm
  obtain ⟨X, hXeq, hXcoords⟩ := exists_iter_split p F x j
  obtain ⟨Y, hYeq, hYcoords⟩ := exists_iter_split p F y k
  set x' : Ainf p F := (p : Ainf p F) ^ j * X with hx'def
  set y' : Ainf p F := (p : Ainf p F) ^ k * Y with hy'def
  have hx'le : gaussValue p F ρ x' ≤ gaussValue p F ρ x :=
    gaussValue_shift_tail_le p F hρ1.le hXcoords
  have hy'le : gaussValue p F ρ y' ≤ gaussValue p F ρ y :=
    gaussValue_shift_tail_le p F hρ1.le hYcoords
  -- the leading term of x'y' has value exactly w(x)·w(y)
  have hlead : gaussTerm p F ρ (x' * y') (j + k)
      = gaussValue p F ρ x * gaussValue p F ρ y := by
    have hprod : x' * y' = (p : Ainf p F) ^ (j + k) * (X * Y) := by
      rw [hx'def, hy'def, pow_add]
      ring
    have hcoord : teichCoeff p F (x' * y') (j + k) = teichCoeff p F (X * Y) 0 := by
      rw [hprod]
      have h0 := teichCoeff_p_pow_mul p F (X * Y) (j + k) 0
      rwa [add_zero] at h0
    have hmul0 : teichCoeff p F (X * Y) 0
        = teichCoeff p F X 0 * teichCoeff p F Y 0 := by
      rw [teichCoeff_zero_eq, teichCoeff_zero_eq, teichCoeff_zero_eq,
        WittVector.mul_coeff_zero]
    have hX0 : teichCoeff p F X 0 = teichCoeff p F x j := by
      have h1 := hXcoords 0
      rwa [add_zero] at h1
    have hY0 : teichCoeff p F Y 0 = teichCoeff p F y k := by
      have h1 := hYcoords 0
      rwa [add_zero] at h1
    rw [gaussTerm, hcoord, hmul0, hX0, hY0, hjspec, hkspec, gaussTerm, gaussTerm,
      show ((teichCoeff p F x j * teichCoeff p F y k : OF F) : F)
        = ((teichCoeff p F x j : OF F) : F) * ((teichCoeff p F y k : OF F) : F) from rfl,
      Valuation.map_mul, pow_add]
    ring
  have hlow : gaussValue p F ρ x * gaussValue p F ρ y ≤ gaussValue p F ρ (x' * y') := by
    rw [← hlead]
    exact gaussTerm_le_gaussValue p F hρ1.le _ _
  have hupp : gaussValue p F ρ (x' * y')
      ≤ gaussValue p F ρ x * gaussValue p F ρ y :=
    (gaussValue_mul_le p F hρ1 x' y').trans
      (mul_le_mul hx'le hy'le zero_le zero_le)
  have hcore : gaussValue p F ρ (x' * y') = gaussValue p F ρ x * gaussValue p F ρ y :=
    le_antisymm hupp hlow
  -- the prefixes are strictly smaller
  have hprefix : ∀ (w : Ainf p F) (n : ℕ) (W : Ainf p F),
      w = (∑ i ∈ Finset.range n,
        WittVector.teichmuller p (teichCoeff p F w i) * (p : Ainf p F) ^ i)
        + (p : Ainf p F) ^ n * W →
      (∀ i < n, gaussTerm p F ρ w i < gaussValue p F ρ w) →
      0 < gaussValue p F ρ w →
      gaussValue p F ρ (w - (p : Ainf p F) ^ n * W) < gaussValue p F ρ w := by
    intro w n W hweq hmin hwpos
    have hsub : w - (p : Ainf p F) ^ n * W = ∑ i ∈ Finset.range n,
        WittVector.teichmuller p (teichCoeff p F w i) * (p : Ainf p F) ^ i := by
      conv_lhs => rw [hweq]
      ring
    rw [hsub]
    have hB : (Finset.range n).sup (gaussTerm p F ρ w) < gaussValue p F ρ w := by
      rw [Finset.sup_lt_iff (by simpa using hwpos)]
      intro i hi
      exact hmin i (Finset.mem_range.mp hi)
    refine lt_of_le_of_lt ?_ hB
    refine gaussValue_finset_sum_le p F hρ1.le _ _ _ fun i hi => ?_
    rw [gaussValue_teichmuller_mul_p_pow p F hρ1.le]
    have : ρ ^ i * perfectoidValuation p F ((teichCoeff p F w i : OF F) : F)
        = gaussTerm p F ρ w i := rfl
    rw [this]
    exact Finset.le_sup hi
  have hxpref : gaussValue p F ρ (x - x') < gaussValue p F ρ x :=
    hprefix x j X hXeq hjmin hxpos
  have hypref : gaussValue p F ρ (y - y') < gaussValue p F ρ y :=
    hprefix y k Y hYeq hkmin hypos
  -- the perturbation is strictly below w(x)·w(y)
  have hpert : gaussValue p F ρ (x * (y - y') + (x - x') * y')
      < gaussValue p F ρ x * gaussValue p F ρ y := by
    refine lt_of_le_of_lt (gaussValue_add_le p F hρ1.le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (gaussValue_mul_le p F hρ1 x (y - y')) ?_
      exact mul_lt_mul_of_pos_left hypref hxpos
    · refine lt_of_le_of_lt (gaussValue_mul_le p F hρ1 (x - x') y') ?_
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy'le zero_le) ?_
      exact mul_lt_mul_of_pos_right hxpref hypos
  -- assemble via the isosceles principle
  have hdecomp : x * y = x' * y' + (x * (y - y') + (x - x') * y') := by
    ring
  rw [hdecomp, gaussValue_add_eq_of_lt p F hρ1 (by rw [hcore]; exact hpert), hcore]

end FarguesFontaine

end
