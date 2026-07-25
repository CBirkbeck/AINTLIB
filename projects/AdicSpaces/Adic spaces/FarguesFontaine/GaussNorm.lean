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

theorem perfectoidValuation_integers :
    (perfectoidValuation p F).Integers ↥(powerBoundedSubring.toSubring F) :=
  (IsPerfectoidField.exists_valuation (p := p) (K := F)).choose_spec

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

theorem coe_p_ne_zero : (p : Ainf p F) ≠ 0 := by
  intro h
  have h1 : ((p : Ainf p F)).coeff 1 = 1 := by
    have h2 := WittVector.teichmuller_mul_pow_coeff (p := p) (R := OF F) 1 1
    simpa using h2
  rw [h] at h1
  simp at h1

private theorem frobeniusEquiv_symm_pow_pow_cancel (b : OF F) (j : ℕ) :
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
      ext m; simp [Nat.lt_succ_iff]
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

private theorem nnreal_mul_max (s a b : NNReal) : s * max a b = max (s * a) (s * b) := by
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

end FarguesFontaine

end
