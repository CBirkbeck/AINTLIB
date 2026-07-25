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
  (mul_le_of_le_one_right zero_le' (perfectoidValuation_le_one p F _))

theorem gaussTerm_le_one {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F ρ x n ≤ 1 :=
  (gaussTerm_le p F ρ x n).trans (pow_le_one₀ zero_le' hρ1)

theorem gaussValue_le_one {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    gaussValue p F ρ x ≤ 1 :=
  ciSup_le fun n => gaussTerm_le_one p F hρ1 x n

theorem bddAbove_range_gaussTerm {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    BddAbove (Set.range (gaussTerm p F ρ x)) :=
  ⟨1, by rintro y ⟨n, rfl⟩; exact gaussTerm_le_one p F hρ1 x n⟩

@[simp]
theorem gaussValue_zero (ρ : NNReal) : gaussValue p F ρ (0 : Ainf p F) = 0 := by
  rw [gaussValue]
  refine le_antisymm (ciSup_le fun n => ?_) zero_le'
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
    · rw [hzero]; exact zero_le'
    · rw [hterm]
      exact le_ciSup (⟨ρ, by
        rintro y ⟨m, rfl⟩
        exact mul_le_of_le_one_right zero_le' (gaussTerm_le_one p F hρ1 x m)⟩ :
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
      lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' hρ1.le hn) hN⟩
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

end FarguesFontaine

end
