/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (unmerged tail of
PhD/PR'd/MvGaussNorm.lean + PhD/ToPR/MvGaussNorm.lean), building on the merged
`Mathlib.RingTheory.MvPowerSeries.GaussNorm`.
-/
import Mathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.WithAbs
import «Adic spaces».Vendored.CoramMvRestricted

/-! # Gauss norm extras: submultiplicativity, achieved norms, multiplicativity (vendored) -/

namespace MvPowerSeries

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ)

section Semiring

variable [Semiring R] (f : MvPowerSeries σ R)
private lemma foo (hc : 0 ≤ c) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))

-- reduce NormedGroup with IsUltraMetric dist to a function with vUltra hypothesis

-- this is a weakening of `Finset.Nonempty.norm_sum_le_sup'_norm`
lemma Finset.Nonempty.map_sum_le_sup'_map
    {α S : Type*} [Semiring S] [LinearOrder S] [AddCommMonoid α] (g : α → S)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → α)
    (Ultra : ∀ a b, g (a + b) ≤ max (g a) (g b)) :
    g (∑ i ∈ s, f i) ≤ s.sup' hs fun x ↦ g (f x) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total (g (∑ i ∈ s, f i)) (g (f j))).imp ?_ ?_ <;> intro h
      · exact (Ultra _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (Ultra _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

-- this is a weakening of `exists_norm_finset_prod_le_of_nonempty`
lemma exists_map_finset_prod_le_of_nonempty {α S : Type*} [Semiring S] [LinearOrder S]
    [AddCommMonoid α] (g : α → S) {ι : Type*} {t : Finset ι} (ht : t.Nonempty) (f : ι → α)
    (Ultra : ∀ a b, g (a + b) ≤ max (g a) (g b)) : ∃ i ∈ t, g (∑ j ∈ t, f j) ≤ g (f i) := by
  simpa [Finset.le_sup'_iff] using Finset.Nonempty.map_sum_le_sup'_map g ht f Ultra

-- this is a weakening of `exists_norm_multiset_prod_le`
lemma exists_map_multiset_prod_le {α S : Type*} [Semiring S] [LinearOrder S]
    [AddCommMonoid α] (g : α → S) {ι : Type*} (Zero : g 0 = 0) (Nonneg : ∀ a, g a ≥ 0)
    (Ultra : ∀ a b, g (a + b) ≤ max (g a) (g b)) (t : Finset ι) [Nonempty ι]
    (f : ι → α) : ∃ i, (t.Nonempty → i ∈ t) ∧ g (∑ j ∈ t, f j) ≤ g (f i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [Zero, Nonneg]
  · exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <|
      exists_map_finset_prod_le_of_nonempty g ht f Ultra

lemma gaussNorm_mul_le (f g : MvPowerSeries σ R) (hc : 0 ≤ c) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g := by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    change (v (coeff t (f * g)) * t.prod fun x1 x2 ↦ c x1 ^ x2) ≤
      (⨆ t, v (coeff t f) * t.prod fun x1 x2 ↦ c x1 ^ x2) *
      ⨆ t, v (coeff t g) * t.prod fun x1 x2 ↦ c x1 ^ x2
    obtain ⟨k, hk, hsum⟩ := exists_map_multiset_prod_le v vZero vNonneg vUltra
      (Finset.antidiagonal t) (fun a ↦ coeff a.1 f * coeff a.2 g)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk
        (Finset.nonempty_def.mpr ⟨(t, 0), by simp⟩)
    have hprod : t.prod (c · ^ ·) = k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·) := by
      simp only [← hk', pow_zero, implies_true, pow_add, Finsupp.prod_add_index']
    simp_rw [hprod]
    refine (mul_le_mul hsum (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2)) (vNonneg _)).trans
      ?_
    have : v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) ≤
        (v (coeff k.1 f) * k.1.prod (c · ^ ·)) * (v (coeff k.2 g) * k.2.prod (c · ^ ·)) := by
      calc
      _ ≤ v (coeff k.1 f) * v (coeff k.2 g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
        mul_le_mul (vMul _ _) (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2))
          (mul_nonneg (vNonneg _) (vNonneg _))
      _ = _ := by ring
    exact this.trans (mul_le_mul (le_gaussNorm v c f hbfd k.1) (le_gaussNorm v c g hbgd k.2)
      (mul_nonneg (vNonneg _) (foo c hc k.2)) (gaussNorm_nonneg v c f vNonneg))
  · exact mul_nonneg (gaussNorm_nonneg v c f vNonneg) (gaussNorm_nonneg v c g vNonneg)

end Semiring

variable [Ring R] (f : MvPowerSeries σ R)

/-- Predicate for when the gaussNorm is achieved by an index. -/
def AchievesGaussNorm (i : σ →₀ ℕ) : Prop :=
  v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f
section absoluteValue

lemma ultrametric_strict {α S : Type*} [Semiring S] [LinearOrder S] [AddCommGroup α]
    (f : α → S) (Ultra : ∀ a b, f (a + b) ≤ max (f a) (f b))
    (Neg : ∀ a, f a = f (-a)) {a b : α}
    (hne : f a ≠ f b) : f (a + b) = max (f a) (f b) := by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (Ultra a b)
  rcases le_max_iff.mp (Ultra (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [Neg b] using hab))

-- this is a version of Fabrizio's apply_sum_eq_of_lt (in Algebra/Order/Ring/IsNonarchimedean)
-- but in our generality of function f + hypothesis
lemma apply_sum_eq_of_lt {α β S : Type*} [Semiring S] [LinearOrder S]
    [AddCommGroup α] (f : α → S) (Ultra : ∀ a b, f (a + b) ≤ max (f a) (f b)) {s : Finset β}
    {l : β → α} (Neg : ∀ a, f a = f (-a)) {k : β} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)) :
    f (∑ i ∈ s, l i) = f (l k) := by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := (Finset.Nonempty.map_sum_le_sup'_map f hNonempty l Ultra)
    simp only [Finset.le_sup'_iff, Finset.mem_erase, ne_eq] at hrest_le
    rw [ultrametric_strict f Ultra Neg (by grind), max_eq_left (le_of_lt (by grind))]

lemma antidiagonal_dominant [DecidableEq σ] (f g : MvPowerSeries σ R) (i j : σ →₀ ℕ)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vNeg : ∀ a, v a = v (-a))
    (hdom : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    v (coeff (i + j) (f * g))  = v (coeff i f * coeff j g) := by
  rw [← vMulEq] at hdom
  rw [coeff_mul, apply_sum_eq_of_lt v vUltra (by grind) (k := (i, j))
    (s := Finset.antidiagonal (i + j)) (Finset.mem_antidiagonal.mpr rfl) hdom]

lemma gaussNorm_le_mul [DecidableEq σ] (f g : MvPowerSeries σ R)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) := by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _  = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀, ← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          have hprod : (i₀ + j₀).prod (c · ^ ·) = i₀.prod (c · ^ ·) * j₀.prod (c · ^ ·) := by
            simp [Finsupp.prod_add_index', pow_add]
          rw [hprod]; ring
    _ = v (coeff i₀ f * coeff j₀ g) * (i₀ + j₀).prod (c · ^ ·) := by rw [vMulEq]
    _ = v (coeff (i₀ + j₀) (f * g)) * (i₀ + j₀).prod (c · ^ ·) := by
      rw [antidiagonal_dominant v f g i₀ j₀ vUltra vMulEq vNeg hdom']
    _ ≤ gaussNorm v c (f * g) := le_gaussNorm v c (f * g) hbfg (i₀ + j₀)

end absoluteValue






lemma gaussNorm_neg [Ring R] (vNeg : ∀ x, v (-x) = v x) (f : MvPowerSeries σ R) :
    gaussNorm v c (-f) = gaussNorm v c f  := by
  simp_rw [gaussNorm]
  have (t : σ →₀ ℕ) : (coeff t) (-f) = - (coeff t) (f) := by rfl
  simp_rw [this, vNeg]

lemma gaussNorm_mul_eq_mul [Ring R] [DecidableEq σ] (f g : MvPowerSeries σ R)
    (hf : HasGaussNorm v c f) (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : ∀ a, v a ≥ 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : ∀ (a b : R), v (a * b) = v a * v b) (vNeg : ∀ (a : R), v (-a) = v a)
    (h_eq_zero : ∀ (x : R), v x = 0 → x = 0) (hc : ∀ (i : σ), 0 < c i)
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) → v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g := by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c g vZero vNonneg h_eq_zero hc hg
    grind
  apply ge_antisymm_iff.mpr
  constructor
  · exact gaussNorm_le_mul v c f g vMulEq vNA (by grind) hfg hdom
  · exact gaussNorm_mul_le v c f g (StrongLT.le hc) vNonneg (by grind) vNA vZero hf hg

end MvPowerSeries
