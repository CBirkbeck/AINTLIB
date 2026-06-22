module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkWitt
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.RingTheory.Nilpotent.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Basic.ThetaTruncProductExpansion

/-!
# Basic Dwork factorization algebra

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- A correction factor at a natural multiple of the nilpotent parameter is
the corresponding natural power of the base correction factor. -/
theorem rescale_exp_trunc_eval₂_natCast_mul_eq_pow
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ : A) (hδ : δ ^ (N + 1) = 0) (t : ℕ) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) =
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ) ^ t := by
  classical
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  have hprod :=
    rescale_exp_trunc_eval₂_finset_prod_eq_sum
      (r := r) (φ := φ) (N := N) (δ := δ) hδ
      (s := (Finset.univ : Finset (Fin t))) (u := fun _ : Fin t => (1 : A))
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A))
        =
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ∑ i : Fin t, (1 : A)) := by
          simp
    _ = ∏ i : Fin t,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (1 : A)) := by
          simpa [Rps] using hprod.symm
    _ = ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) δ) ^ t := by
          simp

/-- Variant of `rescale_exp_trunc_eval₂_natCast_mul_eq_pow` with an extra
argument factor kept outside the natural scalar. -/
theorem rescale_exp_trunc_eval₂_mul_natCast_mul_eq_pow
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ : A) (hδ : δ ^ (N + 1) = 0) (x : A) (t : ℕ) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * ((t : A) * x)) =
      ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x)) ^ t := by
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  have hδx : (δ * x) ^ (N + 1) = 0 := by
    rw [mul_pow, hδ, zero_mul]
  have h :=
    rescale_exp_trunc_eval₂_natCast_mul_eq_pow
      (r := r) (φ := φ) (N := N) (δ := δ * x) hδx t
  have harg : (δ * x) * (t : A) = δ * ((t : A) * x) := by
    ring
  simpa [Rps, harg] using h

/-- A shifted finite Frobenius orbit sum is unchanged when the endpoint wraps
back to the first term. -/
theorem sum_range_pow_shift_eq_of_pow_period
    {A : Type*} [CommSemiring A] (z : A) (r f : ℕ)
    (hperiod : z ^ (r ^ f) = z) :
    (∑ i ∈ Finset.range f, z ^ (r ^ (i + 1))) =
      ∑ i ∈ Finset.range f, z ^ (r ^ i) := by
  cases f with
  | zero =>
      simp
  | succ f =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp [hperiod]

/-- A finite sum over a cyclically shifted range is unchanged when the
last shifted term equals the first term. -/
theorem sum_range_shift_eq_of_last_eq_first
    {A : Type*} [AddCommMonoid A] (g : ℕ → A) (f : ℕ)
    (hperiod : g f = g 0) :
    (∑ i ∈ Finset.range f, g (i + 1)) =
      ∑ i ∈ Finset.range f, g i := by
  cases f with
  | zero =>
      simp
  | succ f =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp [hperiod]

/-- A finite sum over a cyclic range is unchanged by any finite shift. -/
theorem sum_range_shift_iterate_eq_of_period
    {A : Type*} [AddCommMonoid A] (g : ℕ → A) (f m : ℕ)
    (hperiod : ∀ n : ℕ, g (n + f) = g n) :
    (∑ i ∈ Finset.range f, g (i + m)) =
      ∑ i ∈ Finset.range f, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (∑ i ∈ Finset.range f, g (i + (m + 1)))
            = ∑ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) (i + 1) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              congr 1
              omega
        _ = ∑ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) i := by
              refine sum_range_shift_eq_of_last_eq_first
                (fun n : ℕ => g (n + m)) f ?_
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod m
        _ = ∑ i ∈ Finset.range f, g i := ih

/-- Product analogue of `sum_range_pow_shift_eq_of_pow_period`. -/
theorem prod_range_pow_shift_eq_of_pow_period
    {A : Type*} [CommMonoid A] (z : A) (r f : ℕ)
    (hperiod : z ^ (r ^ f) = z) :
    (∏ i ∈ Finset.range f, z ^ (r ^ (i + 1))) =
      ∏ i ∈ Finset.range f, z ^ (r ^ i) := by
  cases f with
  | zero =>
      simp
  | succ f =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ']
      simp [hperiod]

/-- A finite product over a cyclically shifted range is unchanged when the
last shifted term equals the first term. -/
theorem prod_range_shift_eq_of_last_eq_first
    {A : Type*} [CommMonoid A] (g : ℕ → A) (f : ℕ)
    (hperiod : g f = g 0) :
    (∏ i ∈ Finset.range f, g (i + 1)) =
      ∏ i ∈ Finset.range f, g i := by
  cases f with
  | zero =>
      simp
  | succ f =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ']
      simp [hperiod]

/-- A finite product over a cyclic range is unchanged by any finite shift. -/
theorem prod_range_shift_iterate_eq_of_period
    {A : Type*} [CommMonoid A] (g : ℕ → A) (f m : ℕ)
    (hperiod : ∀ n : ℕ, g (n + f) = g n) :
    (∏ i ∈ Finset.range f, g (i + m)) =
      ∏ i ∈ Finset.range f, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (∏ i ∈ Finset.range f, g (i + (m + 1)))
            = ∏ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) (i + 1) := by
              refine Finset.prod_congr rfl ?_
              intro i _hi
              congr 1
              omega
        _ = ∏ i ∈ Finset.range f, (fun n : ℕ => g (n + m)) i := by
              refine prod_range_shift_eq_of_last_eq_first
                (fun n : ℕ => g (n + m)) f ?_
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod m
        _ = ∏ i ∈ Finset.range f, g i := ih

theorem fin_lowerSum_castSucc_eq
    {A : Type*} [AddCommMonoid A] {n : ℕ} (u : Fin (n + 1) → A) (i : Fin n) :
    (∑ j ∈ (Finset.univ.filter (fun j : Fin (n + 1) => j < i.castSucc)), u j) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)), u j.castSucc := by
  have hleft :
      (Finset.univ.filter (fun j : Fin (n + 1) => j < i.castSucc)) =
        Finset.Iio i.castSucc := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  have hright :
      (Finset.univ.filter (fun j : Fin n => j < i)) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  rw [hleft, hright, Fin.Iio_castSucc]
  simpa using (Finset.sum_map (Finset.Iio i) Fin.castSuccEmb u)

theorem fin_lowerSum_last_eq
    {A : Type*} [AddCommMonoid A] {n : ℕ} (u : Fin (n + 1) → A) :
    (∑ j ∈ (Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.last n)), u j) =
      ∑ j : Fin n, u j.castSucc := by
  have hleft :
      (Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.last n)) =
        Finset.Iio (Fin.last n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  rw [hleft, Fin.Iio_last_eq_map]
  exact Finset.sum_map (Finset.univ : Finset (Fin n)) Fin.castSuccEmb u

/-- Square of a finite `Fin`-sum, written with the strict-lower triangular
pair sum used by the second-order theta-product expansion. -/
theorem fin_sum_sq_eq_sum_sq_add_two_lower
    {A : Type*} [CommSemiring A] (n : ℕ) (u : Fin n → A) :
    (∑ i : Fin n, u i) ^ 2 =
      (∑ i : Fin n, u i ^ 2) +
        (2 : A) * ∑ i : Fin n,
          u i * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), u j := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let v : Fin n → A := fun i => u i.castSucc
      have ihv := ih v
      have hsum :
          (∑ i : Fin (n + 1), u i) = (∑ i : Fin n, v i) + u (Fin.last n) := by
        simpa [v] using Fin.sum_univ_castSucc u
      have hsumsq :
          (∑ i : Fin (n + 1), u i ^ 2) =
            (∑ i : Fin n, v i ^ 2) + u (Fin.last n) ^ 2 := by
        simpa [v] using Fin.sum_univ_castSucc (fun i : Fin (n + 1) => u i ^ 2)
      have hpair :
          (∑ i : Fin (n + 1),
            u i * ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j < i), u j) =
            (∑ i : Fin n,
              v i * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), v j) +
              u (Fin.last n) * ∑ i : Fin n, v i := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _hi
          simp [v, fin_lowerSum_castSucc_eq u i]
        · simp [v, fin_lowerSum_last_eq u]
      rw [hsum, hsumsq, hpair]
      rw [show ((∑ i : Fin n, v i) + u (Fin.last n)) ^ 2 =
          (∑ i : Fin n, v i) ^ 2 +
            (2 : A) * (u (Fin.last n) * ∑ i : Fin n, v i) +
              u (Fin.last n) ^ 2 by ring]
      rw [ihv]
      ring

theorem two_mul_nat_choose_two_cast
    {A : Type*} [Ring A] (t : ℕ) :
    (2 : A) * (Nat.choose t 2 : A) = (t : A) * ((t : A) - 1) := by
  have h := congrArg (fun n : ℕ => (n : A)) (Nat.descFactorial_eq_factorial_mul_choose t 2)
  change ((t.descFactorial 2 : ℕ) : A) =
    ((Nat.factorial 2 * Nat.choose t 2 : ℕ) : A) at h
  rw [Nat.cast_descFactorial_two (S := A), Nat.factorial_two, Nat.cast_mul,
    Nat.cast_ofNat] at h
  exact h.symm

/-- Transitivity of ideal congruence, written in subtraction form. -/
theorem sub_mem_trans
    {A : Type*} [Ring A] (I : Ideal A) {x y z : A}
    (hxy : x - y ∈ I) (hyz : y - z ∈ I) :
    x - z ∈ I := by
  rw [show x - z = (x - y) + (y - z) by abel]
  exact I.add_mem hxy hyz


end Furtwaengler

end BernoulliRegular

end
