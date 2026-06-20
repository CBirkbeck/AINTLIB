/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution

/-!
# Polynomial Ring Structure of the p-local Hecke Ring

Shimura's Theorem 3.20: the p-local Hecke ring `R_p^{(n)}` is isomorphic to a polynomial
ring `ℤ[X₁,...,Xₙ]` in `n` variables.

## Main definitions

* `T_gen_diag` — the diagonal for the k-th generator `T(1,...,1,p,...,p)`
* `T_gen` — the k-th generator of `R_p`: `T_gen k = T(1,...,1,p,...,p)` with `k+1` entries of `p`
* `ppowWeight` — weight of a p-power diagonal: sum of exponents

## Main results

* `divChain_T_gen` — the T_gen diagonal satisfies the divisibility chain condition
* `T_gen_mem_R_p` — each generator lies in `R_p`
* `T_gen_generates_R_p` — the generators generate `R_p` (surjectivity)
* `T_gen_algebraically_independent` — the generators are algebraically independent (injectivity)
* `R_p_isPolynomialRing` — Theorem 3.20: `R_p ≅ ℤ[X₁,...,Xₙ]`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2, Theorem 3.20
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section TGen

variable (p : ℕ) (hp : p.Prime)

/-- The diagonal for the k-th generator: `(1,...,1,p,...,p)` with `n-1-k` ones
    followed by `k+1` entries of `p`. Here `k : Fin n`, giving `n` generators. -/
def T_gen_diag (k : Fin n) : Fin n → ℕ :=
  fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p

@[simp]
lemma T_gen_diag_val (k : Fin n) (i : Fin n) :
    T_gen_diag n p k i =
    if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p := rfl

/-- The T_gen diagonal satisfies the divisibility chain condition. -/
lemma divChain_T_gen (k : Fin n) : DivChain n (T_gen_diag n p k) := by
  intro i hi
  simp only [T_gen_diag_val]
  split_ifs <;> first | rfl | omega

/-- The T_gen diagonal has p-power entries (each entry is 1 = p^0 or p = p^1). -/
lemma T_gen_diag_is_ppow (k : Fin n) :
    T_gen_diag n p k =
    ppowDiag n p (fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  funext i
  simp only [T_gen_diag, ppowDiag]
  split_ifs <;> simp

/-- The exponent function for T_gen is monotone. -/
lemma T_gen_exp_monotone (k : Fin n) :
    Monotone (fun i : Fin n ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  intro i j hij
  simp only
  split_ifs <;> omega

variable [NeZero n]

include hp
/-- The k-th generator of R_p: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def T_gen (k : Fin n) : HeckeAlgebra n :=
  T_elem (T_gen_diag n p k)

/-- Each T_gen lies in R_p. -/
lemma T_gen_mem_R_p (k : Fin n) : T_gen n p k ∈ R_p n p hp := by
  have h_eq : T_gen n p k =
      T_elem (ppowDiag n p (fun i ↦ if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1)) :=
    T_elem_congr_diag (n := n) (T_gen_diag_is_ppow n p k)
  rw [h_eq]
  exact T_elem_ppow_mem_R_p n p hp _ (T_gen_exp_monotone n k)

omit hp

end TGen

section Weight

/-- Weight of a p-power diagonal: the sum of all exponents. -/
def ppowWeight (e : Fin n → ℕ) : ℕ := ∑ i, e i

end Weight

section PolynomialRing

variable [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Evaluation homomorphism: `Xₖ ↦ T_gen k`.
    Maps `ℤ[X₁,...,Xₙ]` into the Hecke algebra. -/
noncomputable def evalHom : MvPolynomial (Fin n) ℤ →+* HeckeAlgebra n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra n)) (fun k ↦ T_gen n p k)

/-- `T(1,...,1)` is the multiplicative identity in the Hecke algebra, for any `n`. -/
lemma T_elem_ones_eq_one : T_elem (fun _ : Fin n ↦ 1) = 1 := by
  show HeckeRing.T_single (GL_pair n) ℤ (T_diag (fun _ : Fin n ↦ 1)) 1 = 1
  rw [T_diag_ones]
  exact (HeckeRing.one_def (GL_pair n) (Z := ℤ)).symm

/-- `T(c,...,c)^k = T(c^k,...,c^k)`: scalar diagonal elements are closed under powers. -/
lemma T_scalar_pow (c : ℕ) (hc : 0 < c) (k : ℕ) :
    T_elem (fun _ : Fin n ↦ c) ^ k = T_elem (fun _ : Fin n ↦ c ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    symm
    exact (T_elem_congr_diag n (funext fun _ ↦ by simp)).trans (T_elem_ones_eq_one n)
  | succ k ih =>
    rw [pow_succ', ih, T_diag_scalar_mul n c hc (fun _ ↦ c ^ k) (fun _ ↦ pow_pos hc k)
      (divChain_const n _)]
    exact T_elem_congr_diag n (funext fun _ ↦ by simp only [Pi.mul_apply]; ring)

/-- Each `T_gen k` lies in the range of `evalHom`. -/
lemma T_gen_mem_evalHom_range (k : Fin n) :
    T_gen n p k ∈ (evalHom n p).range :=
  ⟨MvPolynomial.X k, MvPolynomial.eval₂Hom_X' _ _ _⟩

end PolynomialRing

end HeckeRing.GLn

namespace HeckeRing.GLn.Surj

open HeckeRing.GLn HeckeRing.GL2

/-- `T_gen 2 p 0 = T_ad 1 p`: the first generator is `T(1,p)`. -/
lemma T_gen_zero_eq_T_ad (p : ℕ) (hp : p.Prime) : T_gen 2 p (0 : Fin 2) = T_ad 1 p := by
  show T_elem (T_gen_diag 2 p 0) = _
  have h : T_gen_diag 2 p (0 : Fin 2) = ![1, p] := by
    funext i; simp only [T_gen_diag_val]; fin_cases i <;> simp
  rw [h, T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]

/-- `T_gen 2 p 1 = T_pp p`: the second generator is the diamond operator. -/
lemma T_gen_one_eq_T_pp (p : ℕ) (hp : p.Prime) : T_gen 2 p (1 : Fin 2) = T_pp p := by
  show T_elem (T_gen_diag 2 p 1) = _
  have h : T_gen_diag 2 p (1 : Fin 2) = ![p, p] := by
    funext i; simp only [T_gen_diag_val]; fin_cases i <;> simp
  rw [h, T_pp_of_pos p hp]
  exact T_elem_congr_diag (n := 2) (funext fun i ↦ by fin_cases i <;> rfl)

/-- `T_sum(p) = T_gen 0`: the sum T(p) is the first generator for p prime. -/
lemma T_sum_p_eq_T_gen_zero (p : ℕ) (hp : p.Prime) :
    T_sum ⟨p, hp.pos⟩ = T_gen 2 p (0 : Fin 2) := by
  rw [T_gen_zero_eq_T_ad p hp, T_sum_prime p hp]

private lemma X_zero_mem_range (p : ℕ) :
    T_gen 2 p (0 : Fin 2) ∈ (evalHom 2 p).range :=
  ⟨MvPolynomial.X 0, MvPolynomial.eval₂Hom_X' _ _ _⟩

private lemma X_one_mem_range (p : ℕ) :
    T_gen 2 p (1 : Fin 2) ∈ (evalHom 2 p).range :=
  ⟨MvPolynomial.X 1, MvPolynomial.eval₂Hom_X' _ _ _⟩

private lemma T_pp_mem_range (p : ℕ) (hp : p.Prime) :
    T_pp p ∈ (evalHom 2 p).range := by
  rw [← T_gen_one_eq_T_pp p hp]; exact X_one_mem_range p

/-- `T_sum(p^k)` lies in the range of the evaluation homomorphism, for all `k`. -/
lemma T_sum_ppow_in_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ ∈ (evalHom 2 p).range := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
  match k with
  | 0 =>
    rw [show T_sum ⟨p ^ 0, pow_pos hp.pos 0⟩ = T_sum 1 from by congr 1, T_sum_one]
    exact (evalHom 2 p).range.one_mem
  | 1 =>
    have h1 : T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ := by
      congr 1; exact Subtype.ext (pow_one p)
    rw [h1, T_sum_p_eq_T_gen_zero p hp]; exact X_zero_mem_range p
  | k + 2 =>
    have h_rec := T_sum_ppow_recurrence p hp (k + 1) (by omega)
    rw [show k + 1 - 1 = k from by omega, show k + 1 + 1 = k + 2 from by omega] at h_rec
    rw [h_rec, T_sum_p_eq_T_gen_zero p hp]
    exact (evalHom 2 p).range.sub_mem
      ((evalHom 2 p).range.mul_mem (X_zero_mem_range p) (ih (k + 1) (by omega)))
      ((evalHom 2 p).range.zsmul_mem
        ((evalHom 2 p).range.mul_mem (T_pp_mem_range p hp) (ih k (by omega))) (p : ℤ))

/-- `T_ad(1, p^k)` lies in the range of the evaluation homomorphism. -/
lemma T_ad_one_ppow_in_range (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_ad 1 (p ^ k) ∈ (evalHom 2 p).range := by
  match k with
  | 0 => simp only [pow_zero, T_ad_one_one]; exact (evalHom 2 p).range.one_mem
  | 1 => rw [pow_one, ← T_gen_zero_eq_T_ad p hp]; exact X_zero_mem_range p
  | k + 2 =>
    rw [T_ad_one_ppow_eq p hp (k + 2) (by omega), show k + 2 - 2 = k from by omega]
    exact (evalHom 2 p).range.sub_mem (T_sum_ppow_in_range p hp (k + 2))
      ((evalHom 2 p).range.mul_mem (T_pp_mem_range p hp) (T_sum_ppow_in_range p hp k))

/-- `T_elem (ppowDiag 2 p e)` is in the evalHom range when `e` is monotone. -/
lemma T_elem_ppow_in_range (p : ℕ) (hp : p.Prime) (e : Fin 2 → ℕ) (hmono : Monotone e) :
    T_elem (ppowDiag 2 p e) ∈ (evalHom 2 p).range := by
  by_cases he0 : e 0 = 0
  · have h_eq : ppowDiag 2 p e = ![1, p ^ (e 1)] := by
      funext i; simp only [ppowDiag]; fin_cases i <;> simp [he0]
    rw [T_elem_congr_diag (n := 2) h_eq,
      ← T_ad_of_pos 1 (p ^ (e 1)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _)]
    exact T_ad_one_ppow_in_range p hp (e 1)
  · have h_le : e 0 ≤ e 1 := hmono (Fin.zero_le _)
    have h_eq : ppowDiag 2 p e = (fun _ ↦ p ^ (e 0)) * ppowDiag 2 p ![0, e 1 - e 0] := by
      funext i
      simp only [ppowDiag, Pi.mul_apply]
      fin_cases i
      · simp
      · show p ^ e 1 = p ^ e 0 * p ^ (e 1 - e 0)
        rw [← pow_add, Nat.add_sub_cancel' h_le]
    rw [T_elem_congr_diag (n := 2) h_eq,
      ← T_diag_scalar_mul 2 (p ^ (e 0)) (pow_pos hp.pos _) (ppowDiag 2 p ![0, e 1 - e 0])
        (ppowDiag_pos 2 p hp _)
        (divChain_ppow 2 p _ (by
          intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]))]
    apply (evalHom 2 p).range.mul_mem
    · rw [← T_pp_pow p hp (e 0), ← T_gen_one_eq_T_pp p hp]
      exact (evalHom 2 p).range.pow_mem (X_one_mem_range p) _
    · have h2 : ppowDiag 2 p ![0, e 1 - e 0] = ![1, p ^ (e 1 - e 0)] := by
        funext i; simp only [ppowDiag]; fin_cases i <;> simp
      rw [T_elem_congr_diag (n := 2) h2,
        ← T_ad_of_pos 1 (p ^ (e 1 - e 0)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _)]
      exact T_ad_one_ppow_in_range p hp (e 1 - e 0)

/-- Surjectivity of `evalHom` at n=2: every element of `R_p 2 p` is in the range
    of the evaluation homomorphism `ℤ[X₁, X₂] → HeckeAlgebra 2`. -/
theorem T_gen_generates_R_p_two (p : ℕ) (hp : p.Prime) :
    ∀ f ∈ R_p 2 p hp, f ∈ (evalHom 2 p).range := by
  intro f hf
  apply Subring.closure_le.mpr _ hf
  intro x hx
  obtain ⟨e, hmono, rfl⟩ := hx
  exact T_elem_ppow_in_range p hp e hmono

end HeckeRing.GLn.Surj

namespace HeckeRing.GLn.SurjOne

open HeckeRing.GLn

/-- For n=1, `T_gen_diag 1 p 0 = fun _ => p`. -/
private lemma T_gen_diag_one_eq (p : ℕ) : T_gen_diag 1 p (0 : Fin 1) = fun _ ↦ p := by
  funext i; simp [T_gen_diag_val]

/-- n=1 surjectivity: every element of R_p is in the range of evalHom. -/
theorem T_gen_generates_R_p_one (p : ℕ) (hp : p.Prime) :
    ∀ f ∈ R_p 1 p hp, f ∈ (evalHom 1 p).range := by
  intro f hf
  apply Subring.closure_le.mpr _ hf
  intro x hx
  obtain ⟨e, _hmono, rfl⟩ := hx
  have he : ppowDiag 1 p e = fun _ ↦ p ^ (e 0) := by
    funext i; simp [ppowDiag]; congr 1; exact congr_arg e (Subsingleton.elim i 0)
  rw [T_elem_congr_diag 1 he, ← T_scalar_pow 1 p hp.pos (e 0),
    show T_elem (fun _ : Fin 1 ↦ p) = T_gen 1 p (0 : Fin 1) from by
      unfold T_gen; exact (T_elem_congr_diag 1 (T_gen_diag_one_eq p)).symm]
  exact (evalHom 1 p).range.pow_mem (T_gen_mem_evalHom_range 1 p 0) _

end HeckeRing.GLn.SurjOne

namespace HeckeRing.GLn.Inj

open HeckeRing.GLn HeckeRing.GL2

/-- Every element in the image of `evalHom` belongs to `R_p`. -/
lemma evalHom_mem_R_p (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin n) ℤ) :
    evalHom n p P ∈ R_p n p hp := by
  apply MvPolynomial.induction_on P
  · intro a
    show evalHom n p (MvPolynomial.C a) ∈ R_p n p hp
    rw [show evalHom n p (MvPolynomial.C a) = (a : HeckeAlgebra n) from
      MvPolynomial.eval₂Hom_C _ _ _, show (a : HeckeAlgebra n) =
        a • (1 : HeckeAlgebra n) from (zsmul_one a).symm]
    exact (R_p n p hp).zsmul_mem (R_p n p hp).one_mem a
  · intro f g hf hg; rw [map_add]; exact (R_p n p hp).add_mem hf hg
  · intro f i hf
    rw [map_mul]
    refine (R_p n p hp).mul_mem hf ?_
    show evalHom n p (MvPolynomial.X i) ∈ R_p n p hp
    rw [show evalHom n p (MvPolynomial.X i) = T_gen n p i from
      MvPolynomial.eval₂Hom_X' _ _ _]
    exact T_gen_mem_R_p n p hp i

/-- The restricted evaluation homomorphism into `R_p`. -/
noncomputable def evalHomR (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime) :
    MvPolynomial (Fin n) ℤ →+* R_p n p hp where
  toFun P := ⟨evalHom n p P, evalHom_mem_R_p n p hp P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ x y)
  map_mul' x y := Subtype.ext (map_mul _ x y)

/-- For n=1, `T_gen(0)^k = T_elem(fun _ => p^k)`. -/
private lemma T_gen_pow_one (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_gen 1 p (0 : Fin 1) ^ k = T_elem (fun _ : Fin 1 ↦ p ^ k) := by
  rw [show T_gen 1 p (0 : Fin 1) = T_elem (fun _ : Fin 1 ↦ p) from by
    unfold T_gen; exact T_elem_congr_diag 1 (SurjOne.T_gen_diag_one_eq p)]
  exact T_scalar_pow 1 p hp.pos k

/-- An integer scalar times the basis element `T_elem a` is the single `Finsupp` at
`T_diag a` with that coefficient. -/
private lemma intCast_mul_T_elem_eq_single {n : ℕ} [NeZero n] (a : Fin n → ℕ) (c : ℤ) :
    (Int.castRingHom (HeckeAlgebra n)) c * T_elem a =
      (Finsupp.single (T_diag a) c : HeckeAlgebra n) := by
  rw [show (Int.castRingHom (HeckeAlgebra n)) c = c • (1 : HeckeAlgebra n) from by
      rw [zsmul_eq_mul, mul_one]; rfl, smul_mul_assoc, one_mul]
  show c • (Finsupp.single (T_diag a) (1 : ℤ) : HeckeAlgebra n) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- For `n = 1` and `p` prime, the cosets `T_diag (fun _ => p^k)` are injective in `k`:
if they coincide for `b 0` and `s 0`, then `b 0 = s 0`. -/
private lemma T_diag_one_ppow_inj (p : ℕ) (hp : p.Prime) {b s : Fin 1 →₀ ℕ}
    (hb : (T_diag (n := 1) (fun _ ↦ p ^ b 0) : HeckeCoset (GL_pair 1)) =
      T_diag (fun _ ↦ p ^ s 0)) : b 0 = s 0 := by
  have hdiv : ∀ c : Fin 1 →₀ ℕ, DivChain 1 (fun _ : Fin 1 ↦ p ^ c 0) :=
    fun c i hi ↦ absurd hi (by omega)
  have heq := diagonal_representative_unique (n := 1) _ _
    (fun _ ↦ Nat.pow_pos hp.pos) (fun _ ↦ Nat.pow_pos hp.pos) (hdiv b) (hdiv s) hb
  exact Nat.pow_right_injective hp.two_le (congr_fun heq 0)

/-- n=1: evalHom is injective. Different monomials map to distinct basis elements,
    so the images are ℤ-linearly independent. -/
theorem evalHom_injective_one (p : ℕ) (hp : p.Prime) : Function.Injective (evalHom 1 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : evalHom 1 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  set D := T_diag (n := 1) (fun _ ↦ p ^ (s 0))
  have h0 : (evalHom 1 p R).toFun D = 0 := by rw [hR]; rfl
  apply hcoeff
  suffices h : ((evalHom 1 p) R).toFun D = MvPolynomial.coeff s R from h ▸ h0
  show Finsupp.toFun (MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra 1))
    (fun k ↦ T_gen 1 p k) R) D = _
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Fin.prod_univ_one]
  have h_sum_eq : (∑ x ∈ R.support,
      (Int.castRingHom (HeckeAlgebra 1)) (MvPolynomial.coeff x R) * T_gen 1 p 0 ^ x 0) =
    (∑ x ∈ R.support,
      (Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0))
        (MvPolynomial.coeff x R) : HeckeCoset (GL_pair 1) →₀ ℤ)) :=
    Finset.sum_congr rfl (fun x _ ↦ by
      rw [T_gen_pow_one p hp]
      exact intCast_mul_T_elem_eq_single (fun _ ↦ p ^ x 0) (R.coeff x))
  show (∑ x ∈ R.support,
      (Int.castRingHom (HeckeAlgebra 1)) (MvPolynomial.coeff x R) * T_gen 1 p 0 ^ x 0)
        D = MvPolynomial.coeff s R
  rw [h_sum_eq]
  show (∑ x ∈ R.support, (Finsupp.single (T_diag (n := 1) (fun _ ↦ p ^ x 0))
      (MvPolynomial.coeff x R) : HeckeCoset (GL_pair 1) →₀ ℤ)) D = MvPolynomial.coeff s R
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, D]
  rw [Finset.sum_eq_single s (fun b _ hbs ↦ if_neg (fun hb ↦ hbs
    (Finsupp.ext (fun j ↦ by rw [Fin.fin_one_eq_zero j]; exact T_diag_one_ppow_inj p hp hb))))
    (fun hns ↦ absurd hs hns)]
  simp

/-- A two-entry diagonal `![a, b]` is a divisibility chain iff `a ∣ b`. -/
private lemma divChain_two_of_dvd {a b : ℕ} (hab : a ∣ b) :
    DivChain 2 (![a, b] : Fin 2 → ℕ) := by
  intro j hj
  obtain rfl : j = 0 := by omega
  exact hab

/-- Determinant of an SL_n(ℤ) element embedded in GL_n(ℚ) is 1. -/
lemma det_SLnZ_eq_one {g : GL (Fin 2) ℚ} (hg : g ∈ SLnZ_subgroup 2) :
    (↑g : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := hg; simp [mapGL, det_intMat_cast, SpecialLinearGroup.det_coe]

/-- Elements in the same SL_n double coset have the same determinant. -/
lemma det_doubleCoset_eq {g₁ g₂ : (GL_pair 2).Δ}
    (h : (⟦g₁⟧ : HeckeCoset (GL_pair 2)) = ⟦g₂⟧) :
    (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [HeckeCoset.eq_iff] at h
  have hg₁_mem : (g₁ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (g₂ : GL (Fin 2) ℚ) (GL_pair 2).H (GL_pair 2).H := by
    rw [← h]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.mem_doubleCoset.mp hg₁_mem
  have : (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (h₁ * (↑g₂ : GL (Fin 2) ℚ) * h₂).1.det := by rw [heq]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul, det_SLnZ_eq_one hh₁,
    det_SLnZ_eq_one hh₂, one_mul, mul_one] at this
  exact this

/-- The diagonal product of rep(T_diag a) equals ∏ a. -/
lemma prod_rep_T_diag (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(↑(HeckeCoset.rep (T_diag a)) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ∏ i, (a i : ℚ) := by
  have h_eq : (⟦HeckeCoset.rep (T_diag a)⟧ : HeckeCoset (GL_pair 2)) = T_diag a :=
    Quotient.out_eq _
  rw [show T_diag a = (⟦diagMat_delta 2 a⟧ : HeckeCoset (GL_pair 2)) from rfl] at h_eq
  exact (det_doubleCoset_eq h_eq).trans (by simp [diagMat_delta_val 2 a ha, diagMat_det 2 a ha])

/-- Every coset in the support of a mulMap output has determinant = det(g₁) * det(g₂). -/
lemma det_mulMap_eq (g₁ g₂ : (GL_pair 2).Δ)
    (p : HeckeRing.decompQuot (GL_pair 2) g₁ × HeckeRing.decompQuot (GL_pair 2) g₂) :
    (↑(↑(HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)) : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑g₁ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑g₂ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  have h_eq : (⟦HeckeCoset.rep (HeckeRing.mulMap (GL_pair 2) g₁ g₂ p)⟧ :
      HeckeCoset (GL_pair 2)) = HeckeRing.mulMap (GL_pair 2) g₁ g₂ p := Quotient.out_eq _
  rw [det_doubleCoset_eq h_eq]
  show (((p.1.out : GL (Fin 2) ℚ) * (g₁ : GL (Fin 2) ℚ) *
    ((p.2.out : GL (Fin 2) ℚ) * (g₂ : GL (Fin 2) ℚ)) : GL (Fin 2) ℚ) :
    Matrix (Fin 2) (Fin 2) ℚ).det = _
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h1 := det_SLnZ_eq_one (p.1.out.2)
  have h2 := det_SLnZ_eq_one (p.2.out.2)
  rw [h1, h2]; ring

/-- If `D'` appears in the support of `m(rep D₁, rep D₂)`, then the determinant of its
representative is the product of the determinants of `rep D₁` and `rep D₂`. -/
private lemma det_rep_eq_mul_of_m_ne_zero (D₁ D₂ D' : HeckeCoset (GL_pair 2))
    (hm : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (↑(↑(HeckeCoset.rep D₁) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det *
        (↑(↑(HeckeCoset.rep D₂) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [HeckeRing.m_apply] at hm
  have hD'_mem :
      D' ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
    rw [← HeckeRing.m_support]; exact Finsupp.mem_support_iff.mpr hm
  rw [HeckeRing.mulSupport, Finset.mem_image] at hD'_mem
  obtain ⟨p, _, hD'_eq⟩ := hD'_mem
  rw [← hD'_eq]; exact det_mulMap_eq (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p

/-- Determinant tracking: if `f` is supported on cosets of determinant `q^{a₀}`, then
`T_gen(q,0)^{b₀} · f` is supported on cosets of determinant `q^{b₀ + a₀}`. -/
private lemma det_rep_T_gen_zero_pow_mul (q : {p : ℕ // p.Prime}) (a₀ b₀ : ℕ)
    (f : HeckeAlgebra 2) (D' : HeckeCoset (GL_pair 2))
    (hf_det : ∀ D'', f D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = ↑(q.1 ^ a₀ : ℕ))
    (hD' : (T_gen 2 q.1 0 ^ b₀ * f) D' ≠ 0) :
    (↑(↑(HeckeCoset.rep D') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ↑(q.1 ^ (b₀ + a₀) : ℕ) := by
  induction b₀ generalizing f D' with
  | zero =>
    rw [pow_zero, one_mul] at hD'
    simpa only [Nat.zero_add] using hf_det D' hD'
  | succ n ih =>
    rw [pow_succ', mul_assoc] at hD'
    set g' := T_gen 2 q.1 0 ^ n * f
    rw [show T_gen 2 q.1 0 = HeckeRing.T_single (GL_pair 2) ℤ (T_diag (![1, q.1])) 1 from by
        show T_elem (T_gen_diag 2 q.1 0) = _; congr 1
        funext i; fin_cases i <;> simp [T_gen_diag]] at hD'
    obtain ⟨D₂, hD₂_mem, hD₂_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
      rw [show (HeckeRing.T_single (GL_pair 2) ℤ (T_diag (![1, q.1])) 1 * g') D' =
          ∑ D₂ ∈ g'.support, g' D₂ * (HeckeRing.m (GL_pair 2)
            (HeckeCoset.rep (T_diag (![1, q.1]))) (HeckeCoset.rep D₂)) D' from by
          show (Finsupp.sum (Finsupp.single _ 1) (fun D₁' b₁ ↦ g'.sum (fun D₂ b₂ ↦
              b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁') (HeckeCoset.rep D₂)))) D' = _
          rw [Finsupp.sum_single_index (by simp [Finsupp.sum]), Finsupp.sum]
          simp only [one_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
          rfl] at hD'
      exact hD')
    have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag (![1, q.1])))
        (HeckeCoset.rep D₂)) D' ≠ 0 := fun h ↦ hD₂_ne (by rw [h, mul_zero])
    rw [det_rep_eq_mul_of_m_ne_zero _ _ _ hm_ne,
      show (↑(↑(HeckeCoset.rep (T_diag (![1, q.1]))) : GL (Fin 2) ℚ) :
          Matrix (Fin 2) (Fin 2) ℚ).det = (q.1 : ℚ) from by
        rw [prod_rep_T_diag (![1, q.1]) (fun i ↦ by fin_cases i <;> simp [q.2.pos])]
        simp [Fin.prod_univ_two],
      ih f D₂ hf_det (Finsupp.mem_support_iff.mp hD₂_mem)]
    push_cast; ring

lemma T_gen_pow_support_qpower (q : {p : ℕ // p.Prime}) (e : Fin 2 → ℕ)
    (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0) :
    ∃ a : Fin 2 → ℕ, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = q.1 ^ (e 0 + 2 * e 1) := by
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have hf_det : ∀ D'', (T_gen 2 q.1 1 ^ (e 1)) D'' ≠ 0 →
      (↑(↑(HeckeCoset.rep D'') : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
        ↑(q.1 ^ (2 * e 1) : ℕ) := by
    intro D'' hD''
    rw [HeckeRing.GLn.Surj.T_gen_one_eq_T_pp q.1 q.2, HeckeRing.GL2.T_pp_pow q.1 q.2 (e 1)] at hD''
    have h_eq : T_diag (fun _ : Fin 2 ↦ q.1 ^ (e 1)) = D'' := by
      by_contra h
      exact hD'' (by rw [show (T_elem (fun _ : Fin 2 ↦ q.1 ^ (e 1))) D'' =
        (Finsupp.single (T_diag (fun _ : Fin 2 ↦ q.1 ^ (e 1))) (1 : ℤ)) D'' from rfl,
        Finsupp.single_apply, if_neg h])
    rw [← h_eq, prod_rep_T_diag _ (fun i ↦ by fin_cases i <;> simp [pow_pos q.2.pos])]
    push_cast [Fin.prod_univ_two, ← pow_add]; ring_nf
  have h_result := det_rep_T_gen_zero_pow_mul q (2 * e 1) (e 0) _ D hf_det hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_result
  exact mod_cast h_result

/-- Every coset in the support of `T_gen(q,0)^a * T_gen(q,1)^b` has entries
that are powers of `q` (immediate from `T_gen_pow_support_qpower`). -/
lemma T_gen_pow_entries_qpower (q : {p : ℕ // p.Prime})
    (e : Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (T_gen 2 q.1 0 ^ (e 0) * T_gen 2 q.1 1 ^ (e 1)) D ≠ 0)
    (a : Fin 2 → ℕ) (ha : D = T_diag a) (ha_pos : ∀ i, 0 < a i)
    (ha_div : DivChain 2 a) :
    ∀ p : ℕ, p.Prime → p ≠ q.1 → ∀ i, ¬(p ∣ a i) := by
  obtain ⟨a', rfl, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q e D hD
  have ha_eq := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div ha.symm
  subst ha_eq
  intro p hp hpq i h_dvd
  have : p ∣ ∏ j, a j := dvd_trans h_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [ha'_det] at this
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.2).mp (hp.dvd_of_dvd_pow this))

/-- If `(f * g)(D) ≠ 0` in the Hecke ring, there exist `D₁ ∈ supp(f)` and `D₂ ∈ supp(g)`
with `D ∈ mulSupport(rep D₁, rep D₂)`. -/
lemma support_mul_exists (f g : HeckeAlgebra 2) (D : HeckeCoset (GL_pair 2))
    (hD : (f * g) D ≠ 0) :
    ∃ D₁ D₂, f D₁ ≠ 0 ∧ g D₂ ≠ 0 ∧
      D ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  have h : (Finsupp.sum f (fun D₁ b₁ ↦ Finsupp.sum g (fun D₂ b₂ ↦
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D ≠ 0 := hD
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  obtain ⟨D₁, hD₁_mem, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨D₂, hD₂_mem, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h₁
  have hfD₁ := Finsupp.mem_support_iff.mp hD₁_mem
  have hgD₂ := Finsupp.mem_support_iff.mp hD₂_mem
  have hm_ne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D ≠ 0 := by
    intro h; exact h₂ (by rw [h, mul_zero, mul_zero])
  refine ⟨D₁, D₂, hfD₁, hgD₂, ?_⟩
  rw [← HeckeRing.m_support]
  exact Finsupp.mem_support_iff.mpr hm_ne

/-- `T_single(T_diag a, α) * T_elem(c,c) = T_single(T_diag(a * c), α)`. -/
lemma T_single_diag_mul_T_scalar (c : ℕ) (hc : 0 < c)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (ha_div : DivChain 2 a) (α : ℤ) :
    HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α * T_elem (fun _ : Fin 2 ↦ c) =
    HeckeRing.T_single (GL_pair 2) ℤ (T_diag (a * (fun _ : Fin 2 ↦ c))) α := by
  have h_single : HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α =
      α • T_elem a := by
    show HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) α =
         α • HeckeRing.T_single (GL_pair 2) ℤ (T_diag a) 1
    rw [HeckeRing.T_single_smul]; congr 1; ring
  rw [h_single, smul_mul_assoc, T_elem_mul_scalar a ha_pos ha_div c hc]
  show α • HeckeRing.T_single (GL_pair 2) ℤ (T_diag (a * fun _ ↦ c)) 1 = _
  rw [HeckeRing.T_single_smul]; congr 1; ring

/-- Scalar shift identity: for any `f : HeckeAlgebra 2`, scalar `c > 0`, and positive
divisibility-chain `b`, evaluating `f * T_elem(c,c)` at `T_diag(b * c)` equals `f(T_diag b)`. -/
lemma T_mul_T_scalar_eval_shifted (c : ℕ) (hc : 0 < c) (f : HeckeAlgebra 2) (b : Fin 2 → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb_div : DivChain 2 b) :
    (f * T_elem (fun _ : Fin 2 ↦ c)) (T_diag (b * (fun _ : Fin 2 ↦ c))) = f (T_diag b) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    show ((0 : HeckeAlgebra 2) * T_elem (fun _ : Fin 2 ↦ c)) (T_diag (b * fun _ ↦ c)) =
      (0 : HeckeAlgebra 2) (T_diag b)
    rw [zero_mul]; rfl
  | add g h ihg ihh =>
    set g' : HeckeAlgebra 2 := g
    set h' : HeckeAlgebra 2 := h
    change ((g' + h') * T_elem (fun _ : Fin 2 ↦ c)) (T_diag (b * fun _ ↦ c)) =
      (g' + h') (T_diag b)
    rw [add_mul,
      show (g' * T_elem (fun _ : Fin 2 ↦ c) + h' * T_elem (fun _ : Fin 2 ↦ c))
            (T_diag (b * fun _ ↦ c)) =
            (g' * T_elem (fun _ : Fin 2 ↦ c)) (T_diag (b * fun _ ↦ c)) +
            (h' * T_elem (fun _ : Fin 2 ↦ c)) (T_diag (b * fun _ ↦ c)) from
        Finsupp.add_apply _ _ _,
      show (g' + h') (T_diag b) = g' (T_diag b) + h' (T_diag b) from Finsupp.add_apply _ _ _,
      ihg, ihh]
  | single D α =>
    obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
    have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
    change (HeckeRing.T_single (GL_pair 2) ℤ D α * T_elem (fun _ : Fin 2 ↦ c))
        (T_diag (b * fun _ : Fin 2 ↦ c)) =
      HeckeRing.T_single (GL_pair 2) ℤ D α (T_diag b)
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos ha_div α]
    show Finsupp.single (T_diag (a * fun _ : Fin 2 ↦ c)) α (T_diag (b * fun _ : Fin 2 ↦ c)) =
      Finsupp.single (T_diag a) α (T_diag b)
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos rfl]
    · have h_ne_1 : T_diag (a * fun _ : Fin 2 ↦ c) ≠ T_diag (b * fun _ : Fin 2 ↦ c) := by
        intro heq
        have h1_eq : a * (fun _ : Fin 2 ↦ c) = b * (fun _ : Fin 2 ↦ c) :=
          diagonal_representative_unique 2 _ _ (fun i ↦ Nat.mul_pos (ha_pos i) hc)
            (fun i ↦ Nat.mul_pos (hb_pos i) hc) (DivChain_mul 2 a _ ha_div (divChain_const 2 c))
            (DivChain_mul 2 b _ hb_div (divChain_const 2 c)) heq
        apply hab
        funext i
        have := congr_fun h1_eq i
        simp only [Pi.mul_apply] at this
        exact Nat.eq_of_mul_eq_mul_right hc this
      have h_ne_2 : T_diag a ≠ T_diag b := fun heq ↦ hab
        (diagonal_representative_unique 2 a b ha_pos hb_pos ha_div hb_div heq)
      rw [if_neg h_ne_1, if_neg h_ne_2]

/-- If `c ∤ d i` for some `i`, the evaluation of `f * T_elem(c,c)` at `T_diag d` is zero. -/
lemma T_mul_T_scalar_eval_zero_of_not_dvd (c : ℕ) (hc : 0 < c) (f : HeckeAlgebra 2) (d : Fin 2 → ℕ)
    (hd_pos : ∀ i, 0 < d i) (hd_div : DivChain 2 d) (i₀ : Fin 2) (hi₀ : ¬ c ∣ d i₀) :
    (f * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero =>
    show ((0 : HeckeAlgebra 2) * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) = 0
    rw [zero_mul]; rfl
  | add g h ihg ihh =>
    set g' : HeckeAlgebra 2 := g
    set h' : HeckeAlgebra 2 := h
    change ((g' + h') * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) = 0
    rw [add_mul,
      show (g' * T_elem (fun _ : Fin 2 ↦ c) + h' * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) =
            (g' * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) +
            (h' * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) from Finsupp.add_apply _ _ _,
      ihg, ihh, add_zero]
  | single D α =>
    obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
    have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
    change (HeckeRing.T_single (GL_pair 2) ℤ D α * T_elem (fun _ : Fin 2 ↦ c)) (T_diag d) = 0
    rw [hD_eq, T_single_diag_mul_T_scalar c hc a ha_pos ha_div α]
    show Finsupp.single (T_diag (a * fun _ : Fin 2 ↦ c)) α (T_diag d) = 0
    rw [Finsupp.single_apply]
    have h_ne : T_diag (a * fun _ : Fin 2 ↦ c) ≠ T_diag d := by
      intro heq
      have h_eq : a * (fun _ : Fin 2 ↦ c) = d :=
        diagonal_representative_unique 2 _ d (fun i ↦ Nat.mul_pos (ha_pos i) hc) hd_pos
          (DivChain_mul 2 a _ ha_div (divChain_const 2 c)) hd_div heq
      apply hi₀
      have := congr_fun h_eq i₀
      simp only [Pi.mul_apply] at this
      exact ⟨a i₀, by linarith [this.symm]⟩
    rw [if_neg h_ne]

/-- For `i ≥ 1`, evaluation of `f * T_pp(p)^i` at `T_diag ![1, k]` is zero (since `p^i ∤ 1`). -/
lemma T_mul_T_pp_pow_eval_at_one_zero (p : ℕ) (hp : p.Prime) (i k : ℕ) (hi : 1 ≤ i)
    (hk : 0 < k) (f : HeckeAlgebra 2) :
    (f * T_pp p ^ i) (T_diag (![1, k] : Fin 2 → ℕ)) = 0 := by
  rw [HeckeRing.GL2.T_pp_pow p hp i]
  apply T_mul_T_scalar_eval_zero_of_not_dvd (p^i) (pow_pos hp.pos i) f
    (![1, k] : Fin 2 → ℕ) (fun idx ↦ by fin_cases idx <;> simp [hk])
    (fun j hj ↦ by
      have : j = 0 := by omega
      subst this; simp) 0
  simp only [Matrix.cons_val_zero]
  intro hdvd
  have hle : p ^ i ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
  have hge : p ≤ p ^ i := Nat.le_self_pow (by omega) p
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- `T_elem ![p^i, p^j] = T_ad(1, p^{j-i}) * T_pp(p)^i` for `i ≤ j` with `p` prime. -/
lemma T_elem_ppow_factor (p : ℕ) (hp : p.Prime) (i j : ℕ) (hij : i ≤ j) :
    T_elem (![p^i, p^j] : Fin 2 → ℕ) = T_ad 1 (p ^ (j - i)) * T_pp p ^ i := by
  rw [T_ad_of_pos 1 (p^(j-i)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      HeckeRing.GL2.T_pp_pow p hp i]
  have h_ji_pos : ∀ idx : Fin 2, 0 < (![1, p^(j-i)] : Fin 2 → ℕ) idx := by
    intro idx; fin_cases idx
    · simp
    · simp [pow_pos hp.pos]
  have h_ji_div : DivChain 2 (![1, p^(j-i)] : Fin 2 → ℕ) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; simp
  rw [T_elem_mul_scalar (![1, p^(j-i)] : Fin 2 → ℕ) h_ji_pos h_ji_div (p^i) (pow_pos hp.pos _)]
  apply T_elem_congr_diag
  funext idx; fin_cases idx
  · simp [Pi.mul_apply]
  · simp [Pi.mul_apply, ← pow_add]; congr 1; omega

/-- The element `T(p, pⁿ)` does not contribute at `T(1, p^{n+1})` (for `n ≥ 1`). -/
private lemma T_elem_p_ppow_eval_at_one_ppow_succ_zero (p : ℕ) (hp : p.Prime) {n : ℕ}
    (hn : n ≠ 0) :
    (T_elem (![p, p ^ n] : Fin 2 → ℕ)) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  show (Finsupp.single (T_diag (![p, p ^ n] : Fin 2 → ℕ)) (1 : ℤ)) _ = 0
  refine Finsupp.single_eq_of_ne' (fun heq ↦ ?_)
  have h_eq : (![p, p ^ n] : Fin 2 → ℕ) = (![1, p ^ (n + 1)] : Fin 2 → ℕ) :=
    diagonal_representative_unique 2 _ _
      (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
      (divChain_two_of_dvd (dvd_pow_self p hn)) (divChain_two_of_dvd (one_dvd _)) heq
  have := congr_fun h_eq 0
  simp only [Matrix.cons_val_zero] at this
  have := hp.one_lt; omega

/-- `(T(1,p) · T(1, pⁿ))` evaluated at the leading coset `T(1, p^{n+1})` equals `1`. -/
private lemma T_ad_one_p_mul_T_ad_one_ppow_eval_leading (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (T_ad 1 p * T_ad 1 (p ^ n)) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [pow_zero, T_ad_one_one, mul_one,
      T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]
    show (Finsupp.single (T_diag (![1, p] : Fin 2 → ℕ)) (1 : ℤ))
         (T_diag (![1, p ^ (0 + 1)] : Fin 2 → ℕ)) = 1
    rw [show (![1, p ^ (0 + 1)] : Fin 2 → ℕ) = (![1, p] : Fin 2 → ℕ) from by
        funext i; fin_cases i <;> simp]
    exact Finsupp.single_eq_same
  · rw [show T_ad 1 p = T_sum ⟨p, hp.pos⟩ from (T_sum_prime p hp).symm,
      T_sum_prime_mul_T_ad p hp n (Nat.pos_of_ne_zero hn)]
    rw [show (T_ad 1 (p ^ (n + 1)) + (if n = 1 then ((p + 1 : ℕ) : ℤ) else (p : ℤ)) •
              T_ad p (p ^ n)) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
          T_ad 1 (p ^ (n + 1)) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) +
            ((if n = 1 then ((p + 1 : ℕ) : ℤ) else (p : ℤ)) • T_ad p (p ^ n))
              (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from Finsupp.add_apply _ _ _,
      T_ad_of_pos 1 (p ^ (n + 1)) Nat.one_pos (pow_pos hp.pos _) (one_dvd _),
      T_ad_of_pos p (p ^ n) hp.pos (pow_pos hp.pos _) (dvd_pow_self p hn)]
    rw [show (T_elem (![1, p ^ (n + 1)] : Fin 2 → ℕ))
          (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 1 from
        Finsupp.single_eq_same]
    rw [show ((if n = 1 then ((p + 1 : ℕ) : ℤ) else (p : ℤ)) • T_elem (![p, p ^ n] : Fin 2 → ℕ))
          (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) =
        (if n = 1 then ((p + 1 : ℕ) : ℤ) else (p : ℤ)) •
          T_elem (![p, p ^ n] : Fin 2 → ℕ) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) from
        Finsupp.smul_apply _ _ _,
      T_elem_p_ppow_eval_at_one_ppow_succ_zero p hp hn,
      smul_zero, add_zero]

/-- A non-leading support element `D₂` of `(T(1,p))ⁿ` contributes `0` to the product
`T(1,p) · (T(1,p))ⁿ` at the leading coset `T(1, p^{n+1})`. -/
private lemma T_ad_one_p_mul_supp_ne_leading_eval_zero (p : ℕ) (hp : p.Prime) (n : ℕ)
    (D₂ : HeckeCoset (GL_pair 2)) (hD₂_ne_zero : ((T_ad 1 p) ^ n) D₂ ≠ 0)
    (hD₂_ne : D₂ ≠ T_diag (![1, p ^ n] : Fin 2 → ℕ)) :
    (HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ)))
      (HeckeCoset.rep D₂)) (T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)) = 0 := by
  have hg_eq : (T_ad 1 p) ^ n = (T_gen 2 p 0) ^ n * (T_gen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
      ![n, 0] D₂ (hg_eq ▸ hD₂_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have ha_prod : a 0 * a 1 = p ^ n := Fin.prod_univ_two a ▸ ha_det
  obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp (ha_prod ▸ dvd_mul_right _ _)
  have ha1_eq : a 1 = p ^ (n - i) := by
    have h : p ^ i * a 1 = p ^ i * p ^ (n - i) := by
      rw [← pow_add, show i + (n - i) = n from by omega, ← ha_prod, hi_eq]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h
  have ha_form : a = (![p ^ i, p ^ (n - i)] : Fin 2 → ℕ) := by
    funext k; fin_cases k
    · exact hi_eq
    · exact ha1_eq
  have hi_ge : 1 ≤ i := by
    by_contra h_not
    obtain rfl : i = 0 := by omega
    exact hD₂_ne (by rw [hDa, ha_form]; simp [pow_zero])
  have hi_le_sub : i ≤ n - i := by
    have h_div := ha_form ▸ ha_div 0 (by omega : 0 + 1 < 2)
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h_div
  rw [hDa, ha_form, ← HeckeRing.T_single_one_mul_T_single_one]
  change (T_elem (![1, p] : Fin 2 → ℕ) * T_elem (![p^i, p^(n-i)] : Fin 2 → ℕ)) _ = 0
  rw [T_elem_ppow_factor p hp i (n - i) hi_le_sub, ← mul_assoc]
  exact T_mul_T_pp_pow_eval_at_one_zero p hp i (p ^ (n + 1)) hi_ge (pow_pos hp.pos _) _

/-- Leading coefficient of `T(1,p)^a`: `(T_ad 1 p)^a` evaluated at the leading coset
`T_diag ![1, p^a]` equals 1. -/
lemma T_ad_one_p_pow_eval_leading (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ((T_ad 1 p) ^ a) (T_diag (![1, p ^ a] : Fin 2 → ℕ)) = 1 := by
  induction a with
  | zero =>
    rw [pow_zero, pow_zero, show (![1, 1] : Fin 2 → ℕ) = (fun _ : Fin 2 ↦ 1) from by
        funext i; fin_cases i <;> rfl, ← T_elem_ones_eq_one 2]
    exact Finsupp.single_eq_same
  | succ n ih =>
    rw [pow_succ']
    set g := (T_ad 1 p) ^ n
    set D_target : HeckeCoset (GL_pair 2) := T_diag (![1, p ^ (n + 1)] : Fin 2 → ℕ)
    set D_leading : HeckeCoset (GL_pair 2) := T_diag (![1, p ^ n] : Fin 2 → ℕ)
    rw [show T_ad 1 p = HeckeRing.T_single (GL_pair 2) ℤ (T_diag (![1, p] : Fin 2 → ℕ)) 1 from
        T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _),
      HeckeRing.mul_def, Finsupp.sum_single_index (by simp [Finsupp.sum])]
    simp only [one_smul]
    show (Finsupp.sum g fun D2 b₂ ↦ b₂ • HeckeRing.m (GL_pair 2)
          (T_diag (![1, p] : Fin 2 → ℕ)).rep D2.rep) D_target = 1
    rw [show (Finsupp.sum g fun D2 b₂ ↦ b₂ • HeckeRing.m (GL_pair 2)
          (T_diag (![1, p] : Fin 2 → ℕ)).rep D2.rep) D_target =
        g.sum (fun D2 b₂ ↦ (b₂ • HeckeRing.m (GL_pair 2)
          (T_diag (![1, p] : Fin 2 → ℕ)).rep D2.rep) D_target) from
      Finsupp.sum_apply, Finsupp.sum]
    have h_leading_in_supp : D_leading ∈ g.support :=
      Finsupp.mem_support_iff.mpr (ih ▸ one_ne_zero)
    rw [← Finset.sum_erase_add _ _ h_leading_in_supp]
    have h_erased : ∀ D₂ ∈ g.support.erase D_leading,
        (g D₂ • HeckeRing.m (GL_pair 2)
          (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D₂)) D_target = 0 := by
      intro D₂ hD₂
      rw [Finset.mem_erase] at hD₂
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [T_ad_one_p_mul_supp_ne_leading_eval_zero p hp n D₂
        (Finsupp.mem_support_iff.mp hD₂.2) hD₂.1, mul_zero]
    have h_sum_zero :
        ∑ x ∈ g.support.erase D_leading, (g x • HeckeRing.m (GL_pair 2)
          (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target = 0 :=
      Finset.sum_eq_zero h_erased
    -- Goal: ∑ + (g D_leading • m ...) D_target = 1
    -- Strategy: prove the leading term equals 1, then linarith with h_sum_zero
    have h_leading_eq : (g D_leading • HeckeRing.m (GL_pair 2)
          (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target = 1 := by
      rw [Finsupp.smul_apply, ih, ← HeckeRing.T_single_one_mul_T_single_one]
      show (1 : ℤ) • (T_elem (![1, p] : Fin 2 → ℕ) * T_elem (![1, p ^ n] : Fin 2 → ℕ)) D_target = 1
      rw [one_smul,
        show T_elem (![1, p] : Fin 2 → ℕ) = T_ad 1 p from
          (T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)).symm,
        show T_elem (![1, p ^ n] : Fin 2 → ℕ) = T_ad 1 (p ^ n) from
          (T_ad_of_pos 1 (p ^ n) Nat.one_pos (pow_pos hp.pos n) (one_dvd _)).symm]
      exact T_ad_one_p_mul_T_ad_one_ppow_eval_leading p hp n
    calc ∑ x ∈ g.support.erase D_leading, (g x • HeckeRing.m (GL_pair 2)
            (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep x)) D_target +
          (g D_leading • HeckeRing.m (GL_pair 2)
            (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target
        = 0 + (g D_leading • HeckeRing.m (GL_pair 2)
              (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target :=
          by rw [h_sum_zero]
      _ = (g D_leading • HeckeRing.m (GL_pair 2)
            (HeckeCoset.rep (T_diag (![1, p] : Fin 2 → ℕ))) (HeckeCoset.rep D_leading)) D_target :=
          zero_add _
      _ = 1 := h_leading_eq

/-- For `a₁ ≠ a₂`, evaluating `(T_ad 1 p)^a₁` at the coset `T(1, p^{a₂})` gives `0`. -/
private lemma T_ad_one_p_pow_eval_at_one_ppow_of_ne (p : ℕ) (hp : p.Prime) {a₁ a₂ : ℕ}
    (ha_ne : a₁ ≠ a₂) :
    ((T_ad 1 p) ^ a₁) (T_diag (![1, p ^ a₂] : Fin 2 → ℕ)) = 0 := by
  by_contra h_ne_zero
  have hg_eq : (T_ad 1 p) ^ a₁ = (T_gen 2 p 0) ^ a₁ * (T_gen 2 p 1) ^ 0 := by
    simp only [pow_zero, mul_one, HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp]
  obtain ⟨a, hDa, ha_pos, ha_div, ha_det⟩ := T_gen_pow_support_qpower ⟨p, hp⟩
      ![a₁, 0] (T_diag (![1, p ^ a₂] : Fin 2 → ℕ)) (hg_eq ▸ h_ne_zero)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at ha_det
  have h_a_eq : a = (![1, p ^ a₂] : Fin 2 → ℕ) :=
    diagonal_representative_unique 2 _ _ ha_pos
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) ha_div
      (divChain_two_of_dvd (one_dvd _)) hDa.symm
  rw [h_a_eq, Fin.prod_univ_two] at ha_det
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at ha_det
  exact ha_ne (Nat.pow_right_injective hp.two_le ha_det.symm)

/-- `(T_ad 1 p)^a₁` times the scalar `T(p^b, p^b)`, evaluated at the shifted leading coset
`T(p^b, p^{a₂+b})`, equals `(T_ad 1 p)^a₁` evaluated at `T(1, p^{a₂})`. -/
private lemma T_ad_one_p_pow_mul_scalar_eval_at_one_ppow (p : ℕ) (hp : p.Prime) (a₁ a₂ b : ℕ) :
    ((T_ad 1 p) ^ a₁ * T_elem (fun _ : Fin 2 ↦ p ^ b))
        (T_diag (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ)) =
    ((T_ad 1 p) ^ a₁) (T_diag (![1, p ^ a₂] : Fin 2 → ℕ)) := by
  rw [show (![p ^ b, p ^ (a₂ + b)] : Fin 2 → ℕ) =
      (![1, p ^ a₂] : Fin 2 → ℕ) * (fun _ : Fin 2 ↦ p ^ b) from by
        funext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, pow_add]]
  exact T_mul_T_scalar_eval_shifted (p ^ b) (pow_pos hp.pos _) _ _
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (divChain_two_of_dvd (one_dvd _))

/-- Kronecker delta lemma: evaluating the monomial `T_gen(p,0)^a₁ * T_gen(p,1)^b₁` at the
diagonal coset `T(p^b₂, p^(a₂+b₂))` gives 1 iff `(a₁, b₁) = (a₂, b₂)`, and 0 otherwise,
under the hypothesis `b₂ ≤ b₁`. -/
lemma monomial_eval_kronecker (p : ℕ) (hp : p.Prime)
    (a₁ b₁ a₂ b₂ : ℕ) (h : b₂ ≤ b₁) :
    (T_gen 2 p 0 ^ a₁ * T_gen 2 p 1 ^ b₁)
        (T_diag (ppowDiag 2 p ![b₂, a₂ + b₂])) =
    if a₁ = a₂ ∧ b₁ = b₂ then 1 else 0 := by
  rw [show (ppowDiag 2 p ![b₂, a₂ + b₂] : Fin 2 → ℕ) = (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ)
      from by funext i; fin_cases i <;> simp [ppowDiag],
    HeckeRing.GLn.Surj.T_gen_zero_eq_T_ad p hp, HeckeRing.GLn.Surj.T_gen_one_eq_T_pp p hp,
    HeckeRing.GL2.T_pp_pow p hp b₁]
  by_cases hmatch : a₁ = a₂ ∧ b₁ = b₂
  · obtain ⟨ha, hb⟩ := hmatch
    rw [if_pos ⟨ha, hb⟩, ha, ← hb, T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp,
      T_ad_one_p_pow_eval_leading p hp a₂]
  · rw [if_neg hmatch]
    by_cases hbeq : b₁ = b₂
    · subst hbeq
      rw [T_ad_one_p_pow_mul_scalar_eval_at_one_ppow p hp,
        T_ad_one_p_pow_eval_at_one_ppow_of_ne p hp (fun heq ↦ hmatch ⟨heq, rfl⟩)]
    · have h_not_dvd : ¬ p ^ b₁ ∣ (![p ^ b₂, p ^ (a₂ + b₂)] : Fin 2 → ℕ) 0 := by
        simp only [Matrix.cons_val_zero, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
        omega
      exact T_mul_T_scalar_eval_zero_of_not_dvd (p ^ b₁) (pow_pos hp.pos _) _ _
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (divChain_two_of_dvd (pow_dvd_pow p (by omega))) 0 h_not_dvd

/-- For `n = 2`, the monomial `∏ₖ T_gen(p,k)^{d k}` over the support of `d` equals
`T_gen(p,0)^{d 0} · T_gen(p,1)^{d 1}` (missing factors contribute `T_gen^0 = 1`). -/
private lemma prod_T_gen_pow_eq_two (p : ℕ) (d : Fin 2 →₀ ℕ) :
    (∏ k ∈ d.support, T_gen 2 p k ^ d k) = T_gen 2 p 0 ^ (d 0) * T_gen 2 p 1 ^ (d 1) := by
  rw [Finset.prod_subset (Finset.subset_univ d.support) (fun k _ hk ↦ by
    rw [Finsupp.notMem_support_iff.mp hk, pow_zero])]
  rw [Fin.prod_univ_two]

/-- Evaluating `evalHom 2 p R` at the coset `D` expands as
`∑_{d ∈ supp R} (R.coeff d) · (T_gen(p,0)^{d 0} · T_gen(p,1)^{d 1}) D`. -/
private lemma evalHom_apply_eq_sum_monomial (p : ℕ) (R : MvPolynomial (Fin 2) ℤ)
    (D : HeckeCoset (GL_pair 2)) :
    (evalHom 2 p R) D =
    ∑ d ∈ R.support, R.coeff d * (T_gen 2 p 0 ^ (d 0) * T_gen 2 p 1 ^ (d 1)) D := by
  change (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 2))
    (fun k : Fin 2 ↦ T_gen 2 p k) R) D = _
  rw [MvPolynomial.eval₂_eq]
  show (∑ d ∈ R.support, (Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d R) *
    ∏ i ∈ d.support, T_gen 2 p i ^ d i) D = _
  rw [show (∑ d ∈ R.support, (Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d R) *
        ∏ i ∈ d.support, T_gen 2 p i ^ d i) D =
      ∑ d ∈ R.support, ((Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d R) *
        ∏ i ∈ d.support, T_gen 2 p i ^ d i) D from Finset.sum_apply' _]
  refine Finset.sum_congr rfl (fun d _ ↦ ?_)
  show (((R.coeff d : ℤ) : HeckeAlgebra 2) * (∏ k ∈ d.support, T_gen 2 p k ^ d k)) D = _
  rw [show ((R.coeff d : ℤ) : HeckeAlgebra 2) = (R.coeff d) • (1 : HeckeAlgebra 2) from
    (zsmul_one _).symm, smul_mul_assoc, one_mul]
  rw [show ((R.coeff d) • (∏ k ∈ d.support, T_gen 2 p k ^ d k : HeckeAlgebra 2)) D =
    R.coeff d • (∏ k ∈ d.support, T_gen 2 p k ^ d k : HeckeAlgebra 2) D from
    Finsupp.smul_apply _ _ _, smul_eq_mul, prod_T_gen_pow_eq_two]

/-- n=2: evalHom is injective. -/
theorem evalHom_injective_two (p : ℕ) (hp : p.Prime) :
    Function.Injective (evalHom 2 p) := by
  intro P Q hPQ
  rw [← sub_eq_zero]; set R := P - Q with hR_def
  have hR : evalHom 2 p R = 0 := by simp [R, map_sub, hPQ]
  by_contra hR_ne
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image R.support
    (fun d : Fin 2 →₀ ℕ ↦ d 1) (MvPolynomial.support_nonempty.mpr hR_ne)
  have hs_coeff : R.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  have h_zero : (evalHom 2 p R) (T_diag (ppowDiag 2 p ![s 1, s 0 + s 1])) = 0 := by rw [hR]; rfl
  rw [evalHom_apply_eq_sum_monomial] at h_zero
  have h_delta : ∀ d ∈ R.support,
      R.coeff d * (T_gen 2 p 0 ^ (d 0) * T_gen 2 p 1 ^ (d 1))
          (T_diag (ppowDiag 2 p ![s 1, s 0 + s 1])) =
      if d = s then R.coeff d else 0 := by
    intro d hd_mem
    rw [monomial_eval_kronecker p hp (d 0) (d 1) (s 0) (s 1) (hs_min d hd_mem)]
    by_cases hds : d = s
    · subst hds; simp
    · rw [if_neg hds, if_neg (fun ⟨h0, h1⟩ ↦ hds (by ext i; fin_cases i; exacts [h0, h1])),
        mul_zero]
  rw [Finset.sum_congr rfl h_delta, Finset.sum_ite_eq_of_mem' R.support s _ hs_mem] at h_zero
  exact hs_coeff h_zero

/-- Surjectivity of `evalHomR` follows from surjectivity onto `R_p`. -/
lemma evalHomR_surjective (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime)
    (h_surj : ∀ f ∈ R_p n p hp, f ∈ (evalHom n p).range) :
    Function.Surjective (evalHomR n p hp) := by
  intro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := h_surj f hf
  exact ⟨P, Subtype.ext hP⟩

/-- Injectivity of `evalHomR` follows from injectivity of `evalHom`. -/
lemma evalHomR_injective (n : ℕ) [NeZero n] (p : ℕ) (_hp : p.Prime)
    (h_inj : Function.Injective (evalHom n p)) :
    Function.Injective (evalHomR n p ‹_›) := by
  intro P Q hPQ
  exact h_inj (Subtype.ext_iff.mp hPQ)

end HeckeRing.GLn.Inj

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n] (p : ℕ) (hp : p.Prime)

/-- Every element of R_p is in the image of evalHom (surjectivity).
    Proved for `n = 1` and `n = 2`; the general case is not yet formalised. -/
theorem T_gen_generates_R_p :
    ∀ f ∈ R_p n p hp, f ∈ (evalHom n p).range := by
  by_cases h1 : n = 1
  · subst h1; exact SurjOne.T_gen_generates_R_p_one p ‹_›
  · by_cases h2 : n = 2
    · subst h2; exact Surj.T_gen_generates_R_p_two p ‹_›
    · sorry -- General n requires Phase B (projection ψ) and Phase C (induction)

include hp in
/-- evalHom is injective. Proved for `n = 1` and `n = 2`;
    the general case is not yet formalised. -/
theorem evalHom_injective :
    Function.Injective (evalHom n p) := by
  by_cases h1 : n = 1
  · subst h1; exact Inj.evalHom_injective_one p ‹_›
  · by_cases h2 : n = 2
    · subst h2; exact Inj.evalHom_injective_two p ‹_›
    · sorry -- General n requires Phase B/C

/-- Shimura Theorem 3.20: the p-local Hecke ring is isomorphic to a polynomial ring.
    `R_p^{(n)} ≅ ℤ[X₁,...,Xₙ]`. -/
noncomputable def R_p_isPolynomialRing :
    MvPolynomial (Fin n) ℤ ≃+* R_p n p hp :=
  RingEquiv.ofBijective (Inj.evalHomR n p hp)
    ⟨Inj.evalHomR_injective n p hp (evalHom_injective n p hp),
     Inj.evalHomR_surjective n p hp (T_gen_generates_R_p n p hp)⟩


end HeckeRing.GLn
