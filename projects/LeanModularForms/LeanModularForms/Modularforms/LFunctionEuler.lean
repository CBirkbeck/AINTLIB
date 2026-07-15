/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Labels.NewformOrbit
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The Euler product of the L-function of a Hecke eigenform

For a normalised Hecke eigenform `f` (a `Newform N k`), the L-function factors as an Euler product
`L(s, f) = ∏_p (1 − aₚ p^{−s} + χ(p) p^{k−1−2s})^{−1}`
over the abscissa-of-absolute-convergence half-plane (`k/2 + 1 < Re s`).  Here `aₙ` are the
normalised Fourier coefficients (`a₁ = 1`) and `χ` is the Nebentypus character.

The proof has three ingredients:

* **Multiplicativity** (`Newform.coeffSeq_coprime_mul`): for coprime `m, n`,
  `a_{mn} = a_m · a_n`.  This is fed to mathlib's `EulerProduct.eulerProduct_tprod`, giving
  `LSeries (lCoeff f) s = ∏_p (∑_{r≥0} a_{p^r} p^{−rs})`.

* **Local factor** (`Newform.localFactor_eq`): the prime-power recursion
  `a_{p^{r+1}} = a_p a_{p^r} − χ(p) p^{k−1} a_{p^{r−1}}` (good `p`) / `a_{p^r} = a_p^r` (bad `p`)
  inverts the local series:
  `(1 − a_p X + χ(p) p^{k−1} X²) · (∑_{r≥0} a_{p^r} X^r) = 1` at `X = p^{−s}`.

* Assembly: `lSeries f s = ∏_p (1 − a_p p^{−s} + χ(p) p^{k−1−2s})^{−1}`.

## References

* [Shi] Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.5 (eq. 3.3.8).
* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9–5.10.
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16.
-/

open scoped BigOperators
open Complex UpperHalfPlane

namespace HeckeRing.GL2

/-! ### Abstract local-factor inversion

A purely formal lemma: a sequence `b` satisfying the degree-2 Hecke recurrence inverts the
local Euler quadratic. -/

namespace LocalFactor

variable {b : ℕ → ℂ} {X c d : ℂ}

private theorem const_mul_X_mul_tsum (hsum : Summable (fun e => b e * X ^ e)) :
    c * X * (∑' e, b e * X ^ e) = c * b 0 * X + ∑' e, c * b (e + 1) * X ^ (e + 2) := by
  have e1 : c * X * (∑' e, b e * X ^ e) = ∑' e, c * b e * X ^ (e + 1) := by
    rw [← hsum.tsum_mul_left (c * X)]; exact tsum_congr fun e => by ring
  have hsumc1 : Summable (fun e => c * b e * X ^ (e + 1)) := by
    have := hsum.mul_left c; exact (this.mul_right X).congr fun e => by ring
  rw [e1, hsumc1.tsum_eq_zero_add]
  have head : c * b 0 * X ^ (0 + 1) = c * b 0 * X := by norm_num
  rw [head]

private theorem const_mul_X_sq_mul_tsum (hsum : Summable (fun e => b e * X ^ e)) :
    d * X ^ 2 * (∑' e, b e * X ^ e) = ∑' e, d * b e * X ^ (e + 2) := by
  rw [← hsum.tsum_mul_left (d * X ^ 2)]; exact tsum_congr fun e => by ring

private theorem tsum_peel_two (hsum : Summable (fun e => b e * X ^ e)) :
    (∑' e, b e * X ^ e) = b 0 + (b 1 * X + ∑' e, b (e + 2) * X ^ (e + 2)) := by
  have hsum_s1 : Summable (fun e => b (e + 1) * X ^ (e + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have hinner : (∑' e, b (e + 1) * X ^ (e + 1)) = b 1 * X + ∑' e, b (e + 2) * X ^ (e + 2) := by
    rw [hsum_s1.tsum_eq_zero_add]
    have e1 : b (0 + 1) * X ^ (0 + 1) = b 1 * X := by norm_num
    rw [e1]
  rw [hsum.tsum_eq_zero_add, hinner]
  have e0 : b 0 * X ^ 0 = b 0 := by simp
  rw [e0]

private theorem tsum_tail_rec_eq_zero (hsum : Summable (fun e => b e * X ^ e))
    (hrec : ∀ e, b (e + 2) = c * b (e + 1) - d * b e) :
    (∑' e, b (e + 2) * X ^ (e + 2))
      - (∑' e, c * b (e + 1) * X ^ (e + 2))
      + (∑' e, d * b e * X ^ (e + 2)) = 0 := by
  have hsum_s1 : Summable (fun e => b (e + 1) * X ^ (e + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have htc : Summable (fun e => c * b (e + 1) * X ^ (e + 2)) := by
    have := hsum_s1.mul_left c; exact (this.mul_right X).congr fun e => by ring
  have htd : Summable (fun e => d * b e * X ^ (e + 2)) := by
    have := hsum.mul_left d; exact (this.mul_right (X ^ 2)).congr fun e => by ring
  have hBC : (∑' e, c * b (e + 1) * X ^ (e + 2)) - (∑' e, d * b e * X ^ (e + 2))
      = ∑' e, b (e + 2) * X ^ (e + 2) := by
    rw [← htc.tsum_sub htd]
    exact tsum_congr fun e => by rw [hrec e]; ring
  linear_combination -hBC

/-- **Abstract local-factor inversion.**  If `b` satisfies the degree-2 Hecke recurrence
`b(e+2) = c·b(e+1) − d·b(e)` with `b 0 = 1`, `b 1 = c`, and `e ↦ b e · X^e` is summable, then
`(1 − c·X + d·X²)·∑' b e X^e = 1`. -/
theorem inv (hsum : Summable (fun e => b e * X ^ e))
    (hb0 : b 0 = 1) (hb1 : b 1 = c)
    (hrec : ∀ e, b (e + 2) = c * b (e + 1) - d * b e) :
    (1 - c * X + d * X ^ 2) * ∑' e, b e * X ^ e = 1 := by
  have expand : (1 - c * X + d * X ^ 2) * (∑' e, b e * X ^ e)
      = (∑' e, b e * X ^ e) - c * X * (∑' e, b e * X ^ e)
        + d * X ^ 2 * (∑' e, b e * X ^ e) := by ring
  rw [expand, const_mul_X_mul_tsum hsum, const_mul_X_sq_mul_tsum hsum, tsum_peel_two hsum, hb0, hb1]
  linear_combination tsum_tail_rec_eq_zero hsum hrec

end LocalFactor

/-! ### Newform coefficient API: multiplicativity and the recurrence -/

namespace Newform

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ}

omit [NeZero N] in
/-- Coefficient of a scalar multiple at the canonical period. -/
private lemma qExp_one_coeff_smul (c : ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (j : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(c • g) : UpperHalfPlane → ℂ)).coeff j =
      c * (UpperHalfPlane.qExpansion (1 : ℝ) (⇑g : UpperHalfPlane → ℂ)).coeff j := by
  change (UpperHalfPlane.qExpansion (1 : ℝ) (c • g.toModularForm')).coeff j = _
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N) c g.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]
  rfl

/-- The full-eigenform scalar of `T_n` on a newform is the `n`-th coefficient `aₙ`. -/
private lemma heckeT_n_cusp_eq_coeffSeq_smul (f : Newform N k) (n : ℕ+) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val f.toCuspForm = coeffSeq f n • f.toCuspForm := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  obtain ⟨c, hc⟩ := f.exists_heckeT_n_cusp_smul n.val
  have hc_eq : c = coeffSeq f n := by
    have h1 : (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val =
        (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n.val f.toCuspForm)).coeff 1 :=
      coeff_n_eq_coeff_one_heckeT_n_cusp n.val f.χ f.toCuspForm f.mem_charSpace
    rw [hc, qExp_one_coeff_smul c f.toCuspForm 1, f.isNorm, mul_one] at h1
    simp only [coeffSeq]; exact h1.symm
  rw [hc, hc_eq]

/-- **General coprime multiplicativity of the coefficient sequence** (DS Theorem 5.8.2): for any
coprime `m, n`, `a_{mn} = a_m · a_n` — for **all** coprime indices, including those sharing factors
with `N`.  Combines the full-eigenform property `T_n f = aₙ · f` with the coprime coefficient shift
`a_m(T_n f) = a_{mn}(f)`. -/
theorem coeffSeq_coprime_mul (f : Newform N k) (m n : ℕ+) (hmn : Nat.Coprime m.val n.val) :
    coeffSeq f ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ = coeffSeq f m * coeffSeq f n := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hmul := coeff_heckeT_n_cusp_coprime_mul n.val f.χ f.toCuspForm f.mem_charSpace m.val hmn
  simp only [coeffSeq, PNat.mk_coe]
  rw [← hmul, heckeT_n_cusp_eq_coeffSeq_smul f n, qExp_one_coeff_smul (coeffSeq f n) f.toCuspForm
    m.val]
  simp only [coeffSeq]; ring

/-- Abbreviation: `coeffSeq f` read at a positive natural index. -/
private noncomputable def a (f : Newform N k) (j : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm).coeff j

private lemma a_eq_coeffSeq (f : Newform N k) (n : ℕ+) : a f n.val = coeffSeq f n := rfl

@[simp] private lemma a_one (f : Newform N k) : a f 1 = 1 := f.isNorm

/-- **Good-prime prime-power recurrence** (DS eq 5.20 / Hecke): for a prime `p ∤ N`,
`a_{p^{r+2}} = a_p · a_{p^{r+1}} − χ(p) p^{k−1} · a_{p^r}`. -/
theorem coeff_ppow_recurrence_good (f : Newform N k) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    a f (p ^ (r + 2)) = a f p * a f (p ^ (r + 1))
      - (↑(f.χ (ZMod.unitOfCoprime p hpN)) : ℂ) * (p : ℂ) ^ (k - 1) * a f (p ^ r) := by
  have hpp : 0 < p := hp.pos
  have hppow : 0 < p ^ (r + 1) := pow_pos hp.pos _
  have hFχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k f.χ := f.mem_charSpace
  have hF : IsNormalisedEigenform_one k f.toCuspForm.toModularForm' := f.isNormalisedEigenform
  have h := eigenform_coeff_multiplicative_one (N := N) k ⟨p, hpp⟩ ⟨p ^ (r + 1), hppow⟩
    hpN (hpN.pow_left _) f.χ hFχ hF
  simp only [PNat.mk_coe] at h
  have hgcd : Nat.gcd p (p ^ (r + 1)) = p := Nat.gcd_eq_left (dvd_pow_self p (Nat.succ_ne_zero r))
  have hunit : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  rw [hgcd, hp.divisors, Finset.sum_insert (by simp [hp.one_lt.ne]),
    Finset.sum_singleton, dif_pos hpN] at h
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    hunit, map_one, Units.val_one, one_mul, Nat.div_one] at h
  rw [show p * p ^ (r + 1) = p ^ (r + 2) by ring] at h
  rw [show p ^ (r + 2) / (p * p) = p ^ r by
        rw [show p * p = p ^ 2 by ring, pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos 2)]] at h
  -- bridge `f.toCuspForm.toModularForm'` (in `h`) to `f.toCuspForm` (in the goal); they are defeq
  have hbridge : (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm.toModularForm') =
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm) := rfl
  rw [hbridge] at h
  -- `h : a p * a (p^(r+1)) = a (p^(r+2)) + χ(p) p^{k-1} a (p^r)`
  show a f (p ^ (r + 2)) = a f p * a f (p ^ (r + 1)) - _ * (p : ℂ) ^ (k - 1) * a f (p ^ r)
  simp only [a]
  rw [h]; ring

/-- **Bad-prime prime-power recurrence**: for a prime `p ∣ N`, `a_{p^{r+1}} = a_p · a_{p^r}`
(the diamond term vanishes), via the `U_p` Fourier relation `a_l(U_p f) = a_{pl}(f)`. -/
theorem coeff_ppow_recurrence_bad (f : Newform N k) (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (r : ℕ) :
    a f (p ^ (r + 1)) = a f p * a f (p ^ r) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- `U_p f = a_p • f`
  have hUp : heckeT_n_cusp k p f.toCuspForm = a f p • f.toCuspForm :=
    f.heckeT_n_cusp_bad_prime_eq p hp hpN
  -- `a_{p^r}(U_p f) = a_{p · p^r}(f) = a_{p^{r+1}}(f)`
  have h1 := heckeT_n_cusp_divN_coeff p hp hpN f.toCuspForm (p ^ r)
  rw [hUp, qExp_one_coeff_smul (a f p) f.toCuspForm (p ^ r),
    show p * p ^ r = p ^ (r + 1) by ring] at h1
  -- `h1 : a_p * a_{p^r} = a_{p^{r+1}}`
  exact h1.symm

/-- The Nebentypus value `χ(p) := (dirichletLift f.χ)(p)`, extended by zero on `p ∣ N`. -/
private noncomputable def chip (f : Newform N k) (p : ℕ) : ℂ :=
  (Newform.dirichletLift f.χ) (p : ZMod N)

/-- For a good prime `p ∤ N`, `χ(p) = f.χ(unitOfCoprime p)`. -/
private lemma chip_good (f : Newform N k) {p : ℕ} (hpN : Nat.Coprime p N) :
    chip f p = (↑(f.χ (ZMod.unitOfCoprime p hpN)) : ℂ) := by
  unfold chip Newform.dirichletLift
  rw [show (p : ZMod N) = ((ZMod.unitOfCoprime p hpN : (ZMod N)ˣ) : ZMod N) from
    (ZMod.coe_unitOfCoprime p hpN).symm, MulChar.ofUnitHom_coe]

/-- For a bad prime `p ∣ N`, `χ(p) = 0`. -/
private lemma chip_bad (f : Newform N k) {p : ℕ} (hpN : ¬ Nat.Coprime p N) :
    chip f p = 0 := by
  unfold chip
  exact MulChar.map_nonunit _ (by rw [ZMod.isUnit_iff_coprime]; exact hpN)

/-- **Unified prime-power recurrence**: for any prime `p`,
`a_{p^{e+2}} = a_p · a_{p^{e+1}} − χ(p) p^{k−1} · a_{p^e}`, where `χ(p) = (dirichletLift f.χ)(p)`
is the Nebentypus value (zero at bad primes). -/
theorem coeff_ppow_recurrence (f : Newform N k) (p : ℕ) (hp : Nat.Prime p) (e : ℕ) :
    a f (p ^ (e + 2)) = a f p * a f (p ^ (e + 1)) - chip f p * (p : ℂ) ^ (k - 1) * a f (p ^ e) := by
  by_cases hpN : Nat.Coprime p N
  · rw [chip_good f hpN]; exact coeff_ppow_recurrence_good f p hp hpN e
  · rw [chip_bad f hpN, zero_mul, zero_mul, sub_zero]
    -- bad prime: `a_{p^{e+2}} = a_p · a_{p^{e+1}}`
    exact coeff_ppow_recurrence_bad f p hp hpN (e + 1)

/-! ### The L-series coefficient sequence -/

/-- The L-series coefficient `lCoeff f.toCuspForm` agrees with the normalised Fourier coefficient
`aₙ` (the level `Γ₁(N)` has strict width `1` at `∞`). -/
theorem lCoeff_eq_a (f : Newform N k) (n : ℕ) :
    ModularForms.lCoeff f.toCuspForm n = a f n := by
  rw [ModularForms.lCoeff_apply, ModularForms.strictWidthInfty_Gamma1_mapGL N]
  rfl

/-! ### Euler product assembly

We feed the L-series summand `g n = lCoeff f n · n^{-s}` (= `LSeries.term (lCoeff f) s`, which is
`a₁`-normalised and coprime-multiplicative) into mathlib's `EulerProduct.eulerProduct_tprod`. -/

open LSeries

variable (f : Newform N k) (s : ℂ)

/-- The L-series summand `g n = aₙ · n^{−s}` of a newform. -/
private noncomputable def lterm : ℕ → ℂ := LSeries.term (ModularForms.lCoeff f.toCuspForm) s

private lemma lterm_zero : lterm f s 0 = 0 := LSeries.term_zero _ _

private lemma lterm_one : lterm f s 1 = 1 := by
  rw [lterm, LSeries.term_of_ne_zero one_ne_zero, lCoeff_eq_a, a_one, Nat.cast_one,
    Complex.one_cpow, div_one]

/-- Multiplicativity of the L-series summand on coprime arguments. -/
private lemma lterm_coprime_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    lterm f s (m * n) = lterm f s m * lterm f s n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn
    rw [Nat.zero_mul, lterm_zero, zero_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn
    rw [Nat.mul_zero, lterm_zero, mul_zero]
  -- both positive: use `a_{mn} = a_m·a_n` and `(mn)^{-s} = m^{-s}·n^{-s}`
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  rw [lterm, LSeries.term_of_ne_zero hmn0, LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', lCoeff_eq_a, lCoeff_eq_a, lCoeff_eq_a]
  have hcop : a f (m * n) = a f m * a f n :=
    coeffSeq_coprime_mul f ⟨m, hm⟩ ⟨n, hn⟩ hmn
  rw [hcop, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  field_simp

/-- Norm-summability of the L-series summand on the absolute-convergence half-plane
`k/2 + 1 < Re s`. -/
private lemma lterm_summable_norm (hs : (k : ℝ) / 2 + 1 < s.re) :
    Summable (fun n => ‖lterm f s n‖) := by
  have hsum : LSeriesSummable (ModularForms.lCoeff f.toCuspForm) s :=
    ModularForms.lSeriesSummable_of_cuspForm f.toCuspForm hs
  rw [LSeriesSummable, ← summable_norm_iff] at hsum
  exact hsum

/-- `(↑(p^e))^(−s) = ((↑p)^(−s))^e`, the nat-power/`cpow` interchange for a prime power. -/
private lemma cpow_ppow (p e : ℕ) :
    ((p : ℂ) ^ (-s)) ^ e = ((p ^ e : ℕ) : ℂ) ^ (-s) := by
  induction e with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_comm]

/-- The L-series summand at a prime power factors as `a_{p^e} · X^e` with `X = p^{−s}`. -/
private lemma lterm_ppow (p : ℕ) (hp : Nat.Prime p) (e : ℕ) :
    lterm f s (p ^ e) = a f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  have hpe : p ^ e ≠ 0 := (pow_pos hp.pos e).ne'
  rw [lterm, LSeries.term_of_ne_zero hpe, lCoeff_eq_a, cpow_ppow, div_eq_mul_inv,
    Complex.cpow_neg]

/-- Norm-summability of the local series `e ↦ a_{p^e} · X^e` (a subsequence of the global
series). -/
private lemma local_summable (p : ℕ) (hp : Nat.Prime p) (hs : (k : ℝ) / 2 + 1 < s.re) :
    Summable (fun e => a f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) := by
  have hinj : Function.Injective (fun e => p ^ e) := Nat.pow_right_injective hp.two_le
  have h := (lterm_summable_norm f s hs).comp_injective hinj
  rw [← summable_norm_iff]
  refine h.congr fun e => ?_
  rw [Function.comp_apply, lterm_ppow f s p hp e]

/-- **The local Euler factor.**  On the absolute-convergence half-plane `k/2 + 1 < Re s`, the
local series at a prime `p` inverts the Hecke quadratic:
`∑_{e≥0} a_{p^e} p^{−es} = (1 − a_p p^{−s} + χ(p) p^{k−1−2s})^{−1}`, equivalently
`(1 − a_p p^{−s} + χ(p) p^{k−1−2s}) · (∑_e a_{p^e} p^{−es}) = 1`. -/
theorem localFactor_mul_eq_one (p : ℕ) (hp : Nat.Prime p) (hs : (k : ℝ) / 2 + 1 < s.re) :
    (1 - a f p * (p : ℂ) ^ (-s) + chip f p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))
        * ∑' e, lterm f s (p ^ e) = 1 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  set X : ℂ := (p : ℂ) ^ (-s) with hX
  set c : ℂ := a f p with hc
  set d : ℂ := chip f p * (p : ℂ) ^ ((k : ℂ) - 1) with hd
  -- rewrite the local series as `∑' e, a_{p^e} X^e`
  have hser : (∑' e, lterm f s (p ^ e)) = ∑' e, a f (p ^ e) * X ^ e :=
    tsum_congr fun e => lterm_ppow f s p hp e
  rw [hser]
  -- the local series inverts `1 − cX + dX²` via the abstract inversion lemma
  have hkey : (1 - c * X + d * X ^ 2) * ∑' e, a f (p ^ e) * X ^ e = 1 := by
    refine LocalFactor.inv (b := fun e => a f (p ^ e)) (local_summable f s p hp hs) ?_ ?_ ?_
    · simp only [pow_zero]; exact a_one f
    · rw [pow_one]
    · intro e
      -- the unified recurrence; bridge `zpow (k-1)` to `cpow ((k:ℂ)-1)`
      have hrec := coeff_ppow_recurrence f p hp e
      have hzc : (p : ℂ) ^ ((k : ℤ) - 1) = (p : ℂ) ^ ((k : ℂ) - 1) := by
        rw [← Complex.cpow_intCast]; push_cast; ring_nf
      rw [hrec, hd, hzc]
  -- convert the quadratic coefficient `d·X²` to `χ(p)·p^{k−1−2s}`
  have hdX2 : d * X ^ 2 = chip f p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
    rw [hd, hX, mul_assoc]
    congr 1
    rw [show ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s) by ring,
      ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0]
    ring_nf
  rw [← hdX2]
  exact hkey

/-- The local series equals the reciprocal of the local Euler factor. -/
theorem localFactor_eq (p : ℕ) (hp : Nat.Prime p) (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∑' e, lterm f s (p ^ e))
      = (1 - a f p * (p : ℂ) ^ (-s) + chip f p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact localFactor_mul_eq_one f s p hp hs))

/-- **Euler product of the L-function of a Hecke eigenform** (Shimura §3.5 eq. 3.3.8;
Diamond–Shurman §5.9–5.10; Miyake Thm 4.5.16).

For a normalised newform `f` of level `Γ₁(N)`, weight `k`, with Nebentypus character `χ`
(`dirichletLift f.χ`, extended by zero on `p ∣ N`), and `s` in the absolute-convergence
half-plane `k/2 + 1 < Re s`, the L-function factors as an Euler product over the primes:
`L(s, f) = ∏_p (1 − aₚ p^{−s} + χ(p) p^{k−1−2s})^{−1}`,
where `aₙ = (lCoeff f.toCuspForm) n` are the normalised Fourier coefficients (`a₁ = 1`). -/
theorem lSeries_eulerProduct (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForms.lSeries f.toCuspForm s =
      ∏' p : Nat.Primes,
        (1 - ModularForms.lCoeff f.toCuspForm p * (p : ℂ) ^ (-s)
          + (Newform.dirichletLift f.χ) (p : ZMod N)
              * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ := by
  -- the Euler product for the multiplicative L-series summand
  have hEP := EulerProduct.eulerProduct_tprod (f := lterm f s) (lterm_one f s)
    (fun {m n} h => lterm_coprime_mul f s h) (lterm_summable_norm f s hs) (lterm_zero f s)
  -- `∑' n, lterm f s n = L(s, f)`
  have hLS : (∑' n, lterm f s n) = ModularForms.lSeries f.toCuspForm s := rfl
  rw [hLS] at hEP
  -- replace each local series by the reciprocal local factor, restated with public coefficients
  rw [← hEP]
  refine tprod_congr fun p => ?_
  rw [lCoeff_eq_a]
  exact localFactor_eq f s (p : ℕ) p.prop hs

end Newform

end HeckeRing.GL2
