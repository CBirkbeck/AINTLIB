import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasse37CoefficientClosedForm

/-!
# The degree-`68` log-coefficient recurrence: `[Tᵐ] log((E₃₇−1)/T)` via the log ODE

This file develops the degree-`68` log-coefficient side of the Artin-Hasse computation: the formal
log `ℓ := logOf(g_AH)` of the normalized numerator `g_AH = (E₃₇−1)/T` satisfies the **log ODE**
`ℓ′·g_AH = g_AH′`, which gives a linear recurrence for its coefficients `ℓₘ := [Tᵐ] ℓ` in terms of
the (proven, closed-form) coefficients `[Tᵏ] g_AH = c(k+1)` (`coeff_gAH_eq`).  It imports only; it
does **not** modify any existing file.  No `sorry`, no `axiom`.

## The log ODE and the coefficient recurrence (proven)

`g_AH` has constant coefficient `1` (`[T⁰] g_AH = c 1 = 1`).  By `subst_deriv_log_mul_one_add`
applied at `a = g_AH − 1` (`HasSubst`, constant coeff `0`), `subst(g_AH−1)(log′)·g_AH = 1`, so
`ℓ′ = subst(g_AH−1)(log′)·(g_AH−1)′ = subst(g_AH−1)(log′)·g_AH′` and hence `ℓ′·g_AH = g_AH′`
(`derivative_logOf_gAH_mul_self`).  Taking `[Tⁿ]` of this identity (with `[T⁰] g_AH = 1`) yields,
for each `n`, the recurrence

  `(n+1)·ℓ_{n+1} = (n+1)·g_{n+1} − ∑_{k=0}^{n-1} (k+1)·ℓ_{k+1}·g_{n−k}`,

`g_j := [Tʲ] g_AH`, which determines `ℓ_{n+1}` from `ℓ_1, …, ℓ_n` and the explicit `g_j = c(j+1)`.

The factorial-weighted target is `formalSum68 = 68!·[T⁶⁸] logOf(g_AH) = 68!·ℓ₆₈`
(`coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff`); this file packages `ℓ₆₈` as a
single explicit rational built from `c(1), …, c(69)`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open PowerSeries

namespace ArtinHasse37

/-- Local shorthand: the normalized Artin-Hasse numerator `g_AH = (E₃₇−1)/T`. -/
def gAH : PowerSeries ℚ := CyclotomicUnits.rationalArtinHasseNormalizedExpMinusOneSeries 37

/-- Local shorthand: the formal log `ℓ = logOf(g_AH)`. -/
def logG : PowerSeries ℚ := PowerSeries.logOf gAH

/-! ## 1. The constant coefficient of `g_AH` is `1` -/

/-- **`[T⁰] g_AH = 1`** (proven): the normalized numerator has constant coefficient `c 1 = 1`. -/
theorem coeff_zero_gAH : (PowerSeries.coeff (R := ℚ) 0) gAH = 1 := by
  rw [gAH, coeff_gAH_eq (by norm_num : (0 : ℕ) ≤ 72), c]
  norm_num

/-- **`constantCoeff g_AH = 1`** (proven). -/
theorem constantCoeff_gAH : PowerSeries.constantCoeff gAH = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_gAH

/-! ## 2. The log ODE `ℓ′·g_AH = g_AH′` -/

/-- **The log ODE** (proven): `(d⁄dX logG)·g_AH = d⁄dX g_AH`.

`g_AH` has constant coefficient `1`, so `a := g_AH − 1` has `HasSubst`; by
`subst_deriv_log_mul_one_add`, `subst(a)(log′)·(1 + a) = subst(a)(log′)·g_AH = 1`.  And
`ℓ′ = (logOf g_AH)′ = subst(a)(log′)·a′ = subst(a)(log′)·g_AH′` (chain rule, `a′ = g_AH′`).  Hence
`ℓ′·g_AH = subst(a)(log′)·g_AH·g_AH′ = g_AH′`.  Mirror of
`KummerLogFormal.derivative_logOf_formalExpNormalizedMinusOne_mul_self`. -/
theorem derivative_logOf_gAH_mul_self :
    (d⁄dX ℚ logG) * gAH = d⁄dX ℚ gAH := by
  have hc0 : PowerSeries.constantCoeff (gAH - 1) = 0 := by
    rw [map_sub, map_one, constantCoeff_gAH, sub_self]
  have hsubst : PowerSeries.HasSubst (gAH - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hc0
  have hgeom :
      PowerSeries.subst (gAH - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * gAH = 1 := by
    have h := Furtwaengler.FiniteLogFormal.subst_deriv_log_mul_one_add (A := ℚ) hsubst
    have hone_add : (1 : PowerSeries ℚ) + (gAH - 1) = gAH := by ring
    rwa [hone_add] at h
  rw [logG, PowerSeries.logOf_eq, PowerSeries.derivative_subst ℚ hsubst]
  have hderiv_sub : d⁄dX ℚ (gAH - 1) = d⁄dX ℚ gAH := by simp
  calc
    (PowerSeries.subst (gAH - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) *
          d⁄dX ℚ (gAH - 1)) * gAH
        = (PowerSeries.subst (gAH - 1) (d⁄dX ℚ (PowerSeries.log ℚ)) * gAH) *
            d⁄dX ℚ (gAH - 1) := by ring
    _ = 1 * d⁄dX ℚ (gAH - 1) := by rw [hgeom]
    _ = d⁄dX ℚ gAH := by rw [one_mul, hderiv_sub]

/-! ## 3. The coefficient recurrence for `ℓ = logOf(g_AH)` -/

/-- **The log-coefficient convolution identity** (proven): for every `n`,

  `∑_{k=0}^{n} (k+1)·([T^(k+1)] logG)·([T^(n−k)] g_AH) = (n+1)·[T^(n+1)] g_AH`.

This is `[Tⁿ]` of the log ODE `ℓ′·g_AH = g_AH′` (`derivative_logOf_gAH_mul_self`): the left side is
`[Tⁿ]((d⁄dX logG)·g_AH)` via `coeff_mul` over the antidiagonal (`[T^k](d⁄dX logG) = (k+1)·[T^(k+1)]
logG`), the right side is `[Tⁿ](d⁄dX g_AH) = (n+1)·[T^(n+1)] g_AH`. -/
theorem logG_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((k : ℚ) + 1) * (PowerSeries.coeff (R := ℚ) (k + 1)) logG *
          (PowerSeries.coeff (R := ℚ) (n - k)) gAH =
      ((n : ℚ) + 1) * (PowerSeries.coeff (R := ℚ) (n + 1)) gAH := by
  have hode := congrArg (PowerSeries.coeff (R := ℚ) n) derivative_logOf_gAH_mul_self
  rw [PowerSeries.coeff_mul, coeff_derivative,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hode
  rw [mul_comm ((n : ℚ) + 1)]
  rw [← hode]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [coeff_derivative]
  ring

/-! ## 4. The explicit log-coefficient sequence `Lr` and the bridge `[Tᵐ] logG = Lr m` -/

/-- **The explicit coefficient sequence** `gco j := c (j+1)`, equal to `[Tʲ] g_AH` for `j ≤ 72`
(`coeff_gAH_eq`).  All entries are concrete rationals. -/
def gco (j : ℕ) : ℚ := c (j + 1)

/-- **The accumulator list** `LrList n = [Lr 0, Lr 1, …, Lr n]` (length `n + 1`), built by
structural recursion: each new entry `Lr (n+1)` is computed from the recurrence reading the previous
entries off the accumulated list.  Avoids well-founded recursion. -/
def LrList : ℕ → List ℚ
  | 0 => [0]
  | (n + 1) =>
      let prev := LrList n
      let s := ∑ k ∈ Finset.range n,
        ((k : ℚ) + 1) * (prev.getD (k + 1) 0) * gco (n - k)
      prev ++ [gco (n + 1) - s / ((n : ℚ) + 1)]

/-- **The explicit log-coefficient sequence** `Lr m`, the `m`-th entry of `LrList m`, defined by the
same recurrence the log ODE forces on `[Tᵐ] logG`:

  `Lr 0 = 0`,  `Lr (n+1) = gco (n+1) − (∑_{k=0}^{n−1} (k+1)·Lr (k+1)·gco (n−k)) / (n+1)`,

with `gco j = c (j+1)`.  For `m ≤ 68`, `Lr m = [Tᵐ] logG = [Tᵐ] log((E₃₇−1)/T)` (`coeff_logG_eq`);
`Lr 68` is the degree-`68` log coefficient. -/
def Lr (m : ℕ) : ℚ := (LrList m).getD m 0

/-- **`LrList` has length `n + 1`** (proven by induction). -/
theorem LrList_length (n : ℕ) : (LrList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [LrList, List.length_append, ih]; simp

/-- **`LrList (n+1)` extends `LrList n`** (proven): `LrList n` is a prefix, so earlier entries are
stable across the accumulation.  Hence `(LrList m).getD k 0 = Lr k` for `k ≤ m`. -/
theorem LrList_getD_eq_Lr {m k : ℕ} (hk : k ≤ m) :
    (LrList m).getD k 0 = Lr k := by
  induction m with
  | zero =>
    interval_cases k
    rfl
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with hlt | heq
    · -- `k ≤ n`: the entry is in the prefix `LrList n`, unchanged by the append.
      have hkn : k ≤ n := by omega
      change ((LrList n) ++ [_]).getD k 0 = Lr k
      rw [List.getD_append _ _ _ _ (by rw [LrList_length]; omega), ih hkn]
    · -- `k = n + 1`: this is the freshly-appended entry, i.e. `Lr (n+1)`.
      subst heq
      rfl

/-- **`Lr` unfolding at a successor** (proven): the defining recurrence, stated for `rw`.
`Lr (n+1)` is the last entry of `LrList (n+1)`, the appended value, and the previous-entry reads
`(LrList n).getD (k+1) 0` equal `Lr (k+1)` for `k < n` (`LrList_getD_eq_Lr`). -/
theorem Lr_succ (n : ℕ) :
    Lr (n + 1) =
      gco (n + 1) -
        (∑ k ∈ Finset.range n, ((k : ℚ) + 1) * Lr (k + 1) * gco (n - k)) / ((n : ℚ) + 1) := by
  have hlen : (LrList n).length = n + 1 := LrList_length n
  change ((LrList n) ++ [_]).getD (n + 1) 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self]
  change (gco (n + 1) - _ / ((n : ℚ) + 1)) = _
  congr 2
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  rw [LrList_getD_eq_Lr (by omega : k + 1 ≤ n)]

/-! ## 5. The bridge `[Tᵐ] logG = Lr m` for `m ≤ 68` -/

/-- **`Lr 0 = 0`** (proven). -/
theorem Lr_zero : Lr 0 = 0 := rfl

/-- **`[T⁰] logG = 0`** (proven): the constant coefficient of `logOf g_AH` is `0` (as
`constantCoeff g_AH = 1`). -/
theorem coeff_zero_logG : (PowerSeries.coeff (R := ℚ) 0) logG = 0 := by
  rw [logG, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_logOf constantCoeff_gAH]

/-- **The bridge `[Tᵐ] logG = Lr m`** (proven): for every `m ≤ 68`, the degree-`m` coefficient of
`logG = log((E₃₇−1)/T)` equals the explicit recursive value `Lr m`.

By strong induction on `m`: the base case `m = 0` is `coeff_zero_logG`/`Lr_zero` (both `0`); the
step at `n + 1` isolates the `k = n` term of the convolution `logG_convolution n`, namely
`(n+1)·([T^(n+1)] logG)·([T⁰] g_AH) = (n+1)·[T^(n+1)] logG` (as `[T⁰] g_AH = 1`), giving

  `(n+1)·[T^(n+1)] logG = (n+1)·g_{n+1} − ∑_{k<n} (k+1)·([T^(k+1)] logG)·g_{n−k}`,

and the strong-induction hypothesis (`[T^(k+1)] logG = Lr (k+1)` for `k < n`) plus the explicit
`g_j = gco j = c (j+1)` (`coeff_gAH_eq`, `j ≤ 72`) make the right side exactly `(n+1)·Lr (n+1)`
(`Lr_succ`).  Cancelling the nonzero `n+1` gives `[T^(n+1)] logG = Lr (n+1)`. -/
theorem coeff_logG_eq : ∀ {m : ℕ}, m ≤ 68 → (PowerSeries.coeff (R := ℚ) m) logG = Lr m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m with
    | 0 => rw [coeff_zero_logG, Lr_zero]
    | (n + 1) =>
      have hconv := logG_convolution n
      -- Split off the `k = n` term: `(n+1)·ℓ_{n+1}·g₀ = (n+1)·ℓ_{n+1}` (since `g₀ = 1`).
      rw [Finset.sum_range_succ, Nat.sub_self, coeff_zero_gAH, mul_one] at hconv
      -- The remaining `∑_{k<n}` terms: rewrite `ℓ_{k+1} = Lr (k+1)` (IH) and `g_{n-k} = gco (n-k)`.
      have hsum : ∑ k ∈ Finset.range n,
            ((k : ℚ) + 1) * (PowerSeries.coeff (R := ℚ) (k + 1)) logG *
              (PowerSeries.coeff (R := ℚ) (n - k)) gAH =
          ∑ k ∈ Finset.range n,
            ((k : ℚ) + 1) * Lr (k + 1) * gco (n - k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ih (k + 1) (by omega) (by omega), gAH,
          coeff_gAH_eq (by omega : n - k ≤ 72)]
        rfl
      rw [hsum] at hconv
      -- `g_{n+1} = c (n+1+1) = gco (n+1)` (`n + 1 ≤ 72`, true as `n + 1 ≤ 68`).
      rw [gAH, coeff_gAH_eq (by omega : n + 1 ≤ 72), show c (n + 1 + 1) = gco (n + 1) from rfl]
        at hconv
      -- Now `(n+1)·([T^(n+1)] logG) = (n+1)·gco(n+1) - ∑ ... = (n+1)·Lr(n+1)`.
      have hnp : ((n : ℚ) + 1) ≠ 0 := by positivity
      rw [Lr_succ]
      -- From `hconv`: `Σ + (n+1)·ℓ = (n+1)·gco(n+1)`, so `ℓ = gco(n+1) − Σ/(n+1)`.
      rw [eq_sub_iff_add_eq]
      field_simp
      linarith [hconv]

end ArtinHasse37

end BernoulliRegular.FLT37.Eichler

end
