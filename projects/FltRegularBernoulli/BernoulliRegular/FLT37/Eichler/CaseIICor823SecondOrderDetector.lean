import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderMatrix

/-!
# The second-order detector vanishes for the descent congruence (`p`-adic-`L` valuation half)

This file proves the **second-order detector-vanishing** half of Washington Proposition 8.12 at
`i = 32` for `p = 37`: for a unit `u : (𝓞 K⁺)ˣ` whose `K`-image is congruent to a rational integer
modulo `37²`, the mod-`37²` `varpi^32` Dwork detector of the descent logarithm vanishes.  Combined
with the genuine leading-coefficient residual `Prop812SecondOrderCoeff37`
(`CaseIICor823SecondOrderMatrix.lean`), this is what discharges
`Cor823Omega32SecondOrderCollapse37` — and hence `R4`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The genuine second-order valuation analysis

The completed-log argument of `u^{36}` is `X^{36} - 1` (`X = EPlus_valuedLocalImage u`).  Unlike the
first order, the second-order analysis cannot use "`X^{36} - 1 ∈ λ^{72}`": the proven
`caseIICor823_localImage_pow36_sub_intCast_pow36_mem_lambdaIdeal_pow72` only gives
`X^{36} - c^{36} ∈ λ^{72}`, and `c^{36} ≡ 1 (mod 37²)` *fails* in general (the descent unit `u` need
not satisfy the sharp Fermat congruence at the second order).  So the argument splits as

  `X^{36} - 1 = (X^{36} - c^{36}) + (c^{36} - 1)`,

with `X^{36} - c^{36} ∈ λ^{72}` (proven) and `c^{36} - 1 ∈ (37) = λ^{36}` (Fermat, a *rational
integer*).

The detector reads the `varpi^32` Dwork coordinate modulo `37²` at the second-order precision
`λ`-level `72`:
* the same-prime logarithm `samePrimeFiniteLog 71 arg` equals `mk(arg) mod λ^{72}` because every
  `n ≥ 2` log term has `λ`-order `≥ 2·36 = 72` (`arg ∈ λ^{36}`, `samePrimeFiniteLog_eq_mk` at the
  *high* level `71` — §1, the level-`N`/power-`m` generalisation of
  `samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le`);
* the `varpi^32` coordinate of `mk(arg) = mk((X^{36}-c^{36}) + (c^{36}-1))` modulo `37²` is `0`: the
  `X^{36}-c^{36}` part lies in `λ^{72}` so its coordinate vanishes mod `37²`, and the `c^{36}-1`
  part
  is a *rational constant*, contributing only to the `varpi^0` coordinate.

## What is built (real, axiom-clean Lean)

* **§1** — `samePrimeFiniteLog_eq_mk_of_mem_pow_high_level`: for `x ∈ λ^m`, `m ≥ 2`, and a level
  `N` with `N + 1 ≤ 2*m`, the same-prime logarithm `samePrimeFiniteLog N x = mk(x) mod λ^{N+1}` (all
  `n ≥ 2` terms vanish). The level-`N`/power-`m` generalisation of the proven
  `…_of_mem_pow_of_two_le`.

* **§2** — `caseIICor823SecondOrder_argCoeffModSq_eq_zero`: the `varpi^32` mod-`37²` Dwork
  coordinate
  of the descent log argument `X^{36} - 1` is `0`, from the `λ^{72}` split (proven non-constant part
  in `λ^{72}` plus the rational constant `c^{36}-1`).

* **§3** — `caseIICor823SecondOrder_detector_descent_eq_zero`: the mod-`37²` `varpi^32` detector of
  the descent logarithm `completedLog(u^{36})` vanishes, for `u` with `37² ∣ algebraMap u - c`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, p. 171),
  §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ## 1. The same-prime logarithm equals its argument at a high precision level

For `x ∈ λ^m` (`m ≥ 2`) and a level `N` with `N + 1 ≤ 2*m`, every `n ≥ 2` term of the same-prime
finite logarithm vanishes (its `λ`-order `n·m - v_p(n)(p-1) ≥ 2m ≥ N+1`), so the logarithm equals
its
argument `mk(x) mod λ^{N+1}`.  The level-`N`/power-`m` generalisation of the proven
`samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le` (which is the special case `N = m`). -/

theorem samePrimeFiniteLogTerm_eq_zero_of_mem_pow_high_level
    {N m n : ℕ} (hp : 3 ≤ p) (hm : 2 ≤ m) (hn : 2 ≤ n) (hN : N + 1 ≤ 2 * m)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m)
    (hxI : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hxI = 0 := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)
  -- `x ^ n ∈ λ^{v(n)(p-1) + s}` with `s = n*m - v(n)(p-1)`.
  set s : ℕ := n * m - n.factorization p * (p - 1) with hs
  have hxpow_s :
      x ^ n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    have hxpow : x ^ n ∈ ((lambdaIdeal p K) ^ m) ^ n := Ideal.pow_mem_pow hx n
    have hxpow_nm : x ^ n ∈ (lambdaIdeal p K) ^ (m * n) := by
      simpa [pow_mul] using hxpow
    have hden_le : n.factorization p * (p - 1) ≤ n * m := by
      have hle := Nat.factorization_mul_pred_le_pred
        (ell := p) (n := n) (Fact.out : Nat.Prime p) hn_ne
      have hle' : n.factorization p * (p - 1) ≤ n - 1 := by
        simpa [Nat.mul_comm] using hle
      have : n - 1 ≤ n * m := (Nat.sub_le n 1).trans
        (Nat.le_mul_of_pos_right n (lt_of_lt_of_le (by decide : 0 < 2) hm))
      exact hle'.trans this
    have hsum : n.factorization p * (p - 1) + s = n * m := by rw [hs]; omega
    have hsum' : n.factorization p * (p - 1) + s = m * n := by
      rw [hsum]; ring
    simpa [hsum'] using hxpow_nm
  -- The term is `samePrimeNatDivEval N n s …`, which is `0` because `N + 1 ≤ s`.
  have hdeg : n.factorization p * (p - 1) ≤ n := by
    have h := Nat.factorization_mul_pred_le_pred (ell := p) (n := n)
      (Fact.out : Nat.Prime p) hn_ne
    omega
  have htermCore :
      samePrimeFiniteLogTermCore (p := p) (K := K) N n x hxI =
        samePrimeNatDivEval (p := p) (K := K) N n s hn_ne (x ^ n) hxpow_s := by
    rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree
      (p := p) (K := K) hn_ne hxI]
    exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
      (p := p) (K := K) hn_ne (Ideal.pow_mem_pow hxI n) hdeg hxpow_s
  rw [samePrimeFiniteLogTerm, htermCore]
  have hNs : N + 1 ≤ s := by
    -- `N + 1 ≤ s = n*m - v(n)(p-1)`: from `N+1 ≤ 2m` and `2m + v(n)(p-1) ≤ n*m` for `n ≥ 2`.
    rw [hs]
    have hle := Nat.factorization_mul_pred_le_pred (ell := p) (n := n)
      (Fact.out : Nat.Prime p) hn_ne
    have hle' : n.factorization p * (p - 1) ≤ n - 1 := by
      simpa [Nat.mul_comm] using hle
    -- The core arithmetic: `2*m + v(n)(p-1) ≤ n*m`, hence `2m ≤ n*m - v(n)(p-1)`.
    have hge : 2 * m + n.factorization p * (p - 1) ≤ n * m := by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · -- `n = 2`: `v_p(2) = 0` (since `p ≥ 3`), so `2m + 0 ≤ 2m`.
        have hn2 : n = 2 := by omega
        subst hn2
        have hv0 : (2 : ℕ).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl (fun hdvd ↦ by
            have := Nat.le_of_dvd (by norm_num) hdvd; omega))
        rw [hv0]; omega
      · -- `n ≥ 3`: `2m + (n-1) ≤ n*m`, and `v(n)(p-1) ≤ n-1`.
        have hprod : (n - 2) * 2 ≤ (n - 2) * m := Nat.mul_le_mul_left _ hm
        have hexp : n * m = 2 * m + (n - 2) * m := by
          conv_lhs => rw [show n = 2 + (n - 2) from by omega]
          rw [add_mul]
        omega
    omega
  rw [samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K) hn_ne hxpow_s hNs]
  simp

theorem samePrimeFiniteLog_eq_mk_of_mem_pow_high_level
    {N m : ℕ} (hp : 3 ≤ p) (hm : 2 ≤ m) (hN : N + 1 ≤ 2 * m)
    {x : ValuedIntegerRing p K} (hx : x ∈ (lambdaIdeal p K) ^ m)
    (hxI : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N x hxI =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x := by
  classical
  unfold samePrimeFiniteLog
  rw [Finset.sum_eq_single 1]
  · exact samePrimeFiniteLogTerm_one_eq_mk (p := p) (K := K) N hxI
  · intro n _hn_range hn_ne_one
    by_cases hn0 : n = 0
    · subst n; simp
    · exact samePrimeFiniteLogTerm_eq_zero_of_mem_pow_high_level
        (p := p) (K := K) hp hm (by omega) hN hx hxI
  · intro hnot
    exfalso
    have hcut : 1 < samePrimeFiniteLogCutoff (p := p) N := by
      calc
        1 < p := (Fact.out : Nat.Prime p).one_lt
        _ ≤ p * (N + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos N)
    exact hnot (by simpa [samePrimeFiniteLogCutoff] using hcut)

/-! ## 1.5. The mod-`p²` `varpi^k` coordinate of a constant and of a `λ^{2(p-1)}`-element

The second-order coefficient `valuedLambdaQuotientDworkCoeffModSq k` kills the constant `varpi^0`
contributions at every positive index `k ≥ 1`, and kills any `λ^{2(p-1)}`-element entirely (its
coordinate congruence with `0`). -/

/-- The mod-`p²` `varpi^k` Dwork coordinate of a rational-integer constant `c` vanishes at every
positive index `k` (`(k : ℕ) ≠ 0`): the constant maps to the `varpi^0` coordinate only. -/
theorem valuedLambdaQuotientDworkCoeffModSq_mk_intCast_eq_zero
    (k : Fin (p - 1)) (hk : (k : ℕ) ≠ 0) (c : ℤ) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1)))
          (c : ValuedIntegerRing p K)) = 0 := by
  classical
  rw [valuedLambdaQuotientDworkCoeffModSq_mk]
  -- `algebraMap (c : ValuedInteger) = dworkParameterPowerLinearMap (Pi.single 0 c')`, whose repr at
  -- `k ≠ 0` is `0`.
  set c' : RationalPadicIntegerRing p :=
    (c : RationalPadicIntegerRing p) with hc'
  have hzero_idx : (0 : ℕ) < p - 1 := by have := (Fact.out : Nat.Prime p).two_le; omega
  have hsingle :
      algebraMap (ValuedIntegerRing p K) (DworkCompleteIntegerRing p K)
          (c : ValuedIntegerRing p K) =
        dworkParameterPowerLinearMap p K
          (Pi.single (⟨0, hzero_idx⟩ : Fin (p - 1)) c') := by
    rw [dworkParameterPowerLinearMap_single_coeff]
    simp only [pow_zero, mul_one]
    rw [hc', map_intCast, map_intCast]
  rw [hsingle, dworkParameterPowerBasis_repr_powerLinearMap]
  rw [Pi.single_eq_of_ne (fun hcontra ↦ hk (by rw [hcontra]))]
  rw [map_zero]

/-- The mod-`p²` `varpi^k` Dwork coordinate of a `λ^{2(p-1)}`-element vanishes (its coordinate
congruence with `0` modulo `p²`, the §1 coordinate congruence with `y = 0`). -/
theorem valuedLambdaQuotientDworkCoeffModSq_mk_eq_zero_of_mem_pow
    (k : Fin (p - 1)) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (2 * (p - 1))) :
    valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) k
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) z) = 0 := by
  rw [show Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) z =
      (0 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (2 * (p - 1))) from by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact hz]
  exact valuedLambdaQuotientDworkCoeffModSq_zero (p := p) (K := K) k

end BernoulliRegular.CyclotomicUnits

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 2. The `varpi^32` mod-`37²` coordinate of the descent log argument vanishes

For `u` with `37² ∣ algebraMap u - c`, the descent log argument `X^{36} - 1` (`X =
EPlus_valuedLocalImage
u`) has its `varpi^32` mod-`37²` Dwork coordinate equal to `0`, via the split
`X^{36} - 1 = (X^{36} - c^{36}) + (c^{36} - 1)` with the non-constant part in `λ^{72}` (proven) and
the constant `c^{36} - 1` contributing only to `varpi^0`. -/

set_option maxHeartbeats 2000000 in
-- The membership ideal `(lambdaIdeal)^(2*(37-1))` over the heavy `adicCompletionIntegers` ring
-- forces
-- a `whnf`/`isDefEq` above the default budget; the §1 coordinate lemmas dodge it but the assembly
-- needs the raised limit (well below the non-terminating `Ideal.pow` `whnf` wall).
/-- **The `varpi^32` mod-`37²` coordinate of the descent log argument is `0`** (proven,
axiom-clean).
For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u - c`, the `varpi^32` mod-`37²` Dwork coordinate of the
descent log argument `(EPlus_valuedLocalImage u)^{36} - 1` vanishes.

Proof: split `X^{36} - 1 = (X^{36} - c^{36}) + (c^{36} - 1)`.  The first summand lies in `λ^{72}` by
the proven `caseIICor823_localImage_pow36_sub_intCast_pow36_mem_lambdaIdeal_pow72`, so its
coordinate
vanishes (`…_mk_eq_zero_of_mem_pow`); the second is the rational constant `c^{36} - 1`, whose
`varpi^32` coordinate vanishes since `32 ≥ 1` (`…_mk_intCast_eq_zero`). -/
theorem caseIICor823SecondOrder_argCoeffModSq_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))))
    (k : Fin (37 - 1)) (hk : (k : ℕ) = 32) :
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
        (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
          ((EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
              ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1)) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set X : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) :=
    (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
      ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) with hX
  -- The split `X³⁶ - 1 = (X³⁶ - c³⁶) + (c³⁶ - 1)`.
  have hsplit : X ^ 36 - 1 =
      (X ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36) +
        ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1) := by ring
  rw [hsplit, map_add, valuedLambdaQuotientDworkCoeffModSq_add]
  -- First summand: in `λ^{2(37-1)} = λ^{72}`, coordinate vanishes.  The proven membership is at
  -- exponent `72`; transport to `2*(37-1)` (definitionally equal) keeping the element opaque to
  -- dodge the `adicCompletionIntegers` `Ideal.pow` `whnf` wall.
  have hmem72 :
      X ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 ∈
        (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)) := by
    have h := caseIICor823_localImage_pow36_sub_intCast_pow36_mem_lambdaIdeal_pow72 u c hc
    rw [hX]
    generalize (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 -
        (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 = W at h ⊢
    convert h using 2
  have h1 : valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
      (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        (X ^ 36 - (c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36)) = 0 :=
    valuedLambdaQuotientDworkCoeffModSq_mk_eq_zero_of_mem_pow (p := 37) k hmem72
  -- Second summand: rational constant `c³⁶ - 1`, `varpi^32` coordinate vanishes.
  have h2 : valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ) k
      (Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1)) = 0 := by
    rw [show ((c : ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1) =
        (((c ^ 36 - 1 : ℤ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ))) from by
          push_cast; ring]
    exact valuedLambdaQuotientDworkCoeffModSq_mk_intCast_eq_zero (p := 37) k (by rw [hk]; decide)
      (c ^ 36 - 1)
  rw [h1, h2, add_zero]

/-! ## 3. The mod-`37²` `varpi^32` detector of the descent logarithm vanishes

For `u` with `37² ∣ algebraMap u - c`, the mod-`37²` `varpi^32` Dwork detector of the descent
logarithm `completedLog(u^{36})` vanishes.  The detector is read at the second-order precision
`λ`-level `72 = 2*(37-1)`: by `completedLog_evalₐ_succ` it is the `varpi^32` coordinate of
`samePrimeFiniteLog 71 arg` (`arg = X^{36} - 1`); by §1 (`arg ∈ λ^{36}`, the proven first-order high
valuation) this equals the coordinate of `mk(arg)`, which §2 makes `0`. -/

/-- **The mod-`37²` `varpi^32` descent detector** (a named wrapper over the heavy
`adicCompletionIntegers` coefficient, used to thread the second-order detector past the elaborator
without `whnf` loops): the mod-`37²` `varpi^32` Dwork coefficient of the descent logarithm
`completedLog(u^{36})` at the second-order precision `λ`-level `72 = 2*(37-1)`. -/
def caseIICor823DescentDetectorSq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
    (⟨32, by norm_num⟩ : Fin (37 - 1))
    (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
      (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
        (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)))

set_option maxHeartbeats 2000000 in
/-- **The mod-`37²` `varpi^32` detector of the descent logarithm vanishes** (proven, axiom-clean).
For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u - c`, the named descent detector
`caseIICor823DescentDetectorSq u` (the mod-`37²` `varpi^32` coordinate of `evalₐ 72
(completedLog(u^{36}))`) is `0`.

Proof: `evalₐ 72 (completedLog W) = samePrimeFiniteLog 71 (completedLogArg W)`
(`completedLog_evalₐ_succ`,
`72 = 71 + 1`) with `completedLogArg W = X^{36} - 1`.  The proven first-order high valuation
`caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred` gives `X^{36} - 1 ∈ λ^{36}`; the
level-`71`/power-`36` same-prime-log lemma `samePrimeFiniteLog_eq_mk_of_mem_pow_high_level`
(`72 ≤ 2·36`) collapses it to `mk(X^{36} - 1)`; and §2
(`caseIICor823SecondOrder_argCoeffModSq_eq_zero`) makes its `varpi^32` coordinate `0`. -/
theorem caseIICor823SecondOrder_detector_descent_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) (c : ℤ)
    (hc : ((37 : 𝓞 (CyclotomicField 37 ℚ)) ^ 2) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ)))) :
    caseIICor823DescentDetectorSq u = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Unfold the named detector to its underlying coefficient (syntactic `unfold`, no `whnf` of the
  -- heavy `adicCompletionIntegers` `Ideal.pow`).
  unfold caseIICor823DescentDetectorSq
  set k : Fin (37 - 1) := ⟨32, by norm_num⟩ with hkdef
  have hk : (k : ℕ) = 32 := rfl
  -- The mod-37 congruence (from mod-37²), feeding the proven first-order high valuation.
  have hc1 : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (c : 𝓞 (CyclotomicField 37 ℚ))) :=
    dvd_trans (dvd_pow_self (37 : 𝓞 (CyclotomicField 37 ℚ)) (by norm_num)) hc
  -- `arg := completedLogArg (u^{36}) = X^{36} - 1`, and `arg ∈ λ^{36}` (proven first-order).
  set W : completedLogDomain (p := 37) (K := CyclotomicField 37 ℚ) :=
    EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u with hW
  have hargeq : completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) W =
      (EPlus_valuedLocalImage (p := 37) (K := CyclotomicField 37 ℚ) u :
        ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ 36 - 1 := by
    rw [hW, completedLogArg, EPlus_completedLogDomainPowPred_coe]
  have hargmem36 : completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) W ∈
      (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ 36 := by
    have hval := caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred u c hc1
    -- `CompletedLogArgHighValuation37 u` is `completedLogArg (…) ∈ λ^{36}`; transport keeping the
    -- element opaque (dodge the `Ideal.pow` `whnf` wall).
    revert hval
    unfold CompletedLogArgHighValuation37
    rw [hW]
    generalize completedLogArg (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u) = A
    intro hval
    convert hval using 2
  -- The detector: `evalₐ 72 (completedLog W) = samePrimeFiniteLog 71 arg = mk(arg)`.
  have hdet : AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
        (completedLog (p := 37) (K := CyclotomicField 37 ℚ) W) =
      Ideal.Quotient.mk ((lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1)))
        (completedLogArg (p := 37) (K := CyclotomicField 37 ℚ) W) := by
    rw [completedLog_evalₐ]
    -- `completedLogCoord W 72 = samePrimeFiniteLog 71 arg = mk(arg)`.
    rw [show (2 * (37 - 1)) = 71 + 1 from rfl]
    rw [show completedLogCoord (p := 37) (K := CyclotomicField 37 ℚ) W (71 + 1) =
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (71 + 1)
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ) W) from
      (completedLog_evalₐ (p := 37) (K := CyclotomicField 37 ℚ) W (71 + 1)).symm]
    rw [completedLog_evalₐ_succ]
    rw [samePrimeFiniteLog_eq_mk_of_mem_pow_high_level (p := 37) (m := 36) (N := 71)
      (by norm_num) (by norm_num) (by norm_num) hargmem36
      (completedLogArg_mem (p := 37) (K := CyclotomicField 37 ℚ) W)]
  rw [hdet, hargeq]
  exact caseIICor823SecondOrder_argCoeffModSq_eq_zero u c hc k hk

end BernoulliRegular.FLT37.Eichler

end
