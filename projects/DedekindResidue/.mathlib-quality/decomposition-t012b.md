# T012-b numeric layer — fully derived route (verified against paper lines 586–631)

## State: step1 PROVEN. Remaining: numerics + final assembly.

Step1: (4/3)√X·log3X·|logκ_K − fK| ≤ (n−1)·ARCH + COEFF·(Σ_K + Σ_ℚ), where
ARCH = log9·(1/2+1/T')e^{T'/2}L(T'), T' = log(X/9), T−T' = log9 (log X − log(X/9) = log 9
needs Real.log_div rewrite), COEFF = (1/2)log9 + 2 + 2/T + 2/T' + 4/T + 4/T'
→ simplify ≤ 2(1 + log9/4 + 3/T + 3/T') ≤ 2(1 + log9/4 + 6/T') = 2·c_{a,T}.

## Brick Γ (digamma evaluation of dSigma's integrals)
- I_sinh(σ) := ∫_{Ioi 0} 1/(2sinh(y/2))(1−e^{−(σ−1/2)y}) = ψ(σ) − ψ(1/2) = ψ(σ)+γ+2log2.
  Proof: integrand = (e^{−y/2} − e^{−σy})/(1−e^{−y}) [algebra: 2sinh(y/2) = e^{y/2}(1−e^{−y})];
  apply GammaSide's digamma_sub_digamma_eq_integral (σ:=1/2)(w:=σ) + realness
  (mathlib Complex.digamma; GammaSide:910 re_digamma_sub_eq_integral is a real version —
  CHECK exact statement first). mathlib: digamma_one_half = −2log2 − γ ✓ digamma_one = −γ ✓
  digamma_apply_add_one (recurrence) ✓ (Complex.digamma, file Gamma/Digamma.lean).
- I_cosh(σ) = π/2 − (ψ((σ+1)/2) − ψ(σ/2))/2.
  Proof: integrand = (e^{−y/2}−e^{−σy})(1−e^{−y})/(1−e^{−2y}); subst w = 2y (integral_comp_mul_left);
  two Gauss pairs: [ψ(3/4)−ψ(1/4)] − [ψ((σ+1)/2)−ψ(σ/2)], all over factor 1/2.
  ψ(3/4)−ψ(1/4) = π: CHECK GammaSide:1086 re_digamma_quarter_sub_half_eq_integral +
  how the weil π/2·r₁ constant was produced (the identity is already in the codebase
  in some form — REUSE; search "pi/2" or "π/2" in GammaSide).
- dSigma_eq: dSigma K σ = 2·vonMangoldtSum K σ + n(log2π − ψ(σ)) + r₁(ψ((σ+1)/2)−ψ(σ/2))/2 − 2/σ.
  [uses γ+log8π − I_sinh = log2π − ψ(σ) since log8π−log4 = log2π; π/2 − I_cosh = (ψ-diff)/2.]

## Brick D (lower bound d_{K,σ} — paper 603–612)
dSigma K σ ≥ 2(log2π − ψ(σ)) − 2/σ = 2log2π − 2ψ(σ+1) ≥ 2log2π − 2ψ(4)
for 1 < σ ≤ 3: uses vonMangoldt ≥ 0 (terms nonneg), n ≥ 2 & log2π − ψ(σ) ≥ 0 (σ ≤ 3;
ψ(3) = 3/2−γ < log2π), r₁-term ≥ 0 (ψ mono), ψ(σ)+1/σ = ψ(σ+1) (digamma_apply_add_one),
ψ mono on reals > 0 (via the I_sinh integral representation: ψ(σ)−ψ(σ') = ∫(e^{−σ'u}−e^{−σu})/(1−e^{−u}) ≥ 0 — 
digamma_sub_digamma_eq_integral directly!). ψ(4) = 11/6 − γ (recurrence ×3 from ψ(1) = −γ).
NUMERIC TARGET: dSigma K σ ≥ 2log2π − 11/3 + 2γ =: dLow > 1.163 — but AVOID decimals:
keep dLow SYMBOLIC and prove Σℚ-upper ≤ dLow directly (Brick Q).

## Brick Q (the ℚ-zero-sum certificate — replaces paper's 0.023095)
zeroSumSigma ℚ 1 ≤ 3(2 − dSigma ℚ 2) [landau_stark_estimate ℚ at σ=2: logΔℚ=0 via Rat.numberField_discr]
dSigma ℚ 2 = 2W + γ + logπ − 1 where W := vonMangoldtSum ℚ 2   [σ=2 elementary:
 ψ(2) = 1−γ; I_sinh(2) = 1+2log2; ψ(3/2) = 2−γ−2log2 (recurrence from ψ(1/2)), ψ(1) = −γ:
 I_cosh(2) = π/2 − (ψ(3/2)−ψ(1))/2 = π/2 − 1 + log2; n=r₁=1:
 d = 2W + (γ+log8π) + π/2 − (1+2log2) − (π/2−1+log2) − 1 = 2W + γ + log8π − 3log2 − 1 = 2W + γ + logπ − 1.]
W ≥ log2/3 + log3/8 + log5/24 + log7/48 [4 explicit prime-ideal terms of 𝓞 ℚ:
 pk := (span(p)-transported ideal, m=0 (i.e. m+1=1)); term = logp·p^{−2}·... wait m=1 term is logp·p^{−2·1}; 
 SUM OVER m: single m=1 terms suffice: logp·p^{−2}. Hmm log2/3 = Σ_m log2·4^{−m} (geometric)! 
 EASIER: take only m=1 terms: W ≥ log2/4 + log3/9 + log5/25 + log7/49 + log11/121 + log13/169
 = 0.1733+0.1221+0.0644+0.0397+0.0198+0.0152 = 0.4345 — just short of 0.4452; add p=17,19,23:
 +0.0098+0.0082+0.0059 = 0.4584 ✓ (9 primes, m=1 only, avoids geometric sums).
 Construction: for prime p, the ideal I_p := Ideal.span {(p:𝓞 ℚ)}?? — absNorm via the
 ringOfIntegersEquiv transport (QSide machinery: absNorm_span_natCast + absNorm_map_ringEquiv).
 IsPrime: transport of (span p).IsPrime in ℤ (Int.span_p prime ⟸ p prime: Ideal.span_singleton_prime).
 tsum ≥ Finset.sum over 9 distinct pk-indices (injectivity: distinct absNorms), terms nonneg:
 Summable.sum_le_tsum (s : Finset) (nonneg off s).]
CHAIN: 3(2 − dℚ2) = 3(3 − 2W − γ − logπ) ≤ 3(3 − 0.9168 − γ − logπ); with γ > 0.577 
(mathlib NumberTheory/Harmonic/EulerMascheroni: CHECK available bounds; if none, γ > 0.5 
might suffice: 3(3 − 0.9168 − 0.5 − 1.1447) = 3·0.4385 = 1.3156 vs dLow = 2log2π−11/3+2γ ≥ 
3.675−3.667+1.0 = 1.008 FAILS with γ=0.5. Need γ ≥ 0.577: then Σℚ ≤ 3(0.3613) = 1.084 ≤ 
dLow = 1.163 ✓. γ-bounds: mathlib eulerMascheroniSeq convergence gives computable bounds — 
CHECK EulerMascheroni.lean for eulerMascheroniSeq_lt/gt lemmas; γ ∈ (γ_n, γ'_n) with n=6-ish.)
Also logπ > 1.1447: π > 3.1415 (Real.pi_gt_3141592) + log mono + certified log(3.1415) > 1.1447 
via exp: e^{1.1447} < 3.1415 ⟸ e^{1.1447} = e·e^{0.1447} ≤ 2.7183·1.1557 = 3.1416 — TIGHT; 
use e^{1.14} ≤ ... target margin: actually need 3−2W−γ−logπ ≤ dLow/3 = 0.3878: 
2W+γ+logπ ≥ 2.6122: 0.9168+0.5772+1.1447 = 2.6387 ✓ margin 0.0265 — distribute: 
W ≥ 0.4584 (as above), γ ≥ 0.5772 (need good γ bound!), logπ ≥ 1.14 (then sum 2.6340 ✓ margin 0.02).
log2π: 2log2π ≥ 2(log2+log3.14) — for dLow ≥ 1.163-avoidance: keep dLow symbolic: FINAL 
inequality to prove: 3(3 − 2W − γ − logπ) ≤ 2log2π − 11/3 + 2γ ⟺ 9 − 6W − 3γ − 3logπ ≤ 
2log2 + 2logπ − 11/3 + 2γ ⟺ 9 + 11/3 ≤ 6W + 5γ + 5logπ + 2log2 ⟺ 12.667 ≤ 6·0.4584 + 
5·0.5772 + 5·1.1447 + 2·0.6931 = 2.750 + 2.886 + 5.7235 + 1.386 = 12.746 ✓ margin 0.079 ✓✓ 
feasible with: W ≥ 0.4584, γ ≥ 0.5772, logπ ≥ 1.1447, log2 ≥ 0.6931 (mathlib log_two_gt_d9 ✓).

## Brick B (the β-bound)
Show (1/2+1/t)e^t·L(t) ≤ 2 for t ≥ log(23/3) [X ≥ 69 → T' = log(X/9) ≥ log(23/3)]:
key: log(1+u) ≤ u − u²/2 + u³/3 ∀ u ≥ 0 [derivative 1/(1+u) ≤ 1−u+u² ⟺ 0 ≤ u³; integrate:
strictMonoOn via hasDerivAt of F(u) = u−u²/2+u³/3−log(1+u), F(0)=0, F'≥0]. Then with
u := 2/(e^t−1) (so e^t·u = 2+u): e^tL ≤ 2 + u²/6·... exact: e^t(u−u²/2+u³/3) = (2+u)(1−u/2+u²/3)
= 2 + u²/6 + u³/3; need (1/2+1/t)(2+u²/6+u³/3) ≤ 2. At t ≥ 2.03, u ≤ 2/(e^{2.03}−1) ≤ 2/6.6 ≤ 0.31:
(1/2+1/2.03)(2+0.0161+0.0100) ≤ 0.99261·2.0261 = 2.0113 HMM RECHECK: 1/2.03 = 0.4926,
sum 0.9926; 2.0261·0.9926 = 2.0113 > 2 FAILS?! Recompute u at t = log(23/3): e^t = 23/3 = 7.667:
u = 2/6.667 = 0.3; u² /6 = 0.015; u³/3 = 0.009: 2.024; 1/t = 1/2.0369 = 0.4909; 0.9909·2.024
= 2.0057 > 2 STILL FAILS. Numeric truth: t₀ = 2.0369: L = log(8.667/6.667) = log(1.3) = 0.26236;
e^t·L = 7.667·0.26236 = 2.0115; ×0.9909 = 1.9933 < 2 ✓ TRUE but my cubic bound on log(1.3) =
0.26379 gives 7.667·0.26379·0.9909 = 2.0042 > 2 — CUBIC INSUFFICIENT at 69. Use QUARTIC:
log(1+u) ≤ u−u²/2+u³/3−u⁴/4+u⁵/5 [same derivative trick: 1/(1+u) ≤ 1−u+u²−u³+u⁴ ⟺ 0 ≤ u⁵ ✓]:
log(1.3) ≤ 0.3−0.045+0.009−0.002025+0.000486 = 0.262461 → e^tL ≤ 2.01230 ×0.9909 = 1.99399 ≤ 2 ✓
margin 0.006. Need also monotone-in-t reduction for t > t₀: u decreasing (e^t mono), 
(1/2+1/t) decreasing, and the assembled (1/2+1/t)(2+u²/6+u³/3−...) — with the quintic form
(2+u)(1−u/2+u²/3−u³/4+u⁴/5) = 2 + u²/6 + ... compute exact polynomial; all u-coefficients ≥0
in the tail ⟹ expression increasing in u ⟹ decreasing in t ✓ + (1/2+1/t) dec ✓ product of 
positive decreasing ✓. And t₀ ≥ 2.03: log(23/3) ≥ 2.03 ⟺ 23/3 ≥ e^{2.03}: e^{2.03} ≤ 
e²·e^{0.03} ≤ 7.3891·1.03046 = 7.6142 ≤ 7.6667 ✓ [e² ≤ 7.3891 from exp_one_lt_d9²-ish; 
e^{0.03} ≤ 1/(1−0.03) = 1.03093 via exp_le_inv... derive from add_one_le_exp(−x)].

## Brick F (final assembly, paper 613–631)
σ := 1 + 1/√(log Δ): needs |Δ| ≥ 3 (K ≠ ℚ ⟸ n ≥ 2: mathlib abs_discr bound — 
NumberField.discr: for n ≥ 2, |Δ| ≥ ... mathlib has `NumberField.abs_discr_gt_two` (n≥2 → |Δ|>2 
i.e. ≥3)? CHECK name; also 2.34-Minkowski `NumberField.abs_discr_ge`). Then 1 < σ ≤ 1+1/√log3 < 3 ✓
(2σ−1)(logΔ + 2/(σ−1)) = (√logΔ+2)² [algebra]; COEFF ≤ 2(1+log9/4+6/T'); assemble:
(4/3)√Xlog3X|logκ−fK| ≤ 2(1+log9/4+6/T')(√logΔ+2)² + (n−1)·6log9/√X ⟹ divide by (4/3)√Xlog3X…
paper final: |logκ−fK| ≤ 2.324logΔ/(√Xlog3X)·[(1+3.88/log(X/9))(1+2/√logΔ)² + 4.26(n−1)/(√XlogΔ)]:
constants: (3/2)(1+log9/4) < 2.324; 6/(1+log9/4) < 3.88; 3log9/(1+log9/4) < 4.26 [log9 = 2log3, 
log3 ∈ (1.0986, 1.09862): 1+log9/4 ∈ (1.5493, 1.5494): (3/2)·1.5494 = 2.3241 < 2.324?? 2.3241 > 2.324 
CAREFUL: 2.324 in the paper is their rounding — CHECK: (3/2)(1+(log9)/4) = 1.5+0.75log3 = 
1.5+0.75·1.098612 = 2.32396 < 2.324 ✓ (need log3 < 1.09867: certified). 6/1.549653 = 3.8718 < 3.88 ✓; 
3·2.197224/1.549653 = 4.2538 < 4.26 ✓.]
Final: belabas_friedman_thm1 in MainTheorem.lean (replace sorry; MainTheorem imports Theorem1 ✓).

## BREAKTHROUGH REVISION (supersedes Brick Γ/D digamma plans): NO DIGAMMA NEEDED
Let Is(σ) := ∫_{Ioi 0} 1/(2sinh(y/2))(1−e^{−(σ−1/2)y}), Ic(σ) := cosh version.
- **Recurrence** Is(σ+1) = Is(σ) + 1/σ: difference integrand = e^{−σy}(e^{y/2}−e^{−y/2})/(2sinh(y/2))
  = e^{−σy}; ∫_{Ioi 0} e^{−σy} = 1/σ. [integral_sub + exp integral; PURE ALGEBRA]
- **Is(1) = 2log2** by FTC: integrand = e^{−y/2}/(1+e^{−y/2}); antider −2log(1+e^{−y/2}),
  F(0) = −2log2, F(∞) = 0. [integral_Ioi_of_hasDerivAt_of_tendsto — known pattern]
- ⟹ Is(2) = 1+2log2, Is(3) = 3/2+2log2 free.
- **Is mono in σ** (setIntegral_mono, integrand mono) ⟹ for 1 < σ ≤ 2:
  Is(σ) + 1/σ = Is(σ+1) ≤ Is(3) = 3/2+2log2.
- **Ic ∈ [0, π/2]**: 0 ≤ integrand ≤ 1/(2cosh(y/2)) and GammaSide has
  `∫ 1/(2cosh(u/2)) = π/2` (integral_Ioi_inv_two_cosh, line ~972).
- **Ic(2) = π/2 − (1−log2)**: Ic(2) = π/2 − J, J := ∫e^{−3y/2}/(2cosh(y/2))
  = ∫e^{−2y}/(1+e^{−y}) = 1−log2 by FTC: antider log(1+e^{−y}) − e^{−y}, F(0) = log2−1, F(∞) = 0.
- **dSigma K σ ≥ 2γ + 2log2π − 3** for 1 < σ ≤ 2 (n≥2, W≥0, Ic ≤ π/2, r₁(π/2−Ic) ≥ 0 needs
  r₁ coefficient handling: dSigma has −r₁·Ic ≥ −r₁·π/2 so r₁π/2 − r₁Ic ≥ 0 ✓ drop;
  n(γ+log8π−Is(σ)) ≥ 2(γ+log8π−Is(σ)) needs γ+log8π−Is(σ) ≥ 0: Is(σ) ≤ Is(3) = 3/2+2log2 <
  γ+log8π ✓ numeric-free? log8π = 3log2+logπ: need 3/2+2log2 ≤ γ+3log2+logπ ⟺ 3/2 ≤ γ+log2+logπ
  ≈ 0.577+0.693+1.145 = 2.415 ✓ needs certified γ,log2,logπ lower bounds — OR keep n-coeff as
  n(...) ≥ 2(...) only when (...) ≥ 0 — same certificates);
  then d ≥ 2(γ+log8π) − 2Is(σ) − 2/σ = 2(γ+log8π) − 2(Is(σ)+1/σ) ≥ 2(γ+log8π) − 2(3/2+2log2)
  = 2γ + 2logπ + 2log2 − 3 = 2γ + 2log2π − 3 =: dLow ≈ 1.830.
- **dSigma ℚ 2 = 2W + γ + logπ − 1** exactly (n=r₁=1 values above; the 8π/2cosh constants
  collapse: (γ+log8π) + π/2 − (1+2log2) − (π/2−1+log2) − 1 = γ+logπ−1).
- **Σℚ ≤ 3(2−dℚ2) = 3(3 − 2W − γ − logπ)**; W ≥ Σ_{p∈{2,3,5,7,11,13,17,19,23}} logp/p²
  (m=1 terms only) ≥ 0.4584.
- **FINAL numeric target**: 3(3−2W−γ−logπ) ≤ 2γ+2log2π−3 ⟺ 12 ≤ 6W+5γ+5logπ+2log2+2·...
  recompute: 9−6W−3γ−3logπ ≤ 2γ+2log2+2logπ−3 ⟺ 12 ≤ 6W+5γ+5logπ+2log2:
  6(0.4584)+5(0.5772)+5(1.1447)+2(0.6931) = 2.7504+2.886+5.7235+1.3862 = 12.746 ✓ margin 0.7.
  Certificates needed: log2 > 0.6931 (mathlib log_two_gt_d9 ✓), logπ > 1.1447 
  (π > 3.141592 ✓ + log(3.141592) > 1.1447 ⟸ e^{1.1447} < 3.141592: e·e^{0.1447}:
  bound e^{0.1447} via series/1/(1−x)... or logπ > log3 = 1.0986 (log3 bounds derivable from
  log2 + log(3/2)?? mathlib: Real.log_three bounds? hmm) — with logπ ≥ log3 ≥ 1.0986:
  sum = 2.7504+2.886+5.493+1.3862 = 12.5156 ✓ STILL ≥ 12 with margin 0.5 — log3 route suffices
  IF mathlib has log3 bounds; else logπ ≥ log2 = 0.6931·... no: π ≥ 2·e^{0.4}?? KISS: 
  π > 3 → logπ > log3; log3 = log2 + log(3/2); log(3/2) > 0.405: e^{0.405} < 1.5 ⟸ 
  e^{0.405} ≤ 1/(1−0.405)?? = 1.68 too crude; series: e^{0.405} ≤ 1+0.405+0.082+0.011+0.0011+...
  ≈ 1.4993 < 1.5 ✓ via Real.exp_bound (mathlib exp series remainder) — or check mathlib for 
  ready log-bounds beyond log2 (Analysis.SpecialFunctions.Log.Basic / Mathlib.Analysis.SpecialFunctions.Log.Deriv 
  has abs_log_sub_add_sum_range_le for series-based certificates).
  γ > 0.5772: CHECK Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean for numeric bounds 
  (eulerMascheroniSeq 6 < γ < eulerMascheroniSeq' 6-style). If only weaker bounds exist, 
  margins allow γ > 0.5 IF W strengthened: with γ = 0.5: need 6W ≥ 12 − 2.5 − 5.493 − 1.3862 
  = 2.6208: W ≥ 0.4368 ✓ (already have 0.4584 with 9 primes!) — so even γ > 1/2 works ✓✓ 
  (EulerMascheroni surely has 1/2 < γ). SO: certificates = log2 > 0.693, log3 > 1.098 (or 
  logπ ≥ log3 with log3 = log2+log1.5, log1.5 ≥ 0.405), γ > 1/2, W ≥ 9-prime sum, π > 3.
