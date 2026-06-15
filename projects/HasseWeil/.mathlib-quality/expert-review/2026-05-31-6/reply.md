# Reviewer reply — round 18 (2026-05-31)

## Verdict: finding correct but NOT fatal; pivot to Route 2A (separable factorisation)
The naive det((rπ−s)|E[ℓ])≡deg(rπ−s) is NOT free from the shipped point-map identities; proving it
directly for β=rπ−s needs the Weil-pairing adjoint for the GENUINE dual = the missing σ-bridge/Pic⁰
comparison (isogDual is φ̂φ=[deg], Silverman's adjoint is native because the dual is σ∘φ*∘κ). BUT the
separable-factorisation rescue is SOUND and now recommended:
  β = r π − s = λ ∘ F^e,  F^e = full inseparable (relative p^e-)Frobenius (deg F^e = p^e = deg_i β),
  λ separable with deg λ = deg_s β.
Determinant–degree multiplicativity per factor: Frobenius factor det ≡ p^e (Galois on roots of unity);
separable λ det ≡ deg λ (separable Pic⁰/comap/Weil adjoint, NO hidden inseparable multiplicities).
This localises inseparability to a pure Frobenius power and AVOIDS the full inseparable σ-bridge for rπ−s.

## Q1 — finding correct? YES (with refinement)
Clean matrix algebra gives det(rM−sI)≡N mod ℓ (M=π|E[ℓ], given det M≡q, tr M≡t) — only a CONGRUENCE,
does NOT prove N=deg(rπ−s) as an integer nor N≥0. The sign is the Hasse content. det(β|E[ℓ])≡deg β is the
missing assertion; its Weil-pairing proof needs e(βP,βQ)=e(P,Q)^{deg β}, i.e. the genuine adjoint β̂
(β̂β=[deg β] ALONE is insufficient without e(βP,T)=e(P,β̂T)). So: isogDual+Galois+matrix algebra gives
det≡N, not deg=N. Separable factorisation gives det≡deg for β WITHOUT the full inseparable adjoint for β.

## Q2 — does separable factorisation rescue it? YES, with the FULL p^e-Frobenius
Silverman II.2.12: β=λ∘F^e, F^e:E→E^(p^e) relative p^e-Frobenius (p^e=deg_i β), λ:E^(p^e)→E separable,
deg λ=deg_s β. RESOLVES the supersingular subtlety: use the FULL Frobenius factor F^e, not one-step F_p
nor q-Frobenius. CORRECTION to our candidate: deg F^e = p^e (NOT q^k) in II.2.12 notation. Proof of det≡deg:
  e_E(βP,βQ)=e_E(λF^eP,λF^eQ)=e_{E^(p^e)}(F^eP,F^eQ)^{deg λ}=e_E(P,Q)^{p^e·deg λ}=e_E(P,Q)^{deg β};
nondegeneracy ⟹ det(β|E[ℓ])≡deg β. NEEDS: (1) the factorisation; (2) Weil pairing for E AND the TWIST
E^(p^e); (3) Frobenius compat e(F^eP,F^eQ)=e(P,Q)^{p^e}; (4) separable-isogeny compat e(λA,λB)=e(A,B)^{deg λ}.
Much better targeted than the inseparable σ-bridge. CAVEAT: β=rπ−s must be a GENUINE isogeny object (not a
point-map expression) for factorisation to apply.

## Q3 — Route 2 now easier than Route 1? YES (with the rescue)
Before: both collapsed onto the same inseparable σ-bridge for rπ−s. After: Route 2A needs only the
Frobenius pairing computation (clean) + the SEPARABLE Weil-pairing determinant (where Pic⁰/comap sees the
full=separable degree) + the factorisation. Materially narrower than Route 1 (full inseparable
theorem-of-square / dual additivity). Recommendation: proceed with Route 2A (finite-level Weil pairing +
separable factorisation). Do NOT revert to Route 1 unless the factorisation/twist compat is much harder
than expected.

## Q4 — cleaner route to det≡deg for the sum? NO standard shortcut without adjoint/pairing/kernel-size
(1) Weil pairing adjoint — standard, needs adjoint/dual compat. (2) kernel/cokernel on T_ℓ — gives
ℓ-adic VALUATION not the unit/sign congruence; insufficient for Hasse's sign. (3) picDual as definition
— makes adjoint native but proving picDual∘φ=[deg φ] for INSEPARABLE φ needs ramified divisor pullback =
the same inseparable σ-bridge. ⟹ cleaner path: use picDual/comap ONLY for the separable factor λ, and
Frobenius/Galois for the inseparable factor.

## Recommended 5-step plan
1. State det_mod_l_eq_degree_of_sep_insep_factor: β=λ∘F^e, λ sep, deg F^e=p^e ⟹ det(β|E[ℓ])≡deg β ∀ℓ≠p.
2. Frobenius pairing lemma: e(F^eP,F^eQ)=(e P Q)^{p^e} (clean, Frobenius on μ by z↦z^{p^e}).
3. Separable-isogeny pairing lemma: e(λP,λQ)=(e P Q)^{deg λ} (separable Pic⁰/comap or separable-only
   divisor proof — the remaining σ-bridge, MULT-FREE).
4. Apply II.2.12 factorisation to β=rπ−s (only need existence of λ,F^e + deg β=p^e·deg λ; no need to
   compute e).
5. Finish with the shipped matrix residual (M=π|E[ℓ], det M=q, tr M=t, det(rM−sI)) + integer separation.

## Direct answers
Q1: Finding correct — isogDual+Galois+matrix gives det≡N, not deg=N; the sign needs det≡deg. Separable
factorisation gives det≡deg for rπ−s WITHOUT the full inseparable adjoint.
Q2: Yes — with the FULL p^e-Frobenius factor (λ sep, deg λ=deg_s β); supersingular handled by using the
full inseparable degree (not one-step F).
Q3: Route 2A now genuinely preferable; avoids the hardest inseparable σ-bridge for rπ−s.
Q4: No shortcut avoids adjoint/pairing/kernel-size. Use picDual/comap only for the separable λ, Galois
for the inseparable factor.
