# Reviewer reply — round 17 (2026-05-31)

## Verdict: YES, real bypass — PIVOT to Route 2 (with a finite-level optimization)
The determinant/Tate proof avoids the dual-additivity obstruction. Crucial theorem is NOT ŵ(φ+ψ)=φ̂+ψ̂
but det(ψ_ℓ)=deg ψ (or finite-level det(ψ|E[ℓ])≡deg ψ mod ℓ for every aux prime ℓ≠p). Once available,
the Hasse QF is just the 2×2 determinant identity. PIVOT to Route 2, but OPTIMIZE:
**Do NOT start with the full Tate module. First do a finite-level Weil-pairing proof at E[ℓ] for
arbitrary ℓ≠p, then lift the INTEGER equality by varying ℓ.** Lighter than building T_ℓ(E)≅ℤ_ℓ² + ℤ_ℓ
linear algebra. One finite ℓ insufficient; all aux primes at level ℓ (or one ℓ through all powers ℓⁿ)
is enough.

## Q1 — Bypass genuine? YES.
det(ψ_ℓ)=deg ψ uses the Weil-pairing adjoint + ψ̂ψ=[deg ψ], NOT ŵ(φ+ψ)=φ̂+ψ̂. For P,Q∈E[ℓⁿ]:
e(ψP,ψQ)=e(P,ψ̂ψQ)=e(P,[deg ψ]Q)=e(P,Q)^{deg ψ}; and for 2×2 A, e(AP,AQ)=e(P,Q)^{det A}; nondegeneracy
⟹ det A≡deg ψ mod ℓⁿ. No additivity. CAVEAT: still needs dual EXISTENCE + defining ψ̂ψ=[deg ψ]
(III.6.1a), not III.6.2(c). If the project has the dual up to ψ̂ψ=[deg], Route 2 is the escape hatch.

## Q2 — Minimal det=deg: finite-level mod-ℓ for ALL primes ℓ≠p.
Prove ∀ℓ≠p: det(ψ|E[ℓ])≡deg ψ mod ℓ. Apply to ψ=rπ−s ⟹ deg(rπ−s)≡qr²−trs+s² mod ℓ ∀ℓ≠p ⟹ equal as
integers (an integer divisible by every prime ℓ≠p is 0). Avoids T_ℓ, inverse limits, ℓ-adic dets.
One finite ℓ gives only ≡ mod ℓ (insufficient); one ℓ-tower (all ℓⁿ) OR all primes-at-level-ℓ suffices.
Three formulations: (1) finite-prime ∀ℓ≠p mod ℓ [recommended]; (2) single-ℓ tower mod ℓⁿ (Tate-lite);
(3) full Tate det in ℤ_ℓ. Try (1) first.
Option-1 needs, for arbitrary ℓ≠p: (i) [ℓ] separable; (ii) #E[ℓ]=ℓ² (deg[ℓ]=ℓ² + sep kernel-degree);
(iii) E[ℓ] a 2-dim 𝔽_ℓ-vsp; (iv) Weil pairing e_ℓ bilinear/alternating/nondegenerate; (v) adjoint
e_ℓ(ψP,Q)=e_ℓ(P,ψ̂Q); (vi) det(ψ|E[ℓ])≡deg ψ mod ℓ. HARD WORK overwhelmingly in (iv)+(v) — pairing
construction + nondegeneracy/functoriality, where the Miller/divisor-function layer helps.

## Q3 — Cheaper sign? NO.
deg(rπ−s)·deg(rV−s)=N² gives only |N|. Sign N≥0 from N=det(rπ_ℓ−sI)=deg(rπ−s)≥0 — the missing signed
info. deg(1−π)=#E identifies t but does NOT prove the QF nonneg. Multiplicativity + Cayley–Hamilton
give ℤ[π] relations but not WHICH conjugate/norm is the degree without an independent det/duality
theorem. Finite mod-ℓ det congruence for enough ℓ is the cheaper FORM but still Weil-pairing content.
No point-level/multiplicativity-only argument recovers the sign (short of Stepanov, a different proof).

## Q4 — PIVOT, Tate-lite finite-level. Build order:
- Step 1: E[ℓ] for ℓ≠p: card=ℓ² ([ℓ] sep + deg[ℓ]=ℓ²); make E[ℓ] a 2-dim ZMod ℓ vsp. (uses the
  general separable kernel-degree thm, not the special 1−π one.)
- Step 2 [HARD #1]: Weil pairing e_ℓ:E[ℓ]×E[ℓ]→μ_ℓ via Miller — bilinear, alternating, nondegenerate.
- Step 3 [HARD #2]: adjoint e_ℓ(ψP,Q)=e_ℓ(P,ψ̂Q) (needs only the defining dual property).
- Step 4: det(A_ψ)≡deg ψ mod ℓ (2-dim symplectic linear algebra over ZMod ℓ).
- Step 5: M=π|E[ℓ]: det M≡q, det(I−M)≡#E ⟹ tr M≡t mod ℓ (via det(I−M)=1−tr+det).
- Step 6: det(rM−sI)≡qr²−trs+s² mod ℓ ∀r,s.
- Step 7: D=deg(rπ−s)−(qr²−trs+s²) divisible by every ℓ≠p ⟹ D=0 ⟹ deg(rπ−s)=qr²−trs+s²≥0. Leaf 1 done.
REAL WORK = steps 2 (pairing) + 3 (adjoint); rest is linear algebra + integer congruence. E[ℓ]≅𝔽_ℓ²
easier than the pairing given deg[ℓ]=ℓ² + sep kernel-degree.
CAVEAT: rπ−s must be a GENUINE endomorphism (keep placeholder-cleanup in force); split r=s=0 case.

## Final answers
Q1: Yes — det(ψ_ℓ)=deg ψ uses Weil adjoint + ψ̂ψ=[deg], not dual additivity (still needs dual existence).
Q2: Full Tate not required; finite-level E[ℓ] ∀ℓ≠p suffices (one ℓ insufficient; tower or all-primes ok).
Q3: No cheaper sign; det=deg≥0 is the minimal substantive ingredient (short of Stepanov).
Q4: Pivot. Build prime-level torsion → Weil pairing → adjoint → det≡deg mod ℓ → 2×2 algebra → integer separation.
