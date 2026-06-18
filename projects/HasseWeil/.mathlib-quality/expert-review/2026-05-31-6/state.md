# Expert-review session state — round 18

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–17
- Goal of brief: SOUNDNESS — an adversarial /develop --decompose pass (grounded in a full read of
  Silverman III.8) found the round-17 pivot's premise is QUALIFIED: Route 2's det(ψ|E[ℓ])≡deg ψ for the
  inseparable SUM rπ−s needs the genuine adjoint (= σ-bridge III.6.1b), NOT just isogDual (φ̂φ=[deg]) +
  Galois. The clean machinery gives only det≡N (mod ℓ), not the sign deg=N≥0 (the Hasse content).
  Frobenius alone IS clean via Galois. Ask: confirm/refute; does the separable-factorisation refinement
  rescue it; is Route 2 genuinely easier than Route 1.
- Scope: Leaf 1 endgame; Route 2 viability vs Route 1
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31) — VERDICT: finding confirmed (det≡N not deg=N); pivot to Route 2A
  (separable factorisation β=λ∘F^e, FULL p^e-Frobenius). --decompose on 2A found a SIMPLIFICATION (2A'):
  the generic + r≡0 edge cases have p∤s ⟹ β SEPARABLE (Silverman III.5.5), so only the separable
  compatibility on E (no twists) is needed; the p|s inseparable case is AVOIDED via the discriminant
  argument (Q≥0 on {p∤s} ⟹ t²≤4q ⟹ Q≥0 everywhere). No twist/factorisation infra needed.

## The finding (headline)
det((rπ−s)|E[ℓ])≡N (mod ℓ) is clean (Galois for π + factor-by-factor partner rV−s + (rV−s)(rπ−s)=[N]).
But the SIGN (deg=N) needs Prop 8.6 (det≡deg), via the genuine adjoint e(ψS,T)=e(S,ψ̂T) for the genuine
dual (rπ−s)̂. Factor-by-factor partner rV−s = (rπ−s)̂ iff dual additivity; avoiding that = σ-bridge for
rπ−s = inseparable divisor pullback (Route-1 content). In Silverman it's free (dual DEFINED as σ∘φ*∘κ);
the project's isogDual is φ̂φ=[deg], not the σ-bridge, so it must be established.

## Questions (§4)
| # | Question |
|---|----------|
| Q1 | Confirm/refute: clean route gives only det≡N mod ℓ; the SIGN deg=N needs Prop 8.6 (genuine adjoint/σ-bridge) for rπ−s, not from isogDual+Galois? Any missed path to det≡deg for the sum? |
| Q2 | Does separable factorisation (A) rπ−s=λ∘Frob^k rescue it — Galois kills Frob^k (det≡q^k=deg_i), separable λ uses the Pic⁰/comap dual (where sep degree=full degree)? Factorisation clean (supersingular Frob_{deg_i} subtlety)? Does Prop 8.6 for separable λ avoid the inseparable pullback? |
| Q3 | Honest route comparison: Route 2 genuinely easier than Route 1, or comparable (both need σ-bridge/insep-pullback for rπ−s)? Frobenius clean in Route 2; the sum not. Does (A) tip it to Route 2? |
| Q4 | Better path to det≡deg for the sum — adopt picDual=σ∘classMap∘κ as THE dual (adjoint native, only need picDual∘φ=[deg φ])? Or a standard finite-field det(ψ|E[ℓ])≡deg ψ not via the genuine adjoint? |

## References
Silverman III.8 (read in full: pp.93-99 — pairing construction, Prop 8.1 props, 8.2 adjoint via σ-bridge,
8.6 det=deg), III.6.1 (dual = σ∘φ*∘κ, 6.1a φ̂φ=[deg], 6.1b the σ-bridge), II.2.12 (sep∘Frob^k
factorisation), V.2.3.1 (Hasse via det). PDF offset +18.
