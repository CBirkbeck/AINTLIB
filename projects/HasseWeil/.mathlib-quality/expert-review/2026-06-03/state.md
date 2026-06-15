# Expert-review session state — round 20

- Generated: 2026-06-03
- Audience: senior arithmetic-geometry reviewer (rounds 1–19)
- Goal of brief: strategic guidance — Route 2A reduced to elementary-but-framework-gated per-isogeny witnesses; how to proceed (point-functor bridge vs re-architect)
- Scope: the Hasse bound via the finite-level Weil pairing (Route 2A); the §6 representation obstruction
- Reply received: true (2026-06-03)
- Reply integrated: true (2026-06-03)

## Questions in the brief
| # | Question |
|---|----------|
| Q1 | Fix (A) bridge abstract↔geometric point-map then invoke III.4.10/III.8.2, or (B) retire the decoupling for a single geometric isogeny type? |
| Q2 | Separable-scaling realisation needing NEITHER point-map surjectivity NOR divisor transport — point-map-free via Pic⁰/Abel–Jacobi, leaving only covariance? |
| Q3 | Can deg(φ^*D)=(#ker φ)·deg D for separable φ come from the comorphism (function-field degree) alone, independent of the point-map? |
| Q4 | Cleanest formalisation of e_ℓ(πS,πT)=e_ℓ(S,T)^q: Galois-equivariance vs round-18 Frobenius-factorisation? |
| Q5 | Strategy: §4 done, residue is §6 decoupling — Route 2A still right; (A) point-functor bridge vs (B) re-build pencil isogenies geometrically? |

## Key state at brief time
- BUILT axiom-clean: E[ℓ]≅(ℤ/ℓ)²; Weil pairing (constant-ratio) + bilinear/alternating/μ_ℓ/nondegenerate; CoordHom-free separable adjoint+scaling (weilScales_of_dualComp via divisor-pushforward dual δ=κ∘φ^*∘κ⁻¹, σ-bridge automatic); determinant reduction (det=deg, integer separation); deg(1−π)=#E; separability of 1−π and rπ−s (p∤s) via III.5.2 (a_{α+β}=a_α+a_β now formalised); #ker=deg general.
- REMAINING (the §5 witnesses): for 1−π & rπ−s over K̄ — surjectivity (III.4.10b), covariance (III.8.2), divisor transport div(φ^*h)=φ^*(div h); + Frobenius Galois-equivariance e_ℓ(πS,πT)=e_ℓ(S,T)^q. ALL elementary in Silverman; gated by the abstract-isogeny decoupling (comorphism/point-map independent fields) — the geometric fibre-count machinery lives on a different (point-functor) isogeny type.

## Route arc (rounds 16–19)
- 16: theorem-of-square char-p-broken as written; trace-relation→deg(rπ−s) circular.
- 17: pivot to finite-level Route 2 (det≡deg mod ℓ ∀ℓ≠p); hard work = pairing+adjoint.
- 18: separable-factorisation rescue β=λ∘Frob^e (Galois + separable adjoint).
- 19: Route 2A is the path; separable adjoint via Picard dual picDual=σ∘φ^* (no CoordHom); inseparable π via Galois; don't return to Route 1.
