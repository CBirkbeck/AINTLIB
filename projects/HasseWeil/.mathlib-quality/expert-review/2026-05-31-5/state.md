# Expert-review session state — round 17

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–16
- Goal of brief: ROUTE SELECTION — grounding in Silverman (per user directive "check the proofs, don't
  rely on memory") revealed V.2.3.1 (Silverman's actual finite-field Hasse proof) proves Leaf 1 via the
  ℓ-adic determinant det(ψ_ℓ)=deg ψ (III.8.6, Weil pairing) and BYPASSES dual additivity III.6.2(c)
  entirely. Our exact target becomes the 2×2 identity det(rφ_ℓ−sI)=qr²−trs+s²≥0 (positivity = deg≥0).
  Should we pivot from Route 1 (divisor/dual-additivity) to Route 2 (Weil/Tate)?
- Scope: Leaf 1 endgame; Route 1 vs Route 2
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31) — VERDICT: PIVOT to Route 2 (Weil/Tate). Bypass confirmed.
  OPTIMIZATION: finite-level mod-ℓ Weil pairing ∀ primes ℓ≠p (NOT full Tate module), lift integer
  equality by infinitely-many-primes. 7-step build order; HARD items = pairing construction (step 2)
  + adjoint e_ℓ(ψP,Q)=e_ℓ(P,ψ̂Q) (step 3). Rest = linear algebra + integer congruence.

## The finding (headline)
det(ψ_ℓ)=deg ψ needs only the Weil-pairing adjoint e(φS,T)=e(S,φ̂T) + φ̂φ=[deg φ] (III.6.1a), NOT dual
additivity III.6.2(c). So the QF positive-definiteness (III.6.3) that blocked us for 6 rounds is, on
Route 2, just "det is a quadratic form" (2×2 linear algebra) + "det=deg≥0". The whole bottleneck is an
artefact of Route 1. Miller/divisor-function machinery (already shipped) is the engine the Weil pairing
is built from, so Route 2 is not from zero.

## Questions (§5)
| # | Question |
|---|----------|
| Q1 | Confirm: det(ψ_ℓ)=deg ψ (⟹ Leaf 1 = det(rφ_ℓ−sI)=deg(rπ−s)≥0) needs only Weil adjoint + φ̂φ=[deg], NOT III.6.2(c). Route 2 sidesteps the obstruction? |
| Q2 | Leanest det=deg given Miller machinery: full Tate ℓⁿ-tower needed, or does a bounded level set / single ℓ suffice since the unknown is a specific integer pinned by tr,det∈ℤ? |
| Q3 | The SIGN (deg=N not |N|) cheaper than full Weil pairing — bootstrap from shipped deg(1−π)=#E + deg multiplicativity, or reduction-mod-ℓ for enough ℓ? Or is the Weil determinant minimal? |
| Q4 | The CALL: pivot to Route 2 (Silverman's actual finite-field proof, reuses Miller, no textbook char-free Route-1 proof exists)? Build order + the 1–2 lemmas that are the real work. |

## Settled (do not relitigate)
- ℤ[π]-conjugation shortcut circular (Cor 6.3 uses III.6.2c). Silverman III.6.2(c) bivariate proof
  char-0/perfect-base-only (K(E₁)=F̄(x₁,y₁) imperfect). Round-16 verified.
- Leaf 2 closed axiom-clean. deg(rπ−s)·deg(rV−s)=N² gives only |N| (sign is the Hasse content).

## References
Silverman V.1.1 (p.138, QF+CS route), Lemma 1.2 (CS), V.2.2–2.3 (Weil conj for EC, ℓ-adic rep),
V.2.3 Prop 2.3 (det ψ_ℓ=deg ψ, tr formula = III.8.6), V.2.3.1 (φ²−aφ+q=0, char-poly nonneg ⟹ Hasse),
III.8 (Weil pairing), III.8.6 (det/tr), III.6.1 (dual, 6.1a φ̂φ=[deg]), III.6.2c (additivity, AVOIDED),
III.6.3 (pos-def QF), III.3.5 (Abel). PDF offset +18.
