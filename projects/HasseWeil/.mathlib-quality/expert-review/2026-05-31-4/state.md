# Expert-review session state — round 16

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–15
- Goal of brief: SOUNDNESS — does the theorem-of-square/bivariate proof of dual additivity
  (Silverman III.6.2c) go through char-free over F̄, given the base field K(E₁)=F̄(x₁,y₁) is
  IMPERFECT in char p (the footnote-1 obstruction is on K(E₁), not the constant field)? Or is the
  char-p case genuinely Weil-pairing-only (Ex 3.31)? Plus route comparison + infra gap.
- Scope: Leaf 1 endgame; DualAdd; the char-p viability of the round-15 divisor route
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31) — VERDICT: round-16 concern CORRECT (Silverman's bivariate
  proof is char-0-only; K(E₁) imperfect over F̄), but TOS is char-free in the Picard framework. STAY
  Route 1: prove pulled-back TOS via EXPLICIT Miller/addition-formula function (non-circular), avoid
  public fibre-sum API, minimal point-map→pullback bridge. STRICT CHECKPOINT → Weil/Tate if full fibre
  theory needed. Do NOT replay Silverman's bivariate proof.

## Why this round (the gap that triggered it)
Round-15 said "build the divisor route, char-free over F̄." Scoping revealed: (a) the genuine core is
Silverman's bivariate perspective-switch `ord_{P₁}(f)=e_φ(P₁)`, whose char-0 footnote attaches to
viewing E₂ over the FUNCTION field K(E₁)=F̄(x₁,y₁) — imperfect in char p even over F̄, so "perfect
over F̄" may not discharge it (tension with the reviewer's own round-13 warning); (b) infra the
round-15 estimate assumed is absent — the geometric divisor machinery and the live dual α̂ are on
DIFFERENT, unbridged isogeny notions, and there is no fibre-Finset theory (e_φ=deg_i only parametric).

## Questions (§4)
| # | Question |
|---|----------|
| Q1 | SOUNDNESS: does III.6.2c go char-free over F̄ despite K(E₁)=F̄(x₁,y₁) imperfect in char p? If yes, what replaces perfectness of K(E₁) in ord_{P₁}(f)=e_φ(P₁)? If no, is the divisor proof genuinely char-0-only ⟹ char-p (our generic p∣s) needs the Weil pairing (Ex 3.31)? |
| Q2 | If char-0-only: is Weil/Tate now the MORE MECHANICAL formalization for char p (round-13 est. 500–1500 LOC, one ℓ≠p + full ℓⁿ tower + nondegeneracy + e(φP,Q)=e(P,φ̂Q))? Switch the char-p case? |
| Q3 | Frobenius-specific shortcut: explicit/computational ŵ(rπ−s)=rV−s exploiting π=q-power Frobenius (π*=Frob, V=π̂ explicit, Vπ=[q], π+V=[t]) — via π* on ℤ[π], or T_ℓ / formal group — avoiding the general theorem of the square? |
| Q4 | If staying with divisor route (Q1=yes): leanest fibre/multiplicity handling — explicit Σ_{αP=Q}e_α(P)(P) vs a formulation using only div f (Miller) + Abel that avoids the fibre sum; and the minimal bridge between the two isogeny notions. |

## Settled (do not relitigate)
- Q3-round15 ℤ[π]-conjugation shortcut = CIRCULAR (Cor 6.3 uses III.6.2c twice). Verified vs PDF.
- Leaf 2 closed axiom-clean. DualAdd is the sole Leaf-1 residual; full consumer chain shipped.

## References
Silverman III.6.2(c) p.83–84 + footnote 1 (the K(E₁) perfectness use), Ex 3.31 (Weil-pairing char-p
proof of III.6.2c), III.4.10 (e_φ=deg_i, #φ⁻¹(Q)=deg_s), III.3.5 (Abel), Cor 6.3 (deg = pos-def QF,
uses III.6.2c twice). PDF offset +18.
