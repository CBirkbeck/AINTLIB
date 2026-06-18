# Expert-review session state — round 19

- Generated: 2026-05-31T19:53:40Z
- Audience: same senior arithmetic-geometry reviewer as rounds 1–18
- Goal of brief: strategic + specific-blocker — the Route 2A (finite-level Weil-pairing) endgame for Leaf 1 (qf_nonneg). We built the axiom-clean reduction + foundations and hit three geometric sub-dependencies; the sharpest finding is that the affine "[ℓ] is finite" device (a coordinate-ring map R→R) is PROVABLY IMPOSSIBLE. Ask for the cleanest #E[ℓ]=ℓ² route, pairing soundness, the separable adjoint, and whether Route 2A is still the soundest overall path.
- Scope: Leaf 1 Weil-pairing endgame; Route 2A viability vs alternatives
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31) — VERDICT: Route 2A confirmed soundest; attack §8.1→§8.2→§8.3. Q1: general separable-isogeny fibre count (not CoordHom, not x-line). Q2: constant-quotient pairing def. Q3: picDual adjoint (separable). See integration.md.

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Given that the affine "[ℓ] is finite" device (a coordinate-ring map R→R) provably cannot exist, what is the cleanest constructive route to #E[ℓ]=ℓ² over K̄? Candidates: (a) function-field étale theory (separable ⇒ unramified ⇒ all fibres size deg; integral closure of [ℓ]^*R module-finite); (b) descend to the x-line via the degree-ℓ² map x↦Φ_ℓ/Ψ²_ℓ which DOES have a coordinate witness; (c) Tate-module / kernel-as-group-scheme. Which is least painful, and pitfalls? |
| Q2 | Is the divisor-theoretic Weil pairing e_ℓ(S,T)=g_T(X+S)/g_T(X) (forcing the function-evaluation infrastructure) the soundest route to det ρ_ℓ ≡ deg, or is there a materially shorter path to qf_nonneg — e.g. det ρ_ℓ(φ)≡deg φ without constructing e_ℓ pointwise, or bypassing the pairing/matrix rep entirely for rπ−s? |
| Q3 | Cleanest way to formalise the separable adjoint e_ℓ(φS,T)=e_ℓ(S,φ̂T) (III.8.2) given we have picDual (sorry-free, picDual∘φ=[deg φ], σ-bridge automatic) but NOT the genuine isogeny dual? In particular: can all of Prop 8.6 run with picDual in the role of φ̂, never needing the isogeny dual as a map? |
| Q4 | Strategic: with three geometric sub-dependencies now visible on Route 2A (§8.1 torsion/finite-morphism, §8.2 function evaluation, §8.3 adjoint), is finishing Route 2A still soundest, or steer to (i) Route 1 (degree quadratic form via dual additivity), (ii) a Tate-module / ℓ-adic packaging, or (iii) a different endgame decomposition? Which of §8.1–8.3 to attack first, and is any a warning sign the route is more expensive than it looked at round 18? |

## Ticket-board snapshot at brief time

Source board: `.mathlib-quality/tickets-route2-weil-pairing.md` (Route 2 Weil-pairing tickets). Status at brief time:

- **DONE / axiom-clean (12 of 13 WeilPairing files sorry-free):** the reduction chain (`qf_nonneg_of_pairing_scaling`, Assembly — sorry-free), abstract Prop 8.6 (`PairingDet`), Discriminant (qf_nonneg from {p∤s}), Fiber (fibre=kernel coset), Pullback (mult-1 geometric divisor pullback + degree + σ-section), SigmaBridge (III.6.1b), the pairing-value layer (Constancy: const/pow/mul/refl, parametric on the translation-invariance witness), WeilFunction (weilDivisor, weilFunction_exists, pullbackDiv_sub_isPrincipal), [ℓ]-separability (TorsionSeparable.mulByInt_isSeparable). Leaf 2 (`ker_deg_skeleton`: deg(1−π)=#E) closed.
- **PARAMETRIC:** `torsionSubgroup_card_of_separable_witness` (general [Field F], K̄-ready) gives #E[ℓ]=ℓ² from separability + finite-dim + a Point-level fibre witness — the witness is the unproven input (§8.1).
- **OPEN tickets:** T-R2-PAIRING-DEF (e_ℓ def), T-R2-PAIRING-PROPS (bilinear/alt/nondeg), T-R2-ADJOINT (Prop 8.2), T-R2-DET-DEG (Prop 8.6 assembly), T-R2-REP, T-R2-ASSEMBLE.
- **WONTFIX (verified this round):** T-R2-TORSION-COORDHOM — `(mulByInt ℓ).CoordHom` (R→ₐR) is mathematically impossible ([ℓ]^*x=Φ_ℓ/Ψ²_ℓ has poles at the affine ℓ-torsion); the generic-fibre witness that takes a CoordHom can never be instantiated for [ℓ]; needs a function-field-level III.4.10c re-route (Q1).

## Stuck points (from §8 of brief)

- 8.1 — #E[ℓ]=ℓ² over K̄: the affine "[ℓ] finite" CoordHom R→R is PROVABLY IMPOSSIBLE (poles at the ℓ-torsion; [ℓ] doesn't preserve the affine chart E∖{O}). Frobenius is the unique exception (x↦x^q polynomial). Needs function-field-level III.4.10c. → Q1.
- 8.2 — the translation-invariance witness div(g∘τ_S)=div(g) and pointwise function evaluation g(X+S)/g(X): genuinely new (but bounded) function-field infrastructure; maximal-ideal/valuation transport pieces exist, not yet assembled. → Q2.
- 8.3 — the separable adjoint III.8.2 e_ℓ(φS,T)=e_ℓ(S,φ̂T): have picDual (sorry-free) but not isogDual; route via the Picard dual + multiplicity-free pullback. → Q3.

## Reference list (from §2.2 of brief)

- [Silverman] AEC 2nd ed GTM 106 — III.5.5, III.4.10, III.6.1–6.3, III.8.1–8.6, V.1.1/V.2.3.1.
- Rounds 17 (endorsed finite-level pairing) and 18 (endorsed Route 2A; confirmed det≡N, sign needs separable adjoint) of this correspondence.
