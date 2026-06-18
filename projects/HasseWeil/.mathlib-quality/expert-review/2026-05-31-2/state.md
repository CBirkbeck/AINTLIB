# Expert-review session state — round 14

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–13
- Goal of brief: technical — took the round-13 theorem-of-square route, formalised to the exact additivity step (hmul), hit a concrete obstruction (ideal-extension over 𝔽_q: non-rational fibre points + non-structural group-law linkage). Confirm the cleanest formalizable shape of the fix (divisor/point theorem of square over F̄ + descent).
- Scope: Leaf 1 endgame; the single residual hmul (theorem of the square)
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31, F̄ theorem-of-square target recorded)

## Questions (§4)
| # | Question |
|---|----------|
| Q1 | Is the divisor/point form over F̄ the right target (vs ideal-classMap): [(α₁+α₂)*D]=[α₁*D]+[α₂*D] in Pic⁰ for D∈Div⁰, via "deg 0 + sums-to-O ⟹ principal (Abel)", sums-to-O from the group law (α₁+α₂)(P)=α₁(P)+α₂(P)? |
| Q2 | The sums-to-O crux: immediate from κ_K group-hom + fibre identity, or does it need the genuine theorem of the square on E×E (m*L≅p₁*L⊗p₂*L) pulled back along (α₁,α₂)? We want to AVOID a product-curve E×E divisor API — is the pulled-back-to-E computation self-contained, and what's the minimal fibre lemma needed? |
| Q3 | Descent: consumer only needs additivity as point-map equality over E(F̄). Do we need any descent to 𝔽_q? If so, is "equality of 𝔽_q-morphisms checkable after the faithfully-flat 𝔽_q→F̄" sufficient, no further subtlety? |
| Q4 | Shortcut? Given κ:E≅Pic⁰ is a group iso over any field, the dual relation α̂α=[deg], π̂=V/(rπ)^=rV/[n]^=[n] (non-circular), and the E(F̄) injectivity — is there a route to the SINGLE instance (rπ+[−s])^=(rπ)^+[−s]^ lighter than the full theorem-of-square divisor computation, purely from κ's additivity + the Pic⁰ functoriality we have? |

## Obstruction
ideal-level hmul over 𝔽_q blocked by (O1) non-rational fibre points (imperfectness; same as char-0 Div⁰ killer) + (O2) group-law linkage α(P)=α₁(P)+α₂(P) non-structural in ideal-extension (sum isogeny's comorphism = addPullbackAlgHomPair, no ideal relation). Fix = theorem of square over F̄ (rational fibres) + descend (reviewer's round-13 base-change caution).

## References
Silverman AEC: III.6.1-6.2 (dual, III.6.2(b) pullback-as-divisor, III.6.2(c) char-0 additivity), III.3.4/3.5 (E≅Pic⁰, Abel), III.4.10 (e_φ=deg_i), Ex 3.31 (Weil-pairing additivity — avoided), V.1.1. mathlib Point.toClass (group hom E→ClassGroup).
