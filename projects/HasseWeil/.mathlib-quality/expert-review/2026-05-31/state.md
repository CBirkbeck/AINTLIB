# Expert-review session state — round 13

- Generated: 2026-05-31
- Audience: same senior arithmetic-geometry reviewer as rounds 1–12
- Goal of brief: strategic — Route C built (genuineness/degree-blindness/BRIDGE-003 resolved, hnat unconditional); the LAST residual = dual additivity III.6.2(c) which char-p needs the Weil pairing (Ex 3.31). Get the steer on the LIGHTEST route to the additivity.
- Scope: Leaf 1 endgame; the single residual ŵ(rπ−s)=rV−s
- Reply received: true (2026-05-31)
- Reply integrated: true (2026-05-31, theorem-of-square route recorded)

## Questions (§3)
| # | Question |
|---|----------|
| Q1 | Is the Weil pairing (Ex 3.31) genuinely the lightest char-p route to ŵ(rπ−s)=rV−s, or can the §III.6.2(c) Div⁰/Abel argument run over the PERFECT CLOSURE / alg closure of K(E₁) (f exists there) + descend? Is the only obstruction f-over-imperfect-field (curable by base-change), or a deeper char-p failure? |
| Q2 | Given non-circular ŵ[n]=[n], π̂=V, ŵ(rπ)=rV, is there a route to the SINGLE additivity instance ŵ(rπ+(−s))=ŵ(rπ)+ŵ(−s) via the LINEARITY of the Pic⁰ pullback action (theorem of the cube) in our class-group (κ:E≅Cl(F[E]), ideal-extension) formulation, lighter than the Weil pairing? |
| Q3 | If Q1/Q2 fail: how much of Ex 3.31 is needed for JUST the additivity? Is deg[2]=4→#E[2ⁿ]=4ⁿ→E[2ⁿ]≅(ℤ/2ⁿ)²→e_{2ⁿ}-bilinearity bounded on top of mathlib's division polynomials, or does nondegeneracy/Galois-invariance drag in much more? Does a single auxiliary ℓ≠p suffice vs the full 2ⁿ-tower? |
| Q4 | Any route to deg(rπ−s)=N or |t|≤2√q using the POINT-level infra (π+V=[t], Vπ=[q], Cayley-Hamilton, κ:E≅Pic⁰, α̂α=[deg], E(F̄) infinite) that AVOIDS the dual additivity entirely (cf. Ex 3.32)? |

## Stuck point
ŵ(rπ−s)=rV−s = III.6.2(c) dual additivity. char-0 Div⁰ proof inapplicable (imperfect K(E₁)); char-p = Ex 3.31 = Weil pairing (E[2ⁿ]≅(ℤ/2ⁿ)² + e_{2ⁿ}). Algebraic/uniqueness/trace routes circular. mathlib: division polys yes, E[m]≅(ℤ/m)² + Weil pairing no.

## References
Silverman AEC: III.6.1-6.3 (dual, deg QF), III.6.2(c) p.84 (char-0 Div⁰), Ex 3.31 p.112 (char-p Weil-pairing dual additivity), Ex 3.32 (Cayley-Hamilton + deg≥0 → Hasse), III.4.10 (e_φ=deg_i), III.8 (trace), V.1.1 (Hasse). mathlib EllipticCurve/DivisionPolynomial/*.
