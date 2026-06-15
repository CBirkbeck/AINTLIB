# Expert-review session state — round 11

- Generated: 2026-05-29
- Audience: same senior arithmetic-geometry reviewer as rounds 1–10
- Goal of brief: strategic guidance — VALIDATE the dual-existence finding (h_isDual is a second deep gap, not structural; dual existence subsumes BRIDGE-003) and choose the III.6.2 constructor route before committing multi-week effort
- Scope: Leaf 1 (qf_nonneg) endgame only; specifically the signed degree identity deg(rπ−s)=N and whether "narrow Route A" avoids dual existence
- Reply received: true (2026-05-29)
- Reply integrated: true (2026-05-29)

## Questions in the brief

| # | Question (verbatim from §4 of the brief) |
|---|------------------------------------------|
| Q1 | Is the §3 finding correct — that "narrow Route A" (genuine rV−s via formal-group pole bound, then extensionality, then degree extraction), traced to the bottom, STILL requires genuine dual-isogeny existence for rπ−s (our (ii)), with BRIDGE-003 supplying only (i)? Or is there a way to get IsDualOf (rV−s)(rπ−s) / the signed deg=N from the two-sided comorphism composition [N] + degree multiplicativity that we're missing? |
| Q2 | If Q1 confirms: which dual-existence constructor is lighter given what's shipped (V, IsDualOf V π, π+V=[t], degree multiplicativity, sep/insep degree theory, genuine-isogeny extensionality, ℤ[π]) — (a) Pic⁰(E)≅E + divisor pushforward functoriality, or (b) kernel/factorisation (III.4 quotient curve)? Is dual additivity (φ+ψ)^=φ̂+ψ̂ cleaner in (a) or (b)? Can we get JUST additivity on ℤ[π] + α̂∘α=[deg α] without the full ∃!-dual for every isogeny? |
| Q3 | Is there a route to (★) needing LESS than full dual existence — (a) a direct parallelogram law deg(φ+ψ)+deg(φ−ψ)=2degφ+2degψ not routing through the dual; (b) a Frobenius-twist symmetry deg(rV−s)=deg(rπ−s) (gives only |N|, still needs the sign); (c) the Tate-module/Weil-pairing determinant route — does the §3 finding change the round-10 calculus that it "starts from too little"? |
| Q4 | Meta: does §3 change the round-10 recommendation? Should we ABANDON the formal-group BRIDGE-003 scaffolding (gives (i) not (ii); dual existence gives both) and commit to dual existence via the Q2 route? Or is "narrow Route A" still lighter, with a step for (ii) we've mis-estimated? |

## Ticket-board snapshot at brief time

Leaf 2 (deg(1−π)=#E(F_q)): CLOSED axiom-clean. Leaf 1 (qf_nonneg / 0≤qr²−trs+s²): OPEN, = the signed degree identity deg(rπ−s)=N. Generic case reduced to {h_comp_eq (shipped via bridge, gated on genuine rV−s = Wall A/BRIDGE-003), h_isDual (= dual existence III.6.2, OPEN), now-discharged 0<deg}. Char-divisible edges (p|r/p|s) secondary via [p]=V∘π. GAP-QF-DEGQF ticket tracks this.

## Stuck points (from §3 of brief)

1. h_isDual (IsDualOf (rV−s)(rπ−s)) — equivalent to the conclusion deg(rπ−s)=N given h_comp_eq; needs genuine dual existence III.6.1/6.2 (∃! β, IsDualOf β α — sorry). NOT structural.
2. BRIDGE-003 / Wall A — formal-group kernel-of-reduction pole bound at O; supplies (i) [genuine rV−s] but not (ii) [the dual relation]. §3(B): subsumed by dual existence.
3. The SIGN — qf_nonneg needs signed deg=N not |N|; two-sided composition gives only deg·deg=N².

## Reference list (from brief)

- Silverman AEC: V.1.1 (Hasse), III.6.3 (QF positivity), III.6.1 (dual existence), III.6.2 (deg is a quadratic form / dual additivity), III.4 (factorisation/quotient curve), III.3.4 (Pic⁰(E)≅E), VII.2.2 (kernel of reduction), IV.1.4 (formal group law = BRIDGE-003).
