# Expert-review session state — round 12

- Generated: 2026-05-30
- Audience: same senior arithmetic-geometry reviewer as rounds 1–11
- Goal of brief: strategic — report the Lean negative finding (the round-11 Pic⁰ route is DEGREE-BLIND to inseparability, so it cannot close Leaf 1) and get the steer on the best PULLBACK-LEVEL route for the signed/inseparable degree deg(rπ−s)=N
- Scope: Leaf 1 endgame only; the pullback-level dual / inseparable degree
- Reply received: true (2026-05-30)
- Reply integrated: true (2026-05-30, Route C recorded; build paused per user)

## Questions in the brief (§4)

| # | Question |
|---|----------|
| Q1 | Given the inseparability obstruction, which is the lighter route to the genuine COMORPHISM dual of rπ−s: Route A (formal-group pole bound at O / BRIDGE-003 IV.1.4 → genuine rV−s → double-Vieta → Wall C) or Route B (kernel-quotient E/ker(rπ−s), III.4)? Reuse: V with Vπ=πV=[q], π+V=[t], proved IsDual(V,π), point-map (rV−s)(rπ−s)=[N], genuine-isogeny extensionality, sep/insep degree theory. |
| Q2 | For Route B: does E/ker(β) cleanly handle the INSEPARABLE case p∣s (ker non-étale/infinitesimal)? The usual quotient via β=β_sep∘Frob^k — does it deliver the comorphism INCLUDING the inseparable factor p^k, or just relocate the formal-group content? |
| Q3 | DEGREE-DECOMPOSITION shortcut: rπ−s = Frob^k ∘ σ (σ separable), deg_insep=p^k, deg=p^k·deg_sep. deg_sep=#ker_sep IS visible to point-level/Pic⁰ (now available via E≅Pic⁰). Compute deg_insep from the differential / power of Frobenius dividing rπ−s, multiply ⟹ full deg WITHOUT the formal-group pole bound? Is k readable off (r,s) (k=v_p(s)?) |
| Q4 | A third pullback-level route, or a way to make the now-available E≅Pic⁰ asset contribute to the INSEPARABLE part (so the Pic⁰ work isn't wasted)? |

## Ticket-board snapshot at brief time

Leaf 2 CLOSED. Leaf 1 = signed deg(rπ−s)=N, a pullback/inseparable-level identity. PIC0 route DEAD END for Leaf 1 (degree-blind to inseparability — comap-variance, classNorm∘comap=(·)^inertia=separable degree only; Isogeny.degree=finrank(pullback)=full/inseparable). Reusable Pic⁰ assets banked axiom-clean (E≅Pic⁰ toClassEquiv', ClassGroup.relNorm/map, Isogeny↔ClassGroup bridge, comap III.3.4 toClass_toPointMap). Reverting to pullback-level: Wall-A/BRIDGE-003 (formal-group) OR kernel-quotient III.4. GAP-QF-DEGQF + PIC0 ticket sections updated; b2_log.jsonl has the PIC0-route-leaf1 entry.

## Stuck points (from §3)

1. Pic⁰ point-level functoriality is comap-variance → computes only the SEPARABLE/inertia degree.
2. Isogeny.degree = finrank(pullback) = the FULL degree (incl. inseparable); rπ−s generically inseparable (p∣s, differential multiplier −s).
3. ⟹ Pic⁰ degree-blind; signed deg=N needs a pullback-level route. F̄ base-change doesn't rescue (deg is pullback-level).

## Reference list

- Silverman AEC: V.1.1 (Hasse), III.6.1-3 (dual/QF), III.4 (kernel/quotient, sep/Frobenius factorization), IV.1 (formal group law = BRIDGE-003), VII.2 (kernel of reduction), II.2.4 (morphism from comorphism). III.3.4 (Pic⁰≅E functoriality — now formalized as comap-variance).
