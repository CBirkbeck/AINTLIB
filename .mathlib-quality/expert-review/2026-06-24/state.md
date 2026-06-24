# Expert-review session state

- Generated: 2026-06-24
- Audience: Adic-spaces / Huber expert (fluent in Wedhorn/Huber)
- Goal of brief: Status check (what's done / left) + soundness check (lemmas/defs/thms not
  vacuous or junk) + plan check for remaining work
- Scope: Whole Wedhorn Thm 8.28(b) project + current IRIE/Leaf-A frontier
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Uniform boundedness of `𝒪_X(D)⁺`: false in general + power-bounded reroute correct? Or genuinely bounded for complete strongly noetherian Tate `A`? |
| Q2 | [Hu2] 3.3 and 6.17/6.18 legitimate as cited leaves; σ-compact-free 6.16 adequate? |
| Q3 | Is the R2-transport reduction of Čech acyclicity complete? |
| Q4 | Affinoid interface, headline bundle, derived LL package, and leaf routes — all faithful and free of vacuity/over-hypothesis? (the core soundness ask) |
| Q5 | Is the work-order sensible: (a) fix §8.1 boundedness, (b) close LL-bdd modulo [Hu2] 3.3, (c) finish Leaf C R2-transport, (d) confirm Leaf B OMT residual, (e) collapse headline to axiom-clean? |

## Ticket-board snapshot at brief time (8.28(b) critical path only)

- DONE (axiom-clean): Spa(𝒪(D))≅R(D); LL-unit (7.52(2)); 𝒪_X(D) strongly noetherian (Ex 6.38);
  per-step flat (Prop 8.30 basic step); interface integrally-closed (free); interface OPEN
  (proven this session, 7.19/7.20 absorption).
- BUILT (rest on leaves): Remark 7.55 chain; Cor 8.32 faithfully flat; Banach OMT 6.16; LL-bdd
  (modulo [Hu2] 3.3).
- OPEN: interface power-bounded/boundedness (§8.1 probable statement error); Leaf C R2-transport;
  headline collapse to axiom-clean.

## Stuck points (from §8 of brief)

1. §8.1 — `𝒪_X(D)⁺` boundedness: code states UNIFORM IsBounded; Wedhorn proves POWER-bounded
   (⊆A°) via Lemma 7.20. Probable statement error; reroute = power-bounded + "A° integrally
   closed" (needs: A⁺[T/s]⊆(A_s)°, (A_s)°/(𝒪_X(D))° integrally closed, closure-of-pb stable).
2. §8.2 — deep external Huber leaves: [Hu2] 3.3 (LL-bdd), Prop 6.17/6.18 (Wedhorn "proof
   missing"); we use σ-compact-free 6.16.
3. §8.3 — Leaf C R2-transport: instantiate absolute acyclicity at B=𝒪_X(U), transport via
   Spa(B)≅U (8.2/8.4/8.16).
4. §8.4 — faithfulness/vacuity audit: project history (false noeth-A₀; vacuous open-ideal-basis
   on Tate; false orphans). Asked reviewer to police current live hypotheses.

## Reference list (from §2.2 of brief)

- [W] Wedhorn, Adic Spaces (lecture notes) — all numbered refs.
- [Hu1] Huber, Continuous valuations, Math. Z. 212 (1993).
- [Hu2] Huber, Continuous valuations (companion) — Lemma 3.3 = [W] 7.18.
- [Hu3] Huber, A generalization of formal schemes…, Math. Z. 217 (1994) — 2.6 = [W] 7.54.
