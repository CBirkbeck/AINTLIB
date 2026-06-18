# Expert-review session state

- Generated: 2026-06-18
- Audience: Adic-spaces expert (Huber–Wedhorn theory)
- Goal of brief: Strategic — confirm the whole faithful Thm 8.28(b) decomposition is right, with focus on the A⁺⊆A° encoding gap
- Scope: Broad (full 8.28(b): Leaf A flatness, Leaf B embedding, Leaf C gluing)
- Reply received: true (2026-06-18)
- Reply integrated: true (2026-06-18)

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Encoding the ring-of-integral-elements axiom A⁺⊆A° (Def 7.14(1)): bundle into the A⁺ carrier (a), carry "ring of integral elements" as a per-use hypothesis (b), or derive per concrete instance (c)? Does downstream use (morphisms of affinoid rings, base change, perfectoid layer) prefer one — and does Wedhorn's "it's part of the definition, never re-derived" argue for (a)? |
| Q2 | Is the completion provably affinoid? Is the completed plus-subring of 𝒪_X(D)=A⟨T/s⟩ a ring of integral elements (open, integrally closed, ⊆ 𝒪_X(D)°), incl. at the two-level/iterated completion? Is there a clean "Â⁺ is a ring of integral elements of Â" to cite (Wedhorn 7.47)? |
| Q3 | Exact support vs containment for a maximal 𝔪: confirm exact (supp v = 𝔪) follows from containment (𝔪 ≤ supp v) + maximality (supp v prime ≠ A, 𝔪 maximal) — NO rank-1 domination (correcting an internal note); and that containment suffices for every downstream consumer. |
| Q4 | Pair-free routing A⁺⊆A° vs A⁺⊆A₀: completions fail A⁺⊆A₀ but satisfy A⁺⊆A°; we route 7.45/7.51 through A⁺⊆A° (via "continuous ⇒ v(A°)≤1"). Is that the faithful reading, or is a single ring of definition containing A⁺ ever genuinely needed (making "pair-free" unfaithful)? |
| Q5 | (Strategic, optional) Is the decomposition — sheafiness ⇐ (embedding/Cor 8.32 + flatness) ∧ (gluing/Lemma 8.34 + Laurent acyclicity), flatness via Remark-7.55 chain — the cleanest route, or would you reduce 8.28(b) differently (Tate's standard-cover acyclicity, or a descent sidestepping the per-step localisation-lift)? |

## Ticket-board snapshot at brief time (TaskList; no tickets.md)

- T57 DONE — Delete false noeth-A₀ orphan lemmas
- T58 pending — Strip [IsNoetherianRing P.A₀]/(locSubring) from case-(b) signatures
- T59 pending — Remove forbidden/unjustified added hypotheses (hArch, IsDomain, decorations)
- T60 pending — Fix changed conclusions + false-as-stated sorry statements
- T61 pending — Fix citations (ORPHANs + systematic mislabels)
- T62 in_progress — Def-7.29 faithfulness: IsRational predicate + IsSheafy requantification + R2-wiring
- T63 DONE — Spa(𝒪(D)) ≃ rationalOpen(D)
- T64 DONE — (LL-unit): s_D a unit in 𝒪(D')
- T65 DONE — (LL-bdd): t/s_D power-bounded in 𝒪(D')
- T66 DONE — assemble faithful (LL), instantiate at 𝒪(D)
- T67 DONE — fold Remark 7.55 chain = Leaf A (re-wired faithful, commit 27b16d7)
- T68 pending / B2 — Prop 7.51(2) via Prop 7.49: bottoms at A⁺⊆A° encoding gap (this brief's §8.1, Q1/Q2/Q4)
- T69 DONE — audit OMT (Thm 5.5) statement before Leaf B
- T70 pending — Leaf B (equalizer+OMT) & Leaf C (Čech grind)

## Stuck points (from §8 of brief)

1. §8.1 — A⁺⊆A° encoding gap: bare PlusSubring class drops the Def-7.14 axiom; faithful predicate IsRingOfIntegralElements exists but is unused/unlinked. Bare statement of Spa-point existence is false (A⁺=⊤ counterexample), but A⁺⊆A° (always true for a real affinoid ring) fixes it. The pacing item on the unit/bounded criterion branch.
2. §8.2 — deep external cites (legitimate black boxes): [Hu2] 3.3 (=7.18(1)), [Hu2] 3.9 (=7.48), [Hu3] 2.6 (=7.54).
3. §8.3 — Leaf B inducing-half wiring: 6.16 proved; 6.18(2) closure form + Pettis-lift (Henkel 2014) remaining.

## Reference list (from §2.2 of brief)

[Wedhorn] arXiv:1910.05934v1 · [Hu1] Cont. valuations 1993 · [Hu2] Bewertungsspektrum 1993 · [Hu3] Étale cohomology 1996 · [Henkel 2014] arXiv:1407.5647 · [BGR] Non-Arch. Analysis 1984
