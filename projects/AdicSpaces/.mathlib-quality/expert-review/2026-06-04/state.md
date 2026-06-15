# Expert-review session state

- Generated: 2026-06-04
- Audience: Adic-spaces / Huber expert (fluent in [Hu1]–[Hu3], Wedhorn's Adic Spaces)
- Goal of brief: Strategic guidance — cleanest route to Lemma 7.54 (= [Hu3] 2.6), the
  milestone-gating cover-refinement; whole-8.28(b) context, questions centred on 7.54.
- Scope: Whole Theorem 8.28(b), questions focused on Lemma 7.54.
- Reply received: true (2026-06-04)
- Reply integrated: true (2026-06-04)

## Questions in the brief

| # | Question (verbatim from §9) |
|---|------------------------------|
| Q1 | Elementary route to 7.54 from quasi-compactness + Cor 7.53 + an explicit combinatorial refinement of finitely many rational subsets, avoiding the full [Hu3] 2.6 apparatus — cleanest argument (how to build (f₀,…,fₙ) from a finite subcover (R(Sₖ/sₖ)), why pieces refine + T generates unit ideal)? Analogue of the 7.48 density de-risk. |
| Q2 | Can 8.28(b)'s reduction be restructured to AVOID 7.54 — a different cofinal family of covers (Laurent? unit-generated?) easier to reach from arbitrary covers and still handled by 8.34? (We have the Laurent layer relativised + acyclic.) |
| Q3 | If no shortcut: precise statement + proof SKELETON of [Hu3] Lemma 2.6 (steps, auxiliary facts, which are elementary), to formalise directly mirroring Huber's argument. |
| Q4 | Absolute vs relativised: does 7.54 need to be applied relatively (cover of a rational subset U = Spa O_X(U)) or does the absolute statement over Spa A suffice (invoked once at top, propagated via A.3(2))? |

## Ticket-board snapshot at brief time (gluing half, Čech layer)

DONE (axiom-clean) this session:
- T-CECH-LAURENT-REL (relative IsLaurentCover def + foundation + trivial-cover base case + anchor; deleted a dead sorry)
- T-CECH-LAURENT-DOM (laurent_cover_from_dominating_unit, V.base=D₀ via relative def)
- T-CECH-LAURENT-PROD cons-decomp (+ fixed propA3_bridge under-hypothesis)
- propA3_part3_bridge SEPARATION (direct, restrictionMap_comp)
- (earlier) embedding/Cor 8.32, Prop 7.48, Prop 6.17/6.18, Cor 7.53, Examples 6.38/6.39 / MvTate topology

IN PROGRESS / OPEN:
- propA3_part3_bridge GLUING cocycle (T-CECH-CONSOL-2, direct route; abstract IsOXAcyclic↔IsAcyclic bridge UNNEEDED)
- T-CECH-833 / 833-W828 (Lemma 8.33 3×3 chase)
- T-CECH-740-6 (Prop 7.40(6) height-1 value group)
- T-CECH-PAIR (principal pair + pseudo-uniformiser)
- T-CECH-RATIO / IDEALGEN (8.34 iii/iv structure)

BLOCKED (this brief's subject):
- T-CECH-754 (Lemma 7.54 = [Hu3] 2.6) — milestone-gating; SEVER-D → IMPORT → 834-W828 → WIRE all transitively depend on it.

## Stuck points (from §8 of brief)

1. (heart) Lemma 7.54 — refine arbitrary cover to a T-generated cover; Wedhorn = "[Hu3] 2.6". Gap: Cor 7.53 gives T→cover (easy, in-repo); 7.54 is the converse-with-refinement (build T from a finite subcover). 
2. (secondary) Cor 7.32 inputs: Prop 7.40(6) height-1, principal-pair/pseudo-uniformiser.
3. (secondary) classical Čech: 8.33 3×3 gluing, A.3(3) product-gluing cocycle.

## Reference list (from §2.2)

[Wedhorn] Adic Spaces; [Hu1] Continuous valuations, Math. Z. 212 (1993); [Hu2] (Spa Â≅Spa A,
Prop 3.9); [Hu3] A generalization of formal schemes…, Math. Z. 217 (1994) — Lemma 2.6 = blocker.

## Context

Two prior expert-review rounds (6.17/6.18 open-mapping; 7.48 = [Hu2] 3.9) both reviewer-informed
and since formalised axiom-clean. 7.48 de-risked to an elementary density lemma. This round seeks
the analogue for 7.54.
