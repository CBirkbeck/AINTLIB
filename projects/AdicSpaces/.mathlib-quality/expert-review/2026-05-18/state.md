# Expert-review session state

- Generated: 2026-05-18T07:00:00Z
- Audience: ChatGPT / Claude (math model)
- Goal of brief: Both — soundness check on the four flagged false-as-stated lemmas AND strategic guidance on the IsSheafy proof as a whole
- Scope: Tate acyclicity / IsSheafy chain (Wedhorn Theorem 8.28(b)) — the ~55 sorries in the transitive dependency closure of `isSheafy_ofStronglyNoetherianTate`
- Reply received: true (date: 2026-05-18T08:00:00Z)
- Reply integrated: partial — Stage 1 complete (docstring annotations + 2 signature tightenings + 1 citation fix). Stage 2 (deletions/quarantines/restatements with consumer refactors across 10+ files) pending user re-approval.

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Is the implication "A strongly noetherian Tate ⇒ ∃ noetherian ring of definition of A" correct in any sensible generality, or is the ℂ_p counterexample correct? If ℂ_p is a counterexample, what is the right statement of the analogue of Wedhorn Prop 6.18 without assuming a noetherian ring of definition? Does Wedhorn 8.28(b) still hold when A is strongly noetherian Tate without a noetherian ring of definition? |
| Q2 | Is "noetherian Tate ⇒ strongly noetherian Tate" known in any generality beyond completely valued fields of height 1 (BGR §5.2.6)? If open in general, what is the right setting — restrict to "complete Tate with a noetherian ring of definition" everywhere? |
| Q3 | For F2/F3: do you confirm the analysis that f_i must live in 𝒪_X(C_base) rather than in A? If so, the fix propagates through P3-P8. Is there a slicker formulation than per-leaf transport via Wedhorn Example 6.38? |
| Q4 | Is the project's overall strategy structurally sound, or does it need fundamental restructuring? (a) add noeth-ring-of-def hypothesis; (b) restrict to non-arch field height 1; (c) keep architecture, accept "Wedhorn-clean" wrappers never discharge; (d) something else. |
| Q5 | Can the sheaf-of-sets condition for arbitrary covers be derived from (i) Cor 8.32 + (ii) Lemma 8.34 for standard covers + (iii) refinement transfer (NOT cohomology) — i.e., without developing full Čech machinery? Or does the project genuinely need Wedhorn Appendix A? |
| Q6 | What is the correct Stacks tag for "I-adic completion of noetherian ring is noetherian"? We currently cite 00MA, but verbatim 00MA is Lemma 10.97.1 about completion exactness. |
| Q7 | Where exactly in Wedhorn/Huber is "a power-bounded ⇔ v(a) ≤ 1 for every v ∈ Cont A"? Wedhorn Rem 7.42 is about vertical generations, not power-boundedness. Mis-citation, or intermediate result we're missing? |
| Q8 | The project has both restrictionMap_isLocalization (false in general; convergent denominator tails counterexample) and restrictionMap_flat_via_iteratedMinus (Wedhorn-honest). Currently compiles transitively because restrictionMapHom_surj is sorry-bodied. Sound interim measure or remove false claim now? |
| Q9 | G1, G2 retired-as-false single-map lemmas: delete now (cascade breakage) or keep as sorry'd scaffolding (current policy)? |
| Q10 | Sanity check on F4-F11: do RatioLaurentTree / RatioTreeRealization / unit-generated cover encodings look natural and correct for Wedhorn 8.34 steps (i)-(iv), or restructure to a more abstract "exists chain of refinements" statement? |

## Ticket-board snapshot at brief time

No formal `.mathlib-quality/tickets.md` exists for the IsSheafy chain — the project tracks via:
- The 55 sorries themselves (with docstring discharge plans)
- TaskList items (pending: P3, P4, P5, P6, P7, P8 in the Wedhorn 8.34 tree chain; T-EMBED-TOPO; T-MATHLIB-STACKS-00MA; T-LOCLIFT-PRESERVATION; T-LAURENT-REFINEMENT-TREE-EXISTENCE)
- 9 prior expert-review sessions on related sub-topics (2026-05-11 through 2026-05-15)

## Stuck points (from §8 of brief)

1. Wedhorn 6.18 chain forward direction (B2, B3) — FALSE: ℂ_p counterexample. Strongly noeth Tate ⇏ noeth ring of definition.
2. Wedhorn 6.18 forward implication (B4) — likely OPEN. Noeth Tate ⇏ strongly noeth Tate in general.
3. Wedhorn Lemma 7.54 lifting (F2, F3) — type-misaligned: forces R(C.base) = Spa A.
4. Three B2-flagged signatures with own counterexamples (D15, E1, E2).
5. Wedhorn 8.28(b) acyclicity (H^q=0, q≥1) scoped out; only sheaf-of-sets in current target.

## Reference list (from §2.2 of brief)

- [Wedhorn] Torsten Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, 2019, 107pp
- [Hu1] R. Huber, *Continuous valuations*, Math. Z. 212 (1993)
- [Hu2] R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994)
- [Hu3] R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, AspMath E30, 1996
- [BGR] Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Grundlehren 261, 1984
- [Stacks] Stacks Project; tags 023N (descent for modules), 00MA (completion exactness for finite modules — NOT noetherianness)
- [Hübner] K. Hübner, *Sheafiness of Huber's valuation spectrum*, arXiv:2405.06435
