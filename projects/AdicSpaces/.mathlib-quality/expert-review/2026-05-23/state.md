# Expert-review session state

- Generated: 2026-05-23T12:00:00Z
- Audience: Senior algebraic geometer / Huber–Wedhorn expert
- Goal of brief: Verdict on candidate B2 sub-lemma `strengthened_cover_of_basic_cover` (L4) + soundness check on the 18-leaf decomposition for `isSheafy_ofStronglyNoetherianTate`
- Scope: Whole Wedhorn 8.28(b) critical path (post-audit decomposition.md, 2026-05-23 revision)
- Reply received: true (2026-05-23T12:30:00Z)
- Reply integrated: true (2026-05-23T13:00:00Z)

## Questions in the brief

| # | Question (summary) |
|---|--------------------|
| Q1 | Is the §8.3 falsity analysis of L4 (`strengthened_cover_of_basic_cover`) correct — does `0 ∈ mk_S_D(D)` make the strengthened cover claim fail? |
| Q2 | If L4 is B2, which of three fixes is cleanest: (a) drop 0 from C2's `mk_S_D` source, (b) refactor L4 + consumer to use v(s) ≠ 0, (c) filter the family at consumer level? Hidden gotchas? |
| Q3 | Cascade audit: have we caught all transitive consumers of L4 (the three Tier 0 wrappers)? Should any be re-flagged "open"? |
| Q4 | L1 (`localBasisHyp_of_strongly_noetherian`) cites [Hü21, Lemma 3.8] / [Zav22, §2.3] — does Wedhorn Prop 6.18(1) suffice, promoting L1 to GREEN? |
| Q5 | L11 (`relative_laurent_tree_to_absolute`) is blocked on T-LOCLIFT-PRESERVATION typeclass propagation. Is this structural plumbing or genuine missing math vs Wedhorn 8.34(i)? |
| Q6 | Overall plan soundness + execution-order optimality: F12 → Tate-aux → L1 → L4-audit → L2,L3,L5 → L7,L8 → L9,L10 → L6 → L11 → L12 → L13. Any reorderings? |

## Ticket-board snapshot at brief time (open / in-progress critical-path)

- T-EMBED-TOPO (split into 3 subtickets) — pending
- T-MATHLIB-STACKS-00MA (Stacks 0316, off critical path) — pending
- T-LOCLIFT-PRESERVATION (blocks L11 / L12) — pending
- T-LAURENT-REFINEMENT-TREE-EXISTENCE — in_progress
- P3 (`relative_ratio_split_transports_to_RatioNodeData`) — pending
- P4 (W3-transport `relative_laurent_tree_to_absolute` = L11) — pending
- P5 (W3 `unitGeneratedCover_has_relative_ratioLaurentRefinement` ≈ L9) — pending
- P6 (W2 `exists_first_stage_laurent_tree_unit_generated`) — pending
- P7 (W1 `exists_standard_cover_refining` = L1-L5 chain) — pending
- P8 (assemble `exists_wedhorn_ratio_laurent_refinement_tree_realized`) — pending
- Wave C: F12 move execution (= L18) — pending
- Wave F: Path α wiring (A3 body, A1 embedding = L13) — pending

## Stuck points (from §8 of brief)

1. L4 (`strengthened_cover_of_basic_cover`) candidate B2 — false as stated because `0 ∈ mk_S_D(D)` is possible after `IsCompact.elim_finite_subcover_image` `choose` extraction.
2. Cascade: L4 taints `exists_standard_cover_refining`, `exists_wedhorn_laurent_refinement_tree`, `exists_wedhorn_ratio_laurent_refinement_tree_realized`, `isSheafy_ofStronglyNoetherianTate_proof` (all Tier 0 wrappers).

## Reference list (from §2.2 of brief)

- [Hub93] Huber, Continuous valuations, Math. Z. 1993
- [Hub94] Huber, A generalization of formal schemes and rigid analytic varieties, Math. Z. 1994
- [Hub96] Huber, Étale Cohomology of Rigid Analytic Varieties and Adic Spaces, 1996
- [Wed19] Wedhorn, Adic Spaces, arXiv:1910.05934v1, 2019
- [Hü21] Hübner, The adic tame site, Doc. Math. 2021
- [Zav22] Zavyalov, Quotients of admissible formal schemes and adic spaces by finite groups, §2.3
