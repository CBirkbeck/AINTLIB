# Expert-review session state — round 17

- Generated: 2026-05-15
- Audience: ChatGPT Pro (continuing series; round 17, follow-up to round 16 architectural approval)
- Goal of brief: Specific blocker (P3 architectural obstruction) + approach validation (continue locked architecture or refine?)
- Scope: Full round-17 follow-up — P1+P2 closed, P3 architectural issue (lead question), remaining theorems status
- Reply received: true (2026-05-15)
- Reply integrated: true (2026-05-15)

## Questions in the brief

| # | Question |
|---|----------|
| Q1 | Of options A/B/C in §8.1, which is the right resolution of `plus_open_eq` / `hopen` incompatibility? (A: weaken to inclusion; B: parameterize `plus.P`; C: hypothesis $g_\mathrm{inv} \in A_0$.) Specifically: does the downstream NODE induction need literal equality or only inclusion? |
| Q2 | Is the round-16 architecture still the right target, or does §8.1's obstruction indicate a small architectural refinement? Would Option A break round-15/16's load-bearing reasoning? |
| Q3 | Is the density + uniform-inducing + non-arch strict-triangle sketch in §5.3 the cleanest route to the bridge lemma, or is there a more direct path? Is mathlib's field-only `Valued.extensionValuation` an obstacle or routine to adapt? |
| Q4 | If Option B is preferred, does the existing `HasLocLiftPowerBounded` typeclass (which encodes $1/s$ extension to $A_0$ for rational subsets) generalize to $1/h$ for $h$ a completion-unit, via Wedhorn 7.45 + 7.50? |
| Q5 | Given P3 is blocked: pause P3 and resolve obstruction first (recommended order), or skip to W3 (independent of P3, only W3-transport depends) and tackle easier theorems first? |

## Ticket-board snapshot at brief time

Top-level Tate-acyclicity ticket: `T-LAURENT-REFINEMENT-TREE-EXISTENCE` (in progress).

Sub-tickets within reviewer's round-16 recommended order:

| Ticket | Status |
|---|---|
| `isUnit_relativeUnitGenerator_from_W2_unit` (P1) | done (this round) |
| `isUnit_base_s_in_presheafValue_of_subset` (P2) | done (this round) |
| `comap_canonicalMap_not_vle_zero_of_isUnit_aux` (bridge) | in progress (steps 1–3 done; steps 4–5 documented as the substantive next step) |
| `transport-RatioNodeData` (P3) | **blocked** on §8.1 |
| `relative_laurent_tree_to_absolute` (W3-transport) | open (uses P3) |
| `unitGeneratedCover_has_relative_ratioLaurentRefinement` (W3) | open |
| `exists_first_stage_laurent_tree_unit_generated` (W2) | open |
| `exists_standard_cover_refining` (W1) | open |
| `exists_wedhorn_ratio_laurent_refinement_tree_realized` (I.1-realized) | open |
| `adicCompletion_noetherian` (V.1) | external mathlib gap |

## Stuck points (from §8 of brief)

1. §8.1 — `plus_open_eq` requires `RationalLocData A` whose `hopen` is not constructible from unit-in-$\mathcal{O}(L)$ alone. Three resolution options (A/B/C) outlined.
2. §8.2 — `plus.hopen` specifically requires $1/h$ in `locSubring`; no choice of `plus.T` simultaneously satisfies the rationalOpen equality and the hopen.
3. §8.3 — bridge lemma steps 4–5 (density + non-arch + strict-triangle) not yet formalized; mathematically standard but engineering work.

## Reference list (from §2.2 of brief)

- [Wedhorn 2019] Wedhorn's *Adic Spaces* notes, arXiv:1910.05934.
- [Huber 1993] Huber's adic-spaces monograph.
- [Scholze 2012] Scholze's perfectoid spaces paper.

## Architecture status

Round 16: FINAL APPROVAL of the `RatioLaurentTree A` + `RatioNodeData` + `RatioTreeRealization` architecture. The reviewer's directive: "stop redesigning, start proving the open lemmas". This round 17 reports a structural obstruction encountered during proof execution.
