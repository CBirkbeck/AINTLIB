# Expert-review #2 session state — 2026-06-20

- Generated: 2026-06-20 (follow-up to review #1, 2026-06-19)
- Audience: expert in adic spaces / non-archimedean geometry (Huber–Wedhorn)
- Goal of brief: settle the **embedding/inducing** route for Thm 8.28(b) + 2 soundness checks
- Scope: the embedding half of sheafiness (`ρ : 𝒪(U) → ∏𝒪(Uᵢ)` a topological embedding) + the
  non-open-prime point's completeness + the height-1 generalisation
- Reply received: true (2026-06-20)
- Reply integrated: true (2026-06-20) — see `integration.md`. Q1 route resolved (common-refinement,
  already the project's gluing form), Q2 completeness confirmed essential (add `[CompleteSpace A]`),
  Q3 height-1 = ordered-group fact (no blow-up).

## Questions asked (verbatim §4 of brief)
| # | Question |
|---|---|
| Q1 | the inducing route: (a) descent-compatible closed-image (no intersections) / (b) Čech overlaps (heterogeneous-ring-of-def intersections) / (c) Wedhorn's own = 6.18 module-topology? |
| Q2 | is "non-open prime ⟹ ∃ cont v, 𝔭⊆supp, v≤1 on A°" true WITHOUT completeness, or essential? (T-L3 B2-candidate) |
| Q3 | cleanest formalizable "microbial ⟹ height-1 vertical generalisation" (Rem 4.12) — ordered-group/valuation-ring fact vs blow-up/Krull–Akizuki? |

## Context that triggered this review
- beastmode landed Prop 7.41 (`heightOne_le_one_on_powerBounded`) + reduced T-L3 to one height-1 leaf.
- T-L1 (inducing): the repo proves injectivity via faithfully-flat descent (S⊗_R S, no topology);
  the reviewer-#1's overlap-equalizer closedness needs pairwise intersections, but the repo's
  `interSamePair` requires a common ring of definition and pieces have heterogeneous ones. Route
  decision needed before a large build — hence Q1.
- T-L3 completeness B2-candidate (Q2) + the height-1 leaf depth (Q3).

## Next
Send the brief; integrate via `/expert-review --reply`. On reply: settle Q1 (pick the route),
resolve the Q2 completeness hypothesis decision, and re-plan T-L1 / discharge the T-L3b leaf.
