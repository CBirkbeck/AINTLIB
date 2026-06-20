# Reply integration — 2026-06-20 (embedding/inducing route + soundness)

Brief: `brief.md`. Reply: `reply.md` (this folder). Key claims source/code-verified before integrating.

## Interpretation table

| # | Reviewer point | Maps to | Type | Verified |
|---|---|---|---|---|
| 1 | Q1: route (a) descent⟹closed FAILS (no topological strictness from faithful flatness); (c) 6.18 is CIRCULAR (needs the subspace complete = what we want) | Q1 | rules out (a),(c) | ✓ standard topology/functional analysis |
| 2 | Q1: canonical route = Čech-closedness via **ALL common rational refinements** D₃ (not single intersections) ⟹ no heterogeneous-`P` API | Q1 | the unblock | ✓✓ **the project's `IsSheafy.gluing` (StructureSheaf:311-320) is ALREADY this exact predicate** — no bridge theorem needed |
| 3 | Q2: completeness ESSENTIAL; counterexample `A=𝔽_p[x]` (x)-adic, `𝔭=(x-1)` | Q2 | confirms the B2-candidate | ✓ checked: `(x-1)` maximal, non-open (`(x)+(x-1)=A`), dense; trivial-only support ⟹ no continuous pt; unit in `𝔽_p[[x]]` |
| 4 | Q3: height-1 generization = ordered-group fact (microbial⟹order-hom `Γ→ℝ`, `H=ker`, `Γ/H` height 1); NO blow-up/Krull–Akizuki | Q3 | shrinks the leaf | ✓ matches Wedhorn 5.46 microbial defn; `embed_archimedean_valueGroup_into_real` (sorry) is the harder bracket→ℝ direction |
| 5 | Risks: tensor≠Čech (prove equiv if needed); `E` R-module + `ContinuousSMul`; closed/product cg instances; Spa-completion transports valuations not primes; avoid Zorn for "largest convex H" | all | guardrails | recorded |

UNANSWERED: none — Q1/Q2/Q3 fully answered.

## Net effect — all three blockers resolved

- **T-L1 (inducing) — ROUTE OBSTACLE DISSOLVED.** The heterogeneous-`P` intersection problem I hit in
  beastmode is a non-issue: define `sectionEqualizer` via the **common-refinement compatibility
  predicate** (every rational `D₃ ⊆ Uᵢ ∩ Uⱼ`), reusing the existing `restrictionMap`; closedness =
  `isClosed_iInter` of `isClosed_eq`. **The project's `IsSheafy.gluing` is ALREADY stated with this
  predicate**, so the algebraic separation/gluing theorem plugs in directly — no `tensorCocycle_iff_…`
  bridge. Routes (a)/(c) correctly rejected. T-L1a statement revised on the board.
- **T-L3 (completeness) — B2-CANDIDATE CONFIRMED, fix settled.** Add `[CompleteSpace A]` to T-L3 +
  T-L3b + the StandardCover pair-free consumer; thread from the (complete) headline. CLAUDE.md-(b)
  justified by the `𝔽_p[x]`/`(x-1)` counterexample. Record as a regression note.
- **T-L3b (height-1 point) — DE-RISKED.** Reduces to a clean ordered-group lemma + valuation wrapper +
  Rem 7.42 continuity; NOT the deep blow-up/Krull–Akizuki theory I feared.

## Changes applied (board)
- `tickets.md` T-L1a: status → ROUTE RESOLVED; revised statement to the common-refinement form + sketch.
- `tickets.md` T-L3: added the Q2 completeness resolution (add `[CompleteSpace A]` + counterexample) and
  the Q3 height-1 ordered-group discharge plan.

## Next
Build order now clear: **T-L1** (sectionEqualizer common-refinement + closedness → bundle → OMT) is
unblocked and uses existing infra; **T-L3** = add `[CompleteSpace A]` + thread + discharge the
ordered-group height-1 leaf. Run `/beastmode` (T-L1a is the natural next pickup) or `/develop --continue`
to reticket T-L1b/c with the common-refinement `E`.
