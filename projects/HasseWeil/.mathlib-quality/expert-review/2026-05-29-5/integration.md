# Reply integration — round 11 (2026-05-29)

Reply received from the senior arithmetic-geometry reviewer (rounds 1–11) on 2026-05-29.
Brief: ./brief.md
Reply: ./reply.md

## Interpretation summary

| # | Reviewer point | Maps to | Type |
|---|---|---|---|
| 1 | §3 finding CORRECT: BRIDGE-003 gives (i) [N] not (ii) the dual relation; IsDualOf(rV−s)(rπ−s)⟺deg=N; no sign in degree multiplicativity | Q1 | direct (confirms) |
| 2 | Abandon BRIDGE-003 as Hasse-critical path; keep as reusable infrastructure | Q4 | strategy change |
| 3 | Use Pic⁰ route (not kernel/factorisation) — Pic⁰ gives dual additivity (rπ−s)^=rV−s naturally | Q2 | direct |
| 4 | Refinement: Pic⁰ dual RETURNS genuine β̂; prove point-map=rV−s; extensionality; compare. No addIsog | Q2 | concrete strategy |
| 5 | Narrow frobeniusPlane_dual OK, but general exists_dual likely cleaner/reusable | Q2 | option |
| 6 | No cheaper substitute (parallelogram=same; deg-symmetry=only \|N\|; Tate=heavy; point-count=worse) | Q3 | direct |
| 7 | CAUTION: isolate zero/scalar-collapse branch (rπ−s=0 ⟹ deg 0, Q=0) in global ∀r,s | unprompted | concern |

## Changes applied

- GAP-QF-DEGQF: appended "★★ ROUND-11 CHOSEN PLAN — PIVOT to Pic⁰ dual existence/additivity"; round-10 narrow-Route-A plan marked SUPERSEDED. Recorded the 5-step Pic⁰ critical path + reviewer refinement (dual returns genuine β̂, no addIsog) + Q2/Q3/Q4 verdicts + the zero/scalar-collapse assembly caution.
- BRIDGE-003 (formalIsogenySeries_add) + Wall A (genuineIsogSmulSubV*, addPullback_x_pair_x_ord_neg): DEMOTED from Leaf-1 critical path, RETAINED as reusable infrastructure.
- Memory v13-leaf2-closed.md updated with the round-11 verdict + Pic⁰ pivot.

## Changes rejected by user

- (none)

## Open questions remaining

- None unanswered; all of Q1–Q4 answered decisively.

## Decisions recorded

- Leaf-1 deep route DECIDED: Pic⁰ dual existence/additivity (over kernel/factorisation and over BRIDGE-003).
- BRIDGE-003 / Wall A demoted to infrastructure (not deleted).
- Next action (user-approved): apply integration + START Pic⁰ scoping (sub-ticket plan + lowest piece).
