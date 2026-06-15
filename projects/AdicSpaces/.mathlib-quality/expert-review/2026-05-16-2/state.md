# Expert-review session state — round 21

- Generated: 2026-05-16
- Audience: ChatGPT Pro (continuing series; round 21, follow-up to rounds 17–20)
- Goal of brief: Specific blocker. Round 20 prescribed the domination lemma for P3 with a proof outline assuming Spa compactness. The project's only Spa-compactness theorem for the Tate setting requires seven explicit witnesses, including `hArch` (every valuation has a multiplicatively archimedean value group), which is not derivable from the standing typeclass bundle. The user's hypothesis rule strictly disallows adding `hArch` since the result is mathematically true without it. We need direction on whether to refactor compactness infrastructure, accept hArch as a permitted hypothesis, or take a different proof method.
- Scope: P3 compactness blocker only (the domination lemma's compactness sub-step).
- Reply received: true (2026-05-16)
- Reply integrated: true (2026-05-16)

## Questions in the brief

| # | Question (verbatim from §8 of the brief) |
|---|------------------------------------------|
| Q1 | Which path forward — (a) refactor project compactness to drop hArch, (b) accept hArch as a permitted hypothesis, or (c) a different proof method that doesn't go through Spa compactness? |
| Q2 | Is hArch a genuine restriction in Wedhorn's 8.28(b) or an artifact of one Lean formalisation? If genuine, what breaks for higher-rank valuations? If artifact, what's the correct formulation of Spa compactness? |
| Q3 | What is the cleanest Lean rendering of Wedhorn's 7.31 compactness proof that doesn't need hArch? Where does mul-archimedean enter in the closed-image step, if at all? |
| Q4 | Is there a reformulation of the domination lemma or P3 itself that avoids compactness entirely? Adaptive FG-generator choice? Restricted finite-subset hopen? |
| Q5 | Spirit-of-the-rule interpretation: is project-pattern hArch propagation a violation or legitimate exception of the user's "only add hypothesis if result is false without it" rule? |

## Ticket-board snapshot at brief time

- T-LAURENT-REFINEMENT-TREE-EXISTENCE (parent): in_progress.
- P1, P2: done.
- P3 (`relative_ratio_split_transports_to_RatioNodeData`): open. Round-20
  closure structurally in place; substantive sub-lemma (domination lemma)
  is the only remaining sorry of P3.
- P4 (`relative_laurent_tree_to_absolute`): open. Leaf case shares the
  same compactness-style blocker via the extension claim (Wedhorn 7.49
  reverse) — not addressed in this round.
- P5–P8: open. Round-20's Q3–Q9 unanswered; not in scope for this round.
- T-MATHLIB-STACKS-00MA: open external mathlib gap.

## Stuck points (from §6 of brief)

1. **Discharging compactness for the domination lemma without adding hArch.**
   Three logical paths: (a) refactor infrastructure, (b) accept hArch with
   rule-exception, (c) different proof method. All three need reviewer
   guidance.

## Reference list (from §2.2 of brief)

- [Wedhorn 2019] — Adic Spaces lecture notes (arXiv:1910.05934).
- [Huber 1993] — continuous valuations (Math. Z. 212).
- Round-20 reviewer reply (2026-05-16) — prior round prescription for P3.

## Architectural changes this round

- No code changes this round. The domination lemma remains a sorry in the
  Tate-acyclicity residuals file; the parent P3 sub-lemma
  (`exists_absolute_ratio_rationalLocData_aux`) is structurally complete
  and consumes the domination lemma's output unchanged.
- Brief saved at `.mathlib-quality/expert-review/2026-05-16-2/brief.md`.
- Round-20 session at `.mathlib-quality/expert-review/2026-05-16/` remains
  the precedent for the domination-lemma plan.
