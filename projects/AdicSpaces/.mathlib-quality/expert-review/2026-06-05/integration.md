# Reply integration — 2026-06-05

Reply received from expert reviewer (senior adic-spaces / Huber–Tate) on 2026-06-05.
Brief: brief.md
Reply: reply.md

## Interpretation summary

Verdict: route CONFIRMED faithful on all four questions. Refinements + one defect:

- Q1: faithful. REFINEMENT — topological embedding via equalizer-corestriction + Tate OMT (image is cyclic after injectivity; full product is NOT f.g.), NOT naive Prop 6.18(2) on the full product. Cite Remark 8.20.
- Q2: faithful. CONFIRMED A₀-ideal quantifier (I, not I·A). CAUTION — prove QC via Spv(A,I·A) spectral (7.5) + 7.10 + Thm 7.35, constructible/patch topology, not naive closed-in-compact.
- Q3: 6.17/6.18 + 7.48 genuine external (Henkel zero-seq-of-units OMT right tool); 7.54 internal-buildable (Cor 7.32 + product trick).
- Q4: section rings strongly-noeth via Example 6.38, NOT "noeth+Tate ⟹ strongly-noeth" (FALSE). Ex 6.38's use of 6.17 is faithful, not a hidden noeth-ring-of-def. ℂ_p test confirmed.
- Additional: Cor 8.32 support-inequality suffices ✓; 8.31 bottoms at 6.18 ✓; 8.33 additive-no-domain ✓; 8.34 relative generators in O_X(U) ✓.
- Priority ordering 1–6 confirms keystone-first execution sequence.

## Changes applied

- (A) Inducing leaf (T-SUM-4/E1): reviewer-guidance note — equalizer-corestriction + OMT, not naive 6.18(2) on full product; Remark 8.20 citation.
- (B) Keystone (T-COMPACT-NO-HARCH): reviewer-guidance note — Spv(A,I·A) spectral + 7.5 + 7.10 + Thm 7.35; track constructible/patch topology.
- (C) NEW ticket T-Q4-STRONGNOETH-FIX: replace false noeth+Tate⟹strongly-noeth (`isStronglyNoetherian_of_isNoetherianRing_isTateRing` at prop_8_30_flat_of_faithful_base) with Example 6.38 propagation; VERIFY-FIRST then B2.
- (D) 7.54 framing downgraded (internal-buildable, not deep external).
- (E) Validations + priority-ordering confirmation recorded.

All in `.mathlib-quality/tickets.md`, "Reviewer guidance (expert-review reply, 2026-06-05)" block in the 2026-06-05 EXECUTION ROADMAP section.

## Changes rejected by user

- (none)

## Open questions remaining (reviewer addressed all four)

- (none unanswered) — all of Q1–Q4 answered directly.

## Decisions recorded but not actioned

- Henkel zero-seq-of-units OMT confirmed the right tool for 6.17/6.18 (keep current Banach-OMT infra).
- 7.48 for the Cor 8.32 bridge may use the relative point-lifting (T-SUM-7/T-SUM-8 already landed) rather than the monolithic full-homeomorphism — consistent with the 2026-06-03 integration.

## Next action (user-approved)

Verify the Q4 defect: read `isStronglyNoetherian_of_isNoetherianRing_isTateRing`'s actual statement; if the bare false implication, log B2 and re-route to Example 6.38.
