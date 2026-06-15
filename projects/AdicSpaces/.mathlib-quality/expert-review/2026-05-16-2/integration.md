# Reply integration — round 21, 2026-05-16

Reply received from ChatGPT Pro on 2026-05-16. Brief: `brief.md`. Reply: `reply.md`.

## Interpretation summary

The reviewer recommends path **(a) locally**: prove a no-`hArch` compactness
lemma for the specific half-space `K⁺` (or for rational opens generally) by
the Wedhorn/Huber Boolean-cube argument, **without** refactoring all of
Spa compactness globally. `hArch` is confirmed as an artifact of the
current Lean proof, not a genuine restriction in Wedhorn 8.28(b). The
domination lemma genuinely needs compactness for uniform `N`; no
reformulation avoids this. The user's hypothesis rule supports the
refactor over `hArch` propagation.

| # | Reviewer point | Maps to | Type |
|---|---|---|---|
| 1 | (a) locally — prove no-hArch compactness for K⁺ or rationalOpen | Q1 | direct answer |
| 2 | hArch is an artifact, not a genuine restriction | Q2 | direct answer |
| 3 | Clean route: Boolean-cube + finitary closed axioms + Tychonoff; no mul-arch needed | Q3 | direct sketch |
| 4 | No compactness-free reformulation; uniform N requires compactness | Q4 | direct answer (negative) |
| 5 | Spirit of user rule supports refactor over hArch propagation | Q5 | direct answer |
| 6 | Audit: hArch likely enters in ONE specific closed-image lemma | meta | guidance |
| 7 | Scope-creep risk: aim for rational-opens, not all of 7.31 | meta | risk flag |

## Action plan

1. **NEW ticket** `T-COMPACT-NO-HARCH` (no-hArch rational-open compactness)
   — sole prerequisite for closing P3's domination lemma.
2. **No change to P3's hypothesis bundle**: `hArch` stays out.
3. **Audit task** (informational): existing `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`
   inherits `hArch`; the new lemma should specialize the closed-image step
   rather than rebuild Spa compactness.
4. **No new ticket for Q4**: reviewer ruled out compactness-free
   reformulation.

## Implementation status (2026-05-16, post-reply)

- T-COMPACT-NO-HARCH added to ticket tracker.
- Reviewer guidance recorded.
- State file updated: Reply received: true, Reply integrated: true.
- Next: work T-COMPACT-NO-HARCH directly.

## Changes applied this round

- Reply saved at `.mathlib-quality/expert-review/2026-05-16-2/reply.md`.
- State updated.
- New file `Adic spaces/SpaCompactNoHArch.lean` created with the target
  lemma statement (`isCompact_preimage_rationalOpen_no_hArch`) and a
  documented proof plan. Body is `sorry`. Added to root import.
- Build clean: 3128 jobs, +1 sorry (in the new file).

## Audit finding: potential discrepancy with reviewer's claim

The reviewer's claim — that continuity for `v ∈ Spv A` on a Tate ring is
encodable as a finitary closed condition on the Bool product without
invoking `MulArchimedean` — does not survive close inspection of the
project's specific `Spa` definition (which uses Wedhorn 7.7's
`IsContinuous`: `{a : v(a) < γ}` open for every `γ`).

Concretely: for higher-rank `v ∈ Spv A` with `v(π) < 1` in `v`'s value
group (but `v` not mul-archimedean), there exist `γ` at a lower rank than
`v(π)` for which `{a : v(a) < γ}` is not open in `A`. Such `v` satisfies
the natural Boolean conditions (`v ≤ 1` on `A⁺`, `v(π) < 1`) but is NOT
in `Spa` under Wedhorn 7.7. The bool-image equality therefore needs an
additional condition that excludes such `v`'s — which is essentially the
mul-archimedean condition on `v`'s value group.

So the existing project use of `hArch` in `image_spa_ιSpv_bool_of_tate`
appears mathematically necessary, not a "specialisation artifact" as the
reviewer suggested. Three possibilities:

1. The reviewer's encoding plan works via a clever finitary trick I have
   not seen (e.g., topology adjustment on the Bool cube, or a different
   axiomatic continuity condition).
2. The reviewer is implicitly using a more permissive definition of
   "Spa" (without explicit Wedhorn 7.7 continuity), where the boolean
   conditions automatically suffice.
3. The reviewer's plan is mathematically incorrect for this specific
   project setup.

This finding warrants either a follow-up clarification round with the
reviewer, or accepting `hArch` as a hypothesis for the domination lemma
(against the user's rule but matching the project pattern).

## Open questions still on the table (deferred to future rounds)

- Q3 from round 20 (P5 W3 explicit recursion) — still unanswered.
- Q4 from round 20 (P6 W2 dominating unit + per-leaf I_units) — still unanswered.
- Q5 from round 20 (P7 W1 standard cover + Zavyalov) — still unanswered.
- Q6–Q9 from round 20 (forward 2.13 datum, T001 non-open prime, 00MA mathlib gap, meta) — still unanswered.

Strategy: close P3 first (via T-COMPACT-NO-HARCH), then re-engage on remaining substantive Wedhorn content.
