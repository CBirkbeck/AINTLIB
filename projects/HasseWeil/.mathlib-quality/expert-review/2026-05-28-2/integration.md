# Reply integration — Round 6 (2026-05-28)

Reply received from the round-1–5 reviewer on 2026-05-28.
Brief: ./brief.md
Reply: ./reply.md

**STATUS: reply recorded, NO code changes applied (user is awaiting the
reviewer's response to the *updated* brief).**

The reply we have answers Q1–Q5 and gives the Strategy-A/B/C verdict, but
it predates the Q6 addition (salvage on the orphaned middle) and the
honest §2.5 accounting. The user re-sent the updated brief (with Q6) and
wants to wait for the reviewer to address Q6 before we execute the
cleanup. So this integration is a **decision record only** — the
Strategy-B execution is deferred until the follow-up reply lands.

## Interpretation summary

| # | Reviewer point | Maps to | Type | Confidence |
|---|---|---|---|---|
| 1 | Placeholder pattern is "semantically poisonous" once named `Isogeny`; fake pullback silently makes false theorems type-check | Q1 | direct (confirms) | high |
| 2 | Acceptable ONLY under explicitly-unsafe name (`Raw`/`Fake`/`PointMapOnly`); never a public `Isogeny` | Q1 | design rule | high |
| 3 | **Strategy B now** (delete records; bare point-map where only point-map used; genuine isogeny where degree/pullback used). Defer C. | A/B/C | decision | high |
| 4 | General `1−α`: witness-parametric `AddIsogData` carrying genuine pullback+compat; NOT Pic⁰; specific α (π_q, [n]) get genuine constructions | Q2 | direct | high |
| 5 | `hq`: explicit for genuine isogenies; none for point-map-only (bare `AddMonoidHom`); optional `_auto` wrapper; not a typeclass | Q3 | direct | high |
| 6 | Q4: enforce compat eventually; start with type separation + quarantine + `IsGenuine` predicate, not a one-shot structure rewrite | Q4 | direct | high |
| 7 | Q5: composed placeholders DO propagate the lie; audit graph-based (tag constructors, dependency closure, negative tests, retire/rename, public-theorem audit) | Q5 | direct + method | high |
| 8 | Immediately rename dead `hasse_bound` → `deprecated_hasse_bound_false_placeholder`; false statement must not share a plausible name | Q5/§2.5 | urgent action | high |
| 9 | 6-step ordered cleanup plan | overall | actionable | high |
| 10 | Q6 (orphaned-middle salvage) | — | **UNANSWERED** (predates Q6) | — |

## Reviewer's 6-step cleanup plan (for when we execute)

1. Quarantine dead theorems (`hasse_bound`, `pointCount_eq`,
   `traceOfFrobenius_sq_le`) — rename / move out of public import path.
2. Introduce point-map-only definitions for `id − π` and `rπ − s`.
3. Replace the ~150 point-map-only call sites with point-map data.
4. Replace the ~4 degree/pullback call sites with genuine isogenies or
   witness-parametric hypotheses (`isogOneSub_negFrobenius W hq`).
5. Add a linter-style audit script for placeholder names flowing into
   `.degree`, `.sepDegree`, `.pullback`, `.toAlgebra`, `isogTrace`,
   `.comp`.
6. Only later strengthen the `Isogeny` structure itself.

## Proposed code actions (DRAFTED, NOT APPLIED)

| # | Action | Files | Risk |
|---|---|---|---|
| P1 | Rename/quarantine dead `hasse_bound`/`hasse_bound_sq`/`traceOfFrobenius_sq_le`/`pointCount_eq` | HasseBound.lean, Frobenius.lean | low |
| P2 | Add `oneSubFrobeniusPointMap` (+ `rSmulSubPointMap`) bare point-map defs | Frobenius/Endomorphism.lean | low |
| P3 | Migrate ~150 point-map-only sites to the bare point-map | ~40 files | mechanical, large |
| P4 | Replace ~4 degree/pullback sites with `isogOneSub_negFrobenius W hq` | IsogenyFactor.lean, Conditional.lean | medium |
| P5 | Delete the 3 placeholder defs once unreferenced | Endomorphism/Frobenius.lean | gated on P3+P4 |
| P6 | Add `IsGenuine` guard + audit doc (lightweight; future-proofing) | new file | low |

## Changes applied

- (none yet — execution deferred per user)

## Open questions remaining

- **Q6** (orphaned-middle salvage): the reviewer has not yet seen the Q6
  version of the brief. The user re-sent the updated brief; awaiting the
  follow-up reply. Once it lands, run `/expert-review --reply` again.

## Decisions recorded (to action once Q6 reply arrives)

- Strategy B is the agreed cleanup path (reviewer + user both endorse).
- Execution order is the reviewer's 6-step plan above.
- `hq` handling: explicit for genuine isogenies, bare point-map otherwise.
- `IsGenuine` predicate: add as a lightweight future guard, not a
  full structure rewrite.
