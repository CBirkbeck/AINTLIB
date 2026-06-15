# Reply integration — 2026-05-11 round 3

Reply received from ChatGPT Pro on 2026-05-11 (round 3).
Brief: ./brief.md
Reply: ./reply.md

## Interpretation summary

The reviewer rejected both stated options (Route A refactor, depth-2 Route B) and
prescribed a **third route**: prove the general Wedhorn 8.30-style theorem
*arbitrary rational restrictions are flat* — `O(E) → O(D)` is flat whenever
`rationalOpen D ⊆ rationalOpen E`. This single theorem discharges T-FLAT-PER-E
because every piece of `per_E_local_covering` is, by construction, a rational
sub-piece of E.

Build the general theorem from:
1. Basic plus flatness: `B → B⟨X⟩/(f-X)` (NO source-side PB hypothesis on f).
2. Basic minus flatness: `B → B⟨X⟩/(1-fX)` (already partly there).
3. Transitivity of rational localizations (finite chain of basic steps).
4. Composition of flat maps.
5. Strong-noetherian Tate preservation at intermediate B-levels.

The current `restrictionMap_flat_via_iteratedPlus` (T-FLAT-PLUS) uses the wrong
abstraction by exposing `IsPowerBounded (D₀.canonicalMap f)` as a source
hypothesis. The plus rational localization is **what makes f power-bounded**;
the correct model is the `f-X` quotient.

For T-EMBED-TOPO: faithful flatness does NOT give topological inducing.
Required toolbox: topological Example 6.38 + strict Laurent two-cover
exactness + refinement induction preserving embeddings. Splits into 3
sub-tickets.

Reviewer-flagged housekeeping:
* `IsNoetherianRing (locSubring …)` should be a derived theorem from
  noetherianity of `P.A₀` + finite T, not a hypothesis.
* Rational localizations of strongly noetherian Tate rings should again be
  strongly noetherian Tate — reusable preservation theorem.

## Changes applied

### Tickets added to `.mathlib-quality/tickets.md` (§ "SESSION 3 REFRAME")

- `T-RATIONAL-FLAT-GENERAL` — general rational-restriction flatness theorem
  (HIGH PRIORITY, supersedes T-FLAT-PER-E).
- `T-RATIONAL-FLAT-BASIC-PLUS` — `B → B⟨X⟩/(f-X)` flat without PB hypothesis (HIGH).
- `T-RATIONAL-FLAT-BASIC-MINUS` — packaging existing minus flatness at the
  rational-localization API level (PARTLY DONE).
- `T-RATIONAL-LOC-TRANSITIVITY` — every rational containment = finite chain of
  basic steps (HIGH PRIORITY).
- `T-STRONG-NOETH-PRESERVATION` — `O(D)` is strongly noetherian Tate when A is
  (MEDIUM PRIORITY).
- `T-LOC-SUBRING-NOETH` — discharge the `IsNoetherianRing (locSubring …)`
  hypothesis locally (LOW PRIORITY housekeeping).
- `T-FLAT-PLUS-REWORK` — rebuild plus flatness without source-side PB
  hypothesis (MEDIUM PRIORITY).
- `T-EMBED-TOPO-EXAMPLE638` — topological version of Example 6.38 (HIGH).
- `T-EMBED-TOPO-STRICT-LAURENT` — strict exactness of Laurent 2-cover Čech
  complex (HIGH).
- `T-EMBED-TOPO-REFINEMENT-TRANSFER` — refinement preserves topological
  embedding (HIGH).

### Tickets superseded

- `T-FLAT-PER-E` (task #18 in the session tracker) — marked superseded.
  Both Route A and depth-2 Route B rejected by reviewer. Replaced by
  T-RATIONAL-FLAT-GENERAL.

### Session 3 reframe section added

A new "SESSION 3 REFRAME" subsection added at the bottom of `tickets.md`,
documenting:
* The session-2 reframe's correctness AND its surfaced new mismatch.
* Why Routes A and B were rejected.
* The reviewer's prescribed third route.
* The reviewer-flagged housekeeping items.

### Decisions recorded but not actioned (correctly noted as not needing tickets)

- `T-NEW-4` and `T-NEW-5` wrapper closures remain valid; once
  `T-RATIONAL-FLAT-GENERAL` lands, the supplied `lane_B_supplier` becomes
  sorry-free via the new flatness route. No ticket change needed.
- `T-COR832-FF-LAURENT`, `T-FF-COMBINED`, `T-FF-LAURENT-AT-E`,
  `T-FLAT-VIA-WEDHORN830` — all remain useful as
  Laurent-direct-shape special cases. No supersession.
- `T-MATHLIB-COMPLETEDLOC` — still decoupled, still LOW priority.

## Tickets unblocked by approval

Once `T-RATIONAL-FLAT-GENERAL` lands:
- `T-NEW-4` and `T-NEW-5` close sorry-free at the wrapper level.
- The retired `restrictionMap_isLocalization` chain is no longer needed
  internally; `tateAcyclicityComplete` can take the new flatness route as
  its `lane_B_supplier`.

## Open questions remaining

None — reviewer answered all six questions directly. No unanswered Qs.

## Files updated

- `.mathlib-quality/tickets.md` — new "SESSION 3 REFRAME" section with 10 new
  tickets + supersession note for T-FLAT-PER-E.
- `.mathlib-quality/expert-review/2026-05-11-3/state.md` — flags flipped
  (Reply received: true, Reply integrated: true).
- `.mathlib-quality/expert-review/2026-05-11-3/integration.md` — this file.
- Task tracker (session #18 deleted/superseded, #19-#23 created).

## Saved for posterity

- `.mathlib-quality/expert-review/2026-05-11-3/brief.md` — original brief.
- `.mathlib-quality/expert-review/2026-05-11-3/reply.md` — reviewer reply.
