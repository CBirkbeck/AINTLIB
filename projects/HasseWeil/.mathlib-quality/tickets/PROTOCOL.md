# Worker Protocol

This document defines how workers (human or AI) check out tickets, work on them,
and update their status. **Every worker MUST read this before claiming a ticket.**

## Overview

The Hasse-Weil project is divided into ~155 tickets in `.mathlib-quality/tickets/`,
organized by Silverman section. Each ticket is a single markdown file with a
specific Lean theorem/definition to prove. Workers claim tickets, work on them,
update their progress in the ticket file, and mark them done when merged.

## Ticket lifecycle

A ticket moves through these states:

```
OPEN → CHECKED-OUT → IN-PROGRESS → REVIEW → DONE
                       ↘ BLOCKED ↗
```

| State | Meaning |
|---|---|
| **OPEN** | Available for claim. No owner. Dependencies should all be DONE. |
| **CHECKED-OUT** | A worker has claimed it but not yet started coding. |
| **IN-PROGRESS** | A worker is actively coding. |
| **BLOCKED** | Worker hit a dependency that isn't done yet; back out. |
| **REVIEW** | Code complete, awaiting merge / verification. |
| **DONE** | Merged into the main project. Sorry-free. |

## Identifying yourself as a worker

When you start working on this project, choose a unique worker ID. Examples:
`worker-A`, `worker-B`, `claude-2026-04-09-1234`, `chris-laptop`, etc. Use the same
ID for all your tickets so the audit trail is consistent. Workers should add their
ID to the top of `INDEX.md` under "Active workers" so others can see who's online.

## Step 1: Find a ticket

1. Open `.mathlib-quality/tickets/INDEX.md`.
2. Filter for `Status: OPEN` tickets.
3. Check each candidate's dependency list. If ANY listed dependency is not `DONE`,
   skip that ticket.
4. Pick one — preferably one that **unblocks the most downstream tickets** (see
   `DEPENDENCIES.md` for the graph).
5. Read the full ticket file. Make sure you understand the Silverman reference and
   the acceptance criteria.

If you cannot find an OPEN ticket whose deps are met, see "When all ready tickets
are taken" below.

## Step 2: Check it out

1. Edit the ticket file. Set:
   ```
   Status: CHECKED-OUT
   Owner: <your-worker-id>
   Checked out at: <ISO timestamp, e.g. 2026-04-09T14:30:00Z>
   ```
2. Append to the Progress log:
   ```
   - 2026-04-09T14:30Z [worker-id] checkout
   ```
3. Update `INDEX.md` to reflect the new status (find the row, change `OPEN` to
   `CHECKED-OUT (worker-id)`).
4. Commit both files in one commit:
   ```
   git add .mathlib-quality/tickets/{INDEX.md,curves/T-II-1-001-*.md}
   git commit -m "checkout T-II-1-001"
   ```

## Step 3: Code

1. Switch the ticket to `Status: IN-PROGRESS`.
2. Write Lean code in the file specified by the ticket's `Module:` field. Create
   the file if it doesn't exist (and add it to the parent's import list).
3. Follow the acceptance criteria EXACTLY:
   - Match the Lean theorem name.
   - Match the type signature.
   - Use the namespace specified.
   - Add a docstring with `Reference: Silverman <section>`.
4. Build incrementally:
   ```
   lake build HasseWeil.<your.module>
   ```
   Don't move on until your file builds clean.
5. **Zero sorries, zero axioms** other than mathlib's standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`).

## Step 4: Update progress (every coding session)

Append a progress log entry to the ticket file at the END of every coding session.
The entry must include what you did, what state the code is in, and what's next.

```
- 2026-04-09T16:00Z [worker-id] Defined `MyTheorem`. Proof skeleton in place,
  three intermediate lemmas still needed: `lemma_a`, `lemma_b`, `lemma_c`. Will
  attack `lemma_a` next session. Build status: passes with 3 sorries (intentional,
  marked TODO).
```

You should commit ticket updates alongside Lean code in the SAME commit so the
audit trail is consistent.

## Step 5: Mark done

When the work is complete (zero sorries, builds clean):

1. Set `Status: REVIEW` in the ticket file.
2. Add to the Progress log:
   ```
   - 2026-04-10T11:00Z [worker-id] Complete. lake build HasseWeil.<module> passes
     with 0 sorries. Commit hash: abcd1234.
   ```
3. Update `INDEX.md` to `REVIEW (worker-id)`.
4. (Optional) request review by another worker. After review passes:
5. Set `Status: DONE` in both the ticket and `INDEX.md`. Add the merge commit hash.

## Conflict resolution

### Two workers want the same ticket

- The first worker to commit the checkout wins. The second worker must back out
  (revert their local checkout) and pick a different ticket.
- Always pull the latest before checking out to minimize this.

### Stale checkouts

A ticket is considered **stale** if it has been `CHECKED-OUT` or `IN-PROGRESS` for
more than 7 days with no Progress log entries.

Any other worker may release a stale ticket:

1. Add to the Progress log:
   ```
   - 2026-04-16T09:00Z [other-worker-id] release stale (no activity since 2026-04-09)
   ```
2. Set `Status: OPEN`, clear `Owner:`, clear `Checked out at:`.
3. Update `INDEX.md`.
4. Commit the release.

The original worker is welcome to re-claim the ticket later.

### Dependency was DONE but turned out incomplete

Sometimes a "DONE" ticket leaves a gap that a downstream ticket discovers. If this
happens:

1. Set the affected ticket to `Status: BLOCKED`.
2. Add a Progress log entry explaining what's missing.
3. File a new ticket (or reopen the upstream one) for the gap.
4. Pick a different open ticket and work on that instead.

### When all ready tickets are taken

If every OPEN ticket whose deps are met is already checked out, then you're
synch-locked. Three options:

1. Look for a DONE-but-buggy ticket and offer to review/fix it (set `Status: REVIEW`
   if it isn't already, do the review work, mark DONE).
2. Look for stale checkouts (see above) and release one.
3. Pick an ambitious ticket whose deps aren't all done yet, but prove the deps as
   sub-goals first. This is risky but sometimes necessary.

## Code quality

Every Lean file produced must:

1. Build with `lake build HasseWeil.<module>` with **zero errors and zero sorries**.
2. Have NO `axiom` declarations beyond mathlib's standard ones.
3. Each public theorem/def has a docstring referencing `Silverman <section>`.
4. Match the naming conventions in the existing project (see existing files for
   examples). Use camelCase for definitions, snake_case for theorems where
   appropriate (matching mathlib).
5. The file builds cleanly without `set_option linter.<X> false` overrides where
   possible.
6. No `show` tactic abuse (use `change` instead).
7. No `maxHeartbeats` overrides without a documented reason.

## Communication

- All worker communication happens through ticket Progress logs. Don't use chat,
  Slack, or DMs for ticket-related discussion — it has to be in the audit trail.
- If you need to coordinate with another worker, leave a note in their ticket's
  Progress log: `[worker-id] @other-worker can you confirm <X>?`.
- Cross-ticket discussion goes in `INDEX.md` under a "Discussion" section if
  needed.

## Stop conditions

A worker should STOP and not commit:

- If `lake build` fails. Fix it before committing.
- If you've added a sorry that wasn't in the original ticket. Only allowed in
  intermediate states; must be removed before `Status: REVIEW`.
- If you don't understand the Silverman reference. Ask first.
- If your work would require modifying a ticket that you don't own. File a new
  ticket or comment in the other ticket.

## Anti-drift gates (added 2026-05-08, refined per external reviewer)

The project has had a recurring failure mode: workers ship `_of_witness` /
`_of_X` theorems (witness-parametric closures that take the substantive
content as a hypothesis) and the bound's hypothesis count fails to shrink.
At least one circular instance has been identified — a theorem whose
hypothesis was logically equivalent to its conclusion in the ambient
context. The following gates are non-negotiable:

1. **Witness-parametric theorems are allowed but must be namespaced.**
   Theorems that take substantive content as a hypothesis (anything ending
   in `_of_witness`, `_of_X`, `_of_card_match`, etc.) must live in a file
   under a `Conditional`, `Assuming`, or `OfWitnesses` namespace, OR the
   theorem name must use one of those suffixes consistently. They are
   scaffolding, not deliverables.

2. **PARTIAL → DONE requires unconditional discharge.** A ticket cannot
   move from PARTIAL to DONE via further parametrisation. The transition
   requires that the ticket's named mathematical statement be proved
   without a new hypothesis equivalent to the statement.

3. **Dependency labels on every witness-parametric theorem.** Every
   `_of_X` theorem must have a docstring or comment block of the form:
   ```
   -- depends_on: <ticket-id-or-named-theorem>
   -- consumes: <the substantive lemma name(s) the witness embodies>
   ```
   This makes the audit trail explicit and prevents silent re-introduction
   of a circular layer.

4. **Circularity check.** A theorem of the form `T_of_H : H → C` is
   rejected if `H` is logically equivalent to `C` (or implies `C`) in the
   ambient context. Reviewers and coordinators must catch this BEFORE the
   commit lands. The known circular instance was "given `#ker φ = deg φ`,
   conclude the fixed-field equality" — but `#ker φ = deg φ` is the
   conclusion of Silverman III.4.10(c), the very theorem the bound chain
   wants. Any future witness whose statement implies V.1.3 (i.e.,
   `#E(F_q) = deg(1-π)`) directly is rejected.

5. **Per-session metric: unconditional theorem endpoints landed.** Forward
   progress on the bound is measured by **unconditional theorem endpoints
   landed**, not by raw commits or axiom-clean declaration count. A
   session shipping 9 commits of `_of_X` reducers but zero unconditional
   discharges is a drift session.

6. **Coordinator-side verification.** Before acknowledging any commit
   batch, run `grep -n "_of_witness\|_of_[A-Z]" <touched files>` and
   identify whether new witness arrows were added; if so, push back
   BEFORE the next directive. Coordinators relay drift, not just commits.

The conditional-consumer pattern (e.g., `hasse_bound_of_witnesses` in
`Hasse/Final.lean`) remains valid and useful — it isolates the substantive
inputs the bound consumes. What is NOT valid is shipping further layers
above an existing conditional consumer that take the SAME substantive
content under different names. Use a conditional file once; do not stack.

## Quick reference card

```
OPEN  → check deps in INDEX → claim → CHECKED-OUT
CHECKED-OUT → start coding → IN-PROGRESS
IN-PROGRESS → log every session → REVIEW (when done)
REVIEW → another worker checks → DONE
BLOCKED → file/wait/back out → OPEN

Every commit: ticket file + Lean file + INDEX.md (if status changed)
Every session end: append Progress log entry
Stale = 7+ days no activity, anyone can release
```
