---
name: teach-multipass-audit
description: Teaches the multi-pass audit methodology that catches structural defects in /develop ticket plans before /beastmode hits them. Apply after every /develop session.
---

# /teach — Multi-Pass Audit Methodology

This document teaches the multi-pass audit procedure used to break down
ticket plans (from `/develop`) into pieces that each fit a < 50 LOC
Lean proof sketch.  It catches three classes of structural defects
that a single math-soundness pass misses:

1. **Math-correct but Lean-infeasible** — the math holds but the Lean
   proof needs 200+ LOC, has API friction the auditor didn't anticipate,
   or requires helper lemmas that aren't surfaced.
2. **Existential-when-canonical-needed** — a sub-lemma returns a
   `Classical.choose` witness that a downstream combiner needs to
   recover canonically (e.g., to construct an `Equiv.Perm`).
3. **Cascading-restatement-leverage missed** — an abstract-operator
   hypothesis (∃ Φ, ...) where a Miyake-faithful explicit
   slash-sum/coset-list formulation reduces work for many consumers.

## When to apply

Run multi-pass audit **after `/develop`** has produced a ticket board,
**before `/beastmode`** starts execution.  If `/beastmode` returns
B2 (SCOPE / DEFINITION ERROR) or hits API friction across multiple
sorries, that's the signal to re-audit.

Multi-pass audit is **not** a replacement for `/develop`'s
math-soundness checks; it's an **additional layer** that asks "is
each ticket's Lean proof tractable per-lemma?"

## The checklist (10 items, NEW1–NEW6 are the audit-multipass additions)

For each sorry / each ticket, run:

### Original 4 (math-soundness)

1. **Math soundness** — does the Lean statement match the source
   (Miyake / Diamond–Shurman / etc.)?
2. **Counterexample sweep** — does any input satisfy the hypothesis
   yet violate the conclusion?
3. **Hypothesis tightness** — is each hypothesis genuinely used in the
   proof?  Are any redundant?
4. **Repo infrastructure** — does any existing proven lemma in the
   project (or mathlib) already do this?

### New 6 (multi-pass additions, the audit's value-add)

5. **NEW1 LEAN PROOF SKELETON (10–30 lines)** — write the proof's main
   structure as a tactic stub.  If you can't sketch it in 10–30 lines,
   that's a sub-ticket trigger: the proof needs further decomposition.

6. **NEW2 LOC ESTIMATE FROM SKELETON** — with the skeleton in hand,
   estimate realistic Lean LOC including bridging tactics
   (`push_cast`, `simp`, `omega`).  50–100 LOC is normal; 200+ is a
   sub-ticket trigger.

7. **NEW3 API FRICTION PATTERNS** — flag known-hard patterns:
   - `ZMod.castHom` composed with `Int.cast` / `chineseRemainder`.
   - `finCongr` cast for `Fin n ≃ Fin m` where `n = m` propositionally
     but not definitionally.
   - `Matrix.GeneralLinearGroup.mkOfDetNeZero` proof-irrelevance.
   - `UpperHalfPlane.σ γ` for matrix products (the project's
     `σ_mapGL_real_eq_id` fires only on `mapGL ℝ s`, not products).
   - Slash multiplicativity across `mapGL ℝ` and `mkOfDetNeZero`.
   - `▸` motive failures on dependent types.
   - Generic structure casts (`Matrix _ _ (ZMod (p*q))` ↔
     `Matrix _ _ (ZMod N)` via `▸` of `p*q = N`).

   Each flagged pattern becomes a named **helper lemma** with its own
   sub-ticket.

8. **NEW4 CANONICAL-vs-EXISTENTIAL** — if this lemma is consumed by a
   combiner that needs uniqueness/bijectivity/`Equiv` construction, is
   the existential witness enough?  If not, restate to return a
   *canonical* witness (e.g., an explicit Möbius formula instead of
   `∃ m'`), OR add a uniqueness conjunct.

9. **NEW5 CASCADING-RESTATEMENT LEVERAGE** — would restating this
   lemma *Miyake-faithfully* (replacing an abstract operator hypothesis
   with the explicit slash sum / coset list) reduce downstream work
   for **≥ 2 consumers**?  If yes, restate now; the leverage cascades.

10. **NEW6 HELPER ENUMERATION** — list every sub-lemma the proof
    will need.  Each becomes a private lemma in the proof file or a
    separate sub-ticket.  Cross-cutting helpers (used by ≥ 3 lemmas)
    deserve a `multipass_*` prefix and a dedicated section.

## Pass structure

Each sorry / ticket gets **at least three passes**:

### Pass A — cold checklist sweep

Apply checklist 1–10 with no prior context.  Output per sorry:

- A verdict: ✓ tractable / 🟡 needs restate / 🔴 blocked.
- The sub-tickets spawned (helper lemmas, restatements).
- Proposed statement changes.

The output of Pass A is a **list of restatements (R1–Rn)** and a
**list of helpers (C-cross-cutting, H-lemma-specific)**.

### Pass B — helper-graph dedup + structural recheck

With Pass-A's sub-tickets in hand:

- **Merge shared friction patterns**: if F11 (`σ`-factor for
  det-positive matrix product) appears in 4 helpers, make ONE
  canonical helper `multipass_sigma_eq_id_of_det_pos` and re-route.
  Expect ~30% reduction in helper count.

- **Structural recheck on NEW4**: for each canonical-witness
  restatement, verify the **combiner** that consumes it can now
  construct its `Equiv` / `Injective` / etc.  If not, restate
  further or add more conjuncts.

- **Tighten LOC estimates**: with helpers deduplicated, re-estimate
  each leaf's LOC.

### Pass C — final feasibility + ordering

Each leaf must be in one of two states:

- **Compiled and `lake build` clean** — closure achieved.
- **Sketch in the audit doc, < 50 LOC pending** — work proceeds
  cleanly in the next `/beastmode` iteration.

Anything > 50 LOC pending → further sub-ticket.

Pass C also produces an **execution ordering** across phases:

```
Phase 0 — Restatements (signature edits, ~80 LOC total)
Phase 1 — Cross-cutting helpers (~120 LOC total)
Phase 2 — Primitive lemmas (number theory, matrix arith)
Phase 3 — Slash-sum / character chain
Phase 4 — Diagram / level-commutation
Phase 5 — Main lemma (combiner)
```

### Pass D — precise statements for deferred helpers (optional)

Some helpers in Pass A/B are deferred because their precise statements
require nontrivial infrastructure (e.g., `UpperHalfPlane.mk` for
`(z+m)/p`).  Pass D refines these statements when the consumer is
about to be attacked.

## Worked example

See `.mathlib-quality/audit-multipass-2026-05-17.md` for a complete
worked example on the SMO chain (16 sorries audited; 7 restatements +
16 helpers spawned).  Net effect: every leaf had < 50 LOC pending
sketch by end of Pass C.

## Anti-patterns to watch for

The audit catches these classes of defects:

- **"Existential targets in combiners"** — if T5a-3 needs `σ :
  Equiv.Perm`, T5a-3a's `∃ m', ...` is insufficient.  NEW4 fires.

- **"Abstract operator hypothesis"** — if the lemma takes `Φ : LinearMap`
  satisfying a q-shift, the q-shift doesn't pin Φ on non-V_p-lifted
  inputs, so combinators using Φ on V_l-lifted inputs are
  underdetermined.  NEW5 fires (restate to explicit slash sum).

- **"σ-factor handwave"** — Miyake says "the slash by det-positive
  matrices commutes with σ-conjugation".  In Lean, this is a specific
  lemma that needs proving / referencing.  NEW3 fires (helper).

- **"Matrix-level CRT"** — Miyake says "by CRT".  ZMod.chineseRemainder
  is for scalars; matrix-level CRT requires entry-wise + det
  verification + cast.  NEW3 fires (helper).

## Integration with /develop

After `/develop` finishes a ticket board:

1. Run `/teach` (this doc) over each ticket.
2. Spawn restatements + helpers as new tickets per Pass A/B output.
3. Update parent tickets' `Depends on` fields.
4. Run `/develop --status` to verify the board.
5. Hand to `/beastmode`.

The cost of multi-pass audit is ~30 min per ticket board; the savings
is avoiding ~5 wasted `/beastmode` iterations that would have hit
structural blockers.

## Templates

### Restatement template (Rn)

```markdown
**Rn**: Restate `<lemma_name>` (was: <old form>).

**Why**: <NEW4 or NEW5 trigger>.

**New statement**:
```lean
<new statement with canonical/explicit form>
```

**Downstream impact**: <list of consumers that now work>.
```

### Cross-cutting helper template (Cn)

```markdown
**Cn**: `multipass_<name>` — <one-line description>.

**Friction pattern**: <NEW3 pattern this addresses>.

**Used by**: <list of consumers>.

**Statement**:
```lean
<lemma signature + brief proof or sorry>
```

**Source citation**: <Miyake/DS/mathlib reference>.
```

### Lemma-specific helper template (Hn)

Same as Cn but used by a single consumer.

## Stop criterion

Multi-pass audit terminates when **every leaf is at one of**:

- (a) Compiled, `lake build` clean.
- (b) Sketch in this doc + < 50 LOC pending.

If any leaf is at > 50 LOC pending after Pass C, run Pass A again on
just that leaf with deeper decomposition.

The audit is **NOT** done until criterion (a) or (b) holds for every
single leaf — the point of the multi-pass methodology is to make sure
no sorry hides a structural defect.
