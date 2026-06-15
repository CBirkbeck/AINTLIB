# Scottish Book Formalization — Ticket Tracker

**Last updated:** 2026-03-16

## How to use this file

1. **Before starting work:** Find an `OPEN` ticket and change status to `IN PROGRESS (agent: your-name)`
2. **When done:** Change status to `DONE` with the date
3. **If blocked:** Change to `BLOCKED` and note the reason
4. **New tasks:** Add at the bottom with the next ticket number

---

## Active Tickets

### Phase 1: Problem 7 (Priority: HIGH)

| Ticket | Task | Status | Assignee | Depends on | Notes |
|--------|------|--------|----------|------------|-------|
| SCOTTISH-001a | Define `IsUniform A` | DONE | claude | — | In `Problem007.lean` |
| SCOTTISH-001b | Define `IsStablyUniform A` | DONE | claude | 001a | In `Problem007.lean` |
| SCOTTISH-001c | State `problem7` theorem | DONE | claude | 001a, 001b | Compiles, sorry proof |
| SCOTTISH-001d | Prove `DiscreteTopology → IsUniform` | OPEN | — | 001a | Easy: discrete ⇒ everything bounded |
| SCOTTISH-001e | Prove `IsStablyUniform → IsUniform` | OPEN | — | 001a, 001b | Trivial localization |
| SCOTTISH-001f | Prove `IsStablyUniform → IsSheafy` (Buzzard–Verberkmoes) | OPEN | — | 001b | Key known result |

### Phase 2: Low-Hanging Fruit

| Ticket | Task | Status | Assignee | Depends on | Notes |
|--------|------|--------|----------|------------|-------|
| SCOTTISH-002 | Define `IsStronglyNoetherian` | OPEN | — | — | Noetherian completions A⟨T₁,...,Tₙ⟩ |
| SCOTTISH-003 | Define `IsAnalytic` for adic spectra | DONE | claude | — | `IsTrivialValuation`, `SpaIsAnalytic` in Problem010 |
| SCOTTISH-004 | Define/import Banach ring basics | DONE | claude | — | `IsUniformBanach`, `IsNormPowerBounded` in Problem001 |
| SCOTTISH-005 | Define restricted power series `A⟨T⟩` | OPEN | — | — | Completion of A[T] |
| SCOTTISH-006a | State Problem 1 | DONE | claude | 004 | `problem1` compiles |
| SCOTTISH-006b | State Problem 8 | DONE | claude | — | `problem8_sheafy/stablyUniform` compile |
| SCOTTISH-006c | State Problem 10 | DONE | claude | 003 | `problem10_counterexample` compiles |
| SCOTTISH-006d | State Problem 15 | DONE | claude | — | `problem15` + `IsCoherentRing` compiles |
| SCOTTISH-006e | State Problem 24 | DONE | claude | — | `problem24/24'` (flat) compile |
| SCOTTISH-006f | State Problems 29, 30, 31, 37 | OPEN | — | 002, 005 | Need `IsStronglyNoetherian`, `A⟨T⟩` |

### Phase 3: Medium Definitions

| Ticket | Task | Status | Assignee | Depends on | Notes |
|--------|------|--------|----------|------------|-------|
| SCOTTISH-007 | Finite étale morphisms of Huber pairs | OPEN | — | — | For Problems 9, 18 |
| SCOTTISH-008 | O⁺ structure sheaf | OPEN | — | — | For Problems 27, 39 |
| SCOTTISH-009 | Rational localization flatness | OPEN | — | — | For Problem 24 |
| SCOTTISH-010 | Completed tensor products | OPEN | — | — | For Problems 5, 32 |
| SCOTTISH-011 | Seminormalization | OPEN | — | — | For Problems 6, 20, 27 |
| SCOTTISH-012 | State Problems 5, 9, 24, 27, 32, 39 | OPEN | — | 007–011 | Use Tier 2 definitions |

### Phase 4: Perfectoid Theory

| Ticket | Task | Status | Assignee | Depends on | Notes |
|--------|------|--------|----------|------------|-------|
| SCOTTISH-020 | Define perfectoid rings | OPEN | — | — | Algebraic definition |
| SCOTTISH-021 | Define tilting functor | OPEN | — | 020 | R ↦ R♭ |
| SCOTTISH-022 | Define perfectoid spaces | OPEN | — | 020, 021 | Adic spaces + perfectoid |
| SCOTTISH-023 | Almost mathematics basics | OPEN | — | — | Almost ring theory |
| SCOTTISH-024 | Witt vectors topology | OPEN | — | — | Topology on W(R) |
| SCOTTISH-025 | State perfectoid-dependent problems | OPEN | — | 020–024 | 17 problems! |

### Phase 5: Advanced Theories

| Ticket | Task | Status | Assignee | Depends on | Notes |
|--------|------|--------|----------|------------|-------|
| SCOTTISH-030 | Diamonds | OPEN | — | 022 | For Problem 16 |
| SCOTTISH-031 | Rigid analytic spaces | OPEN | — | — | For Problems 11, 25 |
| SCOTTISH-032 | Tilde-inverse limits | OPEN | — | 022 | For Problems 25, 40 |

---

## Completed Tickets

| Ticket | Task | Completed | By |
|--------|------|-----------|----|
| SCOTTISH-001a | `IsUniform A` | 2026-03-16 | claude |
| SCOTTISH-001b | `IsStablyUniform A` | 2026-03-16 | claude |
| SCOTTISH-001c | State `problem7` | 2026-03-16 | claude |
| SCOTTISH-003 | `IsAnalytic` / `IsTrivialValuation` | 2026-03-16 | claude |
| SCOTTISH-004 | `IsUniformBanach` / `IsNormPowerBounded` | 2026-03-16 | claude |
| SCOTTISH-006a | State Problem 1 | 2026-03-16 | claude |
| SCOTTISH-006b | State Problem 8 | 2026-03-16 | claude |
| SCOTTISH-006c | State Problem 10 | 2026-03-16 | claude |
| SCOTTISH-006d | State Problem 15 | 2026-03-16 | claude |
| SCOTTISH-006e | State Problem 24 | 2026-03-16 | claude |

---

## Blocked Tickets

| Ticket | Task | Blocked by | Notes |
|--------|------|------------|-------|
| — | — | — | — |
