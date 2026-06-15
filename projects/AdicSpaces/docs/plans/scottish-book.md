# Nonarchimedean Scottish Book — Formalization Plan

**Goal:** Formalize the statements (not proofs) of the 40 open problems from
[Kedlaya's Nonarchimedean Scottish Book](https://scripts.mit.edu/~kedlaya/wiki/index.php?title=The_Nonarchimedean_Scottish_Book)
in Lean 4, building on our adic spaces library.

**Reference:** The problems originate from the 2015 Arizona Winter School and subsequent
additions through 2022.

---

## Problem Status Overview

| # | Proposer | Status | Priority | Difficulty |
|---|----------|--------|----------|------------|
| 1 | Kedlaya | Open | Medium | Low — needs Banach ring, uniform |
| 2 | Kedlaya | Open | Medium | High — needs perfectoid |
| 3 | Hansen | **Resolved** | — | — |
| 4 | Hansen | Open | Low | High — needs perfectoid |
| 5 | Hansen | Open | Low | High — needs Witt vectors, completed ⊗ |
| 6 | Hansen | Open | Low | High — needs sousperfectoid |
| **7** | **Kedlaya** | **Open** | **HIGH** | **Low — needs IsUniform, IsStablyUniform** |
| 8 | Kedlaya | **Resolved** | — | — |
| 9 | Kedlaya | Open | Medium | Medium — needs finite étale |
| 10 | Kedlaya | Counterexample | Low | Low — needs analytic locus |
| 11 | Conrad | Open | Low | High — needs rigid analytic |
| 12 | Hansen | **Resolved** | — | — |
| 13 | Hansen | **Resolved** | — | — |
| 14 | Kedlaya | Open | Low | High — needs perfectoid fields |
| 15 | Kedlaya | Open | Low | Medium — needs Witt vectors |
| 16 | Hansen | Open | Low | Very High — needs diamonds |
| 17 | Kedlaya | Counterexample | Low | Medium |
| 18 | Kedlaya | Open | Low | High — needs local systems |
| 19 | Kedlaya | Likely Resolved | Low | Medium |
| 20 | Kedlaya | Open | Low | High — needs seminormalization |
| 21 | Kedlaya | Open | Low | High — needs perfectoid residue fields |
| 22 | Kedlaya | Open | Low | High — needs tilting |
| 23 | Kedlaya | Open | Low | Very High |
| 24 | Kedlaya | Open | Medium | Medium — needs flatness |
| 25 | Kedlaya | Open | Low | High — needs rigid analytic |
| 26 | Kedlaya | Open | Low | High — needs perfectoid |
| 27 | Kedlaya | Open | Low | High — needs O⁺ cohomology |
| 28 | Kedlaya | Open | Low | Medium |
| 29 | Zavyalov | **Resolved** | — | — |
| 30 | Zavyalov | Open | Medium | Medium — needs strongly noetherian |
| 31 | Kedlaya | Open | Low | Medium |
| 32 | Kedlaya | Open | Low | High — needs perfectoid + completed ⊗ |
| 33 | Kedlaya | Open | Low | High — needs Witt vectors |
| 34 | Kedlaya | Open | Low | High — needs perfectoid |
| 35 | Kedlaya | Open | Low | Medium |
| 36 | Kedlaya | Open | Low | Very High |
| 37 | Kedlaya | Open | Low | Medium — needs excellent rings |
| 38 | Shahoseini | **Resolved** | — | — |
| 39 | Kedlaya | Open | Low | High — needs O⁺ cohomology |
| 40 | Kedlaya | Open | Low | Very High — needs tilde-limits |

**Resolved:** 3, 8, 12, 13, 29, 38 (6 problems)
**Likely resolved:** 19
**Open:** 33 problems

---

## Definition Dependency Tiers

### Tier 0 — Already formalized (in our repo)

These are available now and need no new work:

| Concept | Location | Used by problems |
|---------|----------|-----------------|
| Huber pairs `(A, A⁺)` | `AdicSpectrum.lean` (`PlusSubring`) | Nearly all |
| Adic spectrum `Spa(A, A⁺)` | `AdicSpectrum.lean` | Nearly all |
| Tate rings | `HuberRings.lean` (`IsTateRing`) | 2,4,5,6,7,9,24,27,28,31,32,33,35,37 |
| Huber rings (f-adic) | `HuberRings.lean` (`IsHuberRing`) | Many |
| Bounded / power-bounded `A°, A°°` | `Bounded.lean` | 1,7,28,34 |
| Rational subsets | `RationalSubsets.lean` | 7,9,24,28 |
| Cont(A) | `ContinuousValuations.lean` | 12 |
| Sheafiness `IsSheafy` | `StructureSheaf.lean` | 7,19,31,32,33 |
| Structure sheaf | `StructureSheaf.lean` | 19,27,30 |
| Localization topology | `LocalizationTopology.lean` | 7,24 |
| Presheaf values (completions) | `Presheaf.lean` | 7 |

### Tier 1 — Small additions to existing modules (1–2 days each)

| Concept | Add to | Used by problems | Depends on |
|---------|--------|-----------------|------------|
| **`IsUniform`** | `Bounded.lean` | **7**, 1, 34, 35 | `IsBounded`, `powerBoundedSubring` |
| **`IsStablyUniform`** | new `Uniform.lean` or `Bounded.lean` | **7**, 2, 5, 9, 35 | `IsUniform`, `RationalLocData` |
| `IsStronglyNoetherian` | `HuberRings.lean` | 29, 30, 31, 37 | `IsTateRing` |
| `IsAnalytic` (no trivial valuations) | `AdicSpectrum.lean` | 10 | `Spa` |
| Banach ring | new `BanachRings.lean` | 1, 17 | Mathlib normed rings |
| Restricted power series `A⟨T⟩` | new `RestrictedPowerSeries.lean` | 29, 31, 37 | `IsHuberRing` |

### Tier 2 — Medium additions (1–2 weeks each)

| Concept | Used by problems | Depends on |
|---------|-----------------|------------|
| Finite étale morphisms of Huber pairs | 9, 18, 21 | `Spa`, Mathlib étale |
| Flatness of rational localizations | 24 | Localization topology |
| O⁺ sheaf (integral structure sheaf) | 27, 39 | Structure sheaf |
| Stalk noetherianity | 30 | Structure sheaf stalks |
| Seminormalization | 6, 20, 27, 39 | Mathlib |
| Excellent rings | 37 | Mathlib |
| Completed tensor products | 5, 32 | Mathlib uniform spaces |

### Tier 3 — Major new theories (months of work)

| Concept | Used by problems | Notes |
|---------|-----------------|-------|
| **Perfectoid rings/spaces** | 2,3,4,5,6,13,14,20,21,22,25,26,32,33,34,38,40 | Massive dependency; ~17 problems need this |
| **Tilting** | 14, 22, 38 | Needs perfectoid |
| **Witt vectors topology** | 5, 15, 33 | `WittVector` in Mathlib, needs topology |
| **Diamonds** | 16 | Needs perfectoid + pro-étale |
| **Rigid analytic spaces** | 11, 25 | Large theory |
| **Tilde-inverse limits** | 25, 40 | Needs perfectoid + pro-systems |

---

## Recommended Work Order

### Phase 1: Problem 7 (START HERE)

**Goal:** State Problem 7 with machine-checked types.

**Tasks:**
1. Define `IsUniform A` in `Bounded.lean` — `IsBounded (powerBoundedSubring A)`
2. Define `IsStablyUniform A` — every rational localization is uniform
3. State `problem7 : IsSheafy A → IsUniform A → IsStablyUniform A`
4. Prove basic implications:
   - `IsStablyUniform → IsUniform` (trivial localization)
   - `IsStablyUniform → IsSheafy` (Buzzard–Verberkmoes)
   - `DiscreteTopology → IsUniform` (everything is bounded)

**Blocking issues:** None — all prerequisites exist.

**Ticket:** SCOTTISH-001

### Phase 2: Low-hanging fruit (Tier 1 definitions)

**Goal:** State problems that only need small additions.

**Tasks:**
1. `IsStronglyNoetherian` → state Problems 30, 37
2. `IsAnalytic` → state Problem 10
3. Banach ring basics → state Problem 1
4. Restricted power series `A⟨T⟩` → state Problems 29, 31

**Tickets:** SCOTTISH-002 through SCOTTISH-006

### Phase 3: Medium definitions (Tier 2)

**Goal:** Build out supporting theories.

**Tasks:**
1. Finite étale morphisms → Problems 9, 18
2. O⁺ sheaf → Problems 27, 39
3. Rational localization flatness → Problem 24
4. Completed tensor products → Problems 5, 32

**Tickets:** SCOTTISH-007 through SCOTTISH-012

### Phase 4: Perfectoid theory (Tier 3)

**Goal:** Define perfectoid rings/spaces to unlock ~17 problems.

This is the biggest single dependency. Suggested approach:
1. Perfectoid rings (algebraic definition)
2. Tilting functor
3. Perfectoid spaces (as adic spaces with perfectoid stalks)
4. Almost mathematics prerequisites

**Tickets:** SCOTTISH-020 through SCOTTISH-025

### Phase 5: Remaining advanced theories

- Diamonds, rigid analytic spaces, tilde-inverse limits
- These are very far out and may not be feasible in the short term

---

## Concept Clustering (which problems share definitions)

**Uniform/stably uniform cluster:** 1, 5, 7, 9, 28, 34, 35
→ Phase 1–2, low barrier

**Sheafiness cluster:** 2, 4, 7, 19, 31, 32, 33
→ `IsSheafy` exists; needs stably uniform + perfectoid

**Strongly noetherian cluster:** 29, 30, 31, 37
→ Phase 2, moderate barrier

**Perfectoid cluster:** 2, 3, 4, 5, 6, 13, 14, 20, 21, 22, 25, 26, 32, 33, 34, 38, 40
→ Phase 4, high barrier (17 problems!)

**Cohomology cluster:** 19, 26, 27, 39
→ Phase 3, needs O⁺ sheaf

---

## File Structure

```
Adic spaces/ScottishBook/
  Problem001.lean  — Problem 1 (Banach ring uniform ⇒ field?)
  Problem002.lean  — Problem 2 (perfectoid Spa ⇒ perfectoid ring?)
  ...
  Problem007.lean  — Problem 7 ★ (sheafy uniform ⇒ stably uniform?)
  ...
  Problem040.lean  — Problem 40 (tilde-inverse limits)
```

Each file contains a docstring with the problem statement and (when formalized)
the Lean definitions and `sorry`'d theorem statement.

---

## Success Criteria

A problem is "stated" when:
1. All definitions in the statement have Lean types (no `sorry` in definitions)
2. The theorem statement type-checks (the proof can be `sorry`)
3. The file compiles with `lake env lean`

A problem is "partially stated" when:
1. Some definitions exist but others are `sorry`'d or use `axiom`
2. The overall structure is clear

---

## Notes for Parallel Workers

- **Read `docs/TICKETS.md`** before starting any task
- **Claim your ticket** by marking it `IN PROGRESS (agent: your-name)`
- **Tier 1 tasks are independent** — multiple agents can work in parallel
- **Tier 2+ tasks may have dependencies** — check the dependency column
- **Problem 7 is the critical path** — prioritize unblocking it
- When adding definitions to existing files, coordinate via `docs/STATUS.md`
