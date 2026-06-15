# Stream D Infrastructure Plan

This plan identifies the core infrastructure needed to unblock the remaining
Stream D tickets, ordered by impact/tractability.

## Current state (2026-04-17)

Stream D: 51 tickets total.
- **25 done/review** (incl. all of IV.4, IV.7-001/002, IV.5-001/002/004/005/006,
  IV.2-006/007/008(n=1)/009/010, IV.6-003)
- **26 blocked** with explicit unblocker annotations
- **0 open**

## Infrastructure chunks needed to unblock remaining tickets

### I. Power series toolkit (isolated, mathlib-quality helpers)

**I-1. `PowerSeries.order_subst`** — order of compositional substitution
  - Statement: `order (subst f g) = order g * order f` when `constantCoeff f = 0`
    (or `⊤` when either is `0`).
  - Needed by: T-IV-7-003 (height of composition).
  - Estimated: 80-120 lines.
  - Self-contained, could be contributed to mathlib directly.

**I-2. `subst_compInverse_eq_X`** — compositional inverse identity
  - Statement: for `f` with `constantCoeff f = 0` and `coeff 1 f = 1`,
    `PowerSeries.subst (compInverse f) f = X`.
  - Needed by: T-IV-5-003 (log iso to Ĝ_a), full T-IV-2-009.
  - Approach: induction on coefficient index; show `compInvTrunc`'s
    coefficients stabilize.
  - Estimated: 150-300 lines. Requires careful coefficient bookkeeping.

**I-3. `compInverse_of_unit`** — generalize compInverse from `coeff 1 = 1` to
  `coeff 1 ∈ R*`.
  - Statement: for `f` with `constantCoeff f = 0` and `IsUnit (coeff 1 f)`,
    construct `g` with `subst g f = X` and `subst f g = X`.
  - Needed by: T-IV-2-008 (general unit case), T-IV-3 via inverse.
  - Approach: scaling trick `g = u⁻¹ · (compInverse (u⁻¹ · f))(u · T)`.
  - Estimated: 100 lines given I-2.

### II. Formal group algebraic machinery

**II-1. `FormalGroup.inverse`** — formal group inverse series
  - Statement: for `F : FormalGroup R`, produce `i : PowerSeries R` with
    `fAdd F X i = 0` (formally, `F(T, i(T)) = 0`).
  - Approach: fAdd F X T has coeff 1 = 1 in T; use compInverse style.
  - Needed by: IV.3 (F(M) construction), abstract group structure.
  - Estimated: 80-120 lines. Depends on I-2 or can be done directly via
    coefficient recurrence.

**II-2. `FormalGroup.evalGroup`** (partial) — F(M) as an abelian group.
  - For `R` complete local with max ideal `M`, the set `M` with operation
    `x +_F y := F(x, y)` is an abelian group.
  - Needed by: T-IV-3-001 to T-IV-3-007.
  - Requires II-1 + convergence proofs in `M`-adic topology (relies on
    `IsAdicComplete`).
  - Estimated: 200-300 lines.

### III. Curve-formal group bridge

**III-1. `formalIsogenySeries`** — induced power series from an isogeny.
  - Statement: `α : Isogeny E₁ E₂` induces a power series `formal_α ∈ F[[T]]`
    expressing `α` in the local parameter `z = -x/y` at `O`.
  - Needed by: T-IV-BRIDGE-001..004.
  - Depends on: T-IV-1-001 (curve-level `z = -x/y`) which itself needs
    curve `IsUniformizerAt` infrastructure.
  - Estimated: ~200 lines once T-IV-1-001 is done.

### IV. Curve uniformizer infrastructure (upstream)

**IV-1. `WeierstrassCurve.zAt0`, `wAt0`** — local parameters at `O`.
  - `z = -x/y`, `w = -1/y` as elements of `K(E)`.
  - Needs: `FunctionField` API, `IsUniformizerAt` predicate on function fields.
  - Likely requires significant mathlib work.
  - Estimated: 300+ lines + mathlib PRs.

**IV-2. Hensel on `R[[T]][X]`** — for T-IV-1-005 and w-series construction.
  - Estimated: substantial (probably already in mathlib for discretely-valued
    rings; needs adaptation).

### V. Elliptic curve formal group axioms (T-IV-2-005)

**V-1. `EllipticCurve.formalGroup : FormalGroup R`** — the existing
  `formalGroupLaw W : FormalGroupLaw R` (in `FormalGroup.lean`) packaged as
  a `FormalGroup R` by proving the four axioms.
  - Associativity is deep (~500 lines of explicit coefficient algebra or a
    universal-ring specialization argument).
  - Commutativity follows from the symmetry of the underlying construction.
  - Unit laws follow from the recurrence structure.
  - Estimated: 800-1500 lines OR a clever universal argument.

---

## Ordering of work (dependency-sorted)

Chunks are ordered so each builds on the previous:

1. **I-1** (order_subst) → unblocks T-IV-7-003
2. **I-2** (subst_compInverse_eq_X) → unblocks T-IV-5-003 substantially
3. **I-3** (compInverse_of_unit) → unblocks T-IV-2-008 fully
4. **II-1** (FormalGroup.inverse) → depends on I-2 or can be done directly;
   unblocks II-2 and IV.3 chain
5. **II-2** (FormalGroup.evalGroup) → unblocks T-IV-3-001..007
6. **V-1** (EC formal group) → unblocks T-IV-2-005, III-1
7. **IV-1** (curve uniformizers) → upstream mathlib work
8. **III-1** (formalIsogenySeries) → unblocks IV-BRIDGE chain

---

## Pragmatic plan for this session

Given context constraints, I'll attempt:

### Priority 1: I-1 (`PowerSeries.order_subst`)
- Cleanest, most isolated, biggest immediate unblock (T-IV-7-003).
- Strategy: case-split on `f = 0` / `g = 0`; otherwise use the
  `X^order(g) * divXPowOrder g` factorization.

### Priority 2: I-2 (`subst_compInverse_eq_X`)
- More complex, but high value.
- Strategy: induction on the coefficient index `n`, using the
  self-correcting property of `compInvTrunc`.

### Priority 3: II-1 (`FormalGroup.inverse`)
- Given I-2, this is a direct application.

If time permits, items II-2 and V-1 are the next priorities.

## Files to create / modify

- **NEW** `HasseWeil/FormalGroup/OrderSubst.lean` — I-1
- **MODIFY** `HasseWeil/FormalGroup/Logarithm.lean` — I-2, I-3
- **NEW or MODIFY** `HasseWeil/FormalGroup/Inverse.lean` — II-1
- **FUTURE** `HasseWeil/FormalGroup/EvalGroup.lean` — II-2
