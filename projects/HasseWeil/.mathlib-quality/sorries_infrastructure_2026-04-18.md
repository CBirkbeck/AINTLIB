# Infrastructure Plan for Remaining 17 Sorries (2026-04-18)

This document maps each remaining sorry to the infrastructure needed to
close it, following Silverman as the primary reference. It organizes the
work into **6 buckets** with tractability/impact estimates.

## Current state (2026-04-18)

- **Sorries**: 17 across 8 files
- **Stream D**: 16 DONE, 12 REVIEW, 23 BLOCKED
- **Core infrastructure complete**: Formal group theory (MulByNat, CharP,
  Logarithm, Height, Hom, Inverse, EvalGroup — the last closed this
  session), LocalExpansion.

## Bucket A — Dual Isogeny Chain (9 sorries)

**Files**: DualIsogeny.lean (8), DegreeQuadraticForm.lean (1)
**Cascades to**: PullbackCoeff.lean:171, Frobenius.lean (partial)

### What Silverman does
III.6.1 (existence+uniqueness of dual), III.6.2 (properties), III.6.3
(deg is positive definite QF).

### Infrastructure chunks

**A-1. Isogeny kernel as finite group** (T-III-4-011, T-III-4-012)
- `Isogeny.kernel` as AddSubgroup — **DONE** (scaffold, 2026-04-18, in
  `HasseWeil/EC/IsogenyKernel.lean`)
- Finiteness + cardinality bound — needs fiber-finiteness for finite
  morphisms of smooth curves (~200 lines).

**A-2. Separability ↔ `#ker = deg`** (T-III-4-015)
- Full III.4.10(c) proof. ~300-500 lines.
- Uses A-1 + T-III-2-009 (translation pullback) + Artin's theorem.

**A-3. Isogeny factorization theorem** (T-III-4-016)
- Silverman III.4.11. ~400-600 lines. Depends on A-2 + T-II-2-001.

**A-4. Quotient curve construction** (T-III-4-017)
- Silverman III.4.12. ~500-900 lines. Deepest piece.

**A-5. Dual isogeny existence + properties** (T-III-6-001 to 009)
- Uses A-3 + A-4. ~300-400 lines.

**Total A-bucket**: ~1700-2800 lines.

### Alternative path (Pic⁰)
Use Pic⁰(E) ≅ E (III.3.4) + `pullback_Pic⁰` to get the dual isogeny
directly. Shorter (~800 lines) BUT requires Pic⁰ infrastructure which
is equally absent.

## Bucket B — AdditionPullback Transcendence (3 sorries)

**File**: AdditionPullback.lean:193, 225, 268
**Blocks**: Frobenius trace cascade (V.1)

### Infrastructure chunks

**B-1. Minpoly coefficients in subfield** (~200 lines)
- When `α` algebraic over `F` inside `K(E)` with `[K(E):F(x_gen)] = 2`,
  minpoly of `α` over `F(x_gen)` has coefficients in
  `F(x_gen) ∩ F̄ = F` (purely transcendental closure).

**B-2. Weierstrass cubic degree parity** (~150 lines)
- If `px = α·y_gen + β` with `α, β ∈ F(x_gen)` and Weierstrass holds,
  cubic-in-x_gen vs quadratic-in-y_gen forces contradiction.

**B-3. `addPullback_x ≠ const`** (~100 lines)
- Weierstrass reduction to contradict `AddNonInverse W α`.

**Total B-bucket**: ~450 lines.

## Bucket C — Formal Isogeny Bridge (2 sorries)

**File**: PullbackCoeff.lean:138 (L171 is Bucket A)
**Blocks**: PullbackCoeff additivity chain

### Infrastructure chunks

**C-1. `formalIsogenySeries`** — power series representation of
`α*(z)` where `z = -x/y` at `O`. ~200-300 lines. Depends on
T-IV-1-001 (curve-level `z = -x/y`).

**C-2. Formal ↔ curve isogeny correspondence** as a ring hom. ~150
lines given C-1.

**Total C-bucket**: ~450 lines (after upstream curve uniformizer work).

## Bucket D — Division Polynomial Wronskian (1 sorry)

**File**: OmegaPullbackCoeff.lean:477
**Blocks**: T-V-1-003 cascade (Frobenius trace via division polynomials)

### Infrastructure

**D-1. Division polynomial recurrences** — already in
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Verify API.

**D-2. Wronskian identity via induction** on `n`. ~500 lines.

**Total D-bucket**: ~500 lines.

## Bucket E — Ramification Jacobian Principality (1 sorry)

**File**: Ramification.lean:751
**Status**: Infrastructure mostly present.

### Infrastructure

**E-1. Cotangent space argument** for principality of `P.map f` given
the Jacobian identity + `d = π·e` factorization. ~150-200 lines.

**Total E-bucket**: ~200 lines.

## Bucket F — Frobenius Trace (1 sorry)

**File**: Frobenius.lean:130
**Status**: Cascades from Bucket B-3.

No standalone infrastructure — pure consequence of B + III.6 (which is A).

## Priority ordering (2026-04-18)

Short-term (this week):
1. **Bucket E** (Ramification Jacobian) — ~200 lines, localized
2. **Bucket B-3** (`addPullback_x ≠ const`) — ~100 lines

Medium-term:
3. **Bucket D** (Wronskian) — ~500 lines
4. **Bucket B-1, B-2** (transcendence) — ~350 lines

Long-term (multi-week):
5-9. **Bucket A** (dual isogeny chain) — ~2000 lines total

Parallel:
- **Bucket C** (formal isogeny bridge) — after curve uniformizers.

## This session's deliveries

✅ **Created** `HasseWeil/EC/IsogenyKernel.lean` — scaffold for Bucket A.
   No sorries; provides `Isogeny.kernel`, `mem_kernel_iff`,
   `zero_mem_kernel`, `kernel_id`, `kernel_comp_le`, `IsSeparable`.

✅ **Updated** tickets T-III-4-015, T-III-4-016, T-III-4-017 with
   detailed Silverman-based proof strategies.

✅ **Closed earlier in session** T-IV-3-001 (F(M) AddCommGroup) via
   `AddGroup.ofLeftAxioms` (commit b07ac2c).

## Next concrete work (in order of tractability)

1. Create `HasseWeil/EC/IsogenyFactor.lean` skeleton — API shape for
   A-2, A-3, A-4.
2. Attempt **Bucket E** (Ramification:751) directly.
3. Attempt **Bucket B-3** (`addPullback_x_ne_const`) directly.
