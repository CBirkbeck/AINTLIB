# T-II-3-008: div(f) = 0 ⇔ f ∈ K̄*

**Status**: PARTIAL (worker-I, 2026-04-21) — (⇐) direction delivered axiom-clean;
(⇒) delivered in **prime-indexed form** via IC-006:
`const_of_valuation_le_one_of_ordAtInfty_nonneg` in `Divisors.lean`.
The original SmoothPoint-indexed statement needs the surjection
SmoothPoint → HeightOneSpectrum under `[IsAlgClosed F]` (T-II-3-009).
**Silverman**: II.3.1(a)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: worker-I (partial)
**Estimated lines**: 30
**Difficulty**: easy (modulo II.1.4)
**Stream**: A

## Depends on
- T-II-1-004 (no zeros/poles ⇒ constant)
- T-II-3-005 (div(f))

## Blocks
- T-II-3-010 (exact sequence)
- T-III-5-001 (translation invariance proof)

## Statement (Silverman II.3.1(a))
For a smooth curve `C` and `f ∈ K̄(C)*`,

```
div(f) = 0  ⇔  f ∈ K̄*.
```

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- A nonzero rational function has trivial divisor iff it is constant.
    Reference: Silverman II.3.1(a). -/
theorem divisorOf_eq_zero_iff_const (C : SmoothPlaneCurve F) (f : C.FunctionField)
    (hf : f ≠ 0) :
    divisorOf C f = 0 ↔ ∃ c : F, f = algebraMap F C.FunctionField c

end HasseWeil.Curves
```

## Notes
- (⇐) constants have all ord = 0.
- (⇒) `div(f) = 0` means f has no zeros or poles. By T-II-1-004, f is constant.

## Progress log

- **2026-04-20** (worker-I): delivered the (⇐) direction in
  `HasseWeil/Curves/Divisors.lean`:
  - `ord_P_algebraMap_F_of_ne_zero : c ≠ 0 → ord_P P (algebraMap F F(C) c) = 0`.
    Proof: rewrite `algebraMap F F(C) c = algebraMap F[C] F(C) (algebraMap F F[C] c)`
    via the scalar tower; show the coordinate-ring image is not in
    `maximalIdealAt P` using `mem_maximalIdealAt_iff_eval_zero` with
    `p = C c`, `q = 0`; conclude via `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`.
  - `divisorOf_algebraMap_F : divisorOf (algebraMap F F(C) c) = 0`
    tagged `@[simp]`. Proof: `Finsupp.ext` + the ord_P lemma above (handling
    the `c = 0` edge case via `map_zero` + `divisorOf_zero`).
  Both axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
  The (⇒) direction is blocked on T-II-1-004 Part 2 (full F(C) version,
  requires `IsDedekindDomain C.CoordinateRing` + integral-closure argument).
