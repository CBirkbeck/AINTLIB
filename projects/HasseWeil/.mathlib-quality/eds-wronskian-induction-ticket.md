# EDS Wronskian Induction Ticket — Mathlib-PR-Shape

**Sorry**: `HasseWeil/OmegaPullbackCoeff.lean:477` — `wronskian_Φ_ΨSq_nat` for `m = n + 5`.

## Goal

Discharge the strong-inductive case `m ≥ 5` of:
```lean
private lemma wronskian_Φ_ΨSq_nat (m : ℕ) :
    Polynomial.derivative (W.Φ (m : ℤ)) * W.ΨSq (m : ℤ) -
      W.Φ (m : ℤ) * Polynomial.derivative (W.ΨSq (m : ℤ)) =
    Polynomial.C ((m : ℤ) : F) * W.preΨ (2 * (m : ℤ))
```

Reference: Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7.

## Existing infrastructure (axiom-clean)

* `wronskian_Φ_ΨSq_zero/one/two/three/four` (m = 0..4): direct computations + ring identities (`wronskian_aux_three`, `wronskian_aux_four`) in `HasseWeil/WronskianAux.lean`.
* `wronskian_X_mul_sub`: structural identity used in the m=4 case.
* `WeierstrassCurve.preΨ_even`, `preΨ_odd`: mathlib EDS recurrences.

## Proof sketch (~400-600 LOC)

Strong induction on `m ≥ 5` using two case-splits (even/odd):

### Even case `m = 2k` for `k ≥ 3`

By `WeierstrassCurve.preΨ_even W k`:
```
preΨ(2k) = preΨ(k) · (preΨ(k+2)·preΨ(k-1)² - preΨ(k-2)·preΨ(k+1)²)
```

Express `Φ(2k)` and `ΨSq(2k)` via the doubling formulas (mathlib provides `Φ_two_mul`, `ΨSq_two_mul` or analogous). The Wronskian:
```
Φ'(2k)·ΨSq(2k) - Φ(2k)·ΨSq'(2k)
```
should expand via product rule into terms involving:
- `Φ'(k)·ΨSq(k) - Φ(k)·ΨSq'(k)` (= induction hypothesis at `k`)
- `Φ(k+1)·ΨSq(k-1)` cross terms (Wronskian identity at smaller indices)

The identity `(2k) · preΨ(2·2k) = (2k) · preΨ(4k)` then matches via `preΨ_even W (2k)` recursively.

### Odd case `m = 2k+1` for `k ≥ 2`

By `WeierstrassCurve.preΨ_odd W k`:
```
preΨ(2k+1) = preΨ(k+2)·preΨ(k)³ - preΨ(k-1)·preΨ(k+1)³
```

Same structure as the even case but with the odd recurrence.

## Substantive content

Each case requires:
1. Symbolic expansion of `Φ`, `ΨSq` at `m` via mathlib's doubling/recurrence formulas.
2. Distribution of `Polynomial.derivative` via product rule (~5-10 applications).
3. Reduction to Wronskian identities at `k`, `k-1`, `k+1`, `k+2` (= induction hypotheses).
4. Cross-term cancellation via auxiliary ring identities (analog of `wronskian_aux_three` / `_four` but for general `k`).

Each case is approximately the size of `wronskian_aux_four` (~57 GB ring elaboration before optimization). The induction structure adds another factor.

## Mathlib-PR shape

This belongs in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` as:

```lean
/-- Silverman III.3.7 — the EDS Wronskian identity. -/
theorem WeierstrassCurve.wronskian_Φ_ΨSq (W : WeierstrassCurve F) [Field F] [DecidableEq F]
    [W.toAffine.IsElliptic] (n : ℤ) :
    Polynomial.derivative (W.Φ n) * W.ΨSq n - W.Φ n * Polynomial.derivative (W.ΨSq n) =
    Polynomial.C (n : F) * W.preΨ (2 * n)
```

Two-step PR plan:

1. **Auxiliary ring identities** (`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Wronskian`):
   - `wronskian_aux_even_step_recurrence` (general k version of `wronskian_aux_four`).
   - `wronskian_aux_odd_step_recurrence` (analog for odd).
   - These will be the heaviest computations (~50K maxHeartbeats each).

2. **Strong induction theorem** (~80 LOC):
   - Open the strong induction.
   - Even case via `preΨ_even` + auxiliary even identity.
   - Odd case via `preΨ_odd` + auxiliary odd identity.

## Estimated effort

- **PR sketch authoring**: 3-5 sessions (sympy verification + careful ring identities).
- **Lean implementation**: 5-10 sessions (heartbeats tuning, simp normalization).
- **Mathlib review cycle**: 2-4 weeks.

## Alternative routes (mathlib-internal)

If a Wronskian identity for elliptic divisibility sequences exists in mathlib indirectly (e.g., via `EllipticDivisibilitySequence`), it could be used. As of this writing, no such direct identity is in mathlib master.

This ticket itself does not discharge the sorry. It documents the substantive content and PR plan. The current axiom-clean per-prime infrastructure (Worker C's verschiebungIsog + IsDualOf certificates, Path A Kähler chain, etc.) bypasses this Wronskian sorry by using a different witness chain (the `omegaPullbackCoeff_eq_formalIsogenyLeading_id` + `_negFrobeniusIsog` axiom-clean path), so closing this sorry is not on the critical Hasse-Weil bound path.
