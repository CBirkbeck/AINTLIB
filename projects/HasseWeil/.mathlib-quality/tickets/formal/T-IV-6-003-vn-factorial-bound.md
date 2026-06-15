# T-IV-6-003: v(n!) ≤ (n−1) v(p) / (p−1)

**Status**: REVIEW
**Silverman**: IV.6.2
**Module**: `HasseWeil/FormalGroup/PadicValFactorial.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: D

## Depends on
- (basic valuation facts)

## Blocks
- T-IV-6-004 (convergence)
- T-IV-6-005 (log iso for large M^r)

## Statement (Silverman IV.6.2)
Let `K` be a field with discrete valuation `v` and uniformizer `π`. Suppose
`v(p) = e` (for residue characteristic `p`). Then for any `n ≥ 1`,
`v(n!) ≤ (n − 1) e / (p − 1)`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

theorem padicValNat_factorial_bound (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ (n - 1 : ℝ) / (p - 1)

end HasseWeil.FormalGroup
```

## Notes
- This is a Legendre/Kummer-style estimate. Sometimes given as
  `v_p(n!) = (n - s_p(n))/(p - 1)` where `s_p` is sum of digits.
- The exact form Silverman uses may need adjustment.

## Progress log

- 2026-04-17: Proved. Implemented in `HasseWeil/FormalGroup/PadicValFactorial.lean`.
  - `padicValNat_factorial_le` — matches the exact ticket statement (with the
    mild and necessary hypothesis `1 ≤ n`, since at `n = 0` the right-hand
    side `(0 - 1 : ℝ)/(p - 1) = -1/(p-1)` is negative while the valuation
    is `0`; Silverman states the bound for `n ≥ 1`).
  - `padicValNat_factorial_div_le` — a hypothesis-free corollary giving
    the (slightly looser) bound `v_p(n!) ≤ n/(p-1)`, valid for all `n ≥ 0`.
  - Built on the mathlib lemma
    `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`
    (in `Mathlib.NumberTheory.Padics.PadicVal.Basic`), which provides the
    strict inequality `(p - 1) * v_p(n!) < n` for `n ≠ 0`. From this the
    `≤ (n - 1)/(p - 1)` bound in ℝ is immediate after a ℕ → ℝ cast and
    division by the positive real `p - 1`.
  - Also imported into `HasseWeil.lean`.
  - Axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
  - No sorry. `lake build HasseWeil.FormalGroup.PadicValFactorial` passes.
