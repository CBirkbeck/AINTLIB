# T-PIC-F-001: `κ ∘ σ̄ = id` (the σ̄-injectivity direction)

**Status**: BLOCKED on T-III-3-003 (worker-K)
**Silverman**: III.3.4(c) (σ injective)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy after T-III-3-003
**Phase**: F

## Depends on
- T-III-3-003 ((P) ~ (Q) ⇒ P = Q) — CHECKED-OUT by worker-K
- T-PIC-A-003 (`picZeroSum`)
- T-PIC-B-001 (`picZeroOfPoint`)
- T-PIC-B-003 (the other direction `σ̄ ∘ κ = id`)

## Blocks
- T-PIC-F-002 (packaging as MulEquiv)
- T-PIC-F-003 (final B-4-003 closure)

## Statement

```lean
@[simp] theorem picZeroOfPoint_picZeroSum
    (D : PicProj₀ (⟨W⟩ : Curves.SmoothPlaneCurve F)) :
    picZeroOfPoint W (picZeroSum W D) = D
```

This is the second direction of the bijection. Combined with T-PIC-B-003,
it makes `picZeroSum` and `picZeroOfPoint` mutually inverse.

## Mathlib check
N/A.

## Naming
`picZeroOfPoint_picZeroSum`.

## Generality
Probably needs `[IsAlgClosed F]` (because T-III-3-003 does).

## Proof approach

Reduce via `Quot.ind` to show that for any `D : Div⁰`,
`picZeroOfPoint W (projectiveDivisorSum W D) ~ D` (linear equivalence).

For this:
- Let `σ(D) = P`. We want `(P) - (O) ~ D` in Div⁰.
- Equivalently, `(P) - (O) - D` is principal.
- T-III-3-003 gives the **uniqueness** of `P ∈ E` such that `D ~ (P) - (O)`.
- The **existence** part of III.3.4(a): for any `D ∈ Div⁰(E)` there is a
  unique `P ∈ E` with `D ~ (P) - (O)`.
- Existence: use Silverman's argument with Riemann-Roch (genus 1: `dim L(D + (O)) = 1`)
  — but we explicitly **avoid** Riemann-Roch in this project.
- **Alternative existence**: by induction on number of points in support of D,
  use the geometric group law to combine adjacent contributions. Each
  `(P_i)` reduces to `(σ(P_i)) - (O) + (some principal)`. After all
  reductions, get `(P) - (O)` with `P = σ(D)`.

The "alternative existence" approach avoids R-R but does ~50 lines of
group-law manipulation. With T-III-3-003 in hand, the uniqueness then
gives that `P = σ(D)` is the right choice.

## Acceptance criteria

`#print axioms HasseWeil.Curves.picZeroOfPoint_picZeroSum` reports only
standard axioms (modulo whatever T-III-3-003 reports).

## Progress log
