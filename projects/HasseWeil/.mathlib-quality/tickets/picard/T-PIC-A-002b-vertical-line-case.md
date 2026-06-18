# T-PIC-A-002b: σ vanishes on `div(x - α)·E` (vertical-line case)

**Status**: DONE
**Silverman**: III.3.5 (special case for vertical lines)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: session
**Estimated lines**: ~80 (delivered)
**Difficulty**: easy
**Phase**: A (sub-piece for unconditional A-002)

## Depends on

- T-PIC-A-001 (DONE) — `projectiveDivisorSum`
- T-II-3-005 (DONE) — `projectiveDivisorOf`

## Blocks

- T-PIC-A-002c (factorization of K(E)*)

## Statement (delivered)

For `α ∈ F` such that the vertical line `x = α` meets E at the inverse
pair `(α, β), (α, -β-...)`:

```lean
theorem projectiveDivisorSum_vertical_line
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (h : ∀ Q : ..., Q.x = P.x → Q = P ∨ Q = -P)
    : projectiveDivisorSum W
        (projectiveDivisorOf (xForm (P.x))) = 0
```

(See `HasseWeil/Curves/PicZero.lean:projectiveDivisorSum_vertical_line`
for the actually-delivered formulation.)

## Mathematical content

The divisor of `x - α`:
- has zeros of order 1 at `(α, β)` and `(α, -β-a₁α-a₃)` (the two affine
  points with x-coord α);
- has a pole of order 2 at the unique infinity point.

So `projectiveDivisor(x - α) = (P) + (-P) - 2·(O)`.

Sum: `P + (-P) - 2·O = 0` in E. Done.

## Generality

`[W.IsElliptic]`. No `[IsAlgClosed F]` needed (we assume the two roots
are F-rational; that's automatic when supplying P explicitly).

## Acceptance criteria

`#print axioms HasseWeil.Curves.projectiveDivisorSum_vertical_line` reports
only standard axioms. **DONE** in PicZero.lean.

## Progress log

- **2026-04-29**: Delivered as `projectiveDivisorSum_vertical_line` and
  multiplicativity helpers `projectiveDivisorSum_projectiveDivisorOf_mul`,
  `_one`, `_inv` (PicZero.lean lines ~200-280, axiom-clean).
