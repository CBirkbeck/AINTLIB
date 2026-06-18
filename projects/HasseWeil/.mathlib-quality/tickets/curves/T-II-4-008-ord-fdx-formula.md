# T-II-4-008: Order formula for f·dx (char 0 vs char p)

**Status**: OPEN
**Silverman**: II.4.3(d)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 70
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-4-007 (ord_P well-defined)
- T-II-1-002 (ord_P)

## Blocks
- T-II-4-009 (almost all ord = 0)
- T-III-1-009 (div(ω) = 0 for invariant differential)

## Statement (Silverman II.4.3(d))
Let `x ∈ K(C)` and `P ∈ C` with `t` a uniformizer at `P`. Let
`e = ord_P(x − x(P))` if `P` is in the affine patch (else `e = ord_P x`).
Then for `f ∈ K(C)`,
- If `char(K) = 0` or `char(K) = p ∤ e`:
  `ord_P(f · dx) = ord_P(f) + e − 1`.
- If `char(K) = p` and `p | e`:
  `ord_P(f · dx) ≥ ord_P(f) + e`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- Order formula for f·dx in characteristic 0 or coprime to e.
    Reference: Silverman II.4.3(d) case 1. -/
theorem Differentials.ord_fdx_coprime (C : SmoothPlaneCurve F) (P : C)
    (x f : C.FunctionField) (e : ℕ) (he : e = (C.ord P (x - constAt P x)).toNat)
    (h : ringChar F = 0 ∨ ¬ ringChar F ∣ e) :
    Differentials.ord C P (f • Differentials.d x) =
      C.ord P f + (e : ℤ) - 1

/-- Order inequality for f·dx in the wild case.
    Reference: Silverman II.4.3(d) case 2. -/
theorem Differentials.ord_fdx_wild (C : SmoothPlaneCurve F) (P : C)
    (x f : C.FunctionField) (e : ℕ) (he : e = (C.ord P (x - constAt P x)).toNat)
    (p : ℕ) (hp : ringChar F = p) (hpe : p ∣ e) :
    C.ord P f + (e : ℤ) ≤ Differentials.ord C P (f • Differentials.d x)

end HasseWeil.Curves
```

## Notes
- This is the key formula used in proving div(ω) = 0 for the invariant
  differential of an elliptic curve (T-III-1-009).
- Proof: write x − x(P) = t^e · u where u is a unit at P. Then dx = (e·t^{e-1}·u
  + t^e · du/dt) dt = t^{e-1}(e·u + t·du/dt) dt. In char 0 or p ∤ e the second
  factor is a unit; in the wild case it can have higher order.

## Progress log
