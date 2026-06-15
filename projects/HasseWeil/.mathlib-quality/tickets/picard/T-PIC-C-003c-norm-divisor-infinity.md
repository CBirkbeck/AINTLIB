# T-PIC-C-003c: Norm-divisor identity at the infinity point

**Status**: OPEN
**Silverman**: II.3.6 (infinity-case)
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: medium
**Phase**: C (sub-piece for unconditional C-003)

## Depends on

- T-PIC-C-003b (affine case)
- Existing `Curves/Infinity.lean` — `ordAtInfty`, `ordAtInfty_intDegree`
- Mathlib: `RatFunc.intDegree_norm` (or equivalent)

## Blocks

- T-PIC-C-003d (assembly)

## Statement

The infinity component of the pushforward divisor matches the infinity
order of the norm:

```lean
theorem pushforward_div_eq_div_norm_at_infinity
    [IsAlgClosed F]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (g : (⟨W₁⟩).FunctionField) (hg : g ≠ 0) :
    -- The multiplicity of ∞ in `pushforwardProjectiveDivisor (div g)`
    -- equals the order of `N(g)` at ∞ in W₂.
    (pushforwardProjectiveDivisor φ cd
      ((⟨W₁⟩).projectiveDivisorOf g)) ProjectiveSmoothPoint.infinity =
      (⟨W₂⟩).ordAtInfty (φ.toCurveMap.pushforward g)
```

## Mathematical content

For `g ∈ K(E₁)*`:
- `ordAtInfty(g) = -intDegree(g)` (existing project result, `Infinity.lean`).
- `intDegree(N(g)) = (deg φ) · intDegree(g)` (mathlib + standard
  algebra-norm property).
- Wait — that's not quite right. The correct identity uses the fiber
  over ∞ in W₂:
  `ordAtInfty_W₂(N(g)) = Σ_{q ↦ ∞_W₂} ramId(q/∞) · ord_q(g)`.

Under `[IsAlgClosed F]`, the residue degree `f(q/∞) = 1` (analogue of
worker-I's affine-point `inertiaDeg = 1`). So:

`ordAtInfty_W₂(N(g)) = Σ_{q ↦ ∞_W₂} ord_q(g) = (φ_*(div g))(∞_W₂)`.

## Naming

`pushforward_div_eq_div_norm_at_infinity`.

## Generality

`[IsAlgClosed F]`. The infinity point on a Weierstrass curve is always
F-rational (it's the point `[0:1:0]`), so no additional hypothesis on
that side.

## Proof approach

Two paths:

### Path A: Direct via `intDegree`
1. Compute `ordAtInfty(N(g))` via `intDegree(N(g))`.
2. Use `Algebra.norm` properties to relate `intDegree(N(g))` to
   `intDegree(g)` and `[K(E₁) : K(E₂)]`.
3. Express the result as a sum over the fiber.

### Path B: Mirror the affine proof
1. Treat ∞ as a height-one prime of the "global" coordinate ring
   (works after passing to the projective coordinate ring).
2. Apply the same `relNorm` factorization as in C-003b.

**Path A** is simpler given `Infinity.lean` already has the
`ordAtInfty ↔ intDegree` bridge. Estimated 50 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.Isogeny.pushforward_div_eq_div_norm_at_infinity
```
reports only standard axioms.

## Risks

- The relation between `intDegree(N(g))` and the fiber sum at ∞ is
  standard but may need bridging through worker-I's fiber-bijection
  lemmas adapted to the infinity point.

- Worker-I's machinery is built around finite affine smooth points.
  Extension to infinity may require ~20 extra LOC of careful re-coding.

## Progress log
