# T-PIC-A-002a: σ vanishes on `div(y - g(x))·E` (general line case)

**Status**: DONE (`projectiveDivisorSum_chord_line` in
`HasseWeil/Curves/Miller.lean`, axiom-clean — combines
`projectiveDivisorOf_coordY_sub_algMap_linePolynomial` and
`projectiveDivisorSum_eq_zero_of_principal`)
**Silverman**: III.2.3 (group law / chord-tangent), used in III.3.5 proof.
**Module**: `HasseWeil/Curves/PicZeroLineCase.lean` (NEW FILE)
**Owner**: —
**Estimated lines**: ~200
**Difficulty**: medium-hard
**Phase**: A (sub-piece for unconditional A-002)

## Depends on

- T-PIC-A-001 (DONE) — `projectiveDivisorSum` definition
- T-PIC-B-001 (DONE) — `kappaDivisor`
- Mathlib `WeierstrassCurve.Affine.Point.add`, `Affine.Point.add_some_some_of_*`
- `HasseWeil/EC/GroupLaw.lean` (existing) — collinearity ↔ sum-zero identity

## Blocks

- T-PIC-A-002c (factorization of K(E)*)
- T-PIC-A-002d (final assembly)
- T-PIC-F-001a (existence in κ ∘ σ̄ = id)

## Statement

For a "line form" `f = y - g(x)` with `g ∈ F(x)` such that the line
intersects `E` at three distinct (or coincident counted with multiplicity)
finite affine points `P, Q, R` with `P + Q + R = O`:

```lean
theorem projectiveDivisorSum_line_case
    (P Q R : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (h_collinear : (Affine.Point.toGroup P) + (Affine.Point.toGroup Q) +
                   (Affine.Point.toGroup R) = 0)
    (g : F(x))
    (h_div : projectiveDivisorOf (lineForm g) =
             single P 1 + single Q 1 + single R 1 - 3 • (single ∞ 1)) :
    projectiveDivisorSum W (projectiveDivisorOf (lineForm g)) = 0
```

(Stated schematically — exact formulation depends on how `lineForm` is
encoded.)

## Mathlib check

Not in mathlib. The chord-tangent group law is encoded in
`Mathlib.AlgebraicGeometry.EllipticCurve.Group` as `Point.add`, but the
DIVISOR-LEVEL identity (line ↔ sum-of-three-points) is not packaged.

## Naming

`projectiveDivisorSum_lineForm_zero_of_collinear` (snake_case).

## Generality

Same as T-PIC-A-001: `[W.IsElliptic]`. No `[IsAlgClosed F]` needed for
this sub-piece (all three intersection points are F-rational by
assumption — the algebraic-closure hypothesis enters when we
**existentially produce** the three points later).

## Proof approach

Two ingredients:

### (i) Divisor identity for `y - g(x)`

For a line form `L(x, y) = y - g(x)` (with `g ∈ F(x)`):

- The intersection `L = 0` ∩ `E` consists of three points (counted with
  multiplicity) in `P²`. Two of these are finite affine, one may be at
  infinity.
- The divisor `(L|_E)` on E (as a function in K(E)) has zeros at the
  three intersection points and a pole of order 3 at the unique infinity
  point of E.
- The order at each affine point is the **intersection multiplicity**,
  which for a line transverse to E is 1.

Formal statement (one direction of the existing `divisorOf`):

```
projectiveDivisorOf (mk (Y - C (g.num) / C (g.denom))) =
    single P_inf 1 + single Q_inf 1 + single R_inf 1 - 3 • single ∞ 1
```

where `P_inf, Q_inf, R_inf` are the three lifts of the three line ∩ E
intersection points to `ProjectiveSmoothPoint`.

### (ii) Sum-of-collinear-points = O

This is **Silverman III.2.3** (geometric definition of the group law):
three points P, Q, R on E are collinear iff their sum in the group law
is O (counting with multiplicity for tangent / inflection cases).

Mathlib's `WeierstrassCurve.Affine.Point.add` is defined exactly this
way. Specifically:
- `add_some_some_of_X_ne` (or its successors) computes `P + Q` via the
  third intersection of the line through P, Q with E, then negates.
- The negation step gives: `R = -(P + Q)`, i.e., `P + Q + R = O`.

So if the line through P, Q passes through R, then by definition
`P + Q + R = O` as group elements.

### Combining (i) and (ii)

```lean
projectiveDivisorSum W (projectiveDivisorOf (lineForm g))
  = projectiveDivisorSum W (single P_inf 1 + single Q_inf 1 + single R_inf 1
                            - 3 • single ∞ 1)
  = (P + Q + R) - 3·O    -- by additive structure of σ + σ at single point
  = 0 - 0                 -- by collinearity, P + Q + R = 0
  = 0
```

## Implementation plan

1. **Define `lineForm`** in K(E): given `g ∈ F(x)`, produce
   `y - g(x) ∈ K(E)`. ~30 LOC.

2. **Compute `divisorOf (lineForm g)` at affine points**: zeros at
   `(x_i, g(x_i))` for `x_i` solutions of the cubic
   `g(x)² + a₁ x g(x) + a₃ g(x) - x³ - a₂ x² - a₄ x - a₆ = 0`. ~80 LOC.

3. **Bridge collinearity to group law**: show that the three solutions
   (P, Q, R) satisfy `P + Q + R = O` by **bouncing through the existing
   `Affine.Point.add` definition** (mathlib). ~50 LOC.

4. **Final assembly**: σ-additivity + collinearity ⇒ σ(div(line)) = 0.
   ~40 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.projectiveDivisorSum_lineForm_zero_of_collinear
```
reports only standard axioms. No new sorries.

## Risks

- The "third intersection point at infinity" sub-case (when the line is
  vertical or asymptotic) needs separate handling. Already covered by
  T-PIC-A-002b (vertical-line case). For non-vertical lines, the third
  intersection is finite.

- The bridge from "polynomial intersection" to "Point.add equation" may
  need 50-100 LOC of careful mathlib unfolding. The relevant mathlib
  lemma is `WeierstrassCurve.Affine.Point.some_add_some_of_X_ne` (or
  similar — needs verification).

- `EC/GroupLaw.lean` may already have collinearity ↔ sum-is-O at the
  generic-point level; reusing it could shave 50 LOC.

## Progress log
