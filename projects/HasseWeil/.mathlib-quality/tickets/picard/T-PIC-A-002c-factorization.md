# T-PIC-A-002c: Factorization of K(E)* into lines, verticals, units

**Status**: DONE-VIA-PARENT (T-PIC-A-002's
`projectiveDivisorSum_eq_zero_of_principal` shipped without needing the
explicit K(E)* factorization — `afInputs_unconditional` proves the
generic σ-vanishing directly via Miller + DivZeroReduce.
Chord/vertical specializations shipped as
`projectiveDivisorSum_chord_line` /
`projectiveDivisorSum_vertical_line_of_principal` in Miller.lean.)
**Silverman**: III.1.3 (K(E) = K(x)[y] / (W) is a quadratic extension)
**Module**: `HasseWeil/Curves/PicZero.lean` (extension)
**Owner**: —
**Estimated lines**: ~200
**Difficulty**: medium
**Phase**: A (sub-piece for unconditional A-002)

## Depends on

- T-III-3-002 (DONE per project state) — `[K(E):K(x)] = 2`
- T-PIC-A-002a (general line case)
- T-PIC-A-002b (vertical line case, DONE)
- Mathlib: `RatFunc F = F(x)`, `Polynomial.factorization`

## Blocks

- T-PIC-A-002d (final assembly)

## Statement

Every `f ∈ K(E)*` is a product (in K(E)*) of:
- units of `F̄*` (constants),
- vertical-line forms `x - α` for `α ∈ F`,
- line forms `y - g(x)` for `g ∈ F(x)`.

Formal statement:

```lean
theorem functionField_multiplicative_decomp
    [IsAlgClosed F]
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0) :
    ∃ (c : F) (xs : Multiset F) (gs : Multiset (RatFunc F)) (es : ℤ),
      f = (algebraMap F _ c) *
          (xs.prod fun α => (xCoordForm W α : FunctionField W)) *
          (gs.prod fun g => (lineForm W g : FunctionField W))
```

(Schematic — exact form depends on `xCoordForm`/`lineForm` definitions.)

## Mathlib check

Not in mathlib in this curve-specific form. The underlying algebra:
- `K(E) = K(x)[y]/(W(x,y))` with W monic of degree 2 in y over K(x).
- So `K(E) = K(x) ⊕ y · K(x)` as K(x)-vector space.
- Hence `f = a(x) + b(x) · y` for `a, b ∈ K(x) = F(x)`.
- If `b = 0`: `f = a(x)` factors via `RatFunc F` (= `F(x)`) into linear
  factors `x - αᵢ`-style and a unit.
- If `b ≠ 0`: `f = b(x) · (y + a(x)/b(x))` — product of (i) `b(x) ∈ F(x)`
  (vertical case via factorization) and (ii) `y - g(x)` for
  `g = -a(x)/b(x) ∈ F(x)` (line case).

## Naming

`functionField_multiplicative_decomp` or
`exists_lineForm_factorization`.

## Generality

`[W.IsElliptic]`. **`[IsAlgClosed F]`** required so that every `a(x) ∈
F(x)` factors fully into linear pieces (no irreducible quadratics).

## Proof approach

Three steps:

### Step 1: Reduce f to "a + by" form

```lean
∃ a b : RatFunc F, f = (algebraMap (RatFunc F) FunctionField a) +
                       (algebraMap (RatFunc F) FunctionField b) *
                       (yCoord : FunctionField)
```

This is **pure algebra**: K(E) is a free K(x)-module of rank 2 with basis
`{1, y}`. Already used implicitly in the project's
`FiniteOverKx.lean`. ~50 LOC.

### Step 2: Case split on `b = 0`

- `b = 0`: `f = a(x) ∈ K(x) ⊆ K(E)`. Apply `RatFunc.factorization` to
  decompose `a` into a unit times linear factors `(x - αᵢ)^eᵢ`. Each
  `(x - αᵢ)` is `xCoordForm`. ~60 LOC.

- `b ≠ 0`: `f = b · (y + a/b) = b · (y - g)` with `g = -a/b ∈ F(x)`.
  Recurse on `b ∈ K(x)*` (case b = 0 above), and the `(y - g)` factor is
  one application of `lineForm`. ~80 LOC.

### Step 3: Bookkeeping

Multiset bookkeeping for the constants and the line-forms collected.
~20 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.functionField_multiplicative_decomp
```
reports only standard axioms.

## Risks

- **`RatFunc F` factorization**: mathlib has `RatFunc.num_div_denom` and
  related, but explicit "factor into linear pieces" may need to be built
  via `Polynomial.factor_eq_prod_of_isAlgClosed`. ~30 LOC of bridging.

- **`yCoord ∈ FunctionField`** as a concrete element needs a definition.
  Probably already exists as `Mathlib.AlgebraicGeometry.EllipticCurve...`
  or in our `Curves/CurveMap.lean`.

- **Quadratic-extension representation** (`f = a + by`): needs
  `[K(E):K(x)] = 2` (T-III-3-002) and an explicit basis. Should plug into
  existing `FiniteOverKx.lean` machinery.

## Progress log
