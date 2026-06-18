# T-PIC-AF-UNIFIED: line + Miller + reduction package (per reviewer Q2)

**Status**: PARTIAL (parity lemma + intermediate point_minus_O shipped)
**Module**: `HasseWeil/Curves/PoleOrderParity.lean` + extensions
**Owner**: —
**Estimated lines**: ~490 total (~70 shipped, ~420 remaining)
**Difficulty**: hard (geometric chord/tangent + algebraic reduction)
**Phase**: A/F (unified package)

## Background

Per reviewer's Q2 corrections, the broken `y - g(x)` factorization plan
in T-PIC-A-002c is replaced by:

1. `line_principal`: divisor of chord/tangent line through P, Q at L is
   `(P) + (Q) + (-(P+Q)) - 3·(O)`.
2. `vertical_principal`: divisor of vertical at P is
   `(P) + (-P) - 2·(O)` (DONE as `projectiveDivisorSum_vertical_line`).
3. `chord_principal` (Miller relation): `(P) + (Q) - (P+Q) - (O) ~ 0`,
   derived from (1) and (2).
4. `degree_zero_divisor_reduce`: For any `D ∈ Div⁰(E)`,
   `D ~ (σ(D)) - (O)` where `σ(D)` is the weighted sum of points.
5. `point_minus_O_principal_eq_zero`: If `(P) - (O)` is principal then
   `P = O`. Proved via pole-order parity (`ord_∞ ∈ {0, -2, -4, ...} ∪
   {-3, -5, -7, ...}`, never `-1`) plus the no-finite-poles → CR-image
   bridge.

From these, derive both witnesses for B-4-003:
- `principal_sum_zero` (h_van_W): if D is principal, σ(D) = 0.
  Proof: D principal ⟹ D ~ 0 ⟹ (σ(D)) - (O) ~ 0 by (4) ⟹ σ(D) = 0 by (5).
- `picZeroOfPoint_sigma_eq` (h_inj_W): the κ ∘ σ̄ = id direction.
  Proof: directly from (4), since D ~ (σ(D)) - (O) means same Pic⁰ class.

## Shipped

### `HasseWeil/Curves/EffectiveSumReduce.lean` (~165 LOC, axiom-clean)

The combinatorial core of the reduction, taking `MillerHypothesis` as
input parameter:

- **`MillerHypothesis W`**: predicate that `(P) + (Q) - (P+Q) - (O)` is
  principal for all `P, Q : W.Point`. The geometric witness function
  (chord/tangent line) is its own ticket — see piece (b) below.
- **`listToDivisor`**, **`listSum`**: helpers for converting a list of
  points to its effective divisor / group sum.
- **`projectiveDivisorSum_listToDivisor`**: `σ` on the list-divisor
  equals the list sum.
- **`effective_sum_reduce`**: for any nonempty list of points,
  `(P_1) + ... + (P_n) ~ (P_1 + ... + P_n) + (n - 1)·(O)`. By induction
  using Miller. Per reviewer Q2's cleaner formulation.

This is the **list-induction reduction** that's the combinatorial heart
of `degree_zero_divisor_reduce`.

### `HasseWeil/Curves/PoleOrderParity.lean` (axiom-clean, ~80 LOC):

- **`coordRingImage_ordAtInfty_ne_neg_one`**: for nonzero `u : C.CR`,
  `ord_∞(algMap u) ≠ -1`. Proved by basis decomposition `u = p • 1 + q • Y`
  + parity (even {-2k} from `p` part, odd {-2k-3} from `q` part).
  Cases: both nonzero (uses `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`),
  only p (`-2 deg p`), only q (`-2 deg q - 3`), both zero (contradicts hu).

- **`funcField_image_ordAtInfty_ne_neg_one`**: function-field version,
  immediate from above.

- **`point_minus_O_principal_eq_zero_of_coord`** (intermediate form):
  if `(P) - (O) = projectiveDivisorOf f` AND `f` is in CR image, then
  `P = 0`. Combines parity with the divisor identity at infinity.

## Outstanding

### (a) **No-finite-poles → CR-image bridge** (for unconditional point_minus_O)

To remove the `h_coord` hypothesis from `point_minus_O_principal_eq_zero_of_coord`,
need:

```lean
theorem mem_coordinateRing_of_no_finite_poles
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    [IsIntegrallyClosed C.CoordinateRing]
    (f : C.FunctionField)
    (h_no_poles : ∀ P : C.SmoothPoint, 0 ≤ C.ord_P P f) :
    ∃ u : C.CoordinateRing, algebraMap _ _ u = f
```

Composition path:
1. For each smooth point P, `ord_P f ≥ 0` ↔ `pointValuation_algebraMap f P ≤ 1`
   (existing in `Infinity.lean:1201`).
2. Each height-one prime v of `CR` corresponds to some `maximalIdealAt P`
   for a smooth point P (via `smoothPointEquivMaxIdeal`, worker-I's
   `NormValuation.lean`).
3. `pointValuation P` = `HeightOneSpectrum.intValuation` for the
   corresponding height-one prime (bridge needs to be packaged; pieces
   exist in `NormValuation.lean`).
4. Apply `mem_coordinateRing_of_valuation_le_one` (Infinity.lean:1374
   via IntegralClosure.lean).

Estimated ~80-150 LOC of bridge work. **Requires `[IsAlgClosed F]`** for the
SmoothPoint ↔ HeightOneSpectrum bijection.

### (b) **Miller / chord_principal relation** (geometric)

The big remaining piece. Construct the chord/tangent line through `P, Q`
on `E` as a specific function `ℓ_{P,Q} : F[x,y]/W = C.CR`, compute its
projective divisor:

```lean
theorem chord_line_projectiveDivisor (P Q : W.Point) (h : P ≠ -Q) :
    projectiveDivisorOf (chord_line P Q) =
      single P.toProj 1 + single Q.toProj 1 +
      single (-(P + Q)).toProj 1 -
      (3 : ℤ) • single ProjectiveSmoothPoint.infinity 1
```

Then:
```lean
theorem chord_principal (P Q : W.Point) :
    single P.toProj 1 + single Q.toProj 1 -
      single (P + Q).toProj 1 - single ∞ 1 ∈ projPrincipalSubgroup
```

derived by subtracting the vertical-line at P+Q from the chord identity.

Internal cases for Miller proof (per reviewer Q2):
- `P = 0`: trivial reduction.
- `Q = 0`: trivial.
- `Q = -P` (vertical line): use vertical_principal directly.
- `P = Q` (tangent line): tangent through P touches at P (multiplicity 2)
  and crosses at -2P; gives `2(P) + (-2P) - 3(O)`. Subtract vertical at
  2P → `2(P) - (2P) - (O) ~ 0`.
- General chord: line through P, Q crosses E at -(P+Q); gives
  `(P) + (Q) + (-(P+Q)) - 3(O)`. Subtract vertical at P+Q.

Each case requires constructing the line as a polynomial and verifying
the divisor.

**Estimated 200-300 LOC**. The most substantial single piece in this
package. Mathlib's `WeierstrassCurve.Affine.Point.add` definition uses
the slope/intercept formulas; can leverage to define the chord as a
polynomial. The divisor computation requires identifying the
intersection points and their multiplicities.

### (c) **degree_zero_divisor_reduce** (combinatorial induction)

Per reviewer Q2's cleaner formulation:
1. List induction on effective divisors:
   `(P_1) + ... + (P_n) ~ (P_1+...+P_n) + (n-1)(O)` using miller_principal.
2. Decompose `D ∈ Div⁰` as `D⁺ - D⁻` with `deg D⁺ = deg D⁻`.
3. Reduce both halves via the list induction.
4. Subtract: `D ~ (σ D⁺) - (σ D⁻) + 0·(O) = (σ D) - (O) + (O - O)`.
5. Use derived `(R) - (S) ~ (R - S) - (O)` from miller_principal.

**Estimated ~120 LOC** of Finsupp/list bookkeeping.

### (d) **Final h_van and h_inj assembly**

After (a), (b), (c) land:

```lean
theorem principal_sum_zero {D : ProjectiveDivisor} (hD : D ∈ projPrincipalSubgroup) :
    projectiveDivisorSum W D = 0
theorem picZeroOfPoint_sigma_eq (D : PicProj₀ ⟨W⟩) :
    picZeroOfPoint W (picZeroSumOfWitness W h_van D) = D
```

Both ~30 LOC each, mechanical from the above.

## Total estimate

| Piece | LOC | Status |
|---|---|---|
| Parity lemma | ~80 | DONE |
| Function-field parity | ~10 | DONE |
| Intermediate point_minus_O | ~60 | DONE |
| MillerHypothesis predicate | ~10 | DONE |
| List-divisor + listSum + σ-list | ~30 | DONE |
| `effective_sum_reduce` (combinatorial core) | ~120 | DONE |
| **`vertical_principal_of_miller`** | ~30 | DONE |
| **`sub_principal_of_miller`** | ~50 | DONE |
| **`NoFinitePolesBridge` predicate** | ~10 | DONE |
| **`pointMinusO_of_bridge`** (conditional) | ~50 | DONE |
| **`DivZeroReduce` predicate** | ~10 | DONE |
| **`PointMinusOPrincipalEqZero` predicate** | ~10 | DONE |
| **`h_inj_of_divZeroReduce`** | ~25 | DONE |
| **`h_van_degZero_of_divZeroReduce_and_pointMinusO`** | ~35 | DONE |
| **`AFInputs` struct + derivations** | ~50 | DONE |
| **`single_diff_kappa_reduce_of_miller`** | ~20 | DONE |
| **`PrincipalImpliesDegZero` predicate** | ~10 | DONE |
| **`AFInputs.h_van` (full)** | ~15 | DONE |
| **`AddHomProperty_of_AFInputs` (final B-4-003 wrapper)** | ~25 | DONE |
| Finsupp ↔ List bridge (multiplicities) | ~50 | OUTSTANDING |
| `DivZeroReduce` PROOF (full Div⁰ via decomposition) | ~80 | OUTSTANDING |
| No-finite-poles → CR bridge PROOF | ~80-150 | OUTSTANDING |
| Miller geometric construction (the big piece) | ~200-300 | OUTSTANDING |
| **Total** | **~990-1160** | **~580 done (~55%)** |

## Key reviewer guidance reflected

- Parity argument structure (Q3) — IMPLEMENTED CORRECTLY (basis
  decomposition, never -1).
- Polynomial-only `f = a(x) + b(x)y` (not rational, per Q3 correction)
  — captured in the no-finite-poles bridge step (a).
- Single uniform `miller_principal` with internal case-split (Q2) —
  noted in (b).
- List-induction reduction (Q2 cleaner formulation) — captured in (c).
- Worker-K's T-III-3-003 NOT needed — package gives both witnesses
  without it.
