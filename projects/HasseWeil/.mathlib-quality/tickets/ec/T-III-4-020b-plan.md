# T-III-4-020b: Division polynomial composition formula — Plan

**Parent ticket**: T-III-4-020 (`mulByInt_comp_eq_mul`)
**Status**: OPEN (plan created; some sub-tickets feasible in session, others multi-session)
**Owner**: worker-J
**Estimated total scope**: 300-500 lines across ~6 sub-tickets

## Goal

Prove:
```
(mulByInt W.toAffine m).pullback.comp (mulByInt W.toAffine n).pullback =
(mulByInt W.toAffine (m * n)).pullback
```
as `K(E) →ₐ[F] K(E)`, for `m, n ∈ ℤ` with `m, n, m·n ≠ 0`.

Via `mulByInt_pullback_unique`, this reduces to showing the composition sends
the generic coordinates to the `[m·n]`-images:
- **X-coord**: `(mulByInt W n).pullback (mulByInt_x W m) = mulByInt_x W (m*n)`
- **Y-coord**: `(mulByInt W n).pullback (mulByInt_y W m) = mulByInt_y W (m*n)`

## Strategy: universal-setting lift + specialization

**Key discovery**: `HasseWeil/Auxiliary/DivisionPolynomial.lean` has the
universal group-law machinery already:
- `zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧`
- `dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n)`
- `addXYZ_smulField : addXYZ ... = ψ(n-m) • smulField (n + m)`

These connect the universal generic point `Jacobian.point` (over `Universal.Ring`)
to the division-polynomial 3-tuples `smulField n`. The group-law identity
`(m*n) • P = m • (n • P)` is automatic on `Point _`, so at the universal level
we should get composition "for free" via coordinate extraction.

Our target `mulByInt_x W m` (in `K(E)` for a specific `W`) is the
base-change/specialization of the universal x-coordinate `smulField n` to `W`.
So the overall path is:

1. **Prove composition in the universal setting** (`smulField m` composed with
   `smulField n` = `smulField (m*n)` up to scaling).
2. **Specialize to our `W`** via base change from `Universal.Ring` to `F`.
3. **Descend to `K(E)`** via the fraction-ring machinery in
   `MulByIntPullback.lean`.

## Sub-ticket decomposition

### T-III-4-020b-1 [FEASIBLE, ~80 lines]: Universal generic point

Define `genericPointInFunctionField : E(K(E))` for our curve W — the generic
point `(x_gen, y_gen)` with its nonsingularity + Weierstrass equation. This
gives us a concrete `Affine.Point` instance in our setting that parallels
`Universal.Jacobian.point`.

**Dependencies**: `HasseWeil/OmegaPullbackCoeff.lean` (`generic_equation`,
`generic_nonsingular` already exist).

**Deliverable**: `genericPoint : W.toAffine.Point` over `K(E)`.

### T-III-4-020b-2 [FEASIBLE, ~60 lines]: mulByInt_x = x(n • genericPoint)

Prove that for `n ≠ 0`,
`mulByInt_x W n = Affine.Point.xOf (n • genericPoint)`
(i.e., `mulByInt_x` is the x-coordinate of the n-th multiple of the generic
point in the group law). This connects our rational-function-based
`mulByInt_x` to the group-structure-based x-coordinate.

**Approach**: Reduce via the universal specialization — mathlib/Auxiliary has
`Affine.zsmul_point_eq_smulX_smulY` which gives the universal form. Base-change
to W.

**Dependencies**: T-III-4-020b-1.

### T-III-4-020b-3 [FEASIBLE, ~40 lines]: Y-coord version of the above

Prove `mulByInt_y W n = Affine.Point.yOf (n • genericPoint)` (up to sign /
Weierstrass negation adjustment).

**Dependencies**: T-III-4-020b-2.

### T-III-4-020b-4 [MEDIUM, ~80 lines]: Pullback interpretation of x(m • Q)

Prove that for an isogeny `φ : E → E` with `φ.pullback (x_gen) = x_Q` (i.e.,
`Q = φ(genericPoint)` has x-coord `x_Q`), we have
`φ.pullback (mulByInt_x W m) = Affine.Point.xOf (m • Q)`.

**Approach**: This is the composition-at-function-field-level statement.
Combining T-III-4-020b-2 + pullback functoriality + the generic point reindexing.

**Dependencies**: T-III-4-020b-2.

### T-III-4-020b-5 [EASY given 1-4, ~20 lines]: X-coord composition identity

Conclude: `(mulByInt W n).pullback (mulByInt_x W m) = mulByInt_x W (m * n)` via
```
LHS = x(m • Q)                               [T-III-4-020b-4 with φ = [n], Q = n•P_gen]
    = x(m • (n • P_gen))                     [T-III-4-020b-2]
    = x((m*n) • P_gen)                       [mul_zsmul, group associativity — FREE]
    = mulByInt_x W (m*n)                     [T-III-4-020b-2]
```

**Dependencies**: T-III-4-020b-2, T-III-4-020b-4.

### T-III-4-020b-6 [EASY given 3-5, ~30 lines]: Y-coord composition identity

Same pattern with Y.

**Dependencies**: T-III-4-020b-3, T-III-4-020b-4 (y-coord version).

### T-III-4-020b-7 [TRIVIAL given 5-6, ~10 lines]: Isogeny-level `mulByInt_comp_eq_mul`

Package the two coordinate identities via `mulByInt_comp_eq_mul_of_generator_witness`.

**Dependencies**: T-III-4-020b-5, T-III-4-020b-6.

## Critical path

```
1 → 2 → 5
    ↓
    3 → 6
    ↓
    4 → 5,6 → 7
```

## Feasibility assessment

* T-III-4-020b-1: Constructing `genericPoint` — feasible; the Weierstrass
  equation + nonsingularity proofs already exist in `OmegaPullbackCoeff.lean`.
* T-III-4-020b-2: The hard one — requires connecting our `mulByInt_x` definition
  (which uses `W.Φ`, `W.ΨSq`) to the Affine.Point group-law x-coordinate. The
  universal setting does this for `Universal.curve`; we need the specialization
  argument. Non-trivial but tractable.
* T-III-4-020b-3 to -7: Routine given -1 and -2.

**Realistic session-bound scope**: T-III-4-020b-1 is achievable in session.
T-III-4-020b-2 may or may not be — depends on how much base-change plumbing is
already in place vs needs building. -3 through -7 are mostly mechanical once
-1 and -2 land.

## What's NOT in scope for this plan

* Direct polynomial-induction proof of the composition identity (the alternate
  strategy) — not taken here because the universal-setting approach is cleaner.
* Full generalization to `Hom(E₁, E₂)` composition — only endomorphism case
  (`Isogeny W W`) is targeted.
