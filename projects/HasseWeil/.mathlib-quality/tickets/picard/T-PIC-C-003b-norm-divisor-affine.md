# T-PIC-C-003b: Norm-divisor identity at affine points

**Status**: OPEN
**Silverman**: II.3.6, II.3.7
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~150
**Difficulty**: hard (the technical core of C-003)
**Phase**: C (sub-piece for unconditional C-003)

## Depends on

- T-PIC-C-003a (ord ↔ multiplicity bridge)
- Worker-I's `Curves/NormValuation.lean` (READ-ONLY)
- Mathlib: `Ideal.relNorm`, `Ideal.relNorm_singleton`,
  `Ideal.relNorm_eq_pow_of_isMaximal`,
  `UniqueFactorizationMonoid.normalizedFactors_prod`

## Blocks

- T-PIC-C-003c (infinity case)
- T-PIC-C-003d (assembly)

## Statement

For an isogeny `φ : E₁ → E₂` with coordinate witness `cd`, and
`g ∈ K(E₁)*`, the affine-point part of the divisor identity:

```lean
theorem pushforward_div_eq_div_norm_at_affine
    [IsAlgClosed F]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (g : (⟨W₁⟩).FunctionField) (hg : g ≠ 0)
    (Q : (⟨W₂⟩).SmoothPoint) :
    -- The multiplicity of Q in `pushforwardProjectiveDivisor (div g)`
    -- equals the order of `N(g)` at Q.
    (pushforwardProjectiveDivisor φ cd
      ((⟨W₁⟩).projectiveDivisorOf g)) (Q.toProjective) =
      ((⟨W₂⟩).ord_P Q (φ.toCurveMap.pushforward g))
```

(`pushforward` here is the algebra norm `N : K(E₁) → K(E₂)`, already
defined in `Curves/CurveMap.lean:252`.)

## Mathlib check

The underlying identity is standard for Dedekind domains:
`relNorm (span {g}) = span {N(g)}` and its consequence in terms of prime
factorizations. Mathlib has:
- `Ideal.relNorm_singleton : relNorm (span {g}) = span {Algebra.intNorm B A g}`
  for finite separable extensions.
- `Ideal.relNorm_eq_pow_of_isMaximal` (or `prod_normalizedFactors_eq_self`).

We need to combine these into the per-point form.

## Naming

`pushforward_div_eq_div_norm_at_affine`.

## Generality

`[IsAlgClosed F]` (inherited from C-003a, NormValuation), and finite
separability of `K(E₁)/K(E₂)` (which is exactly the `Isogeny` data).

## Proof approach

Start from worker-I's machinery and chain:

```
ord_Q (N g) = multiplicity (M_Q) (span {N g})           -- C-003a
            = multiplicity (M_Q) (relNorm (span {g}))   -- relNorm_singleton
            = Σ_{P over Q} ramId(P/Q) · multiplicity (M_P) (span {g})
                                                         -- factor + collect
            = Σ_{P : φ(P) = Q} ord_P g                  -- C-003a + ramId=1
            = (φ_* (div g))(Q)                          -- pushforward def
```

Each step is a separate sub-lemma:

### Sub-lemma 1: `relNorm_singleton` application
~30 LOC; direct from mathlib.

### Sub-lemma 2: factorization of `relNorm (M_Q)` over primes above
~50 LOC; uses `IsDedekindDomain.factor_singleton` plus worker-I's
`smoothPoint_fiber_eq_primesOver`.

### Sub-lemma 3: `inertiaDeg = 1` simplification
~30 LOC; under `[IsAlgClosed F]`, worker-I's
`inertiaDeg_maximalIdealAt = 1` collapses the residue degree to 1.

### Sub-lemma 4: Identifying `pushforward (div g)` at Q with the sum
~40 LOC; unfold `pushforwardProjectiveDivisor` definition and
`Finsupp.mapDomain` semantics.

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.Isogeny.pushforward_div_eq_div_norm_at_affine
```
reports only standard axioms.

## Risks

- The factorization step (Sub-lemma 2) is the most algebraically dense.
  May need `IsDedekindDomain.HeightOneSpectrum` machinery throughout.
  Estimated 50 LOC; could blow up to 100 if mathlib API doesn't
  cooperate cleanly.

- Worker-I's `sum_ramificationIdx_eq_finrank` provides the **degree**
  identity but we need the **per-prime** version. If worker-I's API
  doesn't extend, we may need an additional ~30 LOC of fiber-by-fiber
  rephrasing.

- The `Affine.Point` ↔ `SmoothPoint` ↔ `MaxIdeal` chain has multiple
  hops; getting all the diagram squares to commute may take 50-100 LOC
  of bridge lemmas.

## Progress log
