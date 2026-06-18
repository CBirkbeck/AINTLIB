# T-PIC-C-003a: Bridge `ord_P f = multiplicity (maxIdeal P) (f)`

**Status**: DONE (2026-05-13 — `pointValuation_algebraMap_eq_intValuation` in
`HasseWeil/Curves/Miller.lean`, axiom-clean; combines Worker I's
`pointValuation_algebraMap_eq_exp_count` with mathlib's `intValuation_if_neg`)
**Silverman**: II.1 (DVRs at smooth points; standard ring-theoretic identity)
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean` (extension)
**Owner**: —
**Estimated lines**: ~100
**Difficulty**: medium
**Phase**: C (sub-piece for unconditional C-003)

## Depends on

- Worker-I's `Curves/NormValuation.lean` API (READ-ONLY, no changes)
- T-II-1-002 (DONE) — `ord_P` definition via `pointValuation`
- Mathlib: `IsDedekindDomain.HeightOneSpectrum.intValuation`,
  `UniqueFactorizationMonoid.normalizedFactors`

## Blocks

- T-PIC-C-003b (norm-divisor identity at affine points)

## Statement

For a smooth point `P` of `C` and `f ∈ C.CoordinateRing` (the affine
coordinate ring) nonzero:

```lean
theorem ord_eq_multiplicity_maxIdealAt
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    (P : C.SmoothPoint) {f : C.CoordinateRing} (hf : f ≠ 0) :
    (C.ord_P P f : ℤ) =
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {f})).count (maximalIdealAt P)
```

(Schematic — the exact mathlib lemma names may differ; the content is
"`ord_P` from project = mathlib's prime factorization multiplicity at
the maximal ideal `maximalIdealAt P`".)

For the function-field-element version (`f ∈ K(E)`):

```lean
theorem ord_eq_intValuation
    [IsAlgClosed F] [C.toAffine.IsElliptic]
    (P : C.SmoothPoint) (f : C.FunctionField) (hf : f ≠ 0) :
    (C.ord_P P f : ℤ) =
      (heightOneSpectrum_of_smoothPoint P).intValuation f
```

## Mathlib check

Mathlib has both:
- `IsDedekindDomain.HeightOneSpectrum.intValuation` for valuations from
  height-one primes of a Dedekind domain.
- `UniqueFactorizationMonoid.normalizedFactors.count` for prime
  multiplicities.

These agree (`IsDedekindDomain.HeightOneSpectrum.intValuation_eq`).

What's missing: a lemma identifying the project's `ord_P P f` (defined
via DVR completion at `P`) with one of these.

## Naming

- `ord_eq_multiplicity_maxIdealAt`
- `ord_eq_intValuation`

## Generality

`[IsAlgClosed F] [IsElliptic]` (inherited from worker-I's
`smoothPointEquivMaxIdeal`).

## Proof approach

The project's `pointValuation` is constructed from the DVR
`(C.CoordinateRing).Localization (maximalIdealAt P).primeCompl`. The
mathlib `intValuation` is constructed from
`Localization.AtPrime (maximalIdealAt P)`. These are the same DVR up to
the natural iso.

Key lemmas to invoke:
- `Localization.AtPrime.uniformizer` ↔ project's `uniformizer` (T-II-1-003).
- `IsLocalRing.maximalIdeal` agreement.
- `Multiplicity.normalizedFactors` count via `addValuation` of localized
  units.

Estimated structure:
1. **Local algebra setup** (~30 LOC): set up the DVR and identify
   `maximalIdeal (Localization.AtPrime ...)` with the localized
   `maximalIdealAt P`.
2. **Valuation agreement** (~40 LOC): show
   `pointValuation P = HeightOneSpectrum.intValuation` for the
   corresponding height-one prime.
3. **Multiplicity bridge** (~30 LOC): apply
   `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_count_normalizedFactors`
   (or similar mathlib lemma) to get the multiplicity-count form.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.ord_eq_intValuation
#print axioms HasseWeil.Curves.ord_eq_multiplicity_maxIdealAt
```
both report only standard axioms.

## Risks

- The project's `pointValuation` might not be definitionally equal to
  mathlib's `HeightOneSpectrum.intValuation`; the bridge could require
  unfolding through completions. ~50 LOC of fiddly localization manipulation.

- Need `IsDedekindDomain` on `C.CoordinateRing`, which holds for
  elliptic curves (the coordinate ring of a smooth affine curve is a
  Dedekind domain). Worker-I's `IntegralClosure.lean` should have this
  conditional on the right hypotheses.

## Progress log

* 2026-05-13: Closed. Worker I's `pointValuation_algebraMap_eq_exp_count`
  + `divisorOf_algebraMap_apply_eq_count` in `NormValuation.lean` discharge
  the count-form. `pointValuation_algebraMap_eq_intValuation` in
  `Miller.lean` provides the explicit `pointValuation = intValuation`
  form requested by the ticket. All axiom-clean.
