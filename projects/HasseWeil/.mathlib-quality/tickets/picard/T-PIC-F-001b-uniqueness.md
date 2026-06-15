# T-PIC-F-001b: Uniqueness — `(P) ~ (Q) ⟹ P = Q`

**Status**: BLOCKED on worker-K's T-III-3-003
**Silverman**: III.3.3
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy (after worker-K's T-III-3-003 lands)
**Phase**: F (uniqueness direction — GATED on worker-K)

## Depends on

- **T-III-3-003** (worker-K, CHECKED-OUT, hard) — `(P) ~_div (Q) ⟹ P = Q`

## Blocks

- T-PIC-F-001c (assembly)

## Statement

```lean
theorem kappaDivisor_inj
    [W.IsElliptic] [IsAlgClosed F]
    {P Q : W.Point} (h : kappaDivisor W P ~_div kappaDivisor W Q) :
    P = Q
```

This is the projective-divisor version of worker-K's T-III-3-003, which
states the affine-divisor version. Bridge is straightforward (the
infinity terms cancel).

## Mathematical content

Worker-K's T-III-3-003 (Silverman III.3.3) says: on an elliptic curve,
`(P) ~ (Q)` (linear equivalence of single-point divisors) implies `P = Q`.

Equivalently, in our Pic⁰ language: `kappaDivisor W P ~ kappaDivisor W Q`
(linear equivalence) implies `P = Q`.

This is the "non-isomorphism with ℙ¹" content — if `(P) - (Q) = div(f)`,
then `f` would define a degree-1 map E → ℙ¹, hence an isomorphism, but E
has genus 1 and ℙ¹ has genus 0.

## Naming

`kappaDivisor_inj`.

## Generality

`[IsAlgClosed F]` (inherited from worker-K's T-III-3-003) plus
`[IsElliptic]`.

## Proof approach

Direct consumption of T-III-3-003 once it ships:

```lean
theorem kappaDivisor_inj h := by
  -- Unfold kappaDivisor: (P) - (O) ~ (Q) - (O) ⟹ (P) ~ (Q)
  have h_affine : (Divisor.single P 1 : Divisor _) ~_div Divisor.single Q 1 := by
    -- Translate from projective to affine
    ...
  exact WeierstrassCurve.point_divisor_inj P Q h_affine
```

The "translate from projective to affine" step removes the infinity
contribution from both sides. ~25 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.kappaDivisor_inj
```
reports only standard axioms (modulo whatever T-III-3-003 reports).

## Risks

- **Fully gated on worker-K**. If T-III-3-003 stalls (worker-K's revised
  estimate is 300-500 LOC, hard), F-001b cannot ship.
- **Translation lemma**: `(P) - (O) ~ (Q) - (O)` (projective form) ⟺
  `(P) ~ (Q)` (affine form, modulo trivial infinity correction) is
  straightforward but needs ~10 LOC of bridge.
- **No alternative route**: T-III-3-003 IS the uniqueness in Pic⁰(E) ≅ E.
  Any "alternative" would have to re-prove T-III-3-003.

## Progress log
