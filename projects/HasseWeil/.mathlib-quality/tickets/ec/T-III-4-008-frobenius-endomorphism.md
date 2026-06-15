# T-III-4-008: Frobenius endomorphism on E/F_q

**Status**: DONE (FrobeniusIsogeny.lean — refactor)
**Silverman**: III.4.6
**Module**: `HasseWeil/FrobeniusIsogeny.lean` → `HasseWeil/Frobenius/AsAlgHom.lean`
**Owner**: (existing)
**Estimated lines**: 0 (existing)
**Difficulty**: trivial
**Stream**: C

## Depends on
- T-III-4-001 (Isogeny)
- T-II-2-012 (Frobenius morphism construction)

## Blocks
- T-V-1-001..006 (Hasse bound)
- T-III-5-005 (separability of m + nπ)

## Statement (Silverman III.4.6)
For an elliptic curve `E` defined over `F_q`, the **q-power Frobenius map**
`π : E → E^(q) = E` (the latter equality because `E` is `F_q`-rational) given on
points by `(x, y) ↦ (x^q, y^q)` is an isogeny of degree `q`, sending `O` to `O`.

## Acceptance criteria

Existing in `HasseWeil/FrobeniusIsogeny.lean`. Confirm:
```lean
#check HasseWeil.frobeniusIsogeny
```

## Notes
- The `degree = q` part has a SORRY currently — that's tracked under T-II-2-015.

## Progress log
- 2026-04-08 [auto] marked DONE — modulo the deg = q sorry tracked elsewhere
