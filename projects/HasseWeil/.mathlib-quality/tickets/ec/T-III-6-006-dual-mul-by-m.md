# T-III-6-006: [m]^ = [m] and deg [m] = m²

**Status**: ✅ **DONE for m ≠ 0** (conditional on T-III-6-001's `exists_dual`;
deg formula unconditional for `m ≠ 0`)
**Silverman**: III.6.2(d)
**Module**: `HasseWeil/DualIsogeny.lean` (`isogDual_mulByInt_of_comp` at
line 159) + `HasseWeil/Basic.lean` (`mulByInt_degree`)
**Owner**: (existing)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-6-005 (dual additivity)
- T-III-6-003 (φ̂ ∘ φ = [deg])

## Blocks
- T-III-4-006 (E[m] structure)
- T-V-1-006 (Hasse bound)

## Statement (Silverman III.6.2(d))
- `[m]^ = [m]` for all `m ∈ ℤ`.
- `deg [m] = m²`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

theorem WeierstrassCurve.mulByInt_dual (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (m : ℤ) :
    (E.mulByInt m).dual = E.mulByInt m

theorem WeierstrassCurve.mulByInt_degree (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)]
    (m : ℤ) :
    (E.mulByInt m).degree = m^2

end HasseWeil.EC
```

## Notes
- `[m]^ = [m]`: by induction using dual additivity (T-III-6-005). `[1]^ = [1]`,
  `[m+1]^ = ([m] + [1])^ = [m]^ + [1]^ = [m] + [1] = [m+1]`.
- `deg [m] = m²`: from `[m]^ ∘ [m] = [deg [m]]` and `[m] ∘ [m] = [m²]`, we get
  `[m²] = [deg [m]]`, hence `m² = deg [m]`.

## Progress log
- 2026-04-20 [worker-J audit] `isogDual_mulByInt_of_comp` at
  `HasseWeil/DualIsogeny.lean:159` is the witness form for `[m]̂ = [m]`:
  given `h_comp : (mulByInt E n).comp (mulByInt E n) =
  mulByInt E ((mulByInt E n).degree : ℤ)` (which would follow from
  `mulByInt_comp_eq_mul`, a T-III-4-020-style fact), concludes
  `isogDual E (mulByInt E n) = mulByInt E n` via `isogDual_unique`. The
  degree half (`deg [m] = m²` for `m ≠ 0`) is unconditionally proved by
  `mulByInt_degree` in `HasseWeil/Basic.lean` (returns `(m²).toNat`,
  equal to `m.natAbs²`). Status OPEN → PARTIAL.
- 2026-04-20 [worker-A] **T-III-6-006 CLOSED** (for `m ≠ 0`):
  `isogDual_mulByInt` in new file `HasseWeil/EC/MulByIntDual.lean`
  combines `isogDual_mulByInt_of_comp` + `mulByInt_comp_eq_mul`
  (T-III-4-020b, closed 2026-04-20) + `mulByInt_degree` to conclude
  `[n]̂ = [n]` for `n ≠ 0`, unconditionally modulo the `exists_dual`
  sorry from T-III-6-001. When T-III-6-001 closes, this becomes
  fully axiom-clean.
