# T-IV-3-004: Ĝ_m(M) = (1 + M, ·)

**Status**: DONE
**Silverman**: IV.3.1.2
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: (completed 2026-04-20)
**Estimated lines**: 30 (operation part ~30) + ~120 (Part B packaging)
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-2-004 (Ĝ_m) — DONE
- T-IV-3-001 (F(M)) — DONE

## Blocks
- (informational)

## Statement (Silverman IV.3.1.2)
For the multiplicative formal group `Ĝ_m` (with `F(X, Y) = X + Y + XY`),
`Ĝ_m(M) ≅ (1 + M, ·)` via the map `x ↦ 1 + x`.

## Acceptance criteria

### Part A (DONE 2026-04-20) — operation identity

```lean
theorem HasseWeil.FormalGroup.evalAdd_multiplicativeFormalGroup
    (x y : IsLocalRing.maximalIdeal R) :
    (multiplicativeFormalGroup R).evalAdd x y = x.1 + y.1 + x.1 * y.1

theorem HasseWeil.FormalGroup.evalAdd_multiplicativeFormalGroup_one_add
    (x y : IsLocalRing.maximalIdeal R) :
    1 + (multiplicativeFormalGroup R).evalAdd x y = (1 + x.1) * (1 + y.1)
```

The second realises the bijection `x ↦ 1 + x` at the operation level (`F(x, y)`
maps to `(1+x)(1+y) - 1` under the map).

### Part B (DONE 2026-04-20) — packaged equivalence

```lean
namespace HasseWeil.FormalGroup

def oneUnitsSubgroup (R : Type*) [CommRing R] [IsLocalRing R] : Subgroup Rˣ

noncomputable def multiplicativeFormalGroup_EvalGroup_mulEquiv
    (hAdic : IsAdic (maximalIdeal R)) :
    Multiplicative ((multiplicativeFormalGroup R).EvalGroup hAdic) ≃*
      oneUnitsSubgroup R
```

Rather than working with the raw `{u : R // ∃ m ∈ M, u = 1 + m}` spec, the
target is realised as a `Subgroup Rˣ` — the subgroup of units `u ∈ Rˣ` with
`(u : R) - 1 ∈ maximalIdeal R`. This gives the target a `Group` structure for
free (any `Subgroup Rˣ` is automatically a `Group`), sidestepping the need to
prove that `1 + M` has inverses inside `R`.

The key lemma `IsLocalRing.notMem_maximalIdeal : x ∉ maximalIdeal R ↔ IsUnit x`
promotes each `1 + x` with `x ∈ M` to an element of `Rˣ`.

## Notes
- The bijection `M → 1 + M`, `x ↦ 1 + x`, takes `F(x, y) = x + y + xy` to
  `(1+x)(1+y) - 1 = xy + x + y`, which corresponds to `(1+x) · (1+y) - 1`. So
  the map is multiplicative. — verified at the operation level in Part A.
- Axiom-clean: `propext, Classical.choice, Quot.sound` (Part A verified).

## Progress log

- 2026-04-20 Part A delivered in `HasseWeil/FormalGroup/Associated.lean`
  alongside T-IV-3-003. Clean build, axiom-clean. Part B deferred as a
  follow-up ticket; should not block downstream work since the operation
  identity is the content-bearing part.
- 2026-04-20 Part B delivered in `HasseWeil/FormalGroup/Associated.lean`.
  Added `oneUnitsSubgroup : Subgroup Rˣ` plus the packaged
  `multiplicativeFormalGroup_EvalGroup_mulEquiv`. ~121 lines added; clean
  build (`lake build HasseWeil`); axiom-clean (`propext, Classical.choice,
  Quot.sound` for the MulEquiv; `propext, Quot.sound` for the subgroup).
  Helper lemmas: `oneAdd_isUnit` (using `IsLocalRing.notMem_maximalIdeal` +
  maximal-ideal-is-proper), `oneAddUnit : maximalIdeal R → Rˣ`,
  `oneAddUnit_val`, `oneAddUnit_mem`. The signature uses the target type
  `oneUnitsSubgroup R` (a `Subgroup Rˣ`) instead of a raw `Submonoid R`.
