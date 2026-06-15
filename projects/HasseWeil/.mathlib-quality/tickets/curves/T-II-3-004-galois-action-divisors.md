# T-II-3-004: Galois action on divisors

**Status**: DONE (2026-04-18 — implemented via Phase C infrastructure)
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/GaloisAction.lean`
**Owner**: worker-H
**Estimated lines**: 40 (delivered: ~145 lines across `BaseChange.lean` and `GaloisAction.lean`)
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-3-001 (Divisor) — done

## Blocks
- T-II-3-007 (Pic_K(C))

## Statement
For a curve `C` defined over `K`, the absolute Galois group `G_{K̄/K}` acts on
`C(K̄)`, hence on `Div(C)` by

```
D^σ = Σ n_P (P^σ).
```

A divisor is **defined over K** if `D^σ = D` for all `σ ∈ G_{K̄/K}`. We denote
the K-defined divisors by `Div_K(C)`.

## Why BLOCKED

The project's current `SmoothPlaneCurve F` + `SmoothPoint` types bake in a
single base field `F`. A smooth point carries coordinates `(x y : F)` and a
nonsingularity proof over that same `F`. There is **no notion** of `C(F)`
versus `C(F̄)`, nor of a base-change functor.

Concretely, the ticket statement involves
- `K̄ / K` an algebraic closure (mathlib: `[Algebra K K̄] [IsAlgClosure K K̄]`)
- `C_{K̄}` the base change of `C` to `K̄` (not defined)
- `C(K̄) := C_{K̄}.SmoothPoint` — a type we don't have
- `K̄ ≃ₐ[K] K̄` acting on `C(K̄)` by its action on coordinates

None of these exist in the codebase as of 2026-04-17. Building them is a
significant infrastructure project, not a ~40-line ticket.

### What the project would need

1. **Base change of curves.** `SmoothPlaneCurve.baseChange : SmoothPlaneCurve K
   → {L // [Algebra K L] [Field L]} → SmoothPlaneCurve L`. This requires
   mapping the Weierstrass polynomial through `WeierstrassCurve.map`.

2. **Base-change of points.** For `σ : K̄ ≃ₐ[K] K̄`, there is a natural map
   `C(K̄) → C(K̄)` sending `(x, y) ↦ (σ x, σ y)`. This requires that
   `SmoothPoint` be relativized: `SmoothPoint C L` for `L` a `K`-algebra,
   or at minimum a version `(C.baseChange K̄).SmoothPoint` with the Galois
   action.

3. **Galois action on `Divisor C_{K̄}`.** A standard
   `MulAction (K̄ ≃ₐ[K] K̄) (Divisor C_{K̄})` via `Finsupp.mapDomain`.

4. **The subgroup `Div_K(C)`.** Both as an explicit subgroup of
   `Divisor C_{K̄}` and as an isomorphic copy living over `C` itself.

### Current `Divisor` definition

```lean
-- HasseWeil/Curves/Divisors.lean:27
def Divisor (C : SmoothPlaneCurve F) : Type _ := C.SmoothPoint →₀ ℤ
```

Under the current types, `C.SmoothPoint` already has coordinates in `F`, so the
"Galois fixed-divisor" condition is vacuous: every `D : Divisor C` is trivially
`σ`-invariant (there are no non-trivial σ with any effect). The ticket is only
meaningful once the `F` vs `F̄` distinction is present.

## Acceptance criteria (BLOCKED)

The original stub
```lean
variable {K K̄ : Type*} [Field K] [Field K̄] [Algebra K K̄] [IsAlgClosure K K̄]

noncomputable instance : MulAction (K̄ ≃ₐ[K] K̄) (Divisor C) :=
  Finsupp.mapDomain ∘ MulAction.toEnd

def Divisor.IsDefinedOverK (D : Divisor C) : Prop :=
  ∀ σ : K̄ ≃ₐ[K] K̄, σ • D = D
```
is syntactically wrong in the current project because `C : SmoothPlaneCurve K`
makes `Divisor C` live over `K`-points (which are already K-rational) rather
than over `K̄`-points.

## What would unblock this

Build Stream-A infrastructure for "curves over a base + algebraic closure",
roughly:

1. **T-CURVES-BASECHANGE-001** (~80 lines): define
   `SmoothPlaneCurve.baseChange (C : SmoothPlaneCurve F) (L : Type*) [Field L]
   [Algebra F L] : SmoothPlaneCurve L` and prove basic properties.

2. **T-CURVES-BASECHANGE-002** (~60 lines): relate `C.SmoothPoint` to the
   mathlib `WeierstrassCurve.Affine.Point` and establish base-change for
   points.

3. **T-CURVES-BASECHANGE-003** (~40 lines): define the Galois action
   `K̄ ≃ₐ[K] K̄ ↷ (C.baseChange K̄).SmoothPoint` by function-application on
   coordinates.

4. **T-II-3-004 itself** (~40 lines): state and prove the Galois action on
   `Divisor (C.baseChange K̄)` and the subgroup of `K`-defined divisors.

Alternatively, if the project can live without Galois-defined divisors (e.g.,
if all downstream users of `Div_K` can be reformulated with fields of definition
as hypotheses rather than Galois-invariance), the ticket can be closed by
removing it.

## Progress log

- **2026-04-17** (worker dev): Assessed; the project's single-field formulation
  of `SmoothPlaneCurve` makes the Galois action trivially vacuous. Real
  unblocking needs a base-change functor for curves, which itself is 100+ lines
  of infrastructure. Marked BLOCKED.
