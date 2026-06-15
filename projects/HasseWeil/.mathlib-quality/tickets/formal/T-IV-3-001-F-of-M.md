# T-IV-3-001: F(M) for max ideal M of complete local ring

**Status**: DONE (full `AddCommGroup (IsLocalRing.maximalIdeal R)` instance
delivered 2026-04-18 via `FormalGroup.evalGroup`)
**Silverman**: IV.3 (definition)
**Module**: `HasseWeil/FormalGroup/EvalGroup.lean` (new)
**Owner**: worker-G
**Estimated lines**: 60 (~1100 delivered, including inverse axiom + associativity bridge)
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-2-001 (FormalGroup R)
- (mathlib complete local ring)

## Blocks
- T-IV-3-002..007

## Statement (Silverman IV.3 def)
Let `R` be a complete local ring with maximal ideal `M`. For a formal group law
`F` over `R`, define `F(M)` to be the set `M` equipped with the operation
`x +_F y := F(x, y)` (which converges in the (M)-adic topology because of
completeness).

This makes `F(M)` an abelian group.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The group F(M) for a formal group law F over a complete local ring (R, M).
    Reference: Silverman IV.3. -/
def FormalGroup.evalGroup (F : FormalGroup R) [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    AddCommGroup (IsLocalRing.maximalIdeal R)

end HasseWeil.FormalGroup
```

## Notes
- The convergence requires complete + (M)-adic topology (or similar). Mathlib
  has `IsAdicComplete`.

## Progress log

### 2026-04-17: Binary operation + unit + commutativity delivered

Delivered in `HasseWeil/FormalGroup/EvalGroup.lean`:

- `FormalGroup.evalAdd (F : FormalGroup R) (x y : M) : R` — binary operation,
  defined via `MvPowerSeries.eval₂ (RingHom.id R) ![x.1, y.1] F.toSeries`.
- `FormalGroup.evalAdd_mem : F.evalAdd x y ∈ M` — closure of the operation in M.
  Proof uses `HasSum.mem_of_tendsto` on the closed set `M`, noting the series
  `F(x, y)` has constant coefficient 0 and each non-constant monomial contributes
  a term in M.
- `FormalGroup.evalAdd_zero_zero : F.evalAdd 0 0 = 0`.
- `FormalGroup.evalAdd_comm : F.evalAdd x y = F.evalAdd y x` — commutativity,
  derived from `F.comm` via `FormalGroup.coeff_swap` (coefficient symmetry) and
  reindexing of `HasSum` via a swap equivalence.
- `FormalGroup.evalAdd_zero_right : F.evalAdd x 0 = x.1` — right unit, via
  `F.lunit`-derived `coeff_j0_of_ne_one` (showing `coeff (j,0) F = 0` for j ≠ 1)
  and `HasseWeil.FG.FormalGroup.coeff_10`.
- `FormalGroup.evalAdd_zero_left : F.evalAdd 0 y = y.1` — left unit, via comm
  and right unit.

Axiom-clean (no `sorry`). `lake build` passes.

The setup uses topology/uniform structure hypotheses:
`[IsLocalRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]`
`[IsLinearTopology R R] [T2Space R] [CompleteSpace R]` plus an explicit
`IsAdic (IsLocalRing.maximalIdeal R)` hypothesis.

### 2026-04-17 (update): Formal negation `evalNeg` delivered

Delivered in `HasseWeil/FormalGroup/EvalGroup.lean`:

- `FormalGroup.evalNeg (F : FormalGroup R) (x : M) : R` — formal negation,
  defined via `PowerSeries.eval₂ (RingHom.id R) x.1 F.inverse`, using
  `FormalGroup.inverse` from `HasseWeil/FormalGroup/Inverse.lean`.
- `FormalGroup.evalNeg_mem : F.evalNeg x ∈ M` — closure of the negation in M.
  Proof uses the same `HasSum.mem_of_tendsto` + closed-M argument as
  `evalAdd_mem`, specialised to the univariate `PowerSeries.hasSum_eval₂`.
- Internal helper `powerSeries_eval_mem` (private) generalising the same
  membership argument to any `u : PowerSeries R` with vanishing constant
  coefficient, evaluated at `x ∈ M`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

### Deferred to follow-up work

- **Inverse axiom** `evalAdd_evalNeg`: `F(x, -_F x) = 0` — requires a bridge
  lemma

    `eval_x (fAdd F u v) = eval₂ id ![eval_x u, eval_x v] F.toSeries`

  which pushes a continuous ring hom through `MvPowerSeries.subst`.
- **Associativity** `evalAdd_assoc`: parallel form of the bridge lemma but
  for three variables; requires analogous infrastructure.
- **AddCommGroup instance on M** `FormalGroup.evalGroup`: combines the
  above.

**Technical obstacle (blocks inverse-axiom, associativity, AddCommGroup)**:
The cleanest mathlib route uses `MvPowerSeries.subst`/`eval₂` commutation
(`eval₂_subst`, `comp_subst_apply`), which requires the coefficient ring to
carry the **discrete** uniformity, whereas our `R` has the adic uniformity.
Two routes to deliver the bridge:

1. **Coefficient-level Fubini**: apply `coeff_subst` to the LHS to expand
   `coeff n (fAdd F u v) = ∑ᶠ d, coeff d F * coeff n (u^(d 0) * v^(d 1))`,
   then exchange with the outer `∑ n · x^n` (needs Fubini for `HasSum` of
   finite-support `finsum`s).

2. **Topology juggling**: use `MvPowerSeries.hasSum_aeval` with the
   `WithPiTopology` scoped instances on `PowerSeries R` to get a HasSum for
   `fAdd F u v`. Apply the continuous ring hom `PowerSeries.eval₂Hom` to
   push the HasSum through. Requires coefficient-level identification
   `aeval = subst` (via `coeff_subst`).

Both routes are ~100-200 lines of additional Lean work. Route (2) is the
cleaner approach but runs into subtleties around elaborating
`IsUniformAddGroup (PowerSeries R)` instances under a `letI`.
