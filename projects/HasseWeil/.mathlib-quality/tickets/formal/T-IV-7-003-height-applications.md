# T-IV-7-003: Height applications (selected lemmas)

**Status**: DONE (height_comp closed; axiom-clean)
**Silverman**: IV.7 (selected)
**Module**: `HasseWeil/FormalGroup/Height.lean`
**Owner**: (released)
**Estimated lines**: 60 (actual: ~160 including helpers)
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-7-002 (height of F)

## Blocks
- (informational)

## Statement
Selected lemmas about height needed for downstream results:
- height of composition: `h(f ∘ g) = h(f) + h(g)`  — **DONE**
- height of `[m]` for various `m`  — (not formalized; not blocking V.1)
- relation to ordinary/supersingular case for `Ê` (height 1 vs 2)  — (not
  formalized; Silverman V.3 application)

## Acceptance criteria

```lean
namespace PowerSeries

/-- Order of a univariate substitution, for f with vanishing constant coeff. -/
theorem order_subst {R : Type*} [CommRing R] [NoZeroDivisors R]
    {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    (PowerSeries.subst f g).order = g.order * f.order

end PowerSeries

namespace HasseWeil.FormalGroup

theorem FormalGroupHom.height_comp {F G H : FormalGroup R}
    [NoZeroDivisors R] (p : ℕ) [Fact p.Prime]
    (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    (g.comp f).height p = f.height p + g.height p

end HasseWeil.FormalGroup
```

## Notes
- Only as much as is needed for V.1.
- Requires `[NoZeroDivisors R]` (needed for `PowerSeries.order_mul`) and
  `[Fact p.Prime]` (needed for `padicValNat.mul`). These hypotheses are
  standard for the application (R is typically a field of characteristic p).
- `[Nontrivial R]` is no longer required: the trivial-ring case is absorbed
  by `PowerSeries.order_subst` directly.

## Progress log
- 2026-04-17T21:20Z [worker-G/subagent] Attempted `height_comp` theorem.
  Strategy: reduce to `order (subst f g) = order f * order g` + `padicValNat.mul`.
  The `order_subst` lemma is NOT in mathlib; a bottom-up attempt hit:
  * `PowerSeries.map_zero` not found as named lemma
  * `mul_top`/`top_mul` in `ℕ∞` not directly available
  * `PowerSeries.constantCoeff_zero_eq_coeff_zero` not available
  * `subst f g = f ^ order(g) * subst f (divXPowOrder g)` — needs to be proved
    via `coeff` comparison or a structural lemma. The factoring lemma for
    power series (`g = X^order(g) * divXPowOrder(g)`) exists but combining
    with `subst` doesn't have a direct mathlib lemma.
  Net: filing upstream-blocked. The cleanest path is to first contribute
  `PowerSeries.order_subst` to mathlib, then close this ticket via
  `padicValNat_mul`.
  Height.lean reverted to its T-IV-7-002 state.

- 2026-04-17 (closure): `height_comp` now proven axiom-cleanly in
  `HasseWeil/FormalGroup/Height.lean`, working around the previous obstacles:
  * Proved `order_subst_eq_mul` locally using the `g = X^b * divXPowOrder g`
    decomposition together with `PowerSeries.subst_mul`, `subst_pow`, `subst_X`,
    and `PowerSeries.order_mul/pow`. Handles the three cases `g = 0`, `f = 0`
    (using `subst_zero_eq_zero_of_constantCoeff_zero`), and both nonzero.
  * Proved the cast compatibility lemma `ENat.map_padicValNat_mul` to bridge
    `padicValNat.mul` into `ℕ∞`.
  * The missing mathlib pieces were available under different names: `map_zero`
    for linear maps, `ENat.mul_top` / `ENat.top_mul` for `ℕ∞`, and
    `PowerSeries.coeff_zero_eq_constantCoeff` for the constant-coefficient
    identity.
  * Four private helpers added to `Height.lean` (~160 lines total).
  * Build: `lake build HasseWeil.FormalGroup.Height` passes.
  * Full build `lake build` passes (remaining sorries are in unrelated
    `PullbackCoeff.lean`).
  * Axioms: `#print axioms FormalGroupHom.height_comp` reports only
    `[propext, Classical.choice, Quot.sound]` — no `sorry`, no new axioms.
  * Remaining items (height of `[m]`, supersingular case) are not blocking V.1
    and can be added when needed; moving this ticket to DONE.

- 2026-04-17 (refactor): Extracted the general `PowerSeries.order_subst`
  lemma to a new file `HasseWeil/FormalGroup/OrderSubst.lean`:
  * Public statement: for `f, g : R⟦X⟧` with `constantCoeff f = 0`
    and `[NoZeroDivisors R]`, `order (subst f g) = order g * order f`.
  * No hypothesis on `g`: handles `g = 0` (using AlgHom map_zero),
    `constantCoeff g ≠ 0` (order = 0 from constant coefficient survival),
    and main case via `divXPowOrder g` decomposition.
  * Also handles `Subsingleton R` (trivial ring) uniformly.
  * Private helper `constantCoeff_subst_univariate` extracts the
    `constantCoeff (subst f g) = constantCoeff g` identity.
  * `Height.lean` simplified: removed three obsolete private helpers
    (`subst_zero_eq_zero_of_constantCoeff_zero`, `subst_of_zero_eq_zero`,
    `constantCoeff_subst_of_constantCoeff_zero`, `order_subst_eq_mul`);
    `height_comp` now uses `PowerSeries.order_subst` directly.
  * Dropped `[Nontrivial R]` hypothesis from `height_comp` (the
    `order_subst` lemma absorbs the trivial-ring case).
  * Axioms: both `PowerSeries.order_subst` and `FormalGroupHom.height_comp`
    depend only on `[propext, Classical.choice, Quot.sound]`.
  * `HasseWeil.lean` updated to import `HasseWeil.FormalGroup.OrderSubst`.
