# `/develop --decompose` — J.10 `verschiebung_isDualOf_frobenius` retirement (DRY-RUN GATE)

**Date**: 2026-05-25T23:15Z
**Target**: `HasseWeil.OpenLemmas.verschiebung_isDualOf_frobenius` at `HasseWeil/Hasse/OpenLemmas.lean:835` (currently bare sorry).

## Statement (verbatim from skeleton)

```lean
theorem verschiebung_isDualOf_frobenius
    (hq : 2 ≤ Fintype.card K) :
    ∃ V : Isogeny W.toAffine W.toAffine,
      IsDualOf W.toAffine V (frobeniusIsog W) := by
  let _ := hq
  sorry
```

## Plain-English content

THE SAME STATEMENT is shipped axiom-clean as `HasseWeil.verschiebung_dual_exists` in `HasseWeil/GapSpines.lean:64`. The OpenLemmas.lean copy is a **STALE DUPLICATE** that should be retired by routing through the shipped form.

## Decomposition

### Internal node J.10: the retirement itself

**Statement**: replace `sorry` at line 840 with `exact verschiebung_dual_exists W hq`.

**Required substrate**:
- `verschiebung_dual_exists` from `HasseWeil.GapSpines` — SHIPPED axiom-clean ✓ (line 64).

**The blocker**: ARCHITECTURAL IMPORT CYCLE.

`OpenLemmas.lean` is UPSTREAM of `GapSpines.lean`:
- OpenLemmas → OpenLemmaPrimitives (imports OpenLemmas)
- OpenLemmaPrimitives → RouteBInduction → GapQfKernel → QthRootRouteB → GapSpines (per session record)
- So OpenLemmas CANNOT import GapSpines (cycle).

Adding `import HasseWeil.GapSpines` to OpenLemmas.lean produces:
```
build cycle detected:
  HasseWeil/Hasse/OpenLemmas.lean → ... → HasseWeil.GapSpines → ... → HasseWeil/Hasse/OpenLemmas.lean
```

(Verified empirically earlier this session — see commit log.)

## Attacks attempted

**Attack 1 — Counterexample**: search for any structural mismatch between the two statements. None — they're verbatim the same statement (∃ V : Isogeny W.toAffine W.toAffine, IsDualOf W.toAffine V (frobeniusIsog W)). ✓ identical.

**Attack 2 — Edge case**: any hq variant — both take hq : 2 ≤ Fintype.card K. ✓

**Attack 3 — Discharge attack**: `verschiebung_dual_exists` axiom-clean confirmed earlier (`#print axioms` returned `[propext, Classical.choice, Quot.sound]`). ✓

**Attack 4 — Source-drift**: both ultimately encode Silverman III.6.1 Case 2.

**Attack 5 — Composition**: the discharge would be `exact verschiebung_dual_exists W hq`. Trivial — IF the import were available.

## Architectural alternatives

### Option A: Move `verschiebung_dual_exists` upstream

Move the `verschiebung_dual_exists` declaration to a file that OpenLemmas can already import. The chain of dependencies starts from:
- `mulByInt_q_pullback_qth_root` (GapSpines:40)
- → `mulByInt_q_pullback_subset_frobenius` (GapSpines:47)
- → `mulByInt_q_factors_through_frobenius` (GapSpines:56)
- → `verschiebung_dual_exists` (GapSpines:64) via `verschiebungIsog_isDualOf_frobenius_of_factor`

The chain depth requires either:
1. Moving all of these to a new "VerschiebungBase" file imported by OpenLemmas. Substantial refactor.
2. Inlining the `verschiebung_dual_exists` proof directly into OpenLemmas.lean — requires inlining the entire chain (`Verschiebung.QthRoots`, `Verschiebung.Cascade`, etc.).

Substantial refactor estimated at ~500-1000 LOC of move operations.

### Option B: Move the 4 consumers of `verschiebung_isDualOf_frobenius` DOWNSTREAM

The 4 consumers (per the comment at OpenLemmas.lean:832-834):
- `OpenLemmaPrimitives.lean:1677, 1683, 1685` (3 sites in `trace_eq_pi_plus_dualFrobenius_unconditional`)
- Comment at `Hasse/QuadraticForm.lean:383`

If these consumers were moved to a file downstream of GapSpines, they could use `verschiebung_dual_exists` directly. But:
- `trace_eq_pi_plus_dualFrobenius_unconditional` is consumed by other code in OpenLemmaPrimitives — cascade.
- Moving would require careful reorganisation.

Estimated ~200 LOC of move operations.

### Option C: Add a `verschiebung_isDualOf_frobenius_v2` in a downstream file

Write a downstream alias `verschiebung_isDualOf_frobenius_v2` (in e.g. GapSpines.lean or further downstream) that's defined as `verschiebung_dual_exists`, and rewire the 4 consumers to use this alias. The OpenLemmas.lean sorry stays but is documented as "use v2 instead".

Estimated ~30 LOC (just the alias + retargeting).

### Option D: Accept the architectural debt

Leave the OpenLemmas.lean sorry as a deliberate placeholder, documented as STALE/RETIRABLE. The consumers of `verschiebung_isDualOf_frobenius` in OpenLemmaPrimitives are themselves chained into substrate that has other gaps, so this stale sorry isn't a critical-path blocker.

Estimated: 0 LOC. Status quo.

## Verdict

**The architectural debt (D) is the current strategy** — the sorry is documented as STALE/RETIRABLE in the codebase (per the comment at line 825-834) and the audit document explicitly says "needs architectural decision".

**Recommendation**: Option C (alias in downstream file) is the smallest-cost fix that actually retires the substrate. The 4 consumers can use the alias.

**Estimated LOC for Option C**: ~30 LOC total (1 alias + 4 retargets).

## Source citations

Same as `verschiebung_dual_exists`: Silverman III.6.1 Case 2 (p. 82).

## Prior-B2 log

No match — this is not a B2 (statement is correct, just architecturally duplicated).

## Confidence gate

1. ✓ Substrate identified — the same statement is shipped axiom-clean elsewhere.
2. ✗ Lean skeleton compiles — yes (sorry compiles).
3. ✓ Verbatim source quote (same as verschiebung_dual_exists).
4. ✓ Attack categories: 5 per leaf, REJECTs caught at architecture level.
5. ✓ Prior-B2 log: clean.
6. ✓ Structure: same as upstream-shipped version.

## Next step

Per /develop --decompose protocol: STOP. User decision needed on:
- (A) Substantial upstream move (~500-1000 LOC refactor)
- (B) Move consumers downstream (~200 LOC refactor)
- (C) Downstream alias (~30 LOC, recommended)
- (D) Status quo (no action)

The substrate is REJECTED for direct discharge inside OpenLemmas.lean due to import cycle; alternative architectures all require some refactor.
