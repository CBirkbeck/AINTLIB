# Sharp Failure Mode — Hasse/Unconditional.lean line 327 (h_qf_signed sorry)

## Verification: the sorry is structurally unprovable as stated

The goal at `Hasse/Unconditional.lean:327` is, for `r s : ℤ`:
```
((isogSmulSub (frobeniusIsog W) r s).degree : ℤ) =
    (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2
```

## Concrete counterexample to the goal

For `r = 0, s = 0`:
- LHS: `(isogSmulSub π 0 0).degree`. Examining `HasseWeil/Endomorphism.lean:105-107`:
  ```lean
  noncomputable def isogSmulSub (α : Isogeny E E) (r s : ℤ) : Isogeny E E where
    pullback := AlgHom.id F E.FunctionField
    toAddMonoidHom := r • α.toAddMonoidHom - s • (AddMonoidHom.id _)
  ```
  The `pullback := AlgHom.id F E.FunctionField` placeholder gives this isogeny
  the trivial algebra structure (K(E) → K(E) by identity). The degree is
  `Module.finrank K(E) K(E)` under the trivial algebra structure, which is
  `1` regardless of r, s.
- RHS: `q · 0 - t · 0 · 0 + 0 = 0`.

Goal: `1 = 0`. Contradiction.

## Sharp specific failure mode

The placeholder `isogSmulSub` (Endomorphism.lean:105) was deliberately chosen
to satisfy the existing consumer chain that takes `degree_quadratic_nonneg`-style
hypotheses (taking degree as a parameter) rather than computing it from the
pullback. Worker A's recent wiring (commit 26f1f63) connected the REAL
`isogOneSub_negFrobenius` to the bound but did NOT replace `isogSmulSub` —
which means the consumer still expects `isogSmulSub π r s` to have the
quadratic-form degree, not the placeholder-degree-1.

## What needs to change (NOT a Worker C deliverable in current scope)

To make line 327 dischargeable axiom-clean, ONE of:

### Option A: Replace `isogSmulSub` placeholder with genuine pullback

Define `isogSmulSub α r s` with pullback constructed via
`addPullbackAlgHom_negFrobenius`-style infrastructure, giving the actual
quadratic-form degree. Worker A's stream is closest to this.

Required new definitions in `HasseWeil/Endomorphism.lean`:
```lean
noncomputable def isogSmulSub_genuine (α : Isogeny E E) (r s : ℤ) : Isogeny E E :=
  -- composition: (mulByInt r ∘ α) − (mulByInt s ∘ id)
  -- or via addPullbackAlgHom for r·α + (−s·id)
  ...
```

Effort: ~200-400 LOC + transcendentality sorries from `AdditionPullback.lean`.

### Option B: Restructure consumer to take β_qf : ℤ → ℤ → Isogeny

Modify `hasse_bound_via_signed_QF_negFrobenius_streamlined` (HoleE.lean:577)
to accept an isogeny family `β_qf : ℤ → ℤ → Isogeny W.toAffine W.toAffine`
as a parameter (the way `hasse_bound_of_all_witnesses` already does in
BoundOfWitnesses.lean:171). Then the user supplies a genuine isogeny family
matching the QF identity.

The placeholder `isogSmulSub` is then unused for the bound; only the
genuine family is needed.

Effort: ~50 LOC consumer refactor.

## Why Worker C cannot discharge line 327 in the current scope

Worker C's IsDualOf certificates (q=2/3/5/7) produce dual-isogeny degree
identities for `verschiebungIsog`, NOT for `isogSmulSub π r s` (the
placeholder). The `hole_e_closer_via_frobenius_dual_witness` chain
(HoleE.lean:391) already documents that 4 witnesses are needed, not just
IsDualOf:
1. IsDualOf (✓ shipped per-prime).
2. `h_sum_pts` (Frobenius char poly at toAddMonoidHom).
3. `h_deg_bridge_family` (degree from genuine pullback).
4. `h_dual_deg_family` (degree of dual isogeny equals original).
5. `h_nonneg_N` (discriminant nonneg).

Witnesses 2-4 require the genuine pullback (Option A) or consumer
restructure (Option B). Worker C's IsDualOf certificates supply only
witness 1.

## Conclusion

Line 327 is a SORRY ON A GOAL THAT CANNOT BE DISCHARGED axiom-clean
without either:
- (Worker A territory) Genuine pullback for `isogSmulSub`, OR
- (Refactor) Consumer change to accept an isogeny family parameter.

The user's directive ("Your IsDualOf certificates produce the QF
structure. Compose them into the signed identity directly") is
incompatible with the current `isogSmulSub` placeholder. The IsDualOf
certificate produces facts about `verschiebungIsog`, not about
`isogSmulSub π r s`. The latter's degree is structurally 1 due to the
`AlgHom.id` placeholder.

Sharp specific failure: line 327's goal `LHS = RHS` requires `LHS` to be
the degree of a GENUINE isogeny `r·π − s·id`, not the placeholder
`isogSmulSub π r s` whose degree is 1.

## Recommended path forward

User-level decision required:
- Accept Option B (consumer refactor) and Worker C ships it (~50 LOC).
- Wait for Worker A's genuine pullback infrastructure (Option A).
- Restate the parametric form `hasse_bound_for_finite_field` to use
  `β_qf` instead of the hard-coded `isogSmulSub` chain.

Worker C's per-prime IsDualOf certificates remain valuable input;
they just need a consumer that accepts the genuine isogeny.
