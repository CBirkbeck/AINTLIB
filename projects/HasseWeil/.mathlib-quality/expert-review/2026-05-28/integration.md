# Reply integration — Round 5 (2026-05-28)

Reply received from the round-1–4 reviewer on 2026-05-28.
Brief: `brief.md`
Reply: `reply.md`

## Interpretation summary

| # | Reviewer point | Maps to | Type | Confidence |
|---|---|---|---|---|
| 1 | Counterexample correct; sharp residual is false; diagnosis (conflation of projective morphism with affine ring map) is right | Q1 | direct answer + agreement | high |
| 2 | Choose Option I′ — function-field map + projective/local fibre compatibility, *not* naïve Option I | Q2 (refinement) | direct answer | high |
| 3 | Option II (localisation at D) is an open-cover detour: D = 0 locus may include points with `x^q = x` but non-fixed `y`, so the omitted locus is not exactly the kernel | Q2 | rules out Option II | high |
| 4 | Option III (projective coords) is morally correct but too heavy a refactor given existing function-field/affine-valuation orientation | Q2 | rules out Option III | high |
| 5 | Mathlib lacks `sepDeg(isogeny) = #kernel` at function-field level; refactor the project's own alg-closed fibre count to weaken the `CoordHom` input | Q3 | direct answer | high |
| 6 | Steps 1, 2, 4 + Identities A/B/C survive; CoordHom-side + affine-evaluation-at-kernel-points must retract | Q4 | confirms our salvage analysis | high |
| 7 | Hidden trap (new): affine-evaluation lemmas at kernel points must be excluded or projective/local | unprompted | concrete audit item | high |
| 8 | Hidden trap (new): for `g = 1−π`, preimage of `E∖{O}` is `E∖ker(1−π)`, not `E∖{O}` — geometric reason Option II is a detour | Q4 (geometric why) | concrete trap + explanation | high |
| 9 | Concrete 4-step plan: A preserve FF pullback / B fibre-over-O via valuation (uniformiser likely t = −x/y) / C refactor Step-4 consumer to take FunctionFieldMap + fibreOverPoint / D compose with Step 2 | Q2 implementation | actionable | high |
| 10 | `ProjectiveCurveMapCompat` structure shape suggested (function-field pullback + point map + fibre compatibility) | Q2 implementation | concrete proposal | high |

## Changes applied

**Codebase (committed):**
- `950479c` — A1: retraction annotations on the CoordHom-side chain.
  Added round-5 supersede notes to `oneSubFrob_baseChange_coordHom`,
  `divisibility_witness_x`, `addPullback_x_in_coordRing_range`,
  `divisibility_witness_y`, `addPullback_y_in_coordRing_range`,
  `oneSubFrob_isogBaseChange_toPointMap_eq`. Build remains green.
- `953677d` — A2: `ProjectiveCurveMapCompat` skeleton stub at the end
  of `RouteB` in `PointMap.lean` (documentation block + commented
  Lean sketch; concrete types deferred to follow-up session).

**Codebase (audit, no code change — recorded in memory):**
- A5 audit: Leaf 1 lemmas (`evalAt_preimage_addPullback_x/_y`,
  `addCoordAlgHom_evalAt_x/_y`) all carry the kernel-excluding
  hypothesis `hP : ¬ (P.x = xα ∧ P.y = negY xα yα)`. **They are
  safe.** The unsafe consumer is
  `oneSubFrob_isogBaseChange_toPointMap_eq` itself (it tries to apply
  Leaf 1 to every smooth point, including kernel points where `hP`
  is false). The Option I′ rewire must split into (a) non-kernel
  branch using existing Leaf 1, (b) kernel branch using
  `ProjectiveCurveMapCompat`'s fibre-over-O witness.

**Memory (outside repo):**
- `v13-routeb-coordhom-impossible.md` — appended round-5 reviewer
  confirmation + the deeper geometric reason (preimage of affine open
  trap).
- `v13-routeb-reformulation-options.md` — flagged Option I′ as
  chosen; recorded reviewer's pushback on Options II / III; recorded
  the four-step implementation plan; pointed at the stub commit.
- `v13-routeb-hidden-traps.md` — new memory documenting Trap 1
  (kernel-point evaluation; A5 audit findings) and Trap 2 (preimage
  of affine open under `g = 1 − π`).
- `MEMORY.md` — index updated.

## Changes rejected by user

- A3 (`WireUpPrep` consumer refactor) — deferred to a separate
  session. Heavier than the lightweight annotation/stub work done
  here; needs a deeper read of the consumer's existing height-one
  prime + inertia analysis.
- A4 (build the `oneSubFrobenius_fiber_over_infinity` lemma) —
  deferred for the same reason; also needs the uniformiser-at-O API
  identified first.

## Open questions remaining

None of the reviewer's Q1–Q4 answers are unaddressed — all four were
answered, all four are now reflected in code (A1/A2/A5) or memory
(B1/B2/B3). Two open *implementation* questions for the next session:

- Is `t = −x/y` actually available as a uniformiser at O in the
  project? Check `HasseWeil/OrdAtInftyBridge.lean`,
  `HasseWeil/EC/TranslateValuation.lean`,
  `HasseWeil/Curves/RamificationAtInfinity.lean`.
- Does the project's `Isogeny.sepDegree` API operate cleanly at the
  function-field level (i.e. can it consume a bare
  `K̄(E) →ₐ[K̄] K̄(E)`)? Or does its existing call-site require a
  curve map?

## Decisions recorded but not actioned

- Identity A, B, C are kept in place unchanged — reviewer agrees they
  are true polynomial identities in R and may be useful in the
  Option I′ meromorphic analysis. Their headers in PointMap.lean
  already reflect this.
- The `nReduced_R_div_D_sq` sorry is retained (build remains green
  during rewire); same for `divisibility_witness_x/y`,
  `addPullback_{x,y}_in_coordRing_range`,
  `oneSubFrob_baseChange_coordHom`,
  `oneSubFrob_isogBaseChange_toPointMap_eq`. They will be deleted
  once the Option I′ chain replaces them.
