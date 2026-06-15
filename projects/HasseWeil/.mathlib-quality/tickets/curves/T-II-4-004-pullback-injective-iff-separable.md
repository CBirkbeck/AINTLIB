# T-II-4-004: φ separable ⇔ φ*: Ω_{C₂} → Ω_{C₁} is injective

**Status**: CLOSED for the negFrobenius isogeny — T-II-4-004 fully unconditional axiom-clean. Witness #2 also closed unconditional (`isogOneSub_negFrobenius_finiteDimensional`).
**Silverman**: II.4.2(c)
**Module**: `HasseWeil/Curves/Differentials.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: hard
**Stream**: A/E

## Depends on
- T-II-4-002 (Ω_C is 1-dimensional)
- T-II-2-004 (separable degree)
- (Auxiliary/PullbackKaehler) — generic pullback functor

## Blocks
- T-III-4-015 (separable ⇒ unramified)
- T-III-5-002 (additivity of pullback)

## Statement (Silverman II.4.2(c))
For a nonconstant morphism `φ : C₁ → C₂` of smooth curves, the pullback
`φ* : Ω_{C₂} → Ω_{C₁}` (induced from `φ* : K(C₂) → K(C₁)`) is injective iff
`φ` is separable.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The pullback of differentials along a curve morphism. -/
def Differentials.pullback (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant) :
    Differentials C₂ →ₗ[F] Differentials C₁

/-- φ is separable iff φ*: Ω_{C₂} → Ω_{C₁} is injective.
    Reference: Silverman II.4.2(c). -/
theorem Differentials.pullback_injective_iff_separable
    (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant) :
    Function.Injective (Differentials.pullback φ hφ) ↔ φ.IsSeparable

end HasseWeil.Curves
```

## Notes
- This is the central separability criterion via differentials.
- Connect to `Auxiliary/PullbackKaehler.lean` which already handles a generic
  Kähler-pullback functor.
- Used heavily in III.5 (invariant differential pullback) and III.4 (ramification).

## Progress log

- 2026-05-04 [worker-A] **BOUND-LEVEL CONSUMERS SHIPPED** — Witness #1
  through #3 + bound now have shorter consumer forms with FiniteDim and
  T-II-4-004 absorbed. Session 6 commits (9 axiom-clean):
  * Commit 33: `omegaPullbackCoeff_eq_formalIsogenyLeading_id` (BRIDGE-001 for id).
  * Commit 34: `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` (BRIDGE-001 for π).
  * Commit 35: `omegaPullbackCoeff_mulByInt_neg_one` axiom-clean (avoiding the
    Wronskian sorry — direct via `omegaPullbackCoeff_unique` + `mulByInt_pullback_y_neg_one`).
  * Commit 36: `omegaPullbackCoeff_negFrobeniusIsog = 0` axiom-clean
    (chain rule via `omegaPullbackCoeff_comp_of_base`).
  * Commit 37: `isogOneSub_negFrobenius_isSeparable_of_h_add_only`
    (Witness #1 with T-II-4-004 absorbed; only h_add additivity needed).
  * Commit 38: `isogOneSub_negFrobenius_isSeparable_of_h_coeff_only`
    (shorter; only `omega-coeff = 1` needed).
  * Commit 39: `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_sep_and_fiber`
    (Witness #3 with FiniteDim absorbed via Commit 30).
  * Commit 40: `hasse_bound_via_signed_QF_negFrobenius_no_fin`
    (bound with FiniteDim absorbed).
  * Commit 41: `hasse_bound_via_signed_QF_negFrobenius_h_coeff_only`
    (bound with FiniteDim AND IsSeparable absorbed; takes only h_coeff,
    fiber, kernel-finite, QF).

  The substantive deferred-witness count for the Hasse-Weil bound's
  negFrobenius branch drops to 3 (h_coeff = III.5.2 additivity of
  omega-pullback coefficient; fiber witness; QF identity). The remaining
  two have their own existing witness-parametric chains.

- 2026-05-04 [worker-A] **CLOSED for negFrobenius** — T-II-4-004 fully
  unconditional axiom-clean. Path (a) trans-degree chain succeeded.
  Session 5 commits (10 axiom-clean):
  * Commit 22: `functionField_trdeg_eq_one` — trdeg F K(E) = 1.
  * Commit 23: `weierstrass_functionField_trdeg_eq_one`.
  * Commit 24: `addPullback_x_negFrobenius_isTranscendenceBasis` —
    1-element trans basis.
  * Commit 25: `addPullback_x_negFrobenius_isAlgebraic_subalgebra` —
    K(E) algebraic over `Algebra.adjoin K {addPullback_x}`.
  * Commit 26: `addPullback_x_negFrobenius_isAlgebraic_range_of_witness` —
    lift to `α.pullback.range` via `tower_top_of_subalgebra_le`.
  * Commit 27: `addPullback_x_negFrobenius_mem_range` — discharges the
    membership witness via the layered `addPullbackAlgHom` construction.
  * Commit 28: `addPullback_x_negFrobenius_isAlgebraic_range` —
    composed unconditional algebraicity over the range.
  * Commit 29: `isogOneSub_negFrobenius_isAlgebraic_synonym` — transfer
    to type-synonym via the bijective `AlgEquiv.ofInjective` range iso.
  * Commit 30: `isogOneSub_negFrobenius_finiteDimensional` —
    **WITNESS #2 UNCONDITIONAL** via Commit 18 + 19 + 29.
  * Commit 31: `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero` —
    **T-II-4-004 FULLY UNCONDITIONAL** for negFrobenius via Commit 17 + 30.

- 2026-05-04 [worker-A] **PARTIAL++++** — Witness #2 reduced to a single
  remaining piece (IsAlgebraic over the type-synonym).
  Session 4 commits (3 axiom-clean + scaffold):
  * Commit 18: `isogeny_finiteDimensional_of_isAlgebraic_synonym` —
    Witness #2 producer from `IsAlgebraic + EssFiniteType` over the
    `IsogenyAlgebraSource W α` type-synonym wrapper.
  * Commit 19: `functionField_essFiniteType_F` +
    `isogenyAlgebraSource_essFiniteType` — EssFiniteType for the synonym
    UNCONDITIONAL (via FractionRing localization + tower comp).
  * Commit 20: BRIDGE-001 general α scaffold +
    `omegaPullbackCoeff_eq_formalIsogenyLeading_of_constant_witness` +
    `omegaPullbackCoeff_eq_formalIsogenyLeading_add_witness`.

  Witness #2 status: needs only `Algebra.IsAlgebraic (IsogenyAlgebraSource W α)
  K(E)`. Decomposed into trans-deg-style discharge: K(E) is alg over
  `Algebra.adjoin F {coordX}` (existing instance up to extendScalars),
  giving trdeg ≤ 1; combined with {addPullback_x} alg-indep yields
  IsTranscendenceBasis, which gives algebraicity over the corresponding
  adjoin. Final lift to the synonym needs the specific iso α.pullback
  surjectivity onto α.pullback K(E) viewed in the synonym frame.

- 2026-05-04 [worker-A] **PARTIAL+++** — full T-II-4-004 iff
  `α.IsSeparable ↔ ω-coeff ≠ 0` lands axiom-clean modulo Witness #2 only.
  Three structural bridges closed in this batch:
  * Sub-piece A (`isogeny_isScalarTower`) — broken via @-explicit middle SMul.
  * Cotangent bridge (`Subsingleton ↔ ω-coeff ≠ 0`) — broken via
    `IsogenyAlgebraSource` type-synonym wrapper bypassing the
    `Semiller.toModule` vs `Algebra.toModule` defeq fight.
  * Forward direction (`IsSeparable → ω-coeff ≠ 0`) — direct via
    1-dim Ω + cotangent surjectivity contradiction.

  Session 3 commits (8 axiom-clean + 1 doc):
  * Commit 11: `isogeny_finiteDimensional_of_isAlgebraic_essFiniteType` —
    Witness #2 producer from IsAlgebraic + EssFiniteType.
  * Commit 12: `isogeny_isAlgebraic_of_finite_intermediate` —
    IsAlgebraic from a finite intermediate via tower_top.
  * Commit 13: `IsogenyAlgebraSource` type-synonym wrapper (defeq blocker break).
  * Commit 14: `isogeny_subsingleton_kaehler_of_omegaCoeff_ne_zero` —
    cotangent bridge axiom-clean via type synonym.
  * Commit 15: `isogeny_isSeparable_of_omegaCoeff_ne_zero_finiteDim` —
    reverse direction with FiniteDim only (drops the bridge witness).
  * Commit 16: `isogeny_omegaCoeff_ne_zero_of_isSeparable` —
    forward direction unconditional (NO hypothesis).
  * Commit 17: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim` —
    unified iff witness-parametric on FiniteDim only.

  Remaining: Witness #2 (`FiniteDimensional`) discharge unconditional. Decomposed
  via Commits 11+12 into IsAlgebraic + EssFiniteType pieces; the IsAlgebraic
  discharge needs trans-degree machinery for arbitrary nonconstant isogenies.

- 2026-05-04 [worker-A] **PARTIAL++** — Sub-piece A (`isogeny_isScalarTower`)
  broken; reverse direction shipped witness-parametrically; full T-II-4-004
  iff lands axiom-clean modulo a single bridge witness.

  Session 2 commits (8, all axiom-clean):
  * Commit 10: `isogeny_isSeparable_of_kaehler_witnesses` — Subsingleton +
    EssFiniteType → IsSeparable via mathlib's `iff_isSeparable.mp`.
  * Commit 11: `isogeny_essFiniteType_of_finiteDimensional` — Witness #2
    discharge into EssFiniteType (Module.Finite → FiniteType → EssFiniteType).
  * Commit 12: `isogeny_isSeparable_of_subsingleton_kaehler_finiteDimensional`
    — composition (Subsingleton + Witness #2 → IsSeparable).
  * Commit 13: `isSeparable_iff_subsingleton_kaehler_of_finiteDimensional`
    — algebra-Kähler iff (Subsingleton form, witness-parametric on Witness #2).
  * Commit 14: `subsingleton_relativeKaehler_of_mapBaseChange_surjective`
    — abstract converse cotangent surjectivity.
  * Commit 15: **BREAK Sub-piece A** — `isogeny_isScalarTower` axiom-clean.
    Key insight: state goal type with `@`-explicit instance arguments fixing
    the middle SMul to `α.toAlgebra.toSMul`, forcing the elaborator to use
    `α.toAlgebra` rather than the global `OreLocalization.instSMul`.
  * Commit 16: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses`
    — full T-II-4-004 iff witness-parametric on FiniteDim + bridge.
  * Commit 17: `isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge`
    — composed Witness #1 with FiniteDim + bridge form.

  Remaining substantive piece: bridge `Subsingleton Ω[K(E)/K(E)_α] ↔
  Function.Injective α.pullbackKaehler` (cotangent-sequence iff). Sub-piece A
  break-through unblocks `mapBaseChange F K(E) K(E)` for the discharge.

  Defeq blocker on the bridge discharge: `Semiring.toModule` vs
  `Algebra.toModule` for K(E)-K(E) module structure when @-passing
  α.toAlgebra to `KaehlerDifferential.mapBaseChange`. This is a deeper
  typeclass plumbing issue than Sub-piece A; needs orchestrated @-arg
  passing OR a type-synonym wrapper around K(E) on the source side.

- 2026-05-03 [worker-A] **PARTIAL+** — opened scaffold + scalar half closed
  axiom-clean + algebra half forward chain 3/4 steps + IsScalarTower defeq
  obstruction surfaced. New file `HasseWeil/Curves/Differentials.lean` carries
  ~12 axiom-clean lemmas + 4 sorry-bearing scaffolds.

  Scalar half (`pullbackKaehler injective ↔ ω-coeff ≠ 0`) — axiom-clean
  via 1-dim Ω analysis + field structure of K(E):
  * `omegaPullbackCoeff_ne_zero_of_pullbackKaehler_injective`
  * `pullbackKaehler_injective_of_omegaPullbackCoeff_ne_zero`
  * `pullbackKaehler_injective_iff_omegaPullbackCoeff_ne_zero`

  Algebra half forward chain 3/4 steps axiom-clean:
  * `isogeny_formallyUnramified_of_isSeparable` (via mathlib's
    `Algebra.FormallyUnramified.of_isSeparable`)
  * `isogeny_subsingleton_kaehler_of_isSeparable` (via instance
    `subsingleton_kaehlerDifferential`)
  * `mapBaseChange_surjective_of_subsingleton_relativeKaehler` (abstract,
    via `KaehlerDifferential.exact_mapBaseChange_map`)

  Reverse-direction scaffold + iff composer + composer to full T-II-4-004
  shipped (witness-parametric, axiom-clean for the witness forms).

  **Defeq obstruction (forward chain step 4)**: `isogeny_isScalarTower`
  scaffold remains sorry. Mathlib's typeclass synthesis picks a SMul
  instance for `K(E) → K(E)` that's defeq to but syntactically distinct
  from `α.toAlgebra.toSMul`. Both `IsScalarTower.of_algebraMap_eq` and
  `IsScalarTower.of_algebraMap_smul` constructors fail at the
  `Algebra.smul_def` rewrite step. `isogeny_smul_assoc_identity` (axiom-clean)
  carries the underlying mathematical content; needs typeclass-level
  reconciliation.

  Resolution candidates (next session):
  1. `attribute [local instance high]` priority on `α.toAlgebra`.
  2. Identify Lean's chosen SMul, prove it equals `α.toAlgebra.toSMul`.
  3. Restructure with explicit @-instance passing throughout.
