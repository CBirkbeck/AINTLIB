# Reply integration — 2026-06-24

Reply received 2026-06-24. Brief: brief.md. Reply: reply.md.

## Interpretation summary

| # | Reviewer point | Type | Verified vs code |
|---|----------------|------|------------------|
| 1 | Basic-Laurent flatness should be arbitrary-`f` (Lemma 8.31), not numerator-in-ring-of-definition | direct answer (Q-bdd-2) | ✓ `flat_quotient_{fSubX,oneSubfX}_general` + `presheafValue_flat_of_unitDatum_faithful` are arbitrary-`f`, LL-free, h_pb-free |
| 2 | Prop 8.30 / Leaf A does NOT need general LL-bdd; use basic Laurent steps + compose | direct answer (Q-bdd-2) | ✓ the clean engine exists; the chain detours through `flat_imagePieceDatum_domUnit` (h_pb + LL) |
| 3 | `PlusSubring` missing core axiom `B⁺ ⊆ B°`; fix = include it (or local `hplus`) | unprompted criticism | ✓ EXACTLY the `IsRingOfIntegralElements.subset_powerBounded` field threaded this session — validates the IRIE direction |
| 4 | Uniform IsBounded over-strong; power-bounded (`B⁺ ⊆ B°`) is right | direct answer (Q1) | ✓ matches my §8.1 B2 finding |
| 5 | General non-domain criterion: prove via Wedhorn 7.18, NOT minimal-prime | direct answer (Q-bdd-1) | the recent SpvAI-principal `IsInSpvAI` / `mem_plus` work was heading minimal-prime-ish; reclassify |
| 6 | LL-bdd routes through the general valuative criterion (`mem_plus`) — heavy | concern | ✓ `locLift_divByS_isPowerBounded_faithful` → `mem_plus` → SpvAI continuity + [Hu2] 3.3 |

## Key audit finding (the heart of the re-route)

- `presheafValue_flat_of_unitDatum_faithful (P) (f : A)` is ALREADY the clean route: arbitrary
  `f`, no LL, no `h_pb`, via `unitDatum_quotEquiv` (comparison iso `𝒪(unitDatum P f) ≅
  A⟨X⟩/(f-X)`) + `lemma_8_31_fSubX_flat`.
- The Leaf-A flatness chain (`cor_8_32_productRestriction_faithfullyFlat` →
  `prop_8_30_imagePiece_assembled` → `flat_chainStep_domUnit` → `flat_imagePieceDatum_domUnit`)
  is sorry-free in its BODIES but threads `h_pb` (u/s ∈ B⁺) + `haveI := hasLocLiftPowerBounded_faithful`.
  The `h_pb`/LL are used to bridge `imagePieceDatum {g,u} s` (two-element piece) to `unitDatum gg`
  (gg = u/s) via `imagePieceDatum_domUnit_rationalOpen_eq` + a `restrictionMapHom` iso.
- `prop_8_30_basic_laurent_step_flat` is the OTHER per-step (construction-level power-boundedness,
  LL-free flatness) but requires `D'.T ⊆ E.P.A₀` (the too-narrow "numerator in ring of definition"
  — exactly the reviewer's criticism), so the chain does NOT use it.

## Changes applied

- Tickets/board updated (see task tracker): IRIE direction VALIDATED; §8.1 boundedness CONFIRMED
  as over-strong; LL-bdd + general valuative criterion reclassified as off-the-Leaf-A-flatness-path.
- Re-route ticket added: rebuild the Remark 7.55 chain on `presheafValue_flat_of_unitDatum_faithful`
  (arbitrary-f, LL-free) so Leaf-A flatness drops `h_pb`/LL/[Hu2] 3.3/IRIE-boundedness deps.

## Decisions recorded

- §8.1 boundedness: keep `B⁺ ⊆ B°` (power-bounded) as the IRIE axiom for the affinoid/Spa-point
  role; never uniform IsBounded. Off the Leaf-A flatness path.
- General LL-bdd / valuative criterion: future infrastructure via Wedhorn 7.18 (non-domain), not
  minimal-prime; do not block Prop 8.30 on it.

## Open questions remaining

- None unanswered by the reviewer (Q1–Q5 all addressed). New internal question surfaced: is the
  Remark 7.55 chain's `imagePieceDatum` (two-element) genuinely a single basic Laurent step, or
  does the re-wire require re-encoding the chain with one-element `unitDatum` steps?
