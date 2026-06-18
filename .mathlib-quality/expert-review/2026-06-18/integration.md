# Reply integration — 2026-06-18

Reply received + integrated 2026-06-18. Brief: ./brief.md · Reply: ./reply.md

## Interpretation summary

| Q | Reviewer verdict | Action |
|---|---|---|
| Q1 encoding | Hybrid (a): bare `PlusSubring` carrier + `IsRingOfIntegralElements A⁺` (open+intClosed+≤A°) + `AffinoidRing` bundle; require the instance in all Spa-level theorems | refactor (steps 1-3) |
| Q2 completion affinoid | YES via Wedhorn 7.19 + 7.47 + 8.16; plus-ring = closure of `IntCl(A⁺[T/s])`, NOT closure of `A⁺` image | refactor (steps 5-6); RISK#1 confirmed present |
| Q3 exact vs containment | My maximal-ideal argument correct; containment suffices for the whole sheaf path; exact-for-nonmaximal stays separate | helper (step 8) |
| Q4 pair-free | Faithful BUT correction: "any cont. val ≤1 on A°" is FALSE higher-rank — needs HEIGHT-ONE + Prop 7.41. `A⁺⊆A₀` is a proof artifact, not a Wedhorn hypothesis | refactor 7.45 (step 4); RISK#3/4 confirmed present |
| Q5 strategy | Decomposition is the cleanest faithful route; confirmed | no change |

## Verified risks (present in current code)
1. `locPlusSubring = Subring.closure(A⁺-image ∪ {t/s})` — generated subring, NOT `IntCl(A⁺[T/s])`. (Docstring notes the subtlety; uses generated subring.)
2. (avoid) generic "A° closed ⟹ closures of power-bounded stay power-bounded" — use Lemma 7.47 instead.
3. `exists_spa_point_via_restrictToConvex` (the formalised 7.45) bounds `v` on `A⁺` via `A⁺⊆P.A₀`, NOT height-one + `A⁺⊆A°`.
4. Global typeclass churn — DON'T change the bare `PlusSubring` class; ADD `IsRingOfIntegralElements`/`AffinoidRing` and migrate Spa-level theorems.

## Changes applied
- Task #68 reframed (was B2 → in_progress): "Ring-of-integral-elements interface (A⁺⊆A°) — reviewer-approved refactor" with the 8-step plan.
- B2 on #68 RETRACTED (it was an encoding defect with a clear fix, not a false theorem). The `A⁺=⊤` "counterexample" is not a valid affinoid ring.

## Execution order (proposed)
ROIE-1 (class+bundle+instance wiring) → ROIE-2 (restate Spa-point with [IsRingOfIntegralElements], refactor 7.45 height-one, helper support_eq_maximal_of_le) → ROIE-3 (IntCl plus-ring for rational loc, presheafValue_plus_isRingOfIntegralElements, Prop 7.19+7.47) → ROIE-4 (remove CompatiblePlusSubring from inner path, rerun Leaf A′).

## Open / not actioned
- The faithful re-wiring (commit 27b16d7) stands; ROIE-4 will further clean its inner-path CompatiblePlusSubring use.
- Leaf B inducing-half (6.18) + Leaf C R2-transport unaffected by this refactor.
