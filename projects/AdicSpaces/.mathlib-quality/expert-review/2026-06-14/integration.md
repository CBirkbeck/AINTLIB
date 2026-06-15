# Reply integration — 2026-06-14

Reply received 2026-06-14 (pasted in session). Brief: ./brief.md. Reply: ./reply.md.

## Interpretation summary

- **(LL) obstruction confirmed real** (Q1): it is "stability of the structure-presheaf under
  rational localization in case (b)"; not a Wedhorn flaw. Transporting back to `A` is the same
  theorem renamed — do NOT dodge it.
- **Faithful (LL) route is valuative** (Q2): `Spa(𝒪(D'))≃rationalOpen(D')` + 7.52(2) unit
  criterion (LL-unit) + 7.52(1)/7.18 bounded criterion (LL-bdd). NOT via `A⟨X⟩/I`.
- **Prop 7.51(2) construction corrected** (Q3): use Prop 7.49 (`A/𝔪` Hausdorff+nonzero ⟹
  `Spa(A/𝔪)≠∅`), NOT the trivial valuation (continuous only if `𝔪` open) and NOT a rank-1
  constructor.
- **Pettis-lift unnecessary** (Q4): apply OMT to `𝒪(U)→equalizer E`, not the full product.
  CAUTION: the OMT (Thm 5.5) statement may be overgeneral/false without a Tate-absorption /
  zero-sequence-of-units hypothesis — audit it.
- **Decomposition faithful; order confirmed** (Q5): Spa-comparison/7.52 → faithful (LL) →
  Leaf A → Leaf C → Leaf B.

## Reconciliation with current code (verified this session)

- 7.52(2) unit criterion (`isUnit_iff_forall_not_vle_zero_of_complete`, in the Lemma-7.45 file)
  is **landed sorry-free** — the (LL-unit) tool already exists.
- Spa comparison `Spa(𝒪(D))≃rationalOpen(D)` is **substantially built** (⊇ direction compiles;
  a few residual sorries on the full equiv).
- Prop 7.51(2) (`exists_spa_point_supp_eq_maxIdeal_of_complete`) is a **bare sorry** — needs the
  corrected 7.49 route.
- NET: faithful (LL) is materially **less deep** than the pre-review feasibility map estimated;
  it runs on existing infrastructure rather than a domain-requiring keystone.

## Changes applied (tasks created)

- #63 Step 1 — Spa(𝒪(D))≃rationalOpen(D) sorry-free [central theorem]
- #64 Step 2 — (LL-unit) via 7.52(2)            [blockedBy #63]
- #65 Step 3 — (LL-bdd) valuative lemma          [blockedBy #63]
- #66 Step 4 — assemble faithful (LL)            [blockedBy #64,#65]
- #67 Step 5 — fold Remark 7.55 chain = Leaf A   [blockedBy #66]
- #68 Side  — Prop 7.51(2) via 7.49 (corrected)
- #69 Risk  — audit OMT statement before Leaf B
- #70 Leaf B (equalizer+OMT) & Leaf C (Čech grind) [blockedBy #69]

User directive: work the spine **steps 1→2→3→4 in order**, in-session.

## Decisions recorded

- Drop the "transport back to A" sidestep idea for Leaf A (reviewer: same theorem renamed).
- Drop the trivial-valuation plan for Prop 7.51(2); adopt the 7.49 route.
- Do NOT create a separate Pettis-lift task; instead audit the OMT statement (#69) and apply it
  to the equalizer.

## Open questions remaining

None unanswered — the reviewer addressed all five (Q1–Q5).

## Updates to the feasibility map / memory

`docs/SHEAFY-FEASIBILITY-MAP.md` and the `project_sheafy_feasibility_map` memory should be read
WITH this integration: keystone K1 (faithful (LL)) is now downgraded from "deep, bottoms at
domain-requiring Nullstellensatz" to "valuative, on mostly-existing infrastructure"; K2's route
is corrected (7.49, not trivial valuation); K3 (OMT) needs a statement audit, not a Pettis task.
