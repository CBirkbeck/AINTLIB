# Reply integration — 2026-06-09 (gluing-leaf relativization fork)

Reply received from senior adic-spaces expert on 2026-06-09.
Brief: ./brief.md   Reply: ./reply.md

## Interpretation summary

Reviewer's verdict is decisive and high-confidence: **Route R2** (instantiate the absolute
`O_X`-acyclicity engine at `B := presheafValue U = O_X(U)`, transport back along `Spa(B) ≅ U`) is the
mathematically correct, Wedhorn-intended route. Route R1 (bespoke relative `IsGeneratedBy` theory) is
explicitly discouraged as duplication. The route rests on Wedhorn **Prop 8.2** (homeomorphism +
rational-subset bijection), **Remark 8.4** (section-ring iso = Čech-complex compatibility), **Prop
8.16** (the affinoid-pair identification, fixing `B⁺`). Q2: `B⁺ = O_X⁺(U) = {b : v(b)≤1 ∀v∈U} =`
int. closure of `A⁺`-image **together with T/s**. Q3: only `B` complete needed (free); `[CompleteSpace
A]` is assumed, so no extra issue. Q4: no clean avoidance — `{R(T/t)∩U}` IS the relative cover. Q5:
long pole = Lemma 8.33 / Examples 6.38–6.39 (analytic quotient identification), then Cor 7.32, then
Lemma 7.54 (least deep, but do first if it blocks the formal statement).

Reconciliation: no drift (brief generated same session). Bonus — the point-level Prop-8.2 bijection
already exists in `SpaPresheafValueEquivalence` (`_sub_lemma_C3_main_bijection`,
`exists_spa_presheafValue_of_rationalOpen`, `spa_completion_of_spa_localization`), so R2's foundation
is partly laid.

## Changes applied (to .mathlib-quality/tickets.md)

- Added the **★ R2 RELATIVIZATION** block (R2 committed; 6 transport-layer tickets T-R2-PLUSSUB /
  -HOMEO / -COVER-TRANSPORT / -SECTION-COMPAT / -ACYCLIC-TRANSPORT / -WIRE; analytic-leaf priority
  8.33 → 7.32 → 7.54; design notes for Q2/Q3).
- Marked the G6-reroute roadmap line **SUPERSEDED by R2** (bespoke relative-7.54 / T-CECH-754-REL
  dropped — reviewer: do not build a duplicate relative theory).
- `T-754-REROUTE` resolution re-pointed to R2 (resolved by T-R2-WIRE, not relative-7.54).

## Changes rejected by user
- (none) — user approved all.

## Open questions remaining
- (none unanswered — reviewer addressed all of Q1–Q5.)

## Decisions recorded
- Route = R2 (instantiate at B, transport back). Bespoke relative theory dropped.
- `B⁺ = O_X⁺(U)` per Prop 8.16 (int. closure of A⁺-image + T/s).
- Completeness: only B-complete needed; [CompleteSpace A] assumed.
- De-risk order for analytic leaves: 8.33 → Cor 7.32 → 7.54.
