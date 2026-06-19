# Reply integration — 2026-06-19 (4-leaf decomposition of Thm 8.28(b))

Brief: `REVIEW_BRIEF.md`. Reply: `reply.md` (this folder). All key claims source-verified
against `references/wedhorn.txt` before integrating.

## Interpretation table

| # | Reviewer point | Maps to | Type | Verified |
|---|---|---|---|---|
| 1 | Leaf #4 = Wedhorn 7.52(1)/7.18(1), hypothesis-free; the noetherian thing is the *different* density converse 7.18(3) | Q1 | direct answer; **withdraws the red flag** | ✓ `wedhorn.txt:3161,3619` — 7.52(1) is "any affinoid ring"; 7.18(3) is the only noetherian part |
| 2 | Leaf #1: corestrict ρ to closed equalizer E, apply landed Thm 6.16 (complete target+surjective⟹open); 6.18 unnecessary | Q2 | direct answer; **simplifies leaf** | ✓ Thm 6.16 landed in `BanachOMT.lean`; 6.16 statement matches |
| 3 | Leaf #2 openness automatic: `Iⁿ⊆A⁺ ⟹ IⁿA₀[T/s]` open `⊆ A⁺[T/s]` ⟹ IntCl open; then 7.47(4) | Q3 | direct answer; **confirms + supplies the gap** | ✓ matches 7.19 openness pattern |
| 4 | Leaf #3: general 7.45 enough; +1-line maximality lemma; 7.41 = the A°-bound | Q4a | direct answer; **confirms** | ✓ `wedhorn.txt:3438,3487` |
| 5 | Gluing depends on leaf #2 (relative) + leaf #3 (7.54→7.53→7.51 max-points), not #1/#4 | Q4b | concern raised; **corrects our "independent" claim** | plausible; to re-audit in code |
| 6 | Risks: (a) don't use [Hu2] 3.3(iii) for Q1; (b) don't apply 6.16 to full P (not surjective); (c) localized plus-ring must contain T/s + be integrally closed; (d) gluing not independent of #3 | all | unprompted criticism / guardrails | recorded |

UNANSWERED: none — the reviewer addressed Q1–Q4 fully.

## Changes applied (to the plan; no tickets exist yet — this was decompose-only)

- `decomposition.md`: prepended a "REVISED per /expert-review" section. Leaf #4 red flag
  withdrawn → small hypothesis-free 7.52(1) sub-leaf; leaf #1 retargeted to
  equalizer+6.16 (drop 6.18); leaf #2/#3 confirmed with the openness + maximality details;
  gluing-dependency claim corrected (leaf #3 upstream).
- Nuance recorded (honest vs reviewer's "delete leaf #4"): 7.52(1) is not yet an in-project
  lemma (only 7.52(2) is), so leaf #4 becomes a small hypothesis-free sub-leaf, not a pure
  deletion.

## Revised residual (3 leaves)

1. **Leaf #1** — `productRestriction_isEmbedding_via_equalizer_omt` (equalizer closed +
   complete + continuous-bijective + 6.16-open). MOST tractable now.
2. **Leaf #2** — `presheafValuePlus_isRingOfIntegralElements` via openness chain + 7.47(4).
3. **Leaf #3** — `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` via general 7.45 +
   7.41 + maximality.
- Former **Leaf #4** → `isPowerBounded_of_forall_spa_vle_one` = 7.52(1) (hypothesis-free
  sub-leaf) + `subset_powerBounded` wrapper. Possibly merge with leaf-#3/Cont(A) work.

## Next step

Run `/develop` (full) to turn the revised 3-leaf plan into a ticket board, then `/beastmode`.
Recommended order: leaf #1 (equalizer+6.16, tractable) → former-#4 (7.52(1)) → #3 → #2.
