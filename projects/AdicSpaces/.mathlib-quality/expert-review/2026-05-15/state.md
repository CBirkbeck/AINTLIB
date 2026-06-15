# Expert-review session state

- Generated: 2026-05-15
- Audience: ChatGPT Pro (round 6)
- Goal of brief: Soundness check on the W1–W4 lemma statements — verify that they correctly capture Wedhorn 8.34's content before we attempt proofs
- Scope: Just the W1–W4 lemma statements + their correspondence to Wedhorn 8.34 steps + four architectural questions
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §8 of the brief) |
|---|------------------------------------------|
| Q0 | Are the four lemma statements W1, W2, W3, W4 correctly stated to capture Wedhorn 8.34's actual content? In particular, is the conjunction (W1 → W2 → W3 → W4 → W5 → I.1) a faithful Lean translation of Wedhorn's textbook argument? |
| Q1 | Should W2's `s : Aˣ` be required to be Cor 7.32's dominating unit (with the additional clause "for all v ∈ Spa A A⁺, ∃ f ∈ S with v(s) < v(f)"), or is the existential form sufficient for the downstream W3? |
| Q2 | Wedhorn's Step (iii) refines a unit-generated cover by a Laurent cover of unit ratios f_i f_j⁻¹. These ratios live in 𝒪_X(L), not in A. Which Lean encoding of W3's inner tree is preferable: (a) a relative-labels `RatioLaurentTree` type whose splits live in the running presheaf value, or (b) an absolute denominator-cleared formulation where each ratio split at f_i f_j⁻¹ is encoded as an A-level rational subset transformation with a modified denominator? |
| Q3 | Is W4's statement as written — quantifying over abstract `inner_of` functions — provable, or does the lemma genuinely need to specialise to the canonical W3 inner-tree construction? |
| Q4 | Is the W1–W5 graft architecture (option (a) in round-5 terms) the right path for `IsSheafy A`, or should we pivot to option (c) and formalise Wedhorn's Proposition A.3 (1) directly at the IsInducing level? |

## Ticket-board snapshot at brief time

The project's `.mathlib-quality/tickets.md` carries the round-5 ticket
list with the round-6 progress note appended (= 7 of 9 residuals closed
axiom-clean; W5 extracted from I.4; W1–W4 + V.1 remaining).

Closed residuals (axiom-clean): V.2, III.1, III.2, III.3, I.2, I.3, I.4, II.1, II.2, IV.1.
Closed structural helper (axiom-clean): W5 (`graftAt_allNodesDisjoint`).
Closed headlines (modulo W1–W4 + V.1 transitive sorries): I.1 (`exists_wedhorn_laurent_refinement_tree`), `tateAcyclicityComplete`, `isSheafyComplete`.

## Stuck points (= W1–W4 statements)

1. W1 `exists_standard_cover_refining` — Standard cover existence for arbitrary C (input to Wedhorn 8.34 Step (ii)).
2. W2 `exists_first_stage_laurent_tree_full` — First-stage Laurent tree on s⁻¹·S with allSplitsInducing + allNodesDisjoint + σ-minus unit property (Wedhorn 8.34 Step (i)+(ii)).
3. W3 `exists_inner_ratio_laurent_tree_refining_C` — Inner ratio Laurent tree at each first-stage leaf with Refines L C + inducing + disjointness (Wedhorn 8.34 Step (iii)).
4. W4 `inner_ratio_trees_cross_leaf_disjoint` — Cross-leaf disjointness of canonical W3 inner trees (Lean-formalisation-specific structural property).

## Reference list (from §2.2 of brief)

- [Wed19] Wedhorn, *Adic Spaces* (arXiv:1910.05934)
- [Hub94] Huber, *A generalization of formal schemes and rigid analytic varieties*
- [Hüb21] Hübner, *Adic Tate twists and Iwasawa cohomology*
- [Stacks 023N] (closed)
- [Stacks 00MA] (V.1, external Mathlib gap)
