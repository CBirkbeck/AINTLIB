# Expert-review session state (round 4)

- Generated: 2026-05-26T11:45:00Z
- Audience: Senior algebraic geometer / Huber–Wedhorn expert (same as rounds 1–3)
- Goal of brief: Specific blocker — Route C / Banach OMT sigma-compactness obstruction. After Round-3 recommended Route C as the next sprint, we implemented the Route C scaffold (section equalizer object, closedness, completeness, continuity, bijectivity) and hit a precise mathematical blocker on the final open-mapping step. We need architectural guidance on resolution.
- Scope: Whole sheafiness target (re-stated for self-containment). Length: extended (~9 pages).
- Reply received: true (2026-05-26T12:30:00Z)
- Reply integrated: true (2026-05-26T12:35:00Z)

## Questions in the brief

| # | Question (summary) |
|---|--------------------|
| Q1 | Is adding `[SigmaCompactSpace A]` to the keystone acceptable? What examples of strongly noetherian Tate rings (Tate algebras over Q_p, Z_p-affinoids, perfectoid-pre) are sigma-compact vs not? |
| Q2 | Is `[SeparableSpace A]` (weaker) acceptable? Polish⇒Lindelöf⇒countable subcover suffices for Bourbaki OMT, replacing sigma-compactness. |
| Q3 | Is writing a Bourbaki-form Baire-based Banach OMT in the project the right move? (~200 LOC, keeps keystone signature pristine.) Sub-questions: (i) does a published formal statement exist anywhere? (ii) are there subtle mathematical reasons Bourbaki form is harder/shakier than sigma-compact form? |
| Q4 | Is there a different OMT route entirely? (Metric-based, Stacks-style direct topological inducing, Wedhorn 6.18 internal route?) |
| Q5 | If Route B fallback is the right answer, which residual sigma-walk sub-sorries (W1, W2, W3, I.1 in our labelling) to attack first? |
| Q6 | Meta: should we be faithfully translating Wedhorn/Huber's arguments, or re-deriving the bridge with whatever proof technology is cleanest in Lean? |

## Ticket-board snapshot at brief time

### Route C tickets (added 2026-05-26)
- `route-c-refactor` — done (file refactor moved Route C block past algebraic acyclicity)
- `productRestrictionSubToEqualizer_injective` — done (via tateAcyclicity_separation_via_cor832 / Cor 8.32)
- `productRestrictionSubToEqualizer_surjective` — done (via tateAcyclicity_gluing_via_descent / Stacks 023N)
- `presheafValue_uniformity_isCountablyGenerated` — done (via locBasis ℕ-indexed nhds + IsUniformAddGroup + Completion metric)
- `presheafValue_sigmaCompactSpace` — **B2** (statement false; counterexample ℂ((t)); see `b2_log.jsonl`)
- `sectionEqualizer_uniformity_isCountablyGenerated` — done (via Finite product + subspace)
- `productRestrictionSub_isInducing_tate_empty` — partial (s=0 case proven; s≠0+empty impossible-in-practice, needs extra typeclasses)

### Other open tickets
- `T-OV-1-DENSITY` — Lane A reverse round trip; blocked on T-IDEAL-2
- `T-WEDHORN-618-L3-617` — Wedhorn 6.17; marked structurally done (real proof body, transitive sorry in different ticket)
- `T-WEDHORN-618-L4-618` — Wedhorn 6.18; partial (wedhorn_6_18_unique still sorry'd as B2 false)
- `T-WEDHORN-618-L5-AUDIT` — open, blocked on L4-618
- `T-WEDHORN-618-L6-CLEANWRAPS` — open, blocked on L5

## Stuck points (from §8 of brief)

1. **§8.1 Keystone blocker (the main ask):** Route C's final step needs Banach OMT, mathlib's only variant requires sigma-compactness, sigma-compactness of presheafValue D is mathematically false from the keystone hypothesis set. Counterexample ℂ((t)). Four resolutions: (a) add [SigmaCompactSpace A], (b) add [SeparableSpace A], (c) write Bourbaki-form Baire OMT in-project, (d) switch back to Route B.
2. **§8.2 Empty-cover edge case:** s ≠ 0 + empty cover branch needs extra typeclasses; consumer case-splits on s=0 upstream so branch is unreached. Benign; not asking the reviewer about it.
3. **§8.3 Ruled out:** Route A (algebraic only) insufficient; Round-1 verdict confirmed Round-3.

## Reference list (from §2.2 of brief)

- [Wed19] Wedhorn, *Adic Spaces*, arXiv:1910.05934v1
- [Hu1] Huber, "Continuous valuations", Math. Z. 212 (1993)
- [Hu2] Huber, "A generalization of formal schemes and rigid analytic varieties", Math. Z. 217 (1994)
- [Hu3] Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Aspects of Mathematics E30, Vieweg 1996
- [Bou-TG] Bourbaki, *Topologie Générale* Ch III §3 no. 3 Théorème 1
- [BGR84] Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer 1984
- [Hüb16] Hübner (incomplete reference; full title not in our notes)
