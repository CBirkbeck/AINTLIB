# Expert-review session state

- Generated: 2026-05-27T16:30:00Z
- Audience: Senior expert in adic spaces / rigid analytic geometry (Huber–Wedhorn area)
- Goal of brief: Strategic guidance on the IsSheafy critical path
- Scope: Wide — full project state with both Round-7 ticket-statement defects highlighted
- Length: Generous (≈7,500 words, ~14 pages)
- Reply received: true (2026-05-27)
- Reply integrated: true (2026-05-27)

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Resolution route for the Wedhorn 7.45 lift IsContinuous defect. Three candidates: (a) Adapt Lemma745.exists_spa_point_via_restrictToConvex directly. Single bigger ticket ~200 LOC; (b) Re-decompose with corrected semantics (sub-A: H + u_max ∈ H + cofinal property; sub-B: restrictToConvexBounded; sub-C: continuity discharge); (c) Park and pursue Artin-Rees instead. Which route, and is (a) safe — does the convex-subgroup pattern transfer from Chevalley-V₀ to arbitrary dominating B without extra hypotheses? |
| Q2 | Resolution route for the Hom-presheaf sheaf-condition defect. Three candidates: (a) Restate over rational-cover site only + site-comparison to full Opens; (b) Replace discrete topology placeholder by limit topology over rational covers (= repackages the goal); (c) Bypass — extract IsSheafy from (A, A+) directly without Presheaf.IsSheaf. Which is the right architectural call? Is there a fourth option (relativised sheaf via Yoneda)? |
| Q3 | Path-alpha decision: take (P, [IsNoetherianRing P.A₀]) as explicit parameter. Is this the right long-term call? Specifically: (a) Can we deduce P.A₀ = A° noetherian for the principal pair in a strongly noetherian Tate ring under additional assumptions like A+ = A°? (b) Are there Wedhorn-clean variants that bypass the noetherian-A₀ requirement entirely via a different open-mapping route? |
| Q4 | Architecture of the IsSheafy critical path. With ~70 sorries remaining on the path (Wedhorn 7.45 chain ~10, Artin-Rees chain ~5, structure sheaf ~3, Cor 8.32 leaves ~6, standard-cover ~9), is our decomposition (Cor 8.32 + flat descent for separation; standard-cover + Hübner 3.8 for gluing; Tate-absorbing OMT + restrictToConvex for inducing) the right one? Alternative architecture (Huber 1994 original, or more direct sheafification) that would replace several sorries with a deeper theorem? |
| Q5 | Is the convex-subgroup restrictToConvex pattern (Lemma745) really the canonical route for Spa-point construction from a non-open prime? The Lemma745 proof is ~500 LOC; Wedhorn 7.45 in the textbook is ~1 page. Alternative Spa-point construction (Chevalley extension directly, without convex-subgroup) that would be more Lean-friendly? |
| Q6 | Where does the strongly noetherian Tate hypothesis genuinely bite? We use it in LocalBasisHyp (Hübner 3.8 / Wedhorn 8.34), productRestriction_faithfullyFlat_tate (locSubring noetherianness), and Banach OMT applications. Is each use tight, or could we relax to noetherian + a topological condition (σ-compact)? |
| Q7 | References — anything we are missing? Currently integrated Wedhorn 2019, Huber 1994, BGR, Henkel 2014, Hübner, Zavyalov, Stacks 023N. Other treatments of Wedhorn 8.28(b) (SGA, perfectoid-spaces literature, Bhatt–Scholze) that would suggest a different decomposition or fill in a key step? |

## Ticket-board snapshot at brief time

**Critical-path tickets (sheafy / Wedhorn 8.28(b)):**

| Ticket | Status |
|---|---|
| T-PETTIS-PROP-1-10 | DONE (Henkel Prop 1.10, ~115 LOC) |
| T-ROUTE-C-OMT (Tate-absorbing OMT) | DONE (axiom-clean) |
| T-ROUTE-C-WIRE | DONE |
| T-AR-1 (Artin-Rees in Localization.Away) | DONE (this session) |
| T-AR-2 (radical-relation denominator lift) | DONE (this session) |
| T-SP-SHEAF-A (Presheaf.IsSheaf via Hom-presheaves) | DONE (this session) |
| T-AR-3 (per-n witness extraction) | OPEN (~100-150 LOC) |
| T-AR-4 (final assembly, no-Noeth) | OPEN (one-liner after T-AR-3) |
| T-LEGACY-TATEACYCLICITY-MIGRATE | OPEN (~30-caller refactor) |
| T-WED-745-CONT-A/B/C | SIGNATURE-DEFECTIVE (defect #1) |
| T-SP-SHEAF-B | SIGNATURE-DEFECTIVE (defect #2) |
| T-PRESHEAF-VALUATIONSUBRING-CHAIN | PARTIAL (4/5 sub-conditions done) |
| T-PRESHEAFTATE-ARTIN-REES (parent) | PARTIAL |
| T-STRUCTURESHEAF-ISSHEAF-RESIDUAL | PARTIAL (uses T-SP-SHEAF-A) |
| T-PRESHEAF-MULARCH-RANKONE | OPEN (depends on Wedhorn 4.12 — not in mathlib) |
| T-PRESHEAF-7-42-RESIDUALS | OPEN |
| T-PRESHEAF-LOCLIFT-COMPLETION | PARTIAL |
| T-PRESHEAF-SPA-NONOPEN | OPEN |

**Total sorries:** ~125 (down from 136 at session start). About 70 on IsSheafy critical path.

## Stuck points (from §8 of brief)

1. **Defect #1** — Convex-subgroup signature for Wedhorn 7.45 lift IsContinuous (T-WED-745-CONT-A). Second conjunct "P.I-image units ∉ H" unprovable in Case A.
2. **Defect #2** — Hom-presheaf sheaf condition with discrete-topology placeholder (T-SP-SHEAF-B). Fails for infinite open covers when E is non-discrete.
3. **Defect #3 (long-standing)** — Noetherian P.A₀ from strongly noetherian Tate is false (Nagata-style counterexample). Current resolution: path alpha (explicit hypothesis).
4. **Deep Artin-Rees gap** — locLift_preimage_target_witness_existence_no_noeth (line-1788 sorry). T-AR-3 is the next step.

## Reference list (from §2.2 of brief)

- [Wedhorn 2019] — Adic Spaces, arXiv:1910.05934v1 (primary)
- [Huber 1994] — Math. Z. 217 (Lemma 2.4(i) for Tate-absorbing OMT)
- [BGR] — Non-Archimedean Analysis (§3.7.2/1 Banach OMT, §3.7.2/2 noeth iff submodules closed)
- [Henkel 2014] — arXiv:1407.5647v2 (full proof of Tate-absorbing OMT)
- [Bourbaki BTVS] — Ch. I §3 Lemma 2 (classical Cauchy-lift OMT)
- [Hübner 2021] — Lemma 3.8 (localBasisHyp content)
- [Zavyalov 2024] — §2.3 standard-cover reduction
- [Stacks Project, tag 023N] — Flat descent equalizer

## Most recent landings this session (for reviewer to know what just shipped)

1. `T-AR-1` — `artinRees_locAway` (~20 LOC, axiom-clean) — Artin-Rees specialization to `Localization.Away D₀.s`.
2. `T-AR-2` — `rad_denom_lift_in_target` (~30 LOC, axiom-clean) — radical-relation denominator lift via uniqueness of inverses.
3. `T-SP-SHEAF-A` — `isSheaf_of_homPresheaves_isSheaf` (5 LOC) — definitional unfold; refactored `structurePresheaf_isSheaf` to apply it.
4. Discovery of two SIGNATURE-DEFECTIVE tickets (T-WED-745-CONT-A chain, T-SP-SHEAF-B) — logged to b2_log entries 36, 37.
