# Decomposition — WP (weighted-parity rationally-stably-reduced example)

Companion artifacts: `paper-extraction.md` (Step-1 prose proofs with verbatim [WP]
quotes and tex line locators — the per-leaf source quotes live THERE, keyed by the
tex labels cited in each skeleton docstring), `plan.md` (API design), and the **Lean
skeleton** under `projects/AdicSpaces/Adic spaces/WP/` — the canonical statement of
every leaf, each docstring carrying its [WP] label/line locator.

## Skeleton location (all `lake build` green, sorries only — verified 2026-07-28)

| File | Content | Sorries |
|---|---|---|
| `WP/Weight.lean` | ω, S, heads, tails, exponent splitting (§6.1/§6.4 combinatorics) | 21 |
| `WP/RestrictedComplete.lean` | infinite-σ completeness + radius-1 coefficient API | 8 |
| `WP/Algebra.lean` | 𝒜 = wpSupport, instance stack, monomials, ϖ-bundle | 27 |
| `WP/UniformDomain.lean` | Gauss multiplicativity, 𝒜°=𝒜₀, uniform, domain | 8 |
| `WP/Nonnoetherian.lean` | ψ_m, ideal chain | 5 |
| `WP/Heads.lean` | heads, noetherian/strongly noetherian/sheafy, density | 34 |
| `WP/Tail.lean` | tailCoeff, ρ_N, e_μ, TailC0, Φ | 33 |
| `WP/Perturbation.lean` | pod-independence, PerturbSetup, small perturbation | 14 |
| `WP/Evaluation.lean` | nonarch summability, restrictedEval | 6 |
| `WP/CoeffLocalization.lean` | QHead, head bridge, coeffLocEquiv, HeadModelData | 20 |
| `WP/Reduced.lean` | MvPowerSeries reduced, W-regularity, HeadLocsReduced, ChainReduced | 6 |
| `WP/Chart.lean` | chart datum/model, domain, nonuniform, ¬stably-uniform | 11 |
| `WP/Sheafy.lean` | embedding/gluing fields, wrappers, strong sheafiness | 6 |
| `WP/Main.lean` | headline endpoints at w = id (+ `_of_dvr`) | 0 |

## Result tree (per top-level endpoint; leaves = skeleton decls)

Numbering: E1–E4 = [WP] thm 6.2 (1)–(4). Internal nodes cite the paper's own proof
(locators in `paper-extraction.md`). Every leaf's Lean statement is in the skeleton;
its verbatim source quote is in `paper-extraction.md` under the cited section.

### E1 uniform / domain / nonnoetherian / 𝒜°=𝒜₀  ([WP] prop:parity-uniform-domain 789–811, prop:parity-nonnoetherian 813–834)

- Combinatorial base (leaves, elementary Finsupp): `wpWeight_*`, `WPMem.*`,
  `HeadMem.*`, `tailIdxSubmonoid`, `tailShift/headPart/tailPart` + splitting laws
  (Weight.lean). Discharge: `Finsupp.filter/update` API (verified present:
  `filter_apply/support_filter/filter_add_filter_not/prod_filter_mul_prod_filter_not`,
  Mathlib Data/Finsupp/Basic).
- Analytic base: `isCompleteSpace_general` (port of univariate
  `Restricted.isCompleteSpace`, CoramRestrictedNorm:257 — recon: "port is ~120 lines,
  mechanical"); `normOneClass_one`; coefficient API (norm_coeff_le/continuity/finite
  superlevel — generalize RestrictedGaussAdic:199/207); `isClosed_setOf_coeff_eq_zero`
  (pattern RestrictedLaurent:765).
- 𝒜 construction: `wpSupport` closure fields (mul via `MvPowerSeries.coeff_mul`
  antidiagonal + `WPMem.add`); `isClosed_wpSupport`; instances (NormOneClass;
  constA/norm_constA_mul — pattern JetRings:521/535; piW bundle; IsHuberRing/IsTateRing
  via `FiniteJet.isHuberRing_of_scale` ✓ real bodies already; unconditional instances
  via `exists_norm_window` — pattern Functoriality:160; PlusSubring +
  IsRingOfIntegralElements via `powerBoundedSubring.toSubring` +
  `isRingOfIntegralElements_powerBounded` FiniteJetRings:868).
- Uniform/domain: `norm_amb_mul` (via vendored `isAbsoluteValue`,
  CoramMvRestrictedNorm:270, at LinearOrder ℕ, hnorm := `norm_mul` of the field);
  `norm_wpa_mul` (isometric subring restriction); `isPowerBounded_wpa_iff`
  (pattern UniformDomain:127); `isUniform_WPA`; `Nontrivial/NoZeroDivisors` (pattern
  UniformDomain:72-99); `powerBoundedSubring_eq_unitBall`.
- Nonnoetherian: `psiHom` (monoid partial character; route change documented in the
  file header — the paper's finite-stage compatible family is replaced by the direct
  coefficientwise definition; multiplicativity = complement-is-monoid-ideal, using
  `hw : w n ≥ 1`); `Za_succ_notMem_span`; `not_isNoetherianRing_WPA` (strict chain ⇒
  ¬noetherian; mathlib `IsNoetherianRing` wf characterization).

### E2 (strongly) sheafy  ([WP] thm:parity-strongly-sheafy 1131–1237)

- Heads (internal node; [WP] lem:finite-stage-normal-form 739–787 — DOCUMENTED ROUTE
  CHANGE: support subalgebra + free T_N-module instead of the quotient presentation;
  same downstream interface, FJP-divergence-style):
  `wpHeadSupport` + instances; `wpEvenSupport` (T_N); `evenSupportEquiv` (exponent
  halving reindex → `P K (N+1)`, isometric); `moduleFinite_head_over_even` (the
  rank-2^N normal form eq:parity-factorization); `isNoetherianRing_WPHead`
  (`IsNoetherianRing.of_finite` ✓ verified + FJP `Uniformizer.isNoetherianRing_P`);
  `isNoetherianRing_unitBall_WPHead` (+ FJP `isNoetherianRing_unitBall_of_section`
  transfer, FiniteJetNoetherianVertices:311); `isStronglyNoetherian_WPHead`
  (same finite-module argument for every Tate-variable count — B2-guard: NEVER from
  bare noetherianity; via `restrictedGaussEquiv` bridge ExampleUnitDisc:112 +
  nested-restricted flattening); `isSheafy_WPHead`
  (`isSheafy_of_stronglyNoetherian_828b` ✓ delivered); `exists_head_approx` (density,
  eq:A-completion-of-heads — truncation).
- Tail decomposition ([WP] §6.4 1014–1034): `tailCoeff` + norm/null/injective laws
  (coefficient regrouping via Weight.lean splitting); `eTail`, `eTail_mul`
  (eq:tail-multiplication; disjoint additivity); `rhoHead` (algebra retraction —
  monoid-ideal argument as for ψ); `WaHead`.
- `TailC0` (the ⊕̂^{c₀} receptacle): CommRing/NormedCommRing/Ultra/Complete/NormOne
  instances (twisted convolution; associativity = twist-cocycle identity; completeness
  = same c₀ argument as `isCompleteSpace_general`); `coeff/single/ofHead/toHead` API.
- Perturbation ([WP] lem:small-perturbation 949–1010): `PerturbSetup.datum`
  (+`genPiece_hopen` ✓ RelativePieceKeystone:88), `datum_isRational` (1-unit trick),
  `rationalOpen_datum` (vle-calculus at Spa points), `equiv` (+continuity,
  canonicalMap) — universal-property double lift; `exists_integral_bezout`;
  `podCongrEquiv` (pod-independence — SEARCH FIRST CompletionModelIndependence).
- Evaluation gadget: `summable_of_tendsto_cofinite_nonarch` (SEARCH FIRST
  Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean); `restrictedEval` + C/X/
  continuity/uniqueness (Huber (1.2); generic `chartEval`).
- Coefficientwise localization ([WP] prop:coefficientwise-localization 1036–1095):
  `datumEnum/headGraphRel/QHead` + normed-quotient instances (closed graph ideal =
  `isClosed_graphIdeal` FiniteJetGraphKoszul:1303 at the head; quotient norm — mathlib
  normed-group quotient; SEARCH Analysis.Normed for the ring version); `rhoQ`;
  `headLocEquiv` (+cont): fwd = `IsLocalization.Away.lift` (s unit in QHead by Bezout
  trick) + completion extension via `locTopology`-continuity (FJP chartFwd pattern
  Chart.lean:796); rev = `restrictedEval` at T_i ↦ divByS(t_i) (power-bounded ✓ via
  HasLocLift layer); `liftDatum` + laws; `coeffLocEquiv` (+cont, canonicalMap-compat):
  the c₀-closedness of the graph ideal over 𝒜 via `exists_d1_lift_pow` ✓ delivered
  (KoszulStrictClosed:254) at E := WPHead (needs `isNoetherianRing_unitBall_WPHead` +
  `IsNoetherianRing (P (WPHead) m)` — from `isStronglyNoetherian_WPHead`);
  `TailC0.map` functoriality; `HeadModelData` + `nonempty_headModelData`
  (cor:finite-head-presentation 1097–1127: Bezout-scale → head-approximate →
  perturb → ρ_N-retract Bezout → coeffLocEquiv ∘ perturbEquiv ∘ podCongrEquiv).
- Sheafiness assembly ([WP] proof of thm:parity-strongly-sheafy 1135–1237):
  `productRestrictionSub_isEmbedding_WPA` + `gluing_WPA` (the two IsSheafy fields;
  head-Čech with bounded inverse via `isInducing_of_closedRange_of_topNilpUnit`
  WedhornBanachTheorem:437 + `sectionEqualizer_isClosed` StructureSheaf:271 +
  `presheafValue_uniformity_isCountablyGenerated` StructureSheaf:309, all ✓
  delivered; the split-surjection Spa cover-transfer eq:split-spectrum-map;
  coefficientwise gluing bound eq:coefficientwise-gluing-bound); `isSheafy_WPA`
  (assembly — REAL body already); wrappers `wpPlus/wp_isSheafyFor/-Complete/-For_all/
  wp_structurePresheaf_isSheaf_all` (verbatim FJP wrapper route:
  `isLimitSheaf_of_isSheafy` SheafyPair:550, `isSheafyFor_iff_isSheafyComplete`
  RelativeStandardRefinement:201, `isSheafyFor_structurePresheaf_isSheaf`
  SheafyEndpoints:53 — all ✓ delivered).
- Strong sheafiness: `isSheafy_WPA_shiftWeight` (REAL body — instance of the
  w-uniform theorem); `wp_stronglySheafy` (REAL body); `tateExtEquiv` (the
  nested-vs-flat Fubini/reindex bridge — the ONLY genuinely new plumbing; its
  bicontinuity statement deferred to ticket, needs `mvTateAlgebraTopology'`).

### E4 chart ([WP] §6.2 836–943) — N = 0 instance of the E2 machinery

- `chartHeadDatum` (+T/s/isRational — span-top from `isUnit_piHead`);
  `chartDatum := liftDatum chartHeadDatum` (REAL body);
- `chartQHeadEquiv : QHead(chart) ≅ K⟨X⟩` (+norm) — the univariate rescale W ↦ ϖX
  ([WP] prop:weighted-chart-identification 857–910; its split section q₀/s and
  division identity D(M) 885–905 realize the ISOMETRY; in the model the weighted
  norm eq:weighted-chart-norm is definitional — divergence note: the paper's ℬ₀
  coordinates relate by b = ϖ^{ω}·(model coordinate));
- `isDomain_chartQHead` (Gauss multiplicativity of P K 1); `isDomain_chart`
  (Φ-embedding `isDomain_tailC0` + `tailC0ToMvPowerSeries_injective` + mathlib
  `NoZeroDivisors (MvPowerSeries σ R)` ✓ verified NoZeroDivisors.lean:141);
- `not_isUniform_chartModel` ([WP] eq:Tn-power-norms 933–943: T_n = single δ_n ϖ^{−w n},
  power-bounded via even/odd norm computation, family unbounded needs hwu);
  `not_isUniform_chart` (transport along coeffLocEquiv — `isUniform_of_ringEquiv`
  FiniteJetChart:1537 ✓); `not_isStablyUniform_WPA` (REAL body — IsStablyUniform's
  single field at chartDatum, no IsRational needed ✓ recon); `isReduced_chart`
  (domain ⇒ reduced).

### E3 rationally stably reduced ([WP] §6.6 1239–1297) — conditional + HRW

- `mvPowerSeriesPi`, `exists_injective_pi_quotient` (`nilradical_eq_sInf` ✓,
  `nilradical_eq_zero` ✓), `isReduced_mvPowerSeries` (composition with
  `isReduced_of_injective` ✓, `IsReduced (∀ i, R i)` ✓ Nilpotent/Defs:134,
  MvPowerSeries NoZeroDivisors ✓) — lem:formal-series-reduced, mathlib-grade.
- `rhoQ_regular` (`prop_8_30_flat_clean_proof` ✓ AuditCleanWrappers:113 +
  `Module.Flat.rTensor_preserves_injective_linearMap` ✓ + head domain; NOTE 8.30 is
  stated between presheafValues — a transport through `headLocEquiv` is part of the
  ticket).
- `tailC0ToMvPowerSeries` (+injective, `isReduced_tailC0`, `isDomain_tailC0`) — the
  Φ-embedding ([WP] eq:formal-embedding 1286–1291; multiplicativity = twist
  absorption).
- `HeadLocsReduced` (THE WALL, quarantined; sub-campaign below);
  `isReduced_presheafValue_WPA` (conditional single step);
  `ChainReduced` + `chainReduced_WPA` (iterated form; induction invariant =
  finite-head class; needs a datum/model transport lemma along bicontinuous ring
  isos — ticketed).

### HRW sub-campaign (API gap with its own tree — NOT ticketed yet)

Goal: `HeadLocsReduced K w` — IsReduced (presheafValue DH) for every rational DH on
every head. Classical source: BGR 7.3.2/10 (+ Kedlaya AWS Rk 1.2.16) — cited by [WP]
at 1276–1277 as a black box; NO formalization exists anywhere (verified: no IsReduced
theory for affinoids in mathlib or project). Candidate routes (to be adjudicated with
the ChatGPT 5.6 consult before tickets are cut):
(a) Serre-flavoured: heads are complete intersections over T_N; localizations
    noetherian + flat; needs CM/S₁ + R₀ theory — mathlib has neither CM nor Serre
    R₀+S₁; heavy.
(b) char ≠ 2 generic étaleness of the quadratic tower — FAILS in char 2 (y²−c
    inseparable); partial-result option only.
(c) Uniformity route (reduced classical affinoid ⇒ stably uniform): needs sup-norm
    theory/Noether normalization — the full classical package; heaviest but the
    literature-standard.
(d) Concrete monomial route exploiting the explicit support model of the heads
    (quotient-norm power-multiplicativity criterion at the graph presentation) —
    speculative; ChatGPT consult question.
Until adjudicated, E3 ships conditionally (`hred : HeadLocsReduced K w` hypothesis).
This matches the staging requirement: E1/E2/E4 have NO dependence on HRW.

## Adversarial log (focused on the load-bearing/risky nodes; routine leaves follow
verified FJP patterns and their attack surface is the pattern citation itself)

- **Weight/monoid layer**: attacked via edge cases — ν with overlapping vs disjoint
  supports (subadditivity strict vs equal: 2·δ_n case gives ω = 0 — caught and
  encoded as `wpWeight_add_two_nsmul`); `shiftWeight w 0 = w` FALSE at index 0 —
  caught during skeleton writing, restated through `wpWeight_shiftWeight_zero`.
  SURVIVED (with two statements corrected).
- **TailC0 ring structure**: attacked associativity of the twisted product — the
  twist cocycle [ω(μ)+ω(λ)−ω(μ+λ)] + [ω(μ+λ)+ω(τ)−ω(μ+λ+τ)] is symmetric in
  (μ,λ,τ) — verified by hand; c₀-closure under convolution REQUIRES ‖ρ‖ ≤ 1 (twist
  powers unbounded otherwise) — caught, encoded in `TwistElem.norm_le_one`. SURVIVED.
- **Chart-as-TailC0**: attacked the norm bookkeeping — first attempt ("T_n has
  coordinate X^n, norm 1 — contradicts the paper") was WRONG: the correct coordinate
  is ϖ^{−w n}·1 and the twisted product reproduces eq:Tn-power-norms exactly
  (T_n² = single(2δ_n, X^{2n}·(unit)) of norm 1 ✓, T_n^{2r+1} of norm |ϖ|^{−n} ✓).
  Match with the paper's ℬ verified coefficientwise (b = ϖ^ω · model coordinate).
  SURVIVED after correction — recorded because it is exactly the subtle point.
- **ψ_m multiplicativity**: attacked with the cross-term U^odd·U^odd = U^even
  ("partial character not multiplicative?") — resolved: odd U_{m+1}-exponent forces
  W-content (a ≥ w(m+1) ≥ 1) inside S, so such monomials are killed anyway and their
  products keep W-content; requires the `hw` positivity hypothesis — encoded.
  SURVIVED (hypothesis surfaced).
- **8.30 usage for W-regularity**: attacked the interface — 8.30 is
  presheafValue-to-presheafValue flatness with a restriction map, NOT literally
  "algebraMap 𝒜_N → QHead flat"; the ticket routes through headLocEquiv transport +
  the global datum (`globalLocData` ✓ Presheaf:1141). PLAUSIBLE-with-adapter;
  flagged in the ticket sketch.
- **`IsStablyUniform` refutation**: attacked the quantifier — the class quantifies
  over ALL RationalLocData with NO IsRational guard (recon verified) ⇒ one datum
  suffices and `chartDatum_isRational` is a bonus, not a need. SURVIVED.
- **Prior-B2 sweep** (b2_log.jsonl, 25 entries, consulted 2026-07-28): no name
  collisions with WP declarations. Shape-matches enforced as design constraints:
  "noetherian ⇒ strongly noetherian" NEVER used (T-SUM-6/T-Q4) — strong
  noetherianity of heads proven per-k; `[IsLinearTopology]` NEVER appears; naive
  algebraic presheafValue identifications avoided (P3-IteratedRational) — all
  identifications via completion universal properties/bicontinuous equivs.

## Feasibility

E1 is elementary given the base layers (largest risk: infinite-σ completeness port —
mechanical per recon). E2's risk concentrates in `headLocEquiv`/`coeffLocEquiv`
(the two bridges) and the Čech bound; every ingredient is delivered infrastructure
(Koszul bounded lifts, OMT, 828b at heads) — comparable in size to the FJP
SheafTransfer+Functoriality layer (~3k lines). E4 rides on the same engine at N = 0
plus elementary norm computations. E3's mechanism is short given E2's engine; its
unconditional form is gated by HRW (open sub-campaign, consult pending). The
`tateExtEquiv` bridge is bounded plumbing (Coram Fubini pattern exists for Fin).
