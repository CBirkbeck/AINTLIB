# Ticket Board — Campaign 6: strengthenings (strong sheafiness + Čech acyclicity)

**Contract**: every statement already exists as a `:= by sorry` declaration in the skeleton
(build-verified 2026-08-10, 3332 jobs, branch `wp/strengthenings`). A ticket = *fill the
named sorries*; statements are NOT to be changed (B2-stop if wrong — report, don't bend).
Leaves cite `decomposition.md` (verbatim source quotes + attack logs there).
Priority spine: **T601 → T602 → T603** (campaign A closes the headline
"strongly sheafy ⇏ stably uniform") → T611/T612 → T613/T614 → T615 → T621/T622.
Cadence note: per-campaign milestones carry per-file cleanups; the single `CLEANUP-ALL`
precedes the final (C-headline) stage, `CLEANUP-FINAL` ends the board.

## Summary
- Proof tickets: 11 (10 done — CAMPAIGN A + T611-T614/T617/T618/T619/T621, all axiom-clean). The abstract criterion is instantiation-ready. · planning tickets: 2 · cleanup tickets: 5
- Parallel capacity: 3 (A-track, B-Fubini pair, C-L1)

---

### [T601] A-L1: `wp_tateExt_completeSpace`
- **Status**: done (2026-08-10, axiom-clean) · **File**: `Adic spaces/WP/StrongSheafy.lean:40` · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Statement**: in skeleton (letI `mvTateAlgebraTopology'`; conclusion
  `@CompleteSpace ↥(restrictedMvPowerSeriesSubring s (WPA K w)) (rightUniformSpace _)`).
- **Proof sketch**:
  1. `haveI`-install `mvTate_isUniformAddGroup s` and the ring topology.
  2. Obtain completeness at `mvTateUniformSpace s` from `mvTate_completeSpace s
     (hA_complete := inferInstance)` — the base instance is `WP/Algebra.lean:279`.
  3. Bridge the two uniformities: both are group uniformities of the same
     `IsTopologicalAddGroup`; use the uniqueness lemma
     (`IsUniformAddGroup.toUniformSpace_eq`-circle or rewrite `mvTateUniformSpace` —
     it is a `@[reducible] def`, so `rfl`-level agreement is plausible; if not,
     `UniformSpace.ext` on the two uniformity filters via `uniformity_eq_comap_nhds_zero`).
- **Mathlib lemmas**: `uniformity_eq_comap_nhds_zero`, `UniformSpace.ext`
  (verified existing); project: `mvTate_completeSpace` (MvTateAlgebraTopology.lean:709),
  `mvTate_isUniformAddGroup` (l.603).
- **Sources**: [WP-paper] l.1229 (isometric `c₀`-decomposition); decomposition A-L1.
- **Generality**: any weight `w`, any `s`; no DVR/noetherian hypotheses (pure topology).

### [T602] A-H (MILESTONE): `wp_tateExt_isSheafyComplete`
- **Status**: done (2026-08-10, axiom-clean) · **File**: `Adic spaces/WP/StrongSheafy.lean:57` · **Depends on**: T601 · **Parallel**: no · **Type**: theorem
- **Statement**: in skeleton.
- **Proof sketch**:
  1. `exact (isSheafyComplete_congr (tateExtEquiv s)
     (tateExtToWPA_continuous s) (tateExtEquiv_symm_continuous s)).mpr
     (wp_stronglySheafy ϖ hK₀ s)`.
  2. The congr's instance stack on the source side is exactly the statement's haveI
     chain; on the target side all instances are global. If the continuity lemmas'
     topologies don't unify with the letI syntactically, `show`-rewrite with
     `mvTateAlgebraTopology'` unfolded (it is `@[reducible]`).
- **Mathlib lemmas**: none new. Project: `isSheafyComplete_congr`
  (SheafyRingEquivTransport.lean:96), `tateExtEquiv` (WP/Sheafy.lean:2274),
  `tateExtToWPA_continuous` (l.2284), `tateExtEquiv_symm_continuous` (l.2335),
  `wp_stronglySheafy` (l.2421) — all verified.
- **Sources**: [WP-paper] l.1229–1238; decomposition A-H.
- **Generality**: any `w`, any `s`.

### [T603] A-H-dvr: `wp_tateExt_isSheafyComplete_of_dvr`
- **Status**: done (2026-08-10, axiom-clean) · **File**: `Adic spaces/WP/StrongSheafy.lean:71` · **Depends on**: T602 · **Parallel**: no · **Type**: theorem
- **Proof sketch**: `exact wp_tateExt_isSheafyComplete (Uniformizer.ofDVR K)
  (FiniteJetOver.isNoetherianRing_unitBall K) s` (pattern of `WP/Main.lean:137`).
- **Sources**: decomposition A-H-dvr.

### [CLEANUP-601] /cleanup `Adic spaces/WP/StrongSheafy.lean`
- **Status**: open · **Depends on**: T603 (final per-file cleanup).

---

### [T611] B-L1 and [T612] B-L2: the RestrictedFubini Gauss-transport legs
- **Status**: done ×2 (2026-08-10 — already closed by a prior session; the file docstring's 'WIP frontier' line was stale, now fixed. Both legs + restrictedFubini axiom-clean.) · **File**: `Adic spaces/FJP/RestrictedFubini.lean` (the two
  `sorry` markers; grep `sorry` in the file for exact lines) · **Depends on**: none ·
  **Parallel**: yes (with each other and with the A-track) · **Type**: lemma ×2
- **Proof sketch**: each leg transports Gauss decay across `sumAlgEquiv` (Xia) composed
  with the `Fin`-sum rename: express the (k+m)-variable Gauss norm of a coefficient as a
  sup over split indices (`slot` combinatorics as in WP/Sheafy.lean's
  `unflattenCoeff`/`slotRecomb` cluster, which solved the analogous problem for the
  WPA extension — reuse the pattern), then squeeze the two `Tendsto`-to-zero conditions
  into each other via `Finset`-sup monotonicity.
- **Mathlib lemmas**: `Filter.Tendsto` squeeze lemmas, `Finset.sup'_le`,
  `MvPowerSeries.coeff_*` (standard); project: `sumAlgEquiv` (XiaMvPowerSeriesEquiv),
  the file's own stated statements.
- **Sources**: RestrictedFubini.lean docstring ([hrw-decomposition] tower leaf);
  [Wedhorn] Example 6.38 vocabulary; decomposition B-L1/2.
- **Generality**: as stated in the file (generic `K`, generic variable counts).

### [T613] B-L3: `mvTate_isStronglyNoetherian`
- **Status**: done (2026-08-10, axiom-clean via T617) · **File**: `Adic spaces/FJP/StrongSheafy.lean:40` · **Type**: theorem
- **Proof sketch**: unfold `IsStronglyNoetherian` for the extension: its `m`-variable
  Tate algebra flattens through Fubini (B-L1/2) to the `(n+m)`-variable Tate algebra of
  `A`, which is noetherian by `[IsStronglyNoetherian A]`; transport noetherianity along
  the ring equivalence (`isNoetherianRing_of_surjective` on the equiv's `toRingHom`,
  pattern of WP/HeadReduced.lean:464).
- **Sources**: [Wedhorn] Ex 6.38/Rem 6.37(1); decomposition B-L3.

### [T614] B-L6: `finiteJet_tateExt_completeSpace`
- **Status**: done (2026-08-10, axiom-clean) · **File**: `Adic spaces/FJP/StrongSheafy.lean:50` · **Depends on**: none (mirror T601's proof) · **Parallel**: yes · **Type**: lemma
- **Note for /generalise lane**: after T601+T614, merge the two into one generic lemma.

### [CLEANUP-611] /cleanup `Adic spaces/FJP/RestrictedFubini.lean`
- **Status**: open · **Depends on**: T611, T612 (final per-file cleanup).

### [T615] B-AG1 design pass (PLANNING): the `⟨V⟩`-Milnor row + abstract transfer
- **Status**: done (2026-08-10 — design COMPLETE; conclusion + execution tree recorded under "B-H execution tree" below: Route N normed-first, corner-square parametrization T623–T628, ring-level extended square discovered already-proven in StrictLoc at arity n)
- **(was)**: in_progress (2026-08-10 — AG1.d design LANDED: `MilnorSquareData` + `isSheafy_of_milnorSquare` skeleton elaborating in MilnorSheafTransfer.lean; remaining: AG1.a ⟨V⟩-row design + T618) · **Depends on**: T613 · **Type**: planning
- **Action**: run `/develop --decompose` scoped to B-AG1 (decomposition.md sub-tree
  AG1.a–d): design the abstract `lem:sheaf-transfer` statement (paper l.576–583 —
  [Reviewer] §4.1's criterion), audit the graph-Koszul stack's genericity over the
  corner ring, write the AG1 skeleton, THEN add the B-H execution tickets.
- **Progress**:
  - 2026-08-10 (genericity audit, step 1 done): the graph-Koszul stack
    (FiniteJetGraphKoszul.lean) is ALREADY generic over a normed corner `E` with the
    scale bundle `(t, htu, ht1, ht0, hscale)` + `hE₀ : IsNoetherianRing (unitBall E)`
    (e.g. `syzygy_graph_restricted` at :1255). NO Koszul-layer generalisation needed for
    AG1.b — the extended corners `E⟨V⟩` just need (a) their Gauss-normed structure
    (Coram stack through `restrictedFubini`), (b) `IsNoetherianRing (unitBall (E⟨V⟩))`
    (the Fubini unit-ball identification — RestrictedFubini's original purpose), and
    (c) the scale bundle at `t := image of the base pseudouniformizer`. Remaining AG1
    design work: AG1.a (the ⟨V⟩-integral row, coefficientwise κ=1 section per the
    validation addendum), AG1.d (the abstract transfer statement), and the per-corner
    instance packaging above.
  - 2026-08-10 (transfer-shape audit, step 2): the JetA transfer's push machinery
    (`pushDatumB`/`presheafValueMapB`/`pushCoveringB`, FiniteJetFunctoriality.lean:93/
    170/2226) is Jet-concrete; the abstract AG1.d statement needs a generic
    datum/covering/value push along a continuous ring hom — check
    `PresheafFunctoriality.lean` (core) for the generic backbone before designing:
    CONFIRMED PRESENT: `locMapOfHom (φ : R →+* S) (D)` (generic datum push, :86),
    `presheafValueMapOfHom (φ) (hφ : Continuous φ)` (generic value map, :171) with
    continuity lemmas — the abstract AG1.d transfer is statable over these NOW.
    NEXT SESSION ENTRY POINT: draft the abstract statement
    `isSheafy_of_milnorRow (φB : R →+* B) (φC : R →+* C) (φD ...) (row : ∀ D hD,
    strict-exact 0 → PV(D) → PV(pushB D) ⊕ PV(pushC D) → PV(pushD D) → 0, natural
    under refinement) (hB hC hD : IsSheafy) : IsSheafy R` in a new
    `MilnorSheafTransfer.lean`, mirroring lem:sheaf-transfer l.576–640 verbatim and
    FiniteJetSheafTransfer's chase with the generic pushes; then re-derive
    isSheafy_JetA through it (regression guard) and instantiate at the ⟨V⟩-square.

### [T618] Prove `isSheafy_of_milnorSquare` (sub-ticket of T615)
- **Status**: done (2026-08-10, axiom-clean — the abstract strict-Milnor-descent criterion, reviewer §4.1, is a complete theorem: embedding half via of_comp factorization, gluing half via pushed families + compat transports + D-separation + row_glue + row_injective recovery) · **File**: `Adic spaces/MilnorSheafTransfer.lean` · **Depends on**: none
  (the statement is self-contained) · **Parent**: T615 · **Type**: theorem
- **Proof sketch** (mirror [WP-paper] lem:sheaf-transfer l.585–640 + the concrete chase
  of FiniteJetSheafTransfer.lean): (1) embedding: the product-restriction of `R` factors
  through the vertex product-restrictions via `row_embedding` + `push_natural_*` and the
  vertices' `IsSheafy.embedding` (paper's commutative square, l.600–612); (2) gluing:
  push a matching family to the `B`/`C` vertices (`push_natural_*` preserves matching),
  glue there (`hB`/`hC` gluing), compare the two `D`-images on every pushed piece and
  conclude equality by `D`-separation (`hD` separation), then `row_glue` at the base
  produces the section; per-piece recovery via `row_injective`.
- **Sources**: [WP-paper] l.576–640 (verbatim quotes in decomposition.md campaign B).
- **Progress**:
  - 2026-08-10: pushCoveringB/C + IsRational lemmas landed. EMBEDDING-HALF PLAN
    (refined): f := productRestrictionSub R C₀ (continuous:
    EmbeddingTopo.lean:285); g := σ ∘ per-piece-rows where σ selects, for each
    E ∈ image-cover, a chosen preimage piece (Classical.choice on Finset.mem_image);
    g ∘ f = (vertex product restriction over pushCoveringB/C) ∘ (base row) by
    push_natural_* per component — an embedding (row_embedding C₀.base composed with
    hB.embedding (pushCoveringB, pushCoveringB_isRational) × hC.embedding);
    conclude Topology.IsEmbedding.of_comp. GLUING-HALF per the original sketch.
  - 2026-08-10: EMBEDDING HALF CLOSED (committed 4b27836c5). GLUING half needs one
    more structure amendment first: (i) leg-naturality fields — the legB/legC value
    maps commute with restrictions between pushed-B/C data (legB_mono + legB_natural,
    legC likewise), (ii) pushCoveringD constructor + IsRational (fields exist), so the
    D-comparison can restrict both glued sections to every pushed piece and conclude
    equality from hD separation (= injectivity from hD.embedding at pushCoveringD).
    Then the body: push f via push_natural (matching persists on common refinements —
    needs pushed-refinement transport: a common refinement of pushed pieces need NOT be
    a push — use sectionEqualizer's common-refinement form pushed through the value
    maps; CHECK IsSheafy.gluing's exact compat shape before writing), glue, compare,
    row_glue at base, recover per-piece via row_injective + push_natural.

### [T619] Rationality-gate the MilnorSquareData fields (sub-ticket of T615)
- **Status**: done (2026-08-10 — hypothesis-gating (Plan B): laws quantify over rational data, pushes stay total; constructors take hC₀; the full chase rethreaded and still proven, axiom-clean) · **File**: `Adic spaces/MilnorSheafTransfer.lean` · **Parent**: T615 · **Type**: refactor
- **Reason (instantiation-driven design correction)**: the concrete pushes are
  rationality-gated (`pushDatumB (D) (hD : D.IsRational)`, FiniteJetFunctoriality:93),
  and e.g. mono/cover for non-rational junk data is unprovable — so `pushB` must be
  `(U : RationalLocData R) → U.IsRational → RationalLocData B` and every field gains
  the `IsRational` arguments. Mechanical rethread: structure fields, pushCovering
  constructors (take `hC₀`, image over `covers.attach` with `hC₀.piece`), cast helpers
  unchanged, and the proven chase's ~40 use-sites (rationality always available from
  `hC₀`). THEN the JetA instantiation proceeds field-by-field
  (pushDatumB_isRational:120, mem_rationalOpen_pushDatumB_iff:2146 for mono/cover,
  presheafValueMapB + _restriction for the value maps and naturality, pushedCompatB/C
  for the compat transports, the localized-Milnor row lemmas for
  row_injective/row_glue/row_embedding, and `interOpen` facts).

### [T620] JetA-square MilnorSquareData instantiation (sub-ticket of T615, regression)
- **Status**: done (2026-08-10, axiom-clean — `jetSquare` complete: pushes = classical-dite over `pushDatum*` with `jetPush*_eq` collapse lemmas; laws by groups: s/T/isRational via dif_pos, legs via `square_commutes`, opens via `mem_rationalOpen_pushDatum*_iff` comap chase, push/leg naturality via generic `presheafValueMapOfHom_restriction`, rows via subst-aux + graph bridges + `loc_row_exact` + `loc_pair_isEmbedding`, compat via pair-adapted `interDatum` factoring. Regression `isSheafy_JetA'` proven through `isSheafy_of_milnorSquare`. KEY REUSABLE PATTERN: free-datum subst-aux lemmas — state the law with the pushed datum as a free variable + an equation to `pushDatum*`, `subst`, then `show` the concrete `presheafValueMap*` form, which is defeq by proof irrelevance) · **File**: new `Adic spaces/FJP/MilnorSquareInstance.lean` · **Parent**: T615 · **Type**: def + theorem
- **Plan**: assemble `jetSquare : MilnorSquareData (jB) (iotaC) (φD := legB ∘ jB) …` with
  pushes `fun D => if h : D.IsRational then pushDatumB D h else D-junk` (laws discharged
  with `dif_pos`); homs: `jB` (FiniteJetRings:326), `iotaC` (:320), `rhoC : JetC →+* JetD`
  (:134), the B-leg `JetB →+* JetD` (locate; grep 'rhoB\|JetB F →+* JetD'); field
  discharges from: pushDatumB_isRational (:120), mem_rationalOpen_pushDatumB_iff (:2146)
  for mono/cover, presheafValueMapB + _restriction for value maps/naturality (CHECK
  they equal presheafValueMapOfHom-form or add bridging lemmas), pushedCompatB/C
  (SheafTransfer:212/258), localized-Milnor row lemmas for
  row_injective/row_glue/row_embedding/row_comm, productRestrictionSub machinery.
  Regression goal: `isSheafy_JetA' : IsSheafy (JetA F) := isSheafy_of_milnorSquare … jetSquare …`.
- **Key risk**: presheafValueMapB is a bespoke construction — verify it agrees with
  `presheafValueMapOfHom jB … (pushDatumB D hD)` (same universal-property extension;
  if defs differ, prove the agreement lemma once and rewrite the field discharges
  through it).

### [T616] B-H (MILESTONE): `finiteJet_tateExt_isSheafyComplete`
- **Status**: done (2026-08-11 — AXIOM-CLEAN [propext, Classical.choice, Quot.sound]. 𝓐 is STRONGLY SHEAFY: every finite Tate extension sheafy at every valid ring of integral elements. CAMPAIGN B COMPLETE — both papers' examples strongly sheafy.) · **File**: `Adic spaces/FJP/StrongSheafy.lean:297`.

---

## B-H execution tree (T615 design conclusion, 2026-08-10)

**Route N (normed-first)**: prove `IsSheafy (GraphKoszul.P (JetA F) n)` (the Gauss-normed
radius-one restricted ring) via `isSheafy_of_milnorSquare` at the **normed extended square**
`P(JetA)n → P(JetB)n, P(JetC)n → P(JetD)n` with homs `extJB/extIotaC/extRhoB/extRhoC F n`
(StrictLoc :51–63), then transport to the headline's topological ring
`↥(restrictedMvPowerSeriesSubring n (JetA F))` by a bicontinuous equiv + `isSheafyComplete`
plumbing (campaign-A `tateExtEquiv` pattern).

**Key discovery**: the ⟨V⟩-variables and the graph T-variables are the SAME construction —
the ring-level extended square is ALREADY PROVEN in FiniteJetStrictLocalization at arity n:
`ext_milnorRow_exact` (:120 — this IS AG1.a), `ext_square_commutes` (:73),
`extRhoC_strict_surjective` (:88), `ext_pair_injective` (:179), `ext_max_norm_eq` (:166),
`isNoetherianRing_unitBall_PB/PC/PD` (:293–303), 1-Lipschitz homs via
`norm_mapRestricted_le`. What is missing is ONLY the rational-datum/bridge/loc layer for
the extended square — i.e. prop:localized-milnor over abstract corners. Plan: parametrize
that layer over a **corner-square package** (4 normed ultrametric complete corners + hom
bundle + norm identities + milnor row + scale bundles + unitBall-noetherian at B/C/D),
with the Jet square as regression instance and the P-square as the payoff instance.

### [T623] Generic value-level square coherence + interDatum genericity
- **Status**: done (2026-08-11 — presheafValueMapOfHom_comp in PresheafFunctoriality; interDatum genericity delivered as interDatumOfRational in CornerSquareDatum (T624)) · **File**: `Adic spaces/PresheafFunctoriality.lean` (append) · **Type**: lemma
- **Statement**: `presheafValueMapOfHom_square (φB : R →+* B) (φD : R →+* D)
  (ψ : B →+* D) (hcomm : ψ.comp φB = φD) …
  (hψ : Continuous ψ) … : presheafValueMapOfHom ψ hψ (pushB) (pushD) … ∘
  presheafValueMapOfHom φB … = presheafValueMapOfHom φD …` — the dense-equalizer
  D-coherence proven ONCE generically (pattern: `mapBD_mapB_eq_mapCD_mapC`,
  FiniteJetFunctoriality:1695 — IsLocalization.ringHom_ext on powers + canonicalMap
  computation + DenseRange.equalizer). Corollary: the two-leg form used by `row_comm`.
  ALSO: audit `interDatum` (FiniteJetFunctoriality:2326) — if JetA-fixed, generalize to
  any ring with the needed instances (proof is ring-generic) into PresheafFunctoriality,
  with `rationalOpen_interDatum` + `interDatum_isRational`.
- **Sources**: [FJP] (4.9); the concrete proof at FiniteJetFunctoriality:1695.

### [T624] Corner-square datum layer (parametrized pushDatum + open iffs)
- **Status**: done (2026-08-11 — CornerSquareDatum.lean, 0 warnings) · **File**: new `Adic spaces/CornerSquareDatum.lean` · **Depends on**: T623 · **Type**: def + lemmas
- **Statement**: over `(A B : Type*)` normed-ultrametric Huber with a 1-Lipschitz
  continuous `φ : A →+* B` and openness transport, define `pushDatumOfHom D hD`
  (s := φ D.s, T := D.T.image φ; rationality via `span_image_eq_top`), prove
  `pushDatumOfHom_isRational` and `mem_rationalOpen_pushDatumOfHom_iff` (comap
  characterization; pattern FiniteJetFunctoriality:2146 — uses `comap_mem_spa` +
  `plus_le_comap_of_norm_le`), and `pushDatumOfHom_interOpen` (pattern
  FiniteJetSheafTransfer:147). The Jet pushes become instances (regression check only,
  no rewiring of the concrete files).
- **Sources**: [FJP] Lemma 5.1/5.2 datum layer; concrete patterns cited above.

### [T625] Corner-square strict localization + bridges (THE core)
- **Status**: done (2026-08-11 — COMPLETE, all pushed: CornerSquareLocalization.lean (1189 L) = Pinch package + full abstract §4 chain (Lemmas 4.1/4.3, Prop 4.5 loc layer + ψ-lipschitz + exported quotient-structure helpers); CornerSquareBridge.lean (~1300 L) = CornerEnum + single-corner graphBridge (fwd/rev/roundtrips/continuity) + square naturality N1-N4 + **valueRow_injective/glue/embedding** (prop:localized-milnor at values over the abstract pinch — T627's row fields). KEY LESSONS: instance-diamond on P-rings fixed by set_option backward.isDefEq.respectTransparency false + exported instance-defs (locANormedAddCommGroup etc.); defeq-vs-syntactic friction between S.locB and pushed-corner presentations resolved by show-style hcomp proofs; IsTateRing extends IsHuberRing so bind only IsTateRing) (2026-08-11 — MAJOR PROGRESS, all committed+pushed:
  `FJP/CornerSquareLocalization.lean` (1103 L, 0 warnings) = the `Pinch` package
  structure + NoethPack + the ENTIRE §4 chain abstract: ext-layer (Lemma 4.1),
  ideal_row_surjective + ideal_pullback_controlled + isClosed_IA (Lemma 4.3),
  loc quotient layer with loc_pair_injective / loc_row_exact / loc_norm_le /
  loc_pair_isEmbedding / locψC surjective+open / locA_t2 / locA_completeSpace
  (Prop 4.5). Relations in polyToP-form so vertex instantiation is definitional.
  `FJP/CornerSquareBridge.lean` (in flight): generic CornerEnum + single-corner
  graphBridge (fwd = completion extension, rev = bounded evaluation, round
  trips) — instantiates at all four corners since Pinch.IB/IC/ID are the
  IA-ideals of the pushed data. REMAINING: (i) compile bridge file, (ii)
  square-level naturality squares N1-N4 (dense-equalizer pattern), (iii) the
  T627 value-row consumables valueRow_injective/glue/embedding.) · **File**: new `Adic spaces/CornerSquareLocalization.lean` (+ a second file if >2500 lines) · **Depends on**: T624 · **Type**: theorem stack
- **Statement**: parametrize FiniteJetStrictLocalization's rational-datum layer +
  FiniteJetFunctoriality's bridge layer over the corner-square package: for a rational
  datum enum `e` on the base corner `A` (span ({g} ∪ range f) = ⊤), the graph quotients
  `locA/locB/locC/locD`, `loc_square_commutes`, `loc_pair_injective`, `loc_row_exact`,
  `loc_pair_isEmbedding`, `locRhoC_surjective/openMap`, `locA_t2/completeSpace`; then the
  completion bridges `graphBridge` (`presheafValue D ≃+* locA`, continuous both ways),
  `bridgeFwdB/C/D` + injectivity + continuity, naturality squares
  (`graphBridge_natural_B/C`, `locRhoB_bridgeFwdB`, `locRhoC_bridgeFwdC`), and
  `pairMapBC_injective`. Inputs consumed from the package: Koszul stack at the corners
  (already generic: `syzygy_graph_restricted` over normed E + scale + unitBall-noeth),
  the ring-level row, `ext`-style coefficientwise lemmas re-proven over the package
  (they are `mapRestricted` transports — the StrictLoc arity-n forms are the P-instance
  witnesses that the statements are right).
- **Approach**: transcription-with-generalization of the two concrete files; keep decl
  names with a `CornerSquare.` namespace; the concrete Jet versions stay untouched
  (dedup ticket after the campaign retires them or rewires them as instances).
- **Sources**: [FJP] §4 (Lemmas 4.1/4.3/4.4, Prop 4.5) + §5 bridges — the paper states
  them over corners `E`; the concrete files are the transcription at Jet corners.

### [T626] Extended-square corner package assembly
- **Status**: done (2026-08-11 — ExtendedCornerPackage.lean: exists_flattenPP ring-Fubini + full Huber/Tate stack on P-corners + extPinch + extNoethPack; axiom-clean, 0 warnings) · **Depends on**: T625 (package shape frozen) · **Type**: instance bundle
- **Statement**: instantiate the corner-square package at
  `(P (JetA F) n, P (JetB F) n, P (JetC F) n, P (JetD F) n; extJB/extIotaC/extRhoB/extRhoC)`:
  all fields from existing StrictLoc arity-n lemmas (list in the tree header above) +
  scale bundles `t := const ϖ` (Gauss `hscale` from the vendored stack) + Tate/Huber/
  PlusSubring/T2/Nonarch/Complete instance stack on the P-corners (mirror how JetB/C/D
  got theirs — locate the generic normed→Huber path in FiniteJetRings/UniformDomain).
- **Sources**: [Reviewer] §5.1; StrictLoc §ext.

### [T627] Extended MilnorSquareData instance + `IsSheafy (P (JetA F) n)`
- **Status**: done (2026-08-11 — ExtendedMilnorInstance.lean: powerBounded_le_comap transport, extJetSquare (all fields), isStronglyNoetherian_PB/PC/PD, isSheafy_PB/PC/PD via the CLEAN isSheafy_of_stronglyNoetherian_828b (NOT the _clean-named one, which carries sorry leaves!), isSheafy_extJetA n — ALL axiom-clean) · **Depends on**: T623, T624, T625, T626 · **Type**: def + theorem
- **Statement**: `extJetSquare n : MilnorSquareData (extJB F n) (extIotaC F n)
  ((extRhoC F n).comp (extIotaC F n)) …` — T620's file is the template line-by-line
  (dite pushes + collapse lemmas + subst-aux layer + generic naturality); rows from
  T625's bridges; vertex sheafiness from `isSheafy_of_stronglyNoetherian_828b` at the
  P-corners (strongly noetherian: unitBall-noeth + Fubini `restrictedFubini`, or
  directly `mvTate_isStronglyNoetherian` transported along the normed↔topological
  bridge — pick in-flight). Conclusion `isSheafy_extJetA n : IsSheafy (P (JetA F) n)`.
- **Sources**: T620 (template); [WP-paper] lem:sheaf-transfer instantiation.

### [T628] Normed↔topological bridge + B-H endgame (discharges T616)
- **Status**: done (2026-08-11 — ExtendedSheafyTransport.lean: gaussToTate/tateToGauss continuity + extJetPlus + ext_isSheafyFor/Complete; StrongSheafy.lean:306 sorry FILLED; headline axiom-clean) · **Depends on**: T627 · **Type**: theorem
- **Statement**: (i) `restrictedGaussTateEquiv n : P (JetA F) n ≃+*
  ↥(restrictedMvPowerSeriesSubring n (JetA F))`, bicontinuous (underlying sets: both are
  coefficients→0, JetA's topology is its norm topology; topologies: Gauss balls vs
  `mvTateAlgNhd` via `mvTateAlgNhd_of_coeff_mem_principal`/`mvTateAlgNhd_coeff_mem` —
  the T617-leg combinatorics); (ii) `IsSheafyComplete` endgame: from
  `isSheafy_extJetA` get `IsSheafyFor` at the canonical pair
  (`isLimitSheaf_of_isSheafy`), transport along (i) (`isSheafyComplete_congr` /
  `isSheafyFor` congr as in T602), upgrade by `isSheafyFor_iff_isSheafyComplete`.
  Fill `finiteJet_tateExt_isSheafyComplete` (StrongSheafy.lean:297). Then T616 → done.
- **Sources**: campaign-A endgame (WP/StrongSheafy.lean) — the identical plumbing.

### [CLEANUP-612] /cleanup `Adic spaces/FJP/StrongSheafy.lean`
- **Status**: open · **Depends on**: T616.

---

### [T621] C-L1 (DONE as `unitCover_delta_surjective`)
- **Status**: done (2026-08-10, axiom-clean; home = WedhornCechAcyclicity.lean beside unitCover_isOXAcyclic — the interDatum-based skeleton statement was retired as a planning correction, see Progress)
- **Progress**:
  - 2026-08-10: reconnaissance — the value identifications are
    `laurentPlusBridge`/`laurentMinusBridge` (LaurentRefinementCore.lean:2863/2931)
    with naturality `laurentPlusBridge_restrictionMap`/`laurentMinusBridge_restrictionMap`
    (:3120/:3239), bicontinuity in LaurentOverlap.lean:2136/2184. Intersection-value
    bridge lives in LaurentOverlap.lean (locating). Plan: transport the difference map
    along the three bridges to the concrete quotients, split via
    `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` ([Wedhorn] l.4200; ALSO need the relation-ideal
    decomposition per the ChatGPT addendum), push the two summands back.
  - 2026-08-10 (design note): the existing 8.33 development presents the overlap via
    `overlapDatum P b = laurentMinusDatum (trivialPlusDatum B P b) b` and identifies its
    value through `bivariateOverlap_equiv_B₁₂gen b : TateAlgebra₂ B ⧸ (b−X, 1−bY) ≃+*
    LaurentCover.B₁₂_gen b` (LaurentOverlap.lean:644). NEXT STEP: restate C-L1's
    intersection over `overlapDatum` (planning correction via decomposition.md — my
    interDatum-based skeleton statement predates this reconnaissance), then transport the
    difference-map surjectivity through the ± bridges and bivariateOverlap equiv, closing
    with the Laurent split A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩ + the relation-ideal
    decomposition at the B₁₂_gen level.
  - 2026-08-10 (axiom audit): `wedhorn_lemma_834_part_i_laurent_acyclic` is CLEAN but
    `laurentOverlapBridge_exists_compatible` (LaurentRefinementCore.lean:3735) carries
    sorryAx (parked residuals; 25 sorries in that file). T621 must ride the CLEAN 834
    chain's own overlap identification, NOT the bridge-exists packaging. NEXT: trace
    `laurentProdCoverOf_isOXAcyclic` → its 2-cover gluing base case → the overlap-value
    identification it actually uses (grep the 833-gluing lemma in
    WedhornCechAcyclicity.lean), then state the difference-map surjectivity in THAT
    vocabulary.
  - 2026-08-10 (clean vocabulary located): the clean chain's 2-cover is `unitCover D₀ f`
    with base case `unitCover_isOXAcyclic`, and intersections via
    `RationalLocData.interSamePair` (same-pair form). RESTATE C-L1 as: for the unit
    cover's plus/minus pieces, every element of
    `presheafValue (plus.interSamePair minus h)` is a difference of the two
    restrictions. Proof mirrors unitCover_isOXAcyclic's own value identifications
    (read that proof next; it contains the clean concrete models of the three values).
  - 2026-08-10 (ROUTE FULLY MAPPED): `row3_exact` (LaurentCoverExact.lean:1797) already
    provides `Function.Surjective (deltaMap_gen f)` AXIOM-CLEAN (consumed whole by the
    certified isSheafy path). T621 = (1) build the clean overlap-value bridge
    `presheafValue (U₁.interSamePair U₂) ≃/↪ B₁₂_gen (D₀.canonicalMap f)` with the
    intertwining square `interBridge ∘ restriction-difference = deltaMap_gen ∘
    (bridgePlus × bridgeMinus)` — read `unitCover_delta_eq_zero_of_compat`'s proof
    internals first, they already construct pieces of this; (2) the 6-line chase:
    given z, δ-surjectivity + bridgePlus/Minus surjectivity pulls back a pair, the
    intertwining + interBridge injectivity closes. Statement stays in interSamePair
    vocabulary (update the CechAcyclicityFull.lean skeleton statement accordingly —
    planning correction, my statement predates this trace). · **File**: `Adic spaces/CechAcyclicityFull.lean:41` · **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Proof sketch**:
  1. Identify the three `presheafValue`s via the existing 8.33 development's
     `Examples 6.38/6.39` comparisons (the identifications behind
     `wedhorn_lemma_834_part_i_laurent_acyclic`'s chain).
  2. Split a Laurent-series element: `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` ([Wedhorn] l.4200) —
     locate/prove the split in the ExampleLaurentSeries/LaurentRefinement cluster.
  3. Push the two summands back through the identifications as the pair `(x, y)`.
- **Sources**: [Wedhorn] l.4151–4207 (verbatim quote in decomposition C-L1).
- **Generality**: strongly noetherian Tate `A`, Wedhorn's own hypotheses (mirrors the
  existing 834-part-i signature).

### [T622] C-AG1 design pass (PLANNING): all-degree Čech on `RationalCoveringData`
- **Status**: open · **Depends on**: T621 · **Type**: planning
- **Action**: `/develop --decompose` for C-AG1: multi-intersection data, the Čech complex
  on rational covers (reusing `CechCohomology.lean`'s `IsAcyclic` or an algebraic twin),
  A.3 in all degrees, then the two example headlines (FJP Milnor LES over
  prop:localized-milnor; WP `c₀`-primitives over eq:head-cech's bounded inverse).

### [CLEANUP-621] /cleanup `Adic spaces/CechAcyclicityFull.lean`
- **Status**: open · **Depends on**: T621.

---

### [CLEANUP-ALL-1] /cleanup-all before the final C-headline stage
- **Status**: open · **Depends on**: all open proof tickets above.

### [CLEANUP-FINAL] /cleanup-all
- **Status**: open · **Depends on**: everything.

### [T617] Topological nested Fubini: `restrictedSumRingEquiv` (sub-ticket of T613)
- **Status**: done (2026-08-10, axiom-clean: restrictedNestedEquiv + 3 transport legs + 2 coeff formulas) · **File**: `Adic spaces/FJP/StrongSheafy.lean` ·
  **Depends on**: none · **Parent**: T613 · **Type**: def + 2 lemmas
- **Statement**: over `[CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]`
  `[IsTopologicalRing A] [IsTateRing A]`, with the letI `mvTateAlgebraTopology' n` on
  `B := ↥(restrictedMvPowerSeriesSubring n A)`:
  `restrictedNestedEquiv (n k) : ↥(restrictedMvPowerSeriesSubring k B) ≃+* ↥(restrictedMvPowerSeriesSubring (n + k) A)`
  (via `MvPowerSeries.sumAlgEquiv` + `finSumFinEquiv` reindex), plus the two
  restrictedness-transport lemmas (joint ⟹ nested, nested ⟹ joint).
- **Proof sketch**:
  1. Ambient equivalence: `renameEquiv (finSumFinEquiv (m:=k)(n:=n)).symm` then
     `sumAlgEquiv (Fin k) (Fin n) A` : `MvPowerSeries (Fin (n+k)) A ≃ MvPowerSeries (Fin k) (MvPowerSeries (Fin n) A)`
     (coefficient formulas `coeff_sumAlgEquiv_symm_apply` etc., Vendored/XiaMvPowerSeriesEquiv).
  2. (joint ⟹ nested), inner leg: for fixed outer ν, the inner slice of a cofinitely-null
     joint family is cofinitely null (injection of index sets) — each outer coefficient
     lands in `restrictedMvPowerSeriesSubring n A`.
  3. (joint ⟹ nested), outer leg: a joint-cofinite family has finitely many exceptional
     pairs; the set of outer ν occurring in an exceptional pair is finite, so cofinitely
     many outer coefficients lie entirely in any `mvTateAlgNhd n P j` — outer family → 0
     in `mvTateAlgebraTopology'` (basis: `mvTateAlgBasis'`).
  4. (nested ⟹ joint): given U ⊇ a basis nhd, cofinitely many ν have g_ν entirely in U;
     the finitely many remaining g_ν are each inner-restricted, contributing finitely many
     exceptional μ each — total exceptional pairs finite.
  5. Package: the restricted subrings map onto each other; `RingEquiv` via
     `RingEquiv.ofBijective` on the corestricted map (mul/add from the ambient AlgEquiv).
- **Mathlib lemmas**: `Filter.mem_cofinite`, `Set.Finite.subset`, `Filter.tendsto_nhds`,
  `MvPowerSeries.coeff_*`; project: `sumAlgEquiv`, `coeff_sumAlgEquiv_symm_apply`,
  `mvTateAlgBasis'`, `mvTateAlgNhd` membership lemmas, `MvPowerSeries.IsRestricted`
  (RestrictedPowerSeries.lean:68).
- **Sources**: the standard `A⟨X⟩⟨Y⟩ = A⟨X,Y⟩` (Wedhorn §5.3 vocabulary; the normed-field
  instance is `restrictedFubini`, FJP/RestrictedFubini.lean:353; [WP-paper]
  eq:strong-sheafy-decomposition is the WPA instance).
- **Generality**: any Tate ring `A` — deliberately the maximal form (this is the
  generic leaf both campaign B and future consumers use).
