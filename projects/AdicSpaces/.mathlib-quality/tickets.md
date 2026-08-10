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
- Proof tickets: 9 (8 done — CAMPAIGN A + T611-T614/T617/T621, all axiom-clean). C-L1 landed: the 2-cover augmented complex is exact in ALL degrees. · planning tickets: 2 · cleanup tickets: 5
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
- **Status**: in_progress (2026-08-10 — AG1.d design LANDED: `MilnorSquareData` + `isSheafy_of_milnorSquare` skeleton elaborating in MilnorSheafTransfer.lean; remaining: AG1.a ⟨V⟩-row design + T618) · **Depends on**: T613 · **Type**: planning
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
- **Status**: open · **File**: `Adic spaces/MilnorSheafTransfer.lean` · **Depends on**: none
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

### [T616] B-H (MILESTONE): `finiteJet_tateExt_isSheafyComplete`
- **Status**: blocked (T615 outcome) · **File**: `Adic spaces/FJP/StrongSheafy.lean:60`.

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
