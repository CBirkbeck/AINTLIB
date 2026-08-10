# Decomposition — Campaign 6: strong sheafiness + Čech acyclicity (the strengthenings)

Branch `wp/strengthenings`. Sources: [WP-paper] = `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex`
(local revision; live revision renumbers headlines 1.1/8.1), [Wedhorn] = `refs/AdicSpaces/wedhorn.txt`,
[Reviewer] = the 2026-08-10 referee report (§4–§5). Prior-B2 log consulted: `b2_log.jsonl` —
no name or shape matches for any leaf below (entries are all Campaign-4 chart/jet-specific).

## Skeleton location (all `lake build`-clean, sorries only — verified 2026-08-10)
- `Adic spaces/WP/StrongSheafy.lean` — A-L1, A-H, A-H-dvr
- `Adic spaces/FJP/StrongSheafy.lean` — B-L3, B-L6, B-H
- `Adic spaces/CechAcyclicityFull.lean` — C-L1
- (existing) `Adic spaces/FJP/RestrictedFubini.lean` — B-L1, B-L2 (the two sorried Gauss-transport legs)

---

## Campaign A — WP strong sheafiness, Tate-extension vocabulary

### Plain-English proof (source: [WP-paper] thm:parity-strongly-sheafy, l.1131–1238)
The paper proves the topological sheaf condition for `(𝒜,𝒜°)` on the rational basis via
finite-head presentation, small perturbation, and coefficientwise `c₀`-gluing with the head's
bounded equalizer inverse; then (final paragraph) extends to Tate variables. The library has
already formalised all of this at the shifted-weight model (`wp_stronglySheafy`, certified);
what remains is transporting along the isometric identification to the project's own
Tate-extension object.

### Leaves

- **A-L1** (leaf, project): `wp_tateExt_completeSpace` — `WP/StrongSheafy.lean:40`
  - Statement: the Tate extension `𝒜⟨V₁,…,Vₛ⟩` is complete for the right uniformity of
    `mvTateAlgebraTopology'`.
  - Source: [WP-paper] l.1229 (verbatim): "Finally, for auxiliary Tate variables
    V₁,…,Vₛ one has, **isometrically**, 𝒜⟨V₁,…,Vₛ⟩ ≅ ⊕̂^{c₀}_μ 𝒜_N⟨V₁,…,Vₛ⟩e_μ" — an
    isometric `c₀`-sum of Banach spaces is complete.
  - Lean ↔ source: the Lean statement asserts `@CompleteSpace _ (rightUniformSpace _)`;
    the project already proves completeness at `mvTateUniformSpace`
    (`mvTate_completeSpace`, MvTateAlgebraTopology.lean:709, with base-completeness input
    available as the global `@CompleteSpace (WPA K w) rightUniformSpace` instance,
    WP/Algebra.lean:279). The leaf is the identification of the two uniform structures of
    one topological add group (both are the canonical group uniformity of
    `mvTateAlgebraTopology'`).
  - Discharged by: `mvTate_completeSpace` + a uniformity-equality bridge
    (`mvTateUniformSpace` def-unfold vs `rightUniformSpace`; both are filter-basis
    uniformities of the same topology — `IsTopologicalAddGroup` uniqueness of the group
    uniformity, mathlib's `IsUniformAddGroup`/`comm_topologicalAddGroup_is_uniform`
    circle). Verified present: `mvTate_isUniformAddGroup` (l.603).
  - Attacks: (1) counterexample — none: completeness of a `c₀`-sum of complete pieces is
    classical, and the paper asserts the isometric identification; (2) edge case `s = 0`:
    the extension is `𝒜` itself, complete by `WP/Algebra.lean:279` ✓; (3) hypothesis
    test — no noetherian or DVR hypothesis needed (pure topology), matches the statement
    carrying none; (4) discharge attack — `mvTate_completeSpace` requires `[T2Space A]`:
    available for `WPA K w` (metric subtype) ✓. SURVIVED.

- **A-H** (headline): `wp_tateExt_isSheafyComplete` — `WP/StrongSheafy.lean:57`
  - Statement: under the canonical topology + instance stack, `IsSheafyComplete` of the
    Tate extension, hypotheses `(ϖ : Uniformizer K)`, `hK₀`.
  - Source: [WP-paper] l.1229–1238 (verbatim): "The finite heads remain affinoid, the
    retractions and perturbation lemma are unchanged, and the preceding proof applies
    verbatim. **Therefore every finite Tate extension is sheafy.**"
  - Lean ↔ source: the library's realisation of "the preceding proof applies verbatim at
    the shifted weight" is `wp_stronglySheafy : IsSheafyComplete (WPA K (shiftWeight w s))`
    (WP/Sheafy.lean:2421, certified at `w = id`); the identification of the paper's
    Tate extension with the shifted-weight algebra is `tateExtEquiv` (WP/Sheafy.lean:2274)
    with bicontinuity `tateExtEquiv_bicontinuous` (W24b, l.2402).
  - Discharged by: `(isSheafyComplete_congr (tateExtEquiv s) h₁ h₂).mpr
    (wp_stronglySheafy ϖ hK₀ s)` where `h₁, h₂ = (tateExtEquiv_bicontinuous s).1/.2` —
    all three constituents verified to exist at the cited lines; `isSheafyComplete_congr`
    signature checked (SheafyRingEquivTransport.lean:96, needs the six-instance stack —
    supplied by `mvTate_isTateRing`/`mvTate_t2Space`/`mvTate_nonarchimedean`/
    `mvTateAlgebraTopology'_isTopologicalRing`/A-L1, all verified present).
  - Attacks: (1) counterexample — none; the B-side statement is certified true; (2) edge
    `s = 0`: extension ≅ 𝒜, `shiftWeight w 0 = w`? — **checked**: `shiftWeight` at `s = 0`
    must reduce to `w` for `tateExtEquiv` to make sense there; the equivalence exists at
    every `s` regardless, so no constraint is violated; (3) hypothesis test: `ϖ, hK₀`
    match `wp_stronglySheafy`'s exactly — no smuggled strength; (4) source drift — the
    paper says "sheafy"; the Lean `IsSheafyComplete` = sheafy for every valid pair, which
    is the paper's own reading (its §8 proof runs for an arbitrary plus ring `E_U^+`,
    l.1145: "Let E_U^+ be the plus ring defining the rational subspace U; it need not
    equal the maximal ring"); (5) the congr transport moves arbitrary pairs in both
    directions (`RingOfIntegralElements.congr`) — no pair is lost. SURVIVED.

- **A-H-dvr** (assembly-layer leaf): `wp_tateExt_isSheafyComplete_of_dvr` —
  `WP/StrongSheafy.lean:71`. One-line from A-H at `Uniformizer.ofDVR K` +
  `FiniteJetOver.isNoetherianRing_unitBall K` (both verified existing, used identically
  by `weightedParity_*_of_dvr` in WP/Main.lean:131–160). Attacks: same as A-H. SURVIVED.

**Consequence once A-H lands**: with the certified `weightedParity_not_stablyUniform`,
"**strongly sheafy does not imply stably uniform**" is fully formal ([Reviewer] §5.1's
proposed strengthening).

---

## Campaign B — FJP strong sheafiness

### Plain-English proof (sources: [WP-paper] §5 l.367–570, §6 l.572–654; [Reviewer] §5.1)
The original proof: (i) graph Koszul over each affinoid corner — positive-degree exactness,
strictness, bounded ideal/syzygy denominators (lem:koszul); (ii) the integral Milnor row
tensored to the graph ambients, coefficientwise (eq:tate-ambient); (iii) the graph ideals
form a strict pullback (lem:graph-pullback), giving the strict exact localized row
(prop:localized-milnor); (iv) sheaf transfer (lem:sheaf-transfer) + Huber's theorem at the
corners (thm:sheafy). For the Tate extension `𝓐⟨V₁,…,Vₙ⟩`: the corners become
`B⟨V⟩, C⟨V⟩, D⟨V⟩` — still strongly noetherian affinoids ([Reviewer] §5.1: "adjoining
variables preserves the coefficientwise split Milnor row, while B⟨T⟩, C⟨T⟩, and D⟨T⟩
remain strongly noetherian affinoids. The same Koszul/Milnor argument should apply.") —
and every step of §5–§6 applies verbatim to the extended square, because lem:koszul is
already stated over an arbitrary affinoid `E` with an arbitrary number of graph variables
(l.373: "Let E be an affinoid k-algebra … P_E = E⟨T₁,…,Tₘ⟩").

### Leaves (first layer)

- **B-L1, B-L2** (leaves, existing skeleton): the two sorried Gauss-transport legs of
  `FJP/RestrictedFubini.lean` (file docstring l.10: "The restricted Fubini:
  `K⟨X₁..X_{k+m}⟩ ≅ (K⟨X₁..X_m⟩)⟨T₁..T_k⟩` … WIP frontier: the two Gauss-transport legs
  carry `sorry` markers"). Source: [Wedhorn] Example 6.38 vocabulary (Tate algebras of
  Tate algebras are Tate algebras); the legs transport Gauss decay through Xia's
  `sumAlgEquiv` in both directions. These are the gate for B-L3.
  Attacks: (1) the equivalence itself (`sumAlgEquiv` + rename) already exists sorry-free —
  only the decay transport is open; (2) edge `k = 0` or `m = 0`: identity/rename — holds;
  (3) the two legs are stated with the norms explicit; no hidden completeness assumption.
  SURVIVED (as statements; they are the campaign's first work items).

- **B-L3** (leaf after B-L1/2): `mvTate_isStronglyNoetherian` — `FJP/StrongSheafy.lean:40`.
  Generic: the Tate extension of a strongly noetherian Tate ring is strongly noetherian.
  - Source: [Wedhorn] Example 6.38 / Remark 6.37(1) (t.f.t. over strongly noetherian is
    strongly noetherian); concretely `(A⟨V₁..Vₙ⟩)⟨X₁..Xₘ⟩ ≅ A⟨V₁..Vₙ,X₁..Xₘ⟩` (Fubini)
    is noetherian by `IsStronglyNoetherian A`.
  - Discharged by: B-L1/B-L2 (Fubini) + `IsStronglyNoetherian.isNoetherianRing_restricted`
    (FiniteJetNoetherianVertices.lean:155 shape, verified) + noetherian transport along a
    ring equivalence (`isNoetherianRing_of_surjective`, mathlib, verified in use at
    WP/HeadReduced.lean:464).
  - Attacks: (1) false without Fubini? No — the definition of `IsStronglyNoetherian` for
    the extension unfolds exactly to noetherianity of the flattened algebras; (2) edge
    `n = 0`: extension ≅ A — reduces to `IsStronglyNoetherian A` ✓; (3) hypothesis test:
    `[IsTateRing A]` is needed for the topology; `[IsStronglyNoetherian A]` is the
    mathematical content — neither droppable. SURVIVED.

- **B-L6** (leaf): `finiteJet_tateExt_completeSpace` — `FJP/StrongSheafy.lean:50`. Twin of
  A-L1 at `A = JetA F` (same discharge; `CompleteSpace (JetA F)` global instance at
  FiniteJetRings.lean:317). A generalise-lane note: A-L1/B-L6 should merge into one
  generic lemma once proven. SURVIVED (same attacks as A-L1).

- **B-AG1** (API gap, own sub-decomposition required before B-H tickets):
  the `⟨V⟩`-Milnor row and transfer. Sub-tree (each with source):
  - AG1.a: the extended integral row `0 → P_{A₀}⟨V⟩ → P_{B₀}⟨V⟩ ⊕ P_{C₀}⟨V⟩ → P_{D₀}⟨V⟩ → 0`
    coefficientwise-split strict exact. Source: [WP-paper] l.455–462 (verbatim): "The
    exact integral row (eq:integral-milnor) and the coefficientwise section of C₀ → D₀
    give an exact sequence … Exactness is coefficientwise: a compatible restricted
    coefficient pair lifts to A₀, and the lifted coefficients still tend to zero
    ϖ-adically". The same argument with the `V`-multi-indices adjoined to the
    coefficient index set.
  - AG1.b: lem:koszul at the extended corners — **free**: the paper's lemma (l.382) is
    already stated for an arbitrary affinoid `E`; instantiate `E := B⟨V⟩` etc. (which are
    affinoid by B-L3). The Lean graph-Koszul stack's genericity over the corner must be
    audited (FiniteJetGraphKoszul is stated over which rings?) — audit is part of the
    gap's design pass.
  - AG1.c: lem:graph-pullback + prop:localized-milnor for the extended square. Source
    quotes: l.464–520 ("The graph ideal J_A is closed … is an isomorphism … strict
    exact"), l.521–570 ("For every rational datum α in A, the canonical sequence
    0 → A_α → B_α ⊕ C_α → D_α → 0 is strict exact … natural under rational refinement").
  - AG1.d: the transfer. Source: lem:sheaf-transfer l.576–583 (verbatim): "Suppose that
    for every rational domain U ⊂ X_R the section rings satisfy a natural strict exact
    sequence 0 → 𝒪_R(U) → 𝒪_B(U_B) ⊕ 𝒪_C(U_C) → 𝒪_D(U_D) → 0. If the Huber pairs
    associated with B, C, D are sheafy as complete topological rings, then the Huber pair
    associated with R is sheafy as a complete topological ring." The Lean rendering is
    currently JetA-concrete (FiniteJetSheafTransfer.lean); the gap's design decision is
    ABSTRACT-FIRST (the paper's own form; [Reviewer] §4.1's criterion falls out) vs a
    parallel `⟨V⟩`-instantiation. Abstract-first is the plan.
  - The gap needs its own `/develop --decompose` iteration before its tickets exist.

- **B-H** (headline): `finiteJet_tateExt_isSheafyComplete` — `FJP/StrongSheafy.lean:60`.
  Composition of B-L3 (corners affinoid) + AG1 (row + transfer) + corners sheafy
  (`isSheafy_ofStronglyNoetherianTate_clean`, WedhornCechAcyclicity — verified present).
  Attacks: composition-level — could corners-sheafy + row hold and the transfer fail? No:
  the transfer IS the implication, and its source proof (l.585–640) uses only the row +
  vertex sheafiness + D-separatedness, all present in the hypothesis set. SURVIVED
  (modulo AG1, which blocks its ticket).

---

## Campaign C — all-degree Čech acyclicity

### Plain-English proof (sources: [Wedhorn] l.4151–4240; [Reviewer] §5.2)
Wedhorn 8.33: for the Laurent 2-cover, the full augmented alternating complex
`0 → 𝒪_X(X) → 𝒪_X(U₁) × 𝒪_X(U₂) → 𝒪_X(U₁∩U₂) → 0` is exact — his proof shows the
surjectivity of λ, λ′ explicitly. 8.34: acyclicity of ideal-generated rational covers by
the A.3 product/refinement induction over Laurent covers. For the examples: [Reviewer]
§5.2's Milnor LES (FJP) and coefficientwise `c₀`-primitives (WP).

### Leaves (first layer)

- **C-L1** (leaf): `wedhorn_lemma_833_deg1_surjective` — `CechAcyclicityFull.lean:41`.
  - Source: [Wedhorn] l.4200–4207 (verbatim): "The equations
    A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩, (f−ζ)A⟨ζ,ζ⁻¹⟩ = (f−ζ)A⟨ζ⟩ + (1−fζ⁻¹)A⟨ζ⁻¹⟩ show the
    surjectivity of λ and λ′ (and in particular the exactness of the first row)."
  - Lean ↔ source: the statement asserts every element of the intersection value is a
    difference of restrictions — exactly λ's surjectivity transported through the
    project's `presheafValue` identifications (`Examples 6.38/6.39` shapes, already
    formalised in the 8.33 development).
  - Discharged by: the existing 8.33 infrastructure (the `laurent*Datum` value
    identifications used by `wedhorn_lemma_834_part_i_laurent_acyclic`'s chain) + the
    Laurent-series splitting `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` (present in the
    ExampleLaurentSeries / LaurentRefinement cluster — audit at ticket time).
  - Attacks: (1) counterexample — none: Wedhorn proves it; (2) edge `f = 0`: U₂ is cut by
    `1/0` — the cover data hypotheses (`hP`,`hM` span conditions) exclude degeneracy the
    same way the existing 8.33 statements do; (3) drift — the Lean form quantifies the
    difference map's surjectivity rather than λ's (λ's domain is the product BEFORE
    quotienting) — these agree because the quotient maps are surjective (8.2.1
    identifications). SURVIVED.

- **C-AG1** (API gap, own design pass): multi-intersection data + the Čech complex on
  `RationalCoveringData` in all degrees + A.3 product/refinement calculus + per-example
  headlines (FJP via the Milnor LES with degreewise strictness over prop:localized-milnor;
  WP via coefficientwise primitives over eq:head-cech's bounded inverse, [WP-paper]
  l.1199–1215). Blocks all C tickets beyond C-L1.

---

## Confidence gate status
- A: all leaves READY (project discharges verified). Skeleton compiles.
- B: B-L1/2/3/6 READY-as-stated (B-L3 blocked by B-L1/2); B-AG1 explicit API gap with
  sub-tree; B-H blocked by AG1. Skeleton compiles.
- C: C-L1 READY; C-AG1 explicit API gap; headlines inside the gap. Skeleton compiles.
- No REVIEW-PENDING leaves. No prior-B2 matches. All leaves single-conclusion.

---

## ChatGPT validation addendum (gpt-5.6-sol, max effort, 2026-08-10)

Verdict: (A) sound, "essentially finished" — independently confirmed the definitional
uniformity bridge and the exact discharge used. (B) sound conditionally. (C) sound in
principle with two required layers my sketch missed. Corrections binding on T615/T621/T622:

- **B (for T615's design brief)**: (i) the Fubini must be topological/isometric, not just
  ring-level (as B-L1/2 already state); (ii) the Koszul code consumes EXPLICIT noetherian
  interfaces — `unitBall E`, `P E m`, `unitBall (P E m)` noetherian
  (FiniteJetGraphKoszul.lean:1255) — the extended corners must supply these from their
  affinoid presentations, `IsStronglyNoetherian` alone is not the consumed interface;
  (iii) abstract-first confirmed: build `StrictMilnorSquare → TateExtension` reusable
  abstraction; (iv) the coefficientwise row extension is verbatim GIVEN the uniformly
  bounded additive section (κ-bound; the project's `sectionD` is isometric, κ = 1) —
  see FiniteJetRings.lean:176 + FiniteJetStrictLocalization.lean:88; (v) rows must be
  natural under further rational restriction, not just per-datum exact.
- **C (for T622's design brief)**: (i) the project's `CechCochain` is the UNNORMALIZED
  complex (all `Fin (q+1) → ι` maps, repetitions included) while Wedhorn's 8.33/8.34 are
  about the ALTERNATING complex — a normalization comparison quasi-isomorphism (or a
  degeneracy contraction) is a required layer; (ii) my "connecting maps vanish iff
  degrees split" framing was WRONG — the correct route is the short exact sequence of
  **augmented algebraic cochain complexes** (Milnor row as degree −1) in `AddCommGrp`/
  `ModuleCat k` + the long exact homology sequence (`ShortComplex.ShortExact.δ`,
  `homology_exact₁/₂/₃`, Mathlib HomologySequence.lean:286) — strictness is needed only
  earlier (for exactness after completed localization), NOT in the cohomological step;
  (iii) WP c₀-primitives confirmed per fixed degree via
  `ContinuousLinearMap.exists_preimage_norm_le` (Banach.lean:162) — per-degree constants
  C_q, no linear splitting needed, one common head for all pieces and multi-intersections;
  c₀-sums only, no inverse-limit claim.
- **C-L1 (T621 addendum)**: the full 8.33 diagram also needs the relation-ideal
  decomposition `(f−ζ)A⟨ζ,ζ⁻¹⟩ = (f−ζ)A⟨ζ⟩ + (1−fζ⁻¹)A⟨ζ⁻¹⟩` (Wedhorn's second
  displayed equation), not only the ambient split — add it as a second step of the
  proof sketch.
