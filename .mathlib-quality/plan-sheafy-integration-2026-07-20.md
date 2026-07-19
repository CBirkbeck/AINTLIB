# Sheafy integration campaign — 2026-07-20 (WO0–WO6)

Baseline: branch `dev/adic-spaces`, commit `f88fd95e9`. Builds green:
`«Adic spaces».SheafyRing`, `«Adic spaces».FJP.FiniteJetMain`, `«Adic spaces».StandardRefinement`.

## Regression gates (WO0) — axiom sets must stay `[propext, Classical.choice, Quot.sound]`

| Declaration | Role |
|---|---|
| `FiniteJet.finiteJet_isSheafy` | FJP headline 1 |
| `FiniteJet.finiteJet_isUniform` | FJP headline 2 |
| `FiniteJet.finiteJet_isDomain` | FJP headline 3 |
| `FiniteJet.finiteJet_not_noetherian` | FJP headline 4 |
| `FiniteJet.finiteJet_not_stablyUniform` | FJP headline 5 |
| `ValuationSpectrum.isLimitSheaf_of_isSheafy` | C3+C4 |
| `ValuationSpectrum.isSheafy_of_isLimitSheaf` | C5 |
| `ValuationSpectrum.isSheafy_iff_isLimitSheaf` | C5 iff |
| `ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` | the strongly noetherian theorem |

Statements of these are frozen; no hypothesis or axiom-set changes.

## Source anchors (verified verbatim against local texts this session)

* Wedhorn `references/wedhorn.txt`: Remark 8.20 (:3995 — sheaf of topological rings
  ⟺ `∀T. Hom(T, O(−))` sheaf of sets ⟺ ring-sheaf + product-embedding), Definition
  8.26 (:4040 — f-adic `A` sheafy ⟺ ∀ A⁺ ⊆ Â ring of integral elements,
  `O_{Spa(Â,A⁺)}` sheaf of topological rings), Lemma 7.54 (:3490, proof = [Hu3] 2.6),
  Corollary 7.53-preamble (:3480 — no-common-zero ⟺ span ⊤, complete case),
  Theorem 8.28 (:4051).
* Huber [Hu3] `references/huber1994.txt` Lemma 2.6 (:1180–1210): slot products
  `T = {t₁⋯tₙ}`, admissible subset `S` (some slot hits `sᵢ`), (1) `R(T/t) = ⋂ᵢR(Tᵢ/tᵢ)`,
  (2) slot-max covering, (3) ⟹ span S (complete input) + `R(T/s) = R(S/s)`.
* Kedlaya AWS 2017 (scratchpad `kedlaya2017.txt`): Def 1.2.3 (:476 — O(U) = inverse
  limit of B over rational localizations inside U), Def 1.2.8 (:510 — sheafy pair;
  "depends only on A, not A⁺ (Remark 1.6.9)"), Lemma 1.6.8 (:1256 — proof re-bases:
  "every rational subspace of X is itself the spectrum of a Huber pair", then the
  Huber product trick with Corollary 1.5.21 as the completeness input), Remark 1.6.9
  (:1280), Remark 1.6.10 (:1283 — non-analytic caveat).
* Buzzard–Verberkmoes: cited for the embedding/strictness formulation (Remark 8.20's
  second condition); the project's `IsSheafy.embedding`/`IsLimitSheaf.isEmbedding`.

## WO1 — public structure presheaf (files: CompleteTopCommRingCat, StructurePresheafLimit → new `StructurePresheafBundled.lean`, StructureSheaf)

1. Fix `CompleteTopCommRingCat` coherence: remove independent
   `instTopologicalSpace`/`instIsTopologicalRing` fields; derive topology from the
   uniformity (`UniformSpace.toTopologicalSpace`), keep `IsTopologicalRing` about
   that topology. (Currently an object may carry a topology unrelated to its
   uniformity: `Hom`-continuity refers to the former, `CompleteSpace` to the latter.)
2. `limitPresheaf : Presheaf CompleteTopCommRingCat (SpaTop A)` — obj := bundled
   `limitSections V` (uniformity = subspace-of-product; complete by
   `isClosed_limitSections`; T0 from T2), map := `limitRestrict`; functor laws from
   `limitRestrict_id/_comp`.
3. `IsSheafOfTopologicalRings` (Wedhorn Remark 8.20, representable form): ∀ (T)
   topological ring, `U ↦ ContinuousRingHom T (O(U))` is a sheaf of sets; proved
   equivalent to `IsLimitSheaf` (elementary; the embedding direction via the
   induced-topology test object). New endpoints `isLimitSheaf_iff_homSheaf` etc.
4. Replace public `structurePresheaf`/`structureSheaf`/`AffinoidAdicSpace.sheaf` by
   the limit object; quarantined discrete placeholder demoted to a private/renamed
   legacy def or deleted with its `sorry` (`structurePresheaf_isSheaf`); no public
   name keeps pointing at the placeholder. `AffinoidAdicSpace.sheaf` becomes
   sorry-free.
5. Universe reduction: `IsLimitSheaf` covers with `{ι : Type u}` extended to
   arbitrary `ι : Type v` via range-reduction (`Opens`-valued families factor
   through `Set (Opens _)` ⊆ Type u). New lemma `IsLimitSheaf.glue_of_family`, etc.

Acceptance: builds; `#print axioms` clean on `limitPresheaf_isSheaf`-equivalents,
`AffinoidAdicSpace.sheaf` axiom-free of `sorryAx`; regression gates intact.

## WO2 — genuine A⁺-independence (Kedlaya 1.6.8/1.6.9), new file `StandardDescent.lean`

Analysis (this session): the pair-transfer factors through the A⁺-free standard
condition. Statements about covering DATA are A⁺-independent up to definitional
proof-irrelevance (`presheafValue`, `restrictionMap` don't see `A⁺`; `RationalCovering`'s
Prop fields do); the compatibility hypothesis transfers by the R3 bridge
(`allDataCompatible_iff_exactIntersectionCompatible`, whose exact-intersection form is
pointwise-uniform). The single genuinely relative step (covers of a rational base
`R(D₀)` with generators from `𝒪(D₀)`) is Kedlaya's re-basing; its ring-level keystone
exists (`relativePiece_equiv`) but currently carries `[IsStronglyNoetherian]`.

Deliverables:
1. `trivial cover lemma`: a rational covering with the base among its pieces
   satisfies separation+gluing+embedding unconditionally.
2. Refinement transfer (elementary, noetherian-free; = the factorization principle of
   WO2 task 4, proved as a topology lemma `IsEmbedding.of_comp'`-style +
   separation/gluing transfer): if `C'` refines `C` (same base) and `C'` satisfies
   the axioms and each piece `E` of `C` has the intersection cover `{E ∩ P}`
   separated, then `C` satisfies the axioms.
3. `standardSheafCondition_of_isSheafyFor` — **single-pair** derivation of the
   A⁺-free `StandardSheafCondition` (upgrade of the current
   `standardSheafCondition_of_isSheafyComplete`): the Kedlaya-1.6.9 mechanism.
4. Whole-space Huber 2.6 at complete-Tate scope (noetherian-free): every rational
   covering of the whole space at a given `A⁺` is refined by a `genRestrictedCover`-
   shaped standard cover (project's `exists_form_a_refinement`-chain, hypothesis
   audit + rescope if needed).
5. Pair-transfer at whole-space scope + attempt at general bases; general bases
   need the noetherian-free keystone (blocked-dependency probe: can
   `relativePiece_equiv`'s chain drop `[IsStronglyNoetherian]`?). If blocked, record
   the exact missing declaration; do NOT ship `iff_of_true`.

## WO3 — naming hierarchy (SheafyRing.lean)

* `IsSheafyFor A Aplus` (pair) — keep.
* `IsSheafyComplete A` (complete Tate, ∀ Aplus) — keep.
* current `IsSheafyRing` → **rename `IsSheafyTateRing`** (it is Tate-scoped;
  Definition 8.26 is for general f-adic rings; the non-Tate structure presheaf
  (restriction maps at nonanalytic scope) is missing infrastructure — recorded, not
  concealed). Completion-model independence: for two pairs of definition `P`, `P'`,
  the models are canonically equivalent as topological rings compatibly with the
  maps from `A` — prove `IsSheafyFor`-transport along such an equivalence
  (`isSheafyFor_congr_of_ringTopEquiv`) and derive `P`-independence.
* Legacy class `IsSheafy` gets a deprecation-style docstring: internal finite
  rational criterion, not the literature ring-level notion (name kept for the
  existing proof corpus; public API goes through `IsSheafyFor`).
* `IsSheafyTateRing A ↔ IsSheafyComplete A` for complete Tate `A` needs the
  comparison `A ≅ CompletionModel A P` for complete `A` (Remark 8.3) — via the
  transport theorem above applied to `globalSections`-comparison; else recorded.

## WO4 — noncomplete strongly-noetherian wrapper (SheafyRing.lean)

* `completionModel_isStronglyNoetherian` currently sits inside a section with
  leaked `[PlusSubring A][IsNoetherianRing A][HasLocLiftPowerBounded A][CompleteSpace A]`.
  Audit `presheafValue_isStronglyNoetherian_faithful`'s true requirements; restate
  the transport with only the mathematically necessary hypotheses (target:
  Tate + strongly noetherian, no completeness of `A`, no ambient `A⁺`).
* Final: `isSheafyTateRing_of_stronglyNoetherian : [IsTateRing A]
  [IsStronglyNoetherian A] → IsSheafyTateRing A` (noncomplete OK) — by transport
  into the completed theorem; no duplication of the hard proof.

## WO5 — FJP corollaries (FJP/FiniteJetMain.lean or new FJP/FiniteJetSheafyRing.lean)

* `finiteJet_isSheafyFor` (∀ valid pair), `finiteJet_isSheafyComplete`,
  `finiteJet_isSheafyTateRing`, and the presheaf-level
  `finiteJet_limitPresheaf_isSheaf` via WO1's endpoint. All corollaries; originals
  untouched.

## WO6 — audit

Full builds; `#print axioms` on every endpoint (old + new); audit table
(declaration / meaning / source / hypotheses / axioms / scope); grep pass for
`sorry|admit|axiom|unsafe` and stale claims; explicit answer to the
`IsSheafyRing → public presheaf is a sheaf of topological rings` chain question
with named theorems.
