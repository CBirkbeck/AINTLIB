# Decomposition — STREAM-Y0: the coarse modular curve (M3, Option 2, user-ratified 2026-07-22)

## Goal and skeleton location

**Deliverable**: `YZeroCoarse R N hN hinv : Scheme` = the coarse modular curve `Y₀(N)` over a
fixed `R` with `IsUnit (N : R)`, `N ≥ 3`, as the Borel instance of the uniform
`YHCoarse R N hN hinv H := 𝔐([Γ(N)]).base / H`, with the categorical-quotient universal
property and projection/structure-morphism properties. KM 8.1.1 route at `δ = [Γ(N)]`
(Option 2 of the 2026-07-22 literature survey; user-ratified).

Skeleton (all `:= by sorry`, this session):
- `Moduli/CoarseSpace.lean` (NEW): `RepresentableBy.baseSchemeAction`(+`_over`),
  `isAffine_base_transport`, `gammaFullNaive_exists_representableBy_isAffineHom`,
  `gammaFullNaive_isAffineHom_structMap`, `coarseQuotient`/`coarsePr`/`coarseStruct` (+ 3 spec
  theorems + ∃!-UP + 3 instances), `borel`, `semiBorel_le_borel`, `YHCoarse`, `YZeroCoarse`.
- `Moduli/EngineMouth.lean` (+1): `exists_representableBy_isAffine_of_rigidNoeth_of_torsor`.
- `Moduli/EngineWiring.lean` (+2): `exists_representableBy_isAffine_baseChange_two/three`.
- `Moduli/Recollement.lean` (+1): `exists_representableBy_isAffineHom_of_baseChange_cover`.

## Prose proof (mirroring the sources)

KM 8.1.1 (print p. 224, verbatim): "We define M(𝒫) as the quotient scheme M(𝒫) = 𝔐(𝒫, δ)/G.
… It 'exists' because 𝔐(𝒫, δ) is itself affine." Over our fixed `R` with `N ≥ 3` invertible,
take `δ = [Γ(N)]` (representable in-tree: the landed receipts) and `𝒫` trivial, `G = H` acting
through the KM 7.4.2 identifications ((4) verbatim: "identifies [Γ₀(N)] with the quotient of
[Γ(N)] by the Borel subgroup (∗ ∗; 0 ∗) of GL(2, ℤ/Nℤ)"). KM 8.1.5 (p. 226 verbatim
"M(𝒫)/G ≅ M(𝒫/G)") collapses `M([Γ(N)]/H)` to `M([Γ(N)])/H = 𝔐([Γ(N)]).base/H` since
`M(𝒫) = 𝔐(𝒫)` for representable 𝒫 (8.1.1). The quotient exists by the affineness of the
representing base over `Spec R` (KM's existence sentence, executed by the PROVEN
relative-invariant-Spec engine), and its characterizing property is the categorical-quotient
universal property (Loeffler Prop 3.6.1 verbatim: the unique S-scheme "representing the functor
Y ↦ (homs of S-schemes X → Y commuting with the G-action)"; his proof: "for X = Spec(A) affine,
Spec(A^G) works, and one can show that these patch nicely"). The affineness itself follows the
sources' construction: per KM 8.1.1 the local (on `Spec R`) pieces `𝔐(𝒫,δ)/G` are affine
("𝔐(𝒫,δ) is itself affine"), and they "patch together" — in-tree this is exactly the engine's
D(2)/D(3) recollement (EngineWiring/Recollement, Loeffler Thm 3.7.4's proof: two rigidifier
legs glued over `R[1/6]`-agreement).

NOT claimed (source-faithful exclusions): fine representability (Loeffler 3.8.3: −1 ∈ Γ₀(N);
in-tree no-go `hH_refuted_of_neg_one_mem`); base-change functoriality (KM Remark 8.1.7 p. 227
verbatim: "Formation of the coarse moduli scheme does not always commute with base change");
étale/torsor properties of the projection (−1 acts trivially on the scheme, the action is not
free; KM 8.1 makes no such claim). P2 follow-ons, NOT ticketed now: KM 8.1.3.1 geometric points
(needs a KM A7.2.2 source pass first — its proof pages were NOT read this session), KM 8.1.2
normality, Loeffler's smoothness "Fact" (M4, parked).

## Leaves

- **[Y0-ACT] `autBase` + `baseSchemeAction` + `_over`** (CoarseSpace.lean)
  - Source: KM 8.1.1's G-action on 𝔐(𝒫,δ) (p. 224, quoted above); the transport mechanism is
    in-tree Yoneda (`ForMathlib/RepresentableAut.lean:78` `autMulHom : Aut F →* Aut Y`, PROVEN)
    + `SchemeAction.ofAut` (SchemeQuotient.lean:54, PROVEN — the variance-normalizing trick,
    documented at GammaHRepresentability.lean:115-120: "a genuine SchemeAction homomorphism
    (SchemeAction.ofAut, via (·).inv)").
  - Discharge: `EllObj.autBase` EXISTS PROVEN (QuotientProblem.lean:568) and the exact
    ofAut∘autBase∘autMulHom composite is the landed `simulSchemeAction` idiom
    (QuotientProblem.lean:606-616) — `baseSchemeAction` is its absolute-level mirror, a pure
    composition (skeleton already sorry-free for the def). `_over` = `EllHom.base_w` of the
    transported automorphism (field, EllCategory.lean:61).
  - Attacks: (1) variance — Aut-mul in `CategoryTheory.Aut` composes contravariantly to ≫;
    a wrong-order `map_mul'` fails to elaborate, caught at build; `ofAut` exists precisely to
    absorb one inversion — spec follows the in-tree EquivariantRelRepData twist doc, consumers
    (quotient) are H-reindexing-invariant so an overall `γ ↦ γ⁻¹` twist is harmless
    (`FreeAction is invariant under γ ↦ γ⁻¹`, ibid.). (2) `_over` edge: γ = 1 trivially; any γ:
    base_w is a FIELD — no counterexample possible. (3) hidden hypothesis: none — no Finite G
    needed for the action itself (only the quotient needs it). SURVIVED.

- **[Y0-AFF1] `exists_representableBy_isAffine_of_rigidNoeth_of_torsor`** (EngineMouth)
  - Source (verbatim, KM 8.1.1 p. 224): "It 'exists' because 𝔐(𝒫, δ) is itself affine."
    KM pp. 112-116 (the 4.7.0 engine): X₀ = 𝔐(𝒫,δ)/G with 𝔐(𝒫,δ) affine.
  - Discharge: re-walk `representable_of_rigidNoeth_of_torsor` (EngineMouth:628, PROVEN):
    the body ALREADY establishes `haff : IsAffine XM.base` (:646) and obtains
    `⟨X₀, q, hqfull, hqepi, hqlift, hqsurj, hqetale⟩ := exists_engineQuotient …`; the ONE new
    fact is `IsAffine X₀.base`, proven by the unique-iso comparison against
    `Spec Γ(XM.base, ⊤)ᴳ`: `hqlift` (the recorded UP) vs `existsUnique_invariantsπ_lift`
    (AffineQuotient.lean, PROVEN) through `XM.base.isoSpec` — the exact GHB4/f₀_finite_etale
    comparison dance executed 3× this session (v10.349). Then return the ∃-tuple with the
    RepresentableBy already built at the end of the existing proof.
  - Attacks: (1) is X₀.base REALLY affine — could exists_engineQuotient's output be non-affine?
    The UP pins it up to iso against Spec of invariants; IsAffine transports along iso
    (`IsAffine.of_isIso`, in-tree idiom EngineWiring:59) — composition airtight. (2) statement
    drift: conclusion is ∃-form, NOT a change to the landed Prop theorem (additive; the landed
    statement byte-stable). (3) hypothesis strength: same hypothesis set as the landed theorem —
    nothing smuggled. (4) discharge sizes: existing body ≈ 55 lines re-walked + ≈ 40-line
    comparison (grounded: f₀_finite_etale's transport this session was 44 lines). SURVIVED.

- **[Y0-AFF2/3] `exists_representableBy_isAffine_baseChange_two/three`** (EngineWiring)
  - Source: the two legs of Loeffler Thm 3.7.4's proof (p. 18 verbatim: "Both have group
    actions (GL₂(F₃) and GL₂(F₂) × {±1}). Given 𝒫 relatively representable and rigid,
    construct one object by taking ℰ/Y(3) … Take invariants").
  - Discharge: the landed leg proofs (EngineWiring:41-68 / :77-108) verbatim, with the final
    call swapped to [Y0-AFF1]; every hypothesis instantiation (`hQaff3/4` via
    `naiveLevelThree/Four_representable_by_affine` + uniqueUpToIso, `hPaff` via
    `AffineOverEll.baseChange`, htors, RigidNoeth.baseChange) is ALREADY in those proofs.
    Grounded size: 30 lines each → ≈ 35 each.
  - Attacks: (1) the aux witnesses are ∃-affine ALREADY (Bootstrap.lean:79 shape
    `∃ X, IsAffine X.base ∧ Nonempty (RepresentableBy X)` — the idiom this stream reuses);
    sorry-status attack: receipts census (run TODAY, twice) proves the transitive chain
    axiom-clean. (2) universe: the φ's are ULift'd in the legs already. SURVIVED.

- **[Y0-AFF4] `exists_representableBy_isAffineHom_of_baseChange_cover`** (Recollement)
  - Source (verbatim, KM 8.1.1 p. 224): "The resulting R-scheme is clearly independent of the
    auxiliary choice of δ (and so patches together)." — the patching is the in-tree recollement
    (Recollement.lean:4233, PROVEN, incl. the v10.326 B2-amended `hrel` hypothesis which this
    mirror KEEPS — prior-B2 inheritance addressed).
  - Discharge: the landed proof extracts `Xa/Xb := Functor.reprX` of the legs and returns
    `glueEllObj a b Xa Xb (overlapIso …)` via `glueEllObj_representableBy`. New content:
    (i) transport leg-affineness to the reprX's (`isAffine_base_transport`, the
    EngineWiring:53-59 idiom); (ii) `IsAffineHom (glueEllObj …).structMap` target-locally:
    `IsZariskiLocalAtTarget @IsAffineHom` over `D(a) ⊔ D(b) = Spec R` (from `hab`; the
    same cover the file itself glues over), with the restriction over `D(a)` identified with
    `Xa.structMap`-side via the construction's own chart isos (`glueQ` legs; in-file API
    around :1600-1700, :2747). The mirror lives IN Recollement.lean with access to the
    private `glueEllObj`.
  - Attacks: (1) glued-from-affines is NOT absolutely affine in general — correct, which is
    WHY the conclusion is `IsAffineHom structMap` (target-local), not `IsAffine base`; over
    the affine `Spec R` the consumer recovers `IsAffine` if wanted — no false leaf. (2) does
    `D(a) ∪ D(b) = ⊤` need `hab`? Yes and hab is a hypothesis (⟨-1,1⟩ at (2,3) — in-tree
    precedent EngineWiring:118). (3) chart-identification risk: the construction's own
    representability proof needed exactly these charts; if the chart API turns out
    insufficient, fallback = prove the restriction-iso from `glueEllObj_representableBy` +
    `RepresentableBy.baseChange`-uniqueness (uniqueUpToIso at the leg level) — two routes,
    both from PROVEN material. Sizing: the unknown of the plan; bounded by the in-file chart
    API (execution audits `glueQ` first; est. 60-120 lines). SURVIVED (with the two-route
    hedge recorded).

- **[Y0-AFF5] `gammaFullNaive_exists_representableBy_isAffineHom` +
  `isAffine_base_transport` + `gammaFullNaive_isAffineHom_structMap`** (CoarseSpace)
  - Source: composition of the above (KM 8.1.1's full sentence chain).
  - Discharge: AFF5 = [Y0-AFF4] at (a,b) = (2,3), hab = ⟨-1,1, by ring⟩, hrel from
    `(gammaFullNaive_affineOverEll R N hinv).relativelyRepresentable`, legs from [Y0-AFF2/3]
    at P := gammaFullNaiveProblem (its AffineOverEll + rigidNoeth are the landed receipts'
    inputs) — mirroring `representable_of_affineOverEll_of_rigidNoeth` (EngineWiring:115-120)
    verbatim. Transport: `uniqueUpToIso` + `IsIso baseHom` + `IsAffine.of_isIso` +
    (`IsAffineHom` from affine source over affine target — mathlib; or transport IsAffineHom
    directly along the base iso by `MorphismProperty.cancel_left_of_respectsIso` +
    `EllHom.base_w`). NOTE the awayHom-vs-awayHomWire defeq seam (both are
    `CommRingCat.ofHom (algebraMap …)` — EngineWiring:35-37 vs Recollement:118; the landed
    :115-120 already composes across it, so the mirror composes identically).
  - Attacks: (1) N ≥ 3 needed? The legs need only AffineOverEll + RigidNoeth (any P);
    hN enters through `gammaFullNaive_rigidNoeth` exactly as in the landed receipt — same
    hypotheses, no drift. (2) `IsAffineHom structMap` vs `IsAffine base`: over `Spec R`
    equivalent; structMap-form chosen as the stable engine-facing signature. SURVIVED.

- **[Y0-DEF/UP/PROPS] `coarseQuotient`/`coarsePr`/`coarseStruct` + spec + UP + instances**
  - Source: KM 8.1.1 quotient (quoted); Loeffler Prop 3.6.1 (p. 17 verbatim above) for the UP.
  - Discharge: pure delegations to the PROVEN relative-invariant-Spec engine at
    `f := X₀.structMap`, `S := Spec R`: `relQuotient`/`relQuotientπ`/`relQuotientStruct`,
    `relQuotientπ_comp_relQuotientStruct`, `hom_comp_relQuotientπ`,
    `existsUnique_relQuotientπ_lift`, `isIntegralHom_relQuotientπ` (freeness-free),
    `surjective_relQuotientπ_of_free` (hfree-free despite the section name),
    `isAffineHom_relQuotientStruct`. One-to-three-liners each.
  - Attacks: (1) freeness — the H-action on the scheme has −1 in its kernel (the [−1]-iso of
    marked curves), so NO étale/finite-free claims are made; integral/surjective/affine are the
    freeness-free engine facts — checked against their statements this session. (2) [Finite G]:
    required by the engine — H ≤ GL₂(ZMod N) finite ✓ (NeZero N). (3) universes: engine's G is
    `Type*`(section `{G}`) — ↥H : Type 0 vs Scheme.{u}: VERIFY at build; fallback = ULift
    reindex as EngineWiring did (precedent :48-51). SURVIVED (universe check delegated to the
    skeleton build).

- **[Y0-BOREL] `borel` + `semiBorel_le_borel` + `YHCoarse`/`YZeroCoarse`**
  - Source (verbatim, KM 7.4.2(4) p. 198): "identifies [Γ₀(N)] with the quotient of [Γ(N)] by
    the Borel subgroup (∗ ∗; 0 ∗) of GL(2, ℤ/Nℤ)." Loeffler Fact 3.8.1 (p. 19): "for
    H = {(⋆ ⋆; 0 ⋆)}, this is Γ₀(N)."
  - Discharge: `borel` closure proofs mirror `semiBorel`'s landed ones (GammaHSemiBorel:65+,
    Matrix.mul_apply/Fin.sum_univ_two + IsUnit-det arguments — simpler here: only the (1,0)
    entry pinned); `semiBorel_le_borel` by unfolding carriers; `YHCoarse` = the haveI-wired
    `coarseQuotient` at `gammaHAut R N H` (LANDED, GammaHRepresentability:3297).
  - Attacks: (1) carrier convention: glSmul is `g • (P,Q) = (g₀₀P + g₁₀Q, g₀₁P + g₁₁Q)` and
    semiBorel pinned entries (0,0)=1, (1,0)=0 — Borel drops the (0,0)-pin only: consistent
    with KM's (∗ ∗; 0 ∗) under the SAME row/column convention as the landed semiBorel (the
    subgroup {g | g 1 0 = 0}). (2) closure: (1,0)-entry of a product of two lower-zero
    matrices = g₁₀h₀₀ + g₁₁h₁₀ = 0 ✓; inverse via adjugate/det entries — for 2×2, inverse's
    (1,0) entry = -g₁₀/det = 0 ✓ real. (3) `YHCoarse` at H = ⊥: quotient by trivial group —
    degenerates safely (engine handles trivial G). SURVIVED.

## Prior-B2 consultation
`b2_log.jsonl`: no name/shape matches with the new leaves. Two ADDRESSED inherited B2s:
(i) Recollement v10.326 bare-presheaf amendment — [Y0-AFF4] keeps `hrel` verbatim;
(ii) the v10.345 orbit-presheaf non-sheafness (GammaH B2) — this stream quotients SCHEMES,
never the orbit presheaf; the coarse scheme represents nothing and no representability
statement is made for it.

## Confidence gate
1. Every leaf discharged from PROVEN in-tree code (cited file:line, read this session) or
   mathlib API (reprX/representableBy/uniqueUpToIso/IsAffine.of_isIso — in-tree usage sites
   cited as witnesses); the single audit-risk (AFF4 chart API) carries a two-route hedge. ✓
2. Skeleton compiles: pending the build launched this session — gate CONDITIONAL on it. (✓/✗
   recorded at ticket-commit time.)
3. Verbatim quotes: KM pp. 100/198/199/224/225/226/227 + Loeffler pp. 17/18/19 — ALL read as
   page images THIS session (2026-07-22). ✓
4. Adversarial blocks per leaf above (≥3 attacks each). ✓
5. b2 log consulted; two inherited B2s addressed by design. ✓
6. Tree mirrors KM 8.1.1's sentence structure: quotient-definition → existence-by-affineness →
   patching; sizes grounded in the in-tree proofs being re-walked (cited line counts). ✓
7. Single-conclusion: every ∃-leaf is a shared-witness existential (X with property ∧
   representability — the witness is shared, NOT split, per statement-splitting.md exception,
   matching the landed Bootstrap:79 idiom); instances/theorems single-conclusion. ✓
