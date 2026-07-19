# Sheafiness completion — live-branch audit (2026-07-19)

**Supersedes** (as status): `SHEAFY-REMAINING-WORK-PLAN.md`, `SHEAFY-FEASIBILITY-MAP.md`,
`STATUS.md` §sheafiness, and the standalone-repo handover's "Audited repository state"
(that handover was audited against the pre-migration snapshot `eaca380`, toolchain
v4.31.0-rc2; its *mandate, literature contract, and phase plan* remain the specification).

## Live target

- Worktree: `aintlib-adic-spaces` (AINTLIB monorepo), branch `dev/adic-spaces`.
- Base commit at takeover: `2e5b1cf60` (v4.33 wave 8) + uncommitted wave-9 repairs.
- Toolchain: `leanprover/lean4:v4.33.0-rc1`, mathlib `fd1d54bcac5c` (2026-07-17).
- Project: `projects/AdicSpaces/Adic spaces/` (lake lib `«Adic spaces»`).

## Wave 9 (this session): v4.33 repair completed, tree green

All remaining v4.33 bump breakage fixed (8 WCA errors + ExampleLaurentSeries +
ExampleUnitDisc + FJP/RestrictedLaurent). Recurring root cause: v4.33 `kabstract`
re-checks embedded proofs/terms at *reducible* transparency, so goals carrying
proofs whose types need a semireducible unfold (e.g. `rfl :
(D₁.interSamePair D₂ h).P = _`, subtype literals proved at a defeq-only type,
`y` used at a defeq datum) reject every `rw`/`erw`/`simp`. Repairs used, in order of
preference:

1. **Named projection lemmas + `Eq.trans` composition** so embedded proofs carry their
   type syntactically: `RationalLocData.interSamePair_P` (LaurentRefinementCore),
   `imagePieceDatum_P` (RelativePieceKeystone), `unitCover_annulus_pair_eq` (WCA — the
   annulus datum's pair proof, substituted at **all 106** occurrences),
   `mk_coeff_mem_isSubring`, `foo_norm_map` (FJP/RestrictedLaurent).
2. **Forward proof instead of goal rewriting** (wave-8 pattern): `hchain`/`hro_eq` in
   `genRestrictedCover_gluing`, the `laurentProdCoverOf_isOXAcyclic` piece-membership
   branches.
3. **`set_option backward.isDefEq.respectTransparency false`** (established per-decl
   escape hatch, ~60 prior uses) on the two dense-side square lemmas
   `unitCover_sq_plus_dense` / `unitCover_sq_minus_dense`, whose `hcomp` goals mix
   `unitCover_plusDatum_B`-typed and `unitDatum …`-typed constants.
4. `Finset.antidiagonal`/`mem_antidiagonal` now resolve to the renamed IsPWO
   (Hahn-series) constants, shadowing the `HasAntidiagonal` export — qualified the ℕ
   uses as `Finset.HasAntidiagonal.*`.

## Phase 0c: live API vs handover specification

| Handover ticket | Live-branch state |
|---|---|
| F1 valid A⁺ bundle | `IsRingOfIntegralElements` (AffinoidRings.lean) is the validity predicate, used by the headline. **No bundle / pair-explicit API yet — to do.** |
| F2 coherent topology | `CompleteTopCommRingCat` still stores an unrelated `TopologicalSpace` + `UniformSpace` (defect confirmed). **Resolution: build the genuine presheaf with completeness/T0 as per-value properties; do not route the new path through the incoherent category.** |
| F3 restrictions without HasLocLiftPowerBounded | `hasLocLiftPowerBounded_faithful(_instance)` (FaithfulLocLift.lean) **proves** the class for complete Tate rings with valid A⁺ (priority 1100). Values of `restrictionMap` are A⁺-independent (`IsLocalization.Away.lift` at proof-irrelevant unit witnesses). Public Tate-scope statements never need the class as a hypothesis. |
| F4 valid localized plus rings | **Done on live branch**: `RationalLocData.completedPlusSubring` = closure-of-integral-closure (Wedhorn 8.16 via 7.19 + 7.47), with instance `presheafValuePlus_isRingOfIntegralElements` (Presheaf.lean:854–889). |
| R1 arbitrary-pair intersections | `interSamePair` (same pair) only. At **Tate** scope, arbitrary-pair valid intersections are constructible via `genPieceDatum` (P-free `rationalOpen`, product trays span ⊤). **To do.** |
| R2 basis + quasi-compactness | `rationalOpen_isOpen` (RationalSubsets.lean), `isCompact_*` family (SpaCompact/SpaCompactNoHArch/SpaQCviaSpvAI). Basis property to be assembled. **Partially exists.** |
| R3 compatibility bridge | Current `IsSheafy.gluing` uses the all-raw-data compatibility. Equivalence with exact-intersection / valid-refinement forms **to do** (proof: factor restriction through the R1 intersection datum). |
| O1–O3 genuine presheaf | **Missing entirely** — `structurePresheaf` is still the locally-fraction placeholder with the discrete topology and the `structurePresheaf_isSheaf` sorry (StructureSheaf.lean:255). Do not fill; quarantine in Phase 7. |
| C1–C5 comparison | **Missing.** |
| P1–P4 A⁺-independence | **Missing.** `StandardCover.lean` is the old (2026-04) reduction scaffold, not `StandardSheafCondition`. |
| S-A/S-B/S-C proof branches | **Assembled and green**: `isSheafy_of_stronglyNoetherian_828b` (WCA:13452) with signature `[CommRing][TopologicalSpace][PlusSubring][IsTateRing][IsStronglyNoetherian][T2Space][IsRingOfIntegralElements A⁺][CompleteSpace(right unif)] → IsSheafy A` — **no CompatiblePlusSubring, no assumed HasLocLiftPowerBounded** (both already removed on the live branch, ahead of the handover baseline). Axiom audit: see below. |
| S-D wrappers | Ring-level definitions (`IsSheafyFor` / `IsSheafyComplete` / `IsSheafyRing`) and the non-complete-A 8.28(b) wrapper **to do**. |

FJP campaign targets (`FiniteJet.finiteJet_isSheafy/isUniform/isDomain/not_noetherian/
not_stablyUniform`, FJP/FiniteJetMain.lean) are sorry-free at file level and
regression-protected.

## Phase 0b: axiom audit (live, post-wave-9, commit `aa28f1f01`)

`#print axioms` on the green tree:

**Axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only — the
regression-protected set; every new wrapper must consume only these):

- `ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` ✓ (the headline)
- `ValuationSpectrum.every_rational_cover_is_OXAcyclic` ✓
- `ValuationSpectrum.cor_8_32_productRestrictionSub_injective` ✓
- `ValuationSpectrum.lemma_8_34_gluing` ✓
- `FiniteJet.finiteJet_isSheafy` / `_isUniform` / `_isDomain` / `_not_noetherian`
  / `_not_stablyUniform` ✓ (all five FJP targets)

**sorryAx-tainted — all on the superseded old S-B route, OFF the headline path**
(the headline's embedding field uses `productRestrictionSub_isInducing_via_equalizer`;
handover rule: leave closed branches closed, do not reopen):

- `productRestrictionSub_isInducing_tate` (StructureSheaf.lean, old OMT route)
- `cor_8_32_productRestrictionSub_isEmbedding` (combines the tainted inducing)
- `isSheafy_ofStronglyNoetherianTate_clean` (duplicate wrapper over the old route;
  candidate for deprecation in Phase 7)

Conclusion: **S-A, S-B, S-C are closed on the live branch.** The remaining program
is the definitional/API work (R/O/C/P/S-D phases), not the 8.28(b) mathematics.

## Program status at end of session (2026-07-19) — all Lean sorry-free

New files (all additive; WCA/828b untouched):

| File | Contents |
|---|---|
| `SheafyFoundations.lean` | F1: `RingOfIntegralElements` bundle + `toPlusSubring` local-instance bridge + pair-explicit `spa`. |
| `StructurePresheafLimit.lean` | O1–O3: `spaOpen`/`spaOpens`/`RationalIndex`/`limitSections` (closed ⇒ complete, T2; initial = projective-limit topology; **no discrete topology anywhere**), continuous functorial `limitRestrict`, the rational comparison `limitEval : limitSections (spaOpens D₀) ≃+* presheafValue D₀` with continuous inverse, `spaOpens_globalLocData : R({1}/1) = ⊤` (Remark 8.3, presheaf level). |
| `RationalIntersection.lean` | R1: `interDatum`/`interRational` (arbitrary-pair valid intersections, Tate; no shared-`P` hypothesis; different-pairs regression example). R3: `AllDataCompatible ⟺ RationalRefinementCompatible ⟺ ExactIntersectionCompatible` (the legacy `IsSheafy.gluing` input is the literature condition). |
| `RationalBasis.lean` | R2: `exists_isRational_spaOpen_subset` (Wedhorn 7.35(2), Tate — via the `RCoord`-profile inducing + sierpiński unfolding + `interRational` folds) and `isCompact_spaOpen` (7.35(3)). |
| `SheafyPair.lean` | C1–C5: finite rational refinements (`exists_finite_rational_refinement`, `refinementCovering`, `interCovering`); `limitRestrict_injective`, `exists_limitSections_glue`, `isEmbedding_limitRestrictProd` (arbitrary covers, arbitrary opens; Remark 8.20's embedding via the nhds/comap computation on the initial topology); `IsLimitSheaf`; **`isSheafy_iff_isLimitSheaf`** — the finite rational criterion *is* pair-level sheafiness for the genuine presheaf. |
| `SheafyRing.lean` | S-D + P1/P3(→)/P4: `IsSheafyFor` (explicit **bundled valid** choice; `HasLocLiftPowerBounded` existentially bundled, never a public hypothesis), `IsSheafyComplete` (universal valid-`A⁺`, Wedhorn 8.26 complete specialization), `IsSheafyRing` (literal 8.26 over `UniformSpace.Completion A`, completion-package as instance parameters); **`isSheafyFor_of_stronglyNoetherianTate`**, **`isSheafyComplete_of_stronglyNoetherianTate`** (the principal theorems); `isSheafyFor_congr_of_stronglyNoetherianTate` + non-defeq-pairs example (P4 at the 8.28(b) target scope); `StandardCoverData`/`StandardSheafCondition` (Spa-uniform covers; `A⁺`-free signature) + `standardSheafCondition_of_isSheafyComplete`/`_of_stronglyNoetherianTate` (P3, provable direction). |

Phase 7 migration performed: the locally-fraction/discrete `structurePresheaf` is
docstring-quarantined as a legacy placeholder (its sorry intentionally NOT filled,
per the handover prohibition — filling it would "prove" all Tate rings sheafy against
Remark 8.17); the `CompatiblePlusSubring` "Wedhorn Remark 7.17" misattribution is
corrected (b2-log `T-WC-CITATION-CORRECTIONS-2026-05-28`(b)).

## Second pass (same day): `HasLocLiftPowerBounded` purge + items 1 & 2

- **`IsSheafyFor`/`StandardSheafCondition` refactored**: the restriction-map package
  is now **derived** inside the definitions from the complete analytic scope
  (`hasLocLiftPowerBounded_faithful`, a theorem) — `HasLocLiftPowerBounded` appears in
  no public signature, not even existentially. The pair-level definition is scoped to
  complete Tate rings, exactly where Wedhorn's restriction maps exist (Prop 8.2 via
  7.52(2)). Supporting de-leak: `genPieceDatum`/`genPiece_hopen`/
  `pod_absorb_finset_mul_pow` (RelativePieceKeystone) and the R1 datum layer
  (RationalIntersection) no longer capture `[PlusSubring A]`/`[IsHuberRing A]` — the
  intersection/gen-piece *data* are now visibly `A⁺`-free.

- **Item 2 (completion, `SheafyRing.lean`)**: `CompletionModel A P :=
  presheafValue (globalLocData P)` — the project's own `Â = 𝒪_X(X)` (Remark 8.3) —
  now carries a **fully populated, completeness-free** instance stack: complete
  (right uniformity), T2, Huber (`presheafValue_concretePair`), nonarchimedean, and
  Tate when `A` is (completeness-free restatement via `presheafValue_topNilUnit`).
  `IsSheafyRing A` is the **literal Wedhorn Definition 8.26** over this completion,
  with *no* instance parameters. `isSheafyRing_of_stronglyNoetherianTate` proves it
  for complete strongly noetherian Tate `A` (via
  `completionModel_isStronglyNoetherian`, the faithful transport at the whole-space
  datum). **Reduction for the non-complete wrapper**: exactly one transport remains —
  `IsStronglyNoetherian A → IsStronglyNoetherian (CompletionModel A P)` without
  `CompleteSpace A` (the faithful proof sits in Wedhorn828's complete section; its
  `presheafValue_mvRestricted_surjection` chain would need its `CompleteSpace A`
  section hypothesis discharged).

- **Item 1 (cofinality, generation side — `StandardRefinement.lean`)**: the
  `Spv`-level multiplicative toolkit (`Spv.vle_mul_of_vle_of_vle`,
  `Spv.vle_of_vle_mul_right` — the slot-comparison/cancellation engine of Kedlaya
  Lemma 1.6.8), the **maximum argument** (`exists_not_vle_zero_of_span_eq_top`,
  `exists_max_vle_of_span_eq_top`: a valuation cannot vanish on a generating family;
  Kedlaya 1.6.2), and **`StandardCoverData.ofSpanTop`**: for every valid rational
  base and every finite family generating the unit ideal, the generated cover
  `{R(D₀) ∩ R(F/f)}` is `Spa`-**uniformly** subordinate and covering — a genuine
  `StandardCoverData` at every `A⁺` simultaneously. This populates
  `StandardSheafCondition` with Kedlaya's actual covers. **Remaining for full
  P3(←)**: the descent branch of Lemma 1.6.8 — subordinating the product-selection
  pieces of an *arbitrary* rational cover and eliminating the unslotted pieces
  (Wedhorn 7.54's normalization) — the missing API recorded in
  `WedhornStandardCoverRefinement.lean`; the toolkit above is its intended engine.

## Honest remaining items (recorded, none on any theorem's dependency path)

1. **P3(←) descent** (Kedlaya Lemma 1.6.8's refinement of arbitrary rational covers):
   see above — generation side done, descent branch remains
   (`WedhornStandardCoverRefinement.lean`'s recorded missing API).
2. **Non-complete strong-noetherian transport**: the single missing input for the
   non-complete ring-level 8.28(b) wrapper (see Item 2 above).
3. Old sorry-tainted S-B route (`productRestrictionSub_isInducing_tate`,
   `cor_8_32_productRestrictionSub_isEmbedding`, `isSheafy_ofStronglyNoetherianTate_clean`)
   — superseded, off-path, candidates for deletion by the cleanup fleet.
