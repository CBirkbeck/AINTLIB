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

## Honest remaining items (recorded, none on any theorem's dependency path)

1. **P2 general cofinality / P3(←)** (Kedlaya Lemma 1.6.8, Wedhorn 7.54 general
   branch): `StandardSheafCondition A → IsSheafyFor A Aplus` for *generic* complete
   Tate `A` needs every rational cover refined by a standard one; the general
   non-standard-shape branch is the missing API already recorded in
   `WedhornStandardCoverRefinement.lean`. Not needed by the strongly noetherian
   theorems (the 828b input quantifies over all valid pairs directly).
2. **Completion transport** (Wedhorn 7.47 + Tate/strongly-noetherian transfer to
   `Â`): required to *populate* `IsSheafyRing`'s instance parameters and to state the
   non-complete 8.28(b) wrapper. No such transport exists in the project yet; the
   definition is stated with the completion package as visible instance parameters.
3. Old sorry-tainted S-B route (`productRestrictionSub_isInducing_tate`,
   `cor_8_32_productRestrictionSub_isEmbedding`, `isSheafy_ofStronglyNoetherianTate_clean`)
   — superseded, off-path, candidates for deletion by the cleanup fleet.
