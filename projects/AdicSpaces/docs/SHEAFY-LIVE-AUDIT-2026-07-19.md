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

## Phase 0b: axiom audit (live)

(To be filled by `scratchpad/axiom_audit.lean` output — run after each phase.)

## Remaining-program tickets

Tracked in the session task board: F1 bundle → R1+R3 → O1–O3 → C1–C5 → P1–P4 → S-D →
Phase 7/8 migration+verification. New files planned:
`SheafyFoundations.lean`, `StructurePresheafLimit.lean`, `SheafyPair.lean`,
`StandardSheafCondition.lean`, `SheafyRing.lean` — all additive; WCA and the 828b
assembly are regression-protected and not to be re-proved.
