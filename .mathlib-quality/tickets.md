# Ticket Board — Thm 8.28(b) sheafiness, revised 4-leaf plan (post /expert-review 2026-06-19)

## ★ UPDATE 2026-06-22 (/develop --continue — T-L4/HU-e SpvAI leaf: B2 + faithful fix)
- **The HU-e continuity bottom `ofValuation_restrictIdeal_isInSpvAI` was FALSE** (B2,
  `b2_log.jsonl`): general `cGammaIdeal ≠` Wedhorn Def 7.3. User-approved fix = **principal-case**
  faithful replacement `ofValuation_restrictIdealSingle_isInSpvAI` (the only case HU-e needs).
  Infrastructure + TRUE replacement LANDED (build green); bottoms at 2 elementary sub-lemmas.
- **NEW section [T-SPVAI-1..4] + [CLEANUP-SPVAI]** below (sub-dependency of T-L4 / HU-e): Prop 1.20
  (cofinal·bounded), the cofinal + microbial sub-lemmas (both elementary — Prop 1.20 / `cGammaUnits`
  is a convex subgroup; NO deep `minContain` infrastructure), and the `restrictIdealSingle` wiring.
  **Next available: T-SPVAI-1** (no deps) and **T-SPVAI-3** (no deps) — parallel.

## ★ UPDATE 2026-06-21 (/develop resume audit, lean_verify'd + full build 9825 green)
- **Leaf #1 (inducing / Prop 6.18) ELIMINATED** — T-L1a/b/c ✅DONE (commit b3749e9). The headline
  `embedding` field was rewired to ⟨`productRestrictionSub_isInducing_via_equalizer`, injective⟩ via
  the new axiom-clean `isInducing_of_closedRange_of_topNilpUnit` (WedhornBanachTheorem). The
  StructureSheaf 6.18 sorry `productRestrictionSub_isInducing_tate` is OFF the faithful headline path.
- **Remaining headline leaves (~4): T-L2 (ROIE), T-L3 (height-1 analytic), T-L4 ([Hu2] 3.3(i)),
  T-L5 (Spa-QC / Wedhorn 7.35(1))** — the injective half goes via the FLATNESS route and both halves
  transitively use T-L2/T-L3 (corrects an earlier "2 leaves" undercount).
- **NEXT PUSH = T-L4 (Huber 3.3(i))** — UN-PARKED; all deep discharges verified present
  (`IsLocalRing.exists_factor_valuationRing` + `Spv.isContinuous_of_isInSpvAI_of_lt_one` axiom-clean +
  `IsRingOfIntegralElements.subset_powerBounded`). Faithful HU-a…e decomposition under T-L4 below.
- **T-L5 (Spa-QC)** newly TRACKED (was untracked); deepest, deferred to its own decompose pass.

## Summary
- **Foundation DONE** (commits 489fe72 / b5c20a9 / a42bdc9): the `A⁺ ⊆ A°` ring-of-integral-elements
  interface migration (T-ROIE-1/2). Full `lake build` GREEN (3190 jobs). The false `B⁺ ⊆ B₀` route is
  gone; consumers use `[IsRingOfIntegralElements (A⁺)]` + the pair-free Spa criteria.
- **Revised residual = 4 embedding-side leaves** (the expert-review reply
  `.mathlib-quality/expert-review/2026-06-19/`, all key claims source-verified):
  - **T-L1** leaf #1 — topological inducing of `productRestrictionSub` via the equalizer + the
    σ-compact-FREE OMT. (Was "Prop 6.18"; reviewer simplified it to 6.16-on-the-equalizer.)
  - **T-L2** leaf #2 — `(presheafValue D)⁺` is a ring of integral elements (= former T-ROIE-3).
  - **T-L3** leaf #3 — analytic Spa point above a non-open prime (= former T-ROIE-4).
  - **T-L4** former leaf #4 — `isPowerBounded_of_forall_vle_one_spa_of_complete` via **7.52(1)=7.18(1)**
    (NOT the noetherian density converse 7.18(3); the ℂ_p red flag was a mis-citation — WITHDRAWN).
- **Leaf C (gluing)** is the *separate* Čech track (WedhornCechAcyclicity; whole-space chain sorry-free
  per `lemma_8_34_gluing`, R2-transport residual). Not re-ticketed here, but it is a **dependency of
  T-L1** (the algebraic bijection `ρ̃ : R → E` is injectivity ∧ gluing) and, per reviewer Q4b, gluing
  itself depends on **T-L2 + T-L3** (Lemma 7.54 → Cor 7.53 → Prop 7.51 maximal-ideal Spa points).
- Total this board: 4 proof leaves (T-L1 has 3 sub-tickets) + 3 cleanup = 7 entries.

## Dependency graph (bottom-up)
```
T-L4 (7.52(1) criterion) ─────────────► [feeds the LL-bdd / Leaf-A chain, already wired]

T-L3 (leaf #3: Spa points) ──┬─► productRestrictionSub_injective  (embedding.injective)
                             └─► Leaf C (gluing, via 7.54/7.53/7.51) ──┐
T-L2 (leaf #2: completion ROIE) ─► Leaf C (relative use over 𝒪_X(U)) ──┤
                                                                       ▼
   T-L1a EQ-CLOSED ─┐                                          ρ̃ : R → E surjective
   T-L1b EQ-COMPLETE─┼─► T-L1c OMT-inducing (productRestrictionSub_isInducing_tate)
                     │        ▲
   wedhorn_6_16_of_topNilpUnit (landed) ─────────────────────────────┘
                                                                       ▼
   isSheafy_of_stronglyNoetherian_828b = ⟨embedding (T-L1c ∧ T-L3-inj), gluing (Leaf C)⟩
```

---

### [T-L1a] `sectionEqualizer` is closed in the product
- **Status**: ✅ DONE (beastmode 2026-06-20) — `sectionEqualizer` (common-refinement form) +
  `sectionEqualizer_isClosed` PROVEN sorry-free in StructureSheaf.lean (just after
  `productRestrictionSub`); `lake build «Adic spaces».StructureSheaf` green (2787 jobs), no
  warnings on the decls. Proof: `unfold; simp only [Set.setOf_forall]; isClosed_iInter ×5;
  isClosed_eq (restrictionMapHom_continuous _ _ _ |>.comp (continuous_apply _)) (…)`. The
  reviewer's common-refinement predicate matched `IsSheafy.gluing` exactly — no intersection API,
  no tensor bridge. Was: ROUTE RESOLVED (expert-review #2, 2026-06-20), common-refinement form.
- **RESOLUTION (expert-review #2 reply, Q1):** routes (a) [descent⟹closed] and (c) [6.18] are
  rejected (faithful flatness gives no topological strictness; 6.18 on the subspace topology is
  circular). The canonical route is Čech-closedness, but using **ALL common rational refinements**
  `D₃` (rationalOpen ⊆ both pieces), NOT a single intersection datum — each `isClosed_eq` of two
  continuous `restrictionMap`s, intersected. **This sidesteps the heterogeneous-`P` problem entirely
  and needs NO new intersection API.** CRITICAL: the project's `IsSheafy.gluing` field
  (StructureSheaf:311-320) is **ALREADY stated with exactly this common-refinement predicate**
  (`∀ D₁ D₂ D₃ h₃₁ h₃₂, restrictionMap D₁ D₃ (f D₁) = restrictionMap D₂ D₃ (f D₂)`), so NO bridge
  theorem (`tensorCocycle_iff_commonRefinementCompatible`) is needed — define `sectionEqualizer` as
  the carrier of that predicate and reuse the gluing/separation theorem directly.

#### Statement (REVISED — common-refinement form)
```lean
def sectionEqualizer (C : RationalCovering A) : Set (∀ D : ↥C.covers, presheafValue D.1) :=
  {s | ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (s D₁) = restrictionMap D₂.1 D₃ h₃₂ (s D₂)}
theorem sectionEqualizer_isClosed (C : RationalCovering A) : IsClosed (sectionEqualizer C) := by sorry
```
#### Proof sketch
`isClosed_iInter` over `(D₁,D₂,D₃,h₃₁,h₃₂)` of `isClosed_eq (continuous_restrictionMap.comp (continuous_apply D₁)) (…D₂)`.
`restrictionMap`/`restrictionMapHom` continuity = `restrictionMapAlg_continuous` (Presheaf:1353);
`presheafValue D₃` is T2; `continuous_apply` for the product projections.
#### Mathlib lemmas needed
`isClosed_iInter`, `isClosed_eq`, `Continuous.comp`, `continuous_apply`, `restrictionMapHom` continuity.
#### Risks (reviewer): give `E` the R-module structure via `R→S` + verify subspace `ContinuousSMul`;
closed-subspace / finite-product `IsCountablyGenerated` instances likely need explicit `haveI`s.

(superseded original below — kept for the `overlapDiff`/AddSubgroup phrasing only)
- **Status (orig)**: open
- **Progress**:
  - 2026-06-19 **The reviewer's overlap-equalizer needs a general heterogeneous-`P` intersection
    the repo deliberately avoids.** Findings: (1) leaf #1 IS real — `cor_8_32_productRestrictionSub_isEmbedding`
    (RelativePieceKeystone:2405) gets *injectivity* from faithfully-flat **descent** (Stacks 023N,
    `faithfullyFlat_cocycleMap`/`faithfullyFlat_descent_equalizer`, S⊗_R S — no topology, so descent
    gives inj but NOT inducing) and delegates *inducing* to `productRestrictionSub_isInducing_tate`
    (the StructureSheaf:1384 sorry). (2) The reviewer's closedness `E = ker(∏𝒪(Uᵢ) → ∏𝒪(Uᵢ∩Uⱼ))`
    needs the **topological Čech-1 overlaps** `𝒪(Uᵢ∩Uⱼ)` (T2 target) — i.e. the pairwise intersection
    *rational data* + the continuous overlap restriction maps. (3) The only intersection in the repo
    is `RationalLocData.interSamePair` (LaurentRefinementCore:361) which **requires `D₂.P = D₁.P`**
    (its `hopen` proof rebases `D₂.hopen` via `_hP ▸`). The existing route always pins pieces to a
    common `P` (`genPieceDatum D₀.P … interSamePair … rfl`). But `RationalCovering.covers : Finset
    (RationalLocData A)` has pieces with **heterogeneous `.P`**, so `interSamePair` does NOT apply to a
    general cover. A general intersection (heterogeneous-`P` `hopen`) is substantial NEW infra — exactly
    what descent was chosen to avoid.
  - **REPLAN DECISION (user):** (a) build the heterogeneous-`P` Čech-1 infra (general intersection
    `hopen` + overlap maps + closedness + bundle `ρ̃ →ₗ[A]` + cg/complete/ContinuousSMul on `E` + OMT)
    — large in-area sub-development; or (b) normalize a general cover to common-`P` first (via
    `RationalCovering.PinnedTo`, WedhornCoverNormalization:286) then use `interSamePair`; or (c) seek a
    **descent-compatible inducing** argument (avoid intersections entirely, matching the repo's
    architecture) — re-read Wedhorn 8.28's actual inducing step (6.18 module-topology vs Banach). The
    σ-compact-free OMT `wedhorn_6_16_of_topNilpUnit` is ready regardless of which equalizer formulation
    is chosen.
- **File**: StructureSheaf.lean (new decls near `productRestrictionSub`, ~L280)
- **Depends on**: none (pure topology)
- **Parallel**: yes
- **Type**: def + lemma

#### Statement
Define the overlap equalizer `E ⊆ ∏ᵢ 𝒪_X(Uᵢ)` as the kernel of the continuous difference of the two
overlap-restriction maps `∏ᵢ 𝒪_X(Uᵢ) ⇉ ∏_{i,j} 𝒪_X(Uᵢ ∩ Uⱼ)`, and show it is closed:
```lean
noncomputable def sectionEqualizer (C : RationalCovering A) :
    Subgroup (∀ D : C.index, presheafValue (C.piece D))   -- or AddSubgroup of the product
  := AddMonoidHom.ker (overlapDiff C)                       -- (overlapDiff = ρ_{ij}^left - ρ_{ij}^right)

theorem sectionEqualizer_isClosed (C : RationalCovering A) :
    IsClosed (sectionEqualizer C : Set _) := by sorry
```

#### Proof sketch
1. The two overlap maps are continuous (each is a `restrictionMapHom` between completions, continuous
   by `restrictionMapAlg_continuous_of_huber_completion`). Their difference `overlapDiff` is continuous.
2. The target `∏_{i,j} 𝒪_X(Uᵢ∩Uⱼ)` is T2 (finite product of T2 completions).
3. `E = ker(overlapDiff) = overlapDiff ⁻¹ {0}`; preimage of the closed `{0}` under a continuous map →
   closed. (`IsClosed.preimage continuous_overlapDiff isClosed_singleton`.)

#### Mathlib lemmas needed
`continuous_sub`, `IsClosed.preimage`, `isClosed_singleton` (target T2), `AddMonoidHom.ker`,
`continuous_apply`/`Pi.continuous` for the product projections. (All verified to exist.)

#### Sources
Reviewer reply Q2 (`expert-review/2026-06-19/reply.md`): "The equalizer is the kernel of the continuous
difference map from P to the finite overlap product, hence is closed." Standard topology; no Wedhorn
proposition needed (the sheaf-axiom equalizer shape, Wedhorn §8.2 / Def of sheaf).

#### Generality decision
`(C : RationalCovering A)` over the standard Tate `A`-bundle. State `E` as an `AddSubgroup` of the
product (the OMT needs an additive/`A`-module structure on the target, not a ring structure).

---

### [T-L1b] `sectionEqualizer` is a complete, countably-based A-module; `ρ̃ : R → E` continuous bijection
- **Status**: ✅ DONE (2026-06-21, subsumed by T-L1c landing) — the foundational pieces
  (`sectionEqualizer_completeSpace`, `presheafValue_uniformity_isCountablyGenerated`,
  `sectionEqualizer_isCountablyGenerated`, `productRestrictionSub_mem_sectionEqualizer`) +
  the OMT-assembly were all consumed by `productRestrictionSub_isInducing_via_equalizer` (the
  OMT-assembly went via the general WBT helper `isInducing_of_closedRange_of_topNilpUnit`, which
  handles the range-subtype instances internally). Full build green.
- **Status (orig)**: in_progress (beastmode 2026-06-20) — 3 foundational pieces DONE; OMT-assembly core remains.
- **Progress**:
  - 2026-06-20 LANDED (StructureSheaf.lean, all green 2787 jobs): `sectionEqualizer_isClosed` (T-L1a),
    `productRestrictionSub_mem_sectionEqualizer` (image ⊆ E, via `restrictionMap_comp`, no gluing),
    `sectionEqualizer_completeSpace` (E complete = closed in complete ∏).
  - **REMAINING OMT-assembly pieces (the sub-ticket plan; infra is non-ambient):**
    1. `presheafValue_uniformity_isCountablyGenerated (D)` — ⚠ HITS A MATHLIB DIAMOND (beastmode
       2026-06-20, attempted+reverted to keep green): the LaurentRefinementCore:2660-2694 metric chain
       proves cg for `@uniformity (presheafValue D) PseudoMetricSpace.toUniformSpace`, but the OMT needs
       it for the AMBIENT `instUniformSpacePresheafValue D`, and the two are NOT defeq (the metric goes
       through `UniformSpace.pseudoMetricSpace` of the localization → a compounding completion-metric
       uniformity diamond). `FirstCountableTopology (presheafValue D)` does NOT auto-derive (completion
       of first-countable isn't first-countable without metrizability). `lean_loogle` found no
       `IsCountablyGenerated (uniformity (Completion _))` lemma. RESOLUTION OPTIONS: (i) prove the
       uniformity-FILTER equality `@uniformity _ ambient = @uniformity _ metric` and transport cg;
       (ii) restructure E's uniformity via the metric throughout (messy); (iii) find/add a mathlib
       `UniformSpace.Completion` cg-preservation lemma. Then `sectionEqualizer_isCountablyGenerated`
       via finite-Pi + `Filter.comap.isCountablyGenerated` (the Pi/comap part is easy once (1) lands).
    2. E as an **A-module**: `letI : Module A (presheafValue D) := (canonicalMap D).toAlgebra.toModule`
       (non-ambient, cf. FlatnessResults:72-75) + Pi.module + the submodule/`ContinuousSMul` on E.
    3. `productRestrictionToEqualizer : presheafValue C.base →ₗ[A] E` (corestrict via the mem lemma;
       A-linear since restrictionMap is an A-algebra hom).
    4. **Bijective**: injective (the separation, `IsOXAcyclic.separation` / descent); surjective
       (`lemma_8_34_gluing` — needs `[CompleteSpace A][CompatiblePlusSubring A]`, the SIGNATURE
       CASCADE: extend `productRestrictionSub_isInducing_tate` (StructureSheaf:1384) with those +
       thread through `cor_8_32_productRestrictionSub_isInducing/_isEmbedding` (RelativePieceKeystone);
       the headline already has them).
    5. T-L1c: `wedhorn_6_16_of_topNilpUnit` ρ̃ → IsOpenMap → continuous+bijective+open ⇒ homeo →
       `IsInducing.comp IsInducing.subtypeVal` ⇒ `productRestrictionSub_isInducing_tate`.
- **File**: StructureSheaf.lean
- **Depends on**: T-L1a; **Leaf C** (gluing surjectivity); T-L3 (injectivity, transitively)
- **Parallel**: no (needs gluing)
- **Type**: lemmas (instances + the corestricted map)

#### Statement
```lean
-- Closed subspace of the complete product ⇒ complete; finite product of cg ⇒ cg; A-module structure.
instance : CompleteSpace (sectionEqualizer C) := (sectionEqualizer_isClosed C).completeSpace_coe
-- The corestriction of productRestrictionSub to E (lands in E by overlap-compatibility):
noncomputable def productRestrictionToEqualizer (C : RationalCovering A) :
    presheafValue C.base →ₗ[A] sectionEqualizer C := …
theorem productRestrictionToEqualizer_bijective (C : RationalCovering A) :
    Function.Bijective (productRestrictionToEqualizer C) := by sorry
```

#### Proof sketch
1. `CompleteSpace E` from `sectionEqualizer_isClosed C |>.completeSpace_coe` (closed in complete `∏`).
2. `(uniformity E).IsCountablyGenerated` via `Filter.comap.isCountablyGenerated` (subspace of a finite
   product of cg completions) — pattern copied verbatim from `_sub_lemma_L4_3_strict_via_closed_image`
   (WedhornBanachTheorem:1031-1040).
3. `ρ` lands in `E`: `productRestriction` of a global section satisfies the overlap relations
   (`restrictionMap` functoriality / `productRestriction_apply` cocycle) → corestrict to `E`.
4. **Injective**: `productRestrictionSub_injective` / `productRestriction_injective_of_laurentRefinement`
   (exists, StructureSheaf:922/1134; rests transitively on T-L3 Spa points).
5. **Surjective onto E** = the algebraic **gluing** axiom: every overlap-compatible family `(eᵢ) ∈ E`
   glues to a global section. This is **Leaf C** (`lemma_8_34_gluing` / the Čech H⁰-exactness).

#### Mathlib lemmas needed
`IsClosed.completeSpace_coe`, `Filter.comap.isCountablyGenerated`, `Submodule`/`AddSubgroup` subtype
instances, `LinearMap.codRestrict`. (Verified.)

#### Sources
Reviewer Q2: "E is Hausdorff, complete, countably based as a closed subspace of a finite product of
such spaces … separation+gluing give a continuous bijection ρ̃ : R → E." Gluing = Wedhorn Lemma 8.34
(Leaf C); injectivity = Wedhorn 7.45 route (T-L3).

#### Generality decision
`ρ̃` as `M →ₗ[A] N` (A-linear) so `wedhorn_6_16_of_topNilpUnit` applies directly in T-L1c.

---

### [T-L1c] `productRestrictionSub_isInducing_tate` via the σ-compact-free OMT
- **Status**: ✅ DONE (2026-06-21, commit b3749e9, full build 9825 green). Route: NOT the
  StructureSheaf `productRestrictionSub_isInducing_tate` plan — instead a clean general lemma
  `isInducing_of_closedRange_of_topNilpUnit` (WedhornBanachTheorem, axiom-clean: cont+inj A-linear
  with closed range over a ring with a top-nilp unit ⇒ IsInducing, via corestrict-to-range + OMT +
  `Equiv.toHomeomorphOfContinuousOpen` + closed-subtype-inclusion compose) applied in
  `productRestrictionSub_isInducing_via_equalizer` (WedhornCechAcyclicity) at ρ̃ with range =
  closed `sectionEqualizer`. Headline `embedding` field rewired to ⟨via_equalizer, injective⟩;
  the StructureSheaf Prop-6.18 sorry `productRestrictionSub_isInducing_tate` is OFF the faithful
  headline path (still used only by deprecated `_clean`/RPK wrappers). ⚠GOTCHA: the two
  non-canonical `presheafValue` module instances must be passed EXPLICITLY via `@` (FlatnessResults
  pattern) — not synthesised inside the OMT's instance bundle. **Leaf #1 (inducing/6.18) ELIMINATED.**
- **Status (orig)**: open — ⚠ ARCHITECTURE: prove in WedhornCechAcyclicity, NOT StructureSheaf.
- **Progress**:
  - 2026-06-20 (beastmode) cg-uniformity diamond CRACKED + 5 topological foundations landed in
    StructureSheaf (sectionEqualizer_isClosed/_completeSpace/_isCountablyGenerated,
    productRestrictionSub_mem_sectionEqualizer, presheafValue_uniformity_isCountablyGenerated).
  - **ARCHITECTURE FINDING:** the OMT inducing route needs `ρ̃ : R → E` SURJECTIVE = the gluing
    (`lemma_8_34_gluing`, in WedhornCechAcyclicity). But `productRestrictionSub_isInducing_tate`
    lives in StructureSheaf (UPSTREAM of WCA — WCA imports StructureSheaf). So the inducing CANNOT
    use gluing where it currently lives (import cycle). RESOLUTION: prove a new
    `productRestrictionSub_isInducing_via_equalizer` IN WCA (downstream of gluing + the 5 foundations
    + the OMT) and **rewire the headline's `embedding` field** to `⟨new_inducing, cor_8_32_…injective⟩`
    (keep the RPK injectivity; bypass the StructureSheaf inducing sorry, which becomes orphaned).
  - **REMAINING (in WCA):** (1) E as an **A-Submodule** of `∏_D 𝒪_X(D)` — `letI : Module A (presheafValue D)`
    `:= (canonicalMap D).toAlgebra.toModule` per D (FlatnessResults:72 pattern) + `Pi.module` + the
    submodule from the A-linear restriction-map equalizer; (2) `ContinuousSMul A` on R and E (continuity
    of the A-action via `canonicalMap`); (3) `ρ̃ : R →ₗ[A] E` (corestrict, A-linear) continuous; (4)
    surjective (`lemma_8_34_gluing` + `productRestrictionSub_mem_sectionEqualizer`) + injective
    (`cor_8_32_…injective`); (5) `wedhorn_6_16_of_topNilpUnit ϖ … ρ̃` → IsOpenMap → homeo →
    `IsInducing.subtypeVal.comp` ⇒ inducing. ϖ from `IsTateRing.exists_topologicallyNilpotent_unit`.
- **File**: StructureSheaf.lean:1384
- **Depends on**: T-L1a, T-L1b
- **Parallel**: no
- **Type**: theorem (discharge existing sorry)

#### Statement
```lean
theorem productRestrictionSub_isInducing_tate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]
    (C : RationalCovering A) :
    Topology.IsInducing (productRestrictionSub A C)
```

#### Proof sketch (reviewer Q2, faithful σ-compact-free)
1. `R := presheafValue C.base` is complete, cg, T2, and an `A`-module; `E := sectionEqualizer C` is
   complete (T-L1a/b), cg, T2.
2. `ρ̃ := productRestrictionToEqualizer C : R →ₗ[A] E` is continuous (T-L1b step 3 + `continuous_productRestriction`)
   and **surjective** (T-L1b: bijective).
3. Obtain a topologically-nilpotent **unit** `ϖ` from `[IsTateRing A]`
   (`IsTateRing.exists_topologicallyNilpotent_unit`).
4. `wedhorn_6_16_of_topNilpUnit hϖ_nil ϖ.isUnit ρ̃ hρ̃_cont hρ̃_surj : IsOpenMap ρ̃`  — **the
   σ-compact-free OMT (WedhornBanachTheorem:408); do NOT use `isOpenMap_of_completeSpace_of_countablyGenerated`,
   which carries `[SigmaCompactSpace]`, false for Tate `R`.**
5. `ρ̃` continuous + bijective + open ⟹ homeomorphism (`IsOpenMap` + `Continuous` + `Bijective` →
   `Homeomorph`, or `Topology.IsInducing` of a bijective open continuous map).
6. `productRestrictionSub A C = (E ↪ ∏) ∘ ρ̃` where `E ↪ ∏` is `IsInducing.subtypeVal`; composition of
   inducings is inducing → `IsInducing (productRestrictionSub A C)`. (`Topology.IsInducing.comp`.)

This is exactly the `_sub_lemma_L4_3_strict_via_closed_image` (WedhornBanachTheorem:994) pattern, but on
the closed **equalizer** `E` (closedness from T-L1a, NOT from module-finiteness/noetherian-6.18).

#### Mathlib lemmas needed
`wedhorn_6_16_of_topNilpUnit` (WedhornBanachTheorem:408 — verified signature `(f : M →ₗ[A] N) (Continuous f)
(Surjective f) : IsOpenMap f`), `IsTateRing.exists_topologicallyNilpotent_unit`, `Topology.IsInducing.comp`,
`Topology.IsInducing.subtypeVal`, `IsOpenMap.isQuotientMap` / `Homeomorph.ofContinuousOpen`.

#### Sources
Reviewer Q2 + Wedhorn 6.16 (= BGR §3.7.2/1, "Proof Missing", landed faithfully as `wedhorn_6_16_of_topNilpUnit`).
NOT Prop 6.18 (reviewer: "Proposition 6.18 is unnecessary for this application").

#### Generality decision
Keep the existing signature at StructureSheaf:1384 (`[IsTateRing][IsNoetherianRing][IsStronglyNoetherian]
[T2Space][NonarchimedeanRing]`, no `[IsDomain]`, no `P`/noeth-`A₀`). `[IsNoetherianRing A]`/`[IsStronglyNoetherian A]`
are inherited from the headline; not used by the equalizer route itself (the route is σ-compact-free,
module-finiteness-free) — leave them (the headline supplies them) but the proof must not invoke the
noetherian-module-closedness route.

---

### [T-L2] `(presheafValue D)⁺` is a ring of integral elements (leaf #2 = former T-ROIE-3)
- **Status**: open — discharges the 3 `sorry` fields of `presheafValuePlus_isRingOfIntegralElements` (Presheaf.lean:505)
- **File**: Presheaf.lean (+ a `ringOfIntegralElements_completion` named leaf for 7.47(4))
- **Depends on**: none (T-ROIE-1 foundation done)
- **Parallel**: yes
- **Type**: theorem (3 instance fields)

#### Statement
```lean
  isOpen : IsOpen ((presheafValue D)⁺ : Set (presheafValue D))
  isIntegrallyClosed : ∀ a, IsIntegral ↥((presheafValue D)⁺) a → a ∈ (presheafValue D)⁺
  subset_powerBounded : ((presheafValue D)⁺ : Set _) ⊆ TopologicalRing.powerBoundedSubring (presheafValue D)
```

#### Proof sketch (Wedhorn 7.19 + 7.20 + 7.47(4); reviewer Q3)
1. **Precompletion (Wedhorn 7.19, openness is automatic — reviewer Q3):** `C := IntCl(A⁺[T/s]) =
   IntCl(D.locPlusSubring)` is a ring of integral elements of `A_s = Localization.Away D.s`:
   - **open**: `A⁺` open in `A` ⟹ for the ideal of definition `I`, some `Iⁿ ⊆ A⁺` ⟹ `IⁿA₀[T/s]` is an
     open nbhd of 0 in the loc topology and `⊆ A⁺[T/s]`, so `A⁺[T/s]` is open; its integral closure `C ⊇
     A⁺[T/s]` is then open (superset of an open subgroup). (Wedhorn 7.19 openness pattern.)
   - **integrally closed**: `integralClosure_idem` (integral closure is integrally closed).
   - **⊆ (A_s)°**: Wedhorn 7.20 `(A°)⟨T/s⟩ ⊆ (A_s)°` and `C ⊆ (A°)⟨T/s⟩`.
2. **Completion (Wedhorn 7.47(4) = [Hu1] 2.4.3):** state the named leaf
   `ringOfIntegralElements_completion` : "`B` a ring of integral elements of f-adic `A` ⟹ its closure
   `B̂ = ι(B)` is a ring of integral elements of `Â`", citing 7.47(4). `(presheafValue D)⁺ = closure(coeRingHom C)`,
   so the three fields are the three projections of this leaf applied to the 7.19/7.20 input from step 1.

#### Mathlib lemmas needed
`integralClosure_idem`, `Subring.le_topologicalClosure`, openness of subgroup images, `TopologicalRing.powerBoundedSubring`.
The 7.47(4) leaf is the external cite — **but [Hu1] 2.4.3 is IN HAND** (`references/huber1.txt:7467`); it is a
real (substantial) sub-development from [Hu1], not unfulfillable infrastructure.

#### Sources
Wedhorn Prop 7.19 (p.61, `wedhorn.txt:3176`), Lemma 7.20 (p.61, `:3195`), Lemma 7.47(4) (p.68,
`wedhorn.txt:3556`: "Rings of integral elements of A and of Â correspond. Proof. [Hu1] 2.4.3").
[Hu1] = Huber, *Bewertungsspektrum und rigide Geometrie* (Habilitation), 2.4.3 = `huber1.txt:7467`.

#### Generality decision
`(D : RationalLocData A) [PlusSubring A]` + standard bundle. The 7.47(4) leaf stated generally for reuse.

---

### [T-L3] Analytic Spa point above a non-open prime (leaf #3 = former T-ROIE-4)
- **Status**: in_progress (beastmode 2026-06-19) — discharges `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` (Presheaf.lean:2785)
- **Progress**:
  - 2026-06-19: source-confirmed Wedhorn 7.45 (`wedhorn.txt:3488`) gives a **height-1** analytic
    point with p⊆supp; Prop 7.41 (`wedhorn.txt:3438`) = "height-1 ⟹ v≤1 on A°" (≈6-line proof). The
    in-repo `exists_spa_point_via_restrictToConvex` (Lemma745:418, proven) gives an analytic
    continuous point with p⊆supp but bounds on A₀ (not A°) and isn't packaged as height-1. Residual =
    Prop 7.41 sub-lemma + a height-1 analytic point. Spawning the Prop 7.41 sub-ticket first.
  - 2026-06-19 **T-L3 REDUCED + PARTIALLY DONE.** T-L3a (Prop 7.41) PROVEN+verified. Relocated
    `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` after 7.41 in Presheaf.lean and **proved it**
    via the new leaf `exists_heightOne_analytic_cont_supp_ge_of_nonOpen_prime` (Wedhorn 7.45 height-1
    point) + 7.41 (the A° bound). Presheaf builds green (2549); StandardCover+Cor832 green (2950) — the
    relocation/reduction is sound, T-L3 signature unchanged. **The bare T-L3 sorry is gone; the single
    residual is now the height-1-point leaf `exists_heightOne_analytic_cont_supp_ge_of_nonOpen_prime`.**
  - **TWO BLOCKERS on discharging the height-1 leaf (= T-L3b, the remaining sorry):**
    1. **DEEP INFRA** (Rem 4.12 / height-1 generalization): the repo's height-1 machinery is the
       `ofPrime` coarsening (`mulArchimedean_ofPrime_of_height_one`,
       `exists_mem_spa_supp_eq_of_nonOpen_prime_via_heightOne_ofPrime`) which still needs the height-1
       prime `Q` of the valuation ring — the documented "minimal prime above φ(I) is height-1" gap
       (valuation-ring dimension theory; plan `docs/plans/2026-03-18-valuation-prime-convex.md`).
       Substantial missing infra (CLAUDE.md isolate-as-leaf + report).
    2. **⚠ COMPLETENESS SOUNDNESS FLAG (B2-candidate, needs user decision):** Wedhorn 7.45 requires a
       **complete** affinoid (Prop 5.38, A₀ I-adically complete ⟹ I⊆m); the in-repo analytic-point
       construction needs `[IsAdicComplete P.I P.A₀]`. But T-L3 (and the StandardCover pair-free
       consumer `exists_spa_point_with_supp_ge_of_prime`) carry **NO `CompleteSpace`** — the ROIE
       pair→pair-free migration dropped the pair's completeness without re-adding it. They are USED at
       complete rings (Cor832:1624 = `presheafValue`, `presheafValue_isAdicComplete`). So discharging
       T-L3b will need completeness. DECISION (user): (a) add `[CompleteSpace A]` to T-L3 + the
       StandardCover consumer + thread to the ~5 consumer files (CLAUDE.md-(b)-justified IF T-L3 is
       genuinely false without completeness — likely, per Wedhorn 7.45); or (b) prove completeness-free
       via `Spa(A) ≅ Spa(Â)` (Wedhorn 7.48) + 7.45-on-Â (deeper). Do NOT add the hypothesis unilaterally
       (CLAUDE.md). Logged to `b2_log.jsonl`.
  - 2026-06-20 **✅ COMPLETENESS RESOLVED (expert-review #2, Q2): completeness IS essential — ADD
    `[CompleteSpace A]`.** Reviewer gave a counterexample proving the no-completeness statement FALSE:
    `A = 𝔽_p[x]` with the `(x)`-adic topology, `A⁺ = A`, `𝔭 = (x-1)`. `(x-1)` is non-open + dense
    (`1 = x + (1-x) ∈ (x)+(x-1)`); any valuation with support `(x-1)` factors through `𝔽_p` (trivial,
    so open support), so NO continuous valuation has support `⊇ (x-1)`; and in `𝔽_p[[x]]`, `x-1` is a
    unit so no prime lies over it (completion-invariance of Spa transports valuations, not primes —
    dense primes vanish). So CLAUDE.md-(b) is satisfied: add `[CompleteSpace A]` (right-uniformity form)
    to T-L3, `exists_heightOne_analytic_cont_supp_ge_of_nonOpen_prime` (T-L3b), AND the StandardCover
    pair-free consumer `exists_spa_point_with_supp_ge_of_prime`; thread from the headline (complete) down.
    Record the counterexample as a regression note.
  - 2026-06-20 **✅ HEIGHT-1 LEAF ROUTE (T-L3b) RESOLVED (expert-review #2, Q3): ordered-group fact,
    NO blow-up/Krull–Akizuki.** Discharge plan: (1) ordered-group lemma
    `exists_convexSubgroup_quotient_height_one_of_microbial` — microbial `Γ` ⟹ ∃ nontrivial order hom
    `φ : Γ → ℝ` (Wedhorn 5.46), `H := ker φ` (convex, proper), `Γ/H ≅ im φ ⊆ ℝ` archimedean ⟹ height 1;
    (2) valuation wrapper `Valuation.exists_heightOne_verticalGenerization` (same support, vertical
    generization, height 1); (3) continuity-under-vertical-generization (Wedhorn Rem 7.42). The
    in-repo `embed_archimedean_valueGroup_into_real` (Presheaf, a `sorry`) is the bracket→ℝ direction;
    the cleaner route is microbial⟹order-hom (5.46) then `MulArchimedean (Γ/H)`. Blow-up/normalization
    belong ONLY to the noetherian discrete-valuation refinement (not this leaf).
- **File**: Presheaf.lean (+ Lemma745.lean for the 7.41 sub-leaf)
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem exists_cont_supp_ge_powerBounded_of_nonOpen_prime
    {A} [CommRing A] [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] [IsHuberRing A]
    [T2Space A] [NonarchimedeanRing A] {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬ IsOpen (𝔭 : Set A)) :
    ∃ v : Spv A, v ∈ Cont A ∧ 𝔭 ≤ v.supp ∧
      ∀ a ∈ (TopologicalRing.powerBoundedSubring A : Set A), v.vle a 1
```

#### Proof sketch (Wedhorn Lemma 7.45 general branch + Prop 7.41; reviewer Q4a)
1. **Analytic point (general Lemma 7.45, NO noetherian):** the non-open prime `𝔭` is dominated by an
   analytic continuous valuation `v₀` with `𝔭 ≤ supp v₀` (in-repo `exists_spa_point_via_restrictToConvex` /
   `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`). Keep only the **general** branch — drop
   the noetherian-discrete refinement (only needed for exact support / discrete value group).
2. **Height-1 generization (Remark 7.42(2)/4.12):** `v₀` analytic ⟹ ∃ height-1 vertical generization `v`,
   continuous (Rem 7.11(2)), `supp v ⊇ supp v₀ ⊇ 𝔭`.
3. **Bounded on A° (Prop 7.41):** sub-leaf `heightOne_le_one_on_powerBounded` (PROVE it, ≈6 lines): if
   `v(a)>1` for `a∈A°`, pick `b∈A°°` with `v(b)≠0`; `Γ_v` height-1 ⟹ archimedean ⟹ `∃n, v(aⁿb)>1`; but
   `aⁿb∈A°°` ⟹ continuity ⟹ `v(aⁿb)<1`, contradiction.
- **Maximality corollary (reviewer Q4a, already in-repo):** `support_eq_maximal_of_le` (board foundation)
  turns `𝔭 ≤ supp v` into equality when `𝔭` is maximal — used downstream, no new work.

#### Mathlib lemmas needed
height-1/microbial/archimedean valuation API, vertical-generization (`ValuativeRel` / `restrictToConvex`),
`A°°`-continuity (`IsTopologicallyNilpotent`).

#### Sources
Wedhorn Lemma 7.45 (p.67), Remark 7.42(2)/4.12 (p.66), Prop 7.41 (p.66, `wedhorn.txt:3487`). Residual
deep leaf: Lemma 7.45 analytic-point existence (in-repo `restrictToConvex`). **No noetherian ring of
definition** (reviewer Q4a — ℂ_p-safe).

#### Generality decision
Any affinoid `(A, A⁺)`; the `A°` bound is `A⁺`-independent (Prop 7.41 gives `Spa(A,A⁺)` membership for
*every* ring of integral elements `A⁺`).

---

### [T-L3a] Prop 7.41 — `heightOne_le_one_on_powerBounded` (sub-ticket of T-L3)
- **Status**: DONE (beastmode 2026-06-19) — `heightOne_le_one_on_powerBounded` proven sorry-free,
  axiom-clean, `lake build «Adic spaces».Presheaf` green (2549 jobs), no warnings on the decl.
  Proof: reduce to `v a ≤ 1`; by_contra; analytic ⟹ `b∈A°°, v b≠0`; `MulArchimedean.arch` ⟹
  `(v b)⁻¹ ≤ (v a)^k` ⟹ `1 ≤ v(aᵏb)`; `aᵏb∈A°°` (pow_mem + isTopologicallyNilpotent_mul) ⟹
  continuity ⟹ `v(aᵏb)<1`; contradiction. (gcongr for the mul step; not_le for by_contra.)
- **File**: Presheaf.lean (after `rankOne_valueGroup_of_analytic`, ~3516; deps live there)
- **Depends on**: none (all ingredients in-repo)
- **Parent**: T-L3
- **Type**: theorem

#### Statement
```lean
theorem heightOne_le_one_on_powerBounded
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A]
    (x : Spv A) (hx_cont : x ∈ Cont A) (hx_an : ¬ IsOpen (x.supp : Set A))
    (hArch : letI : ValuativeRel A := x.toValuativeRel;
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (a : A) (ha : IsPowerBounded a) : x.vle a 1
```

#### Proof sketch (Wedhorn 7.41, `wedhorn.txt:3438-3444`)
Reduce to `v a ≤ 1` (`Valuation.Compatible.vle_iff_le`). By_contra `1 < v a`. Analytic ⟹ `∃ b ∈ A°°`,
`v b ≠ 0` (`exists_topNilp_ne_zero_of_analytic`); continuity ⟹ `v b < 1` (`topNilp_vle_one_of_continuous`),
and `v b > 0`. `MulArchimedean.arch (v b)⁻¹ (1 < v a)` ⟹ `∃ k, (v b)⁻¹ ≤ (v a)^k` ⟹ `1 ≤ (v a)^k·v b =
v(aᵏb)`. But `aᵏb ∈ A°°` (`(ha.pow k).isTopologicallyNilpotent_mul hb_nil`), so continuity ⟹ `v(aᵏb) < 1`.
`1 ≤ v(aᵏb) < 1`, contradiction.

#### Mathlib lemmas needed
`MulArchimedean.arch`, `inv_mul_cancel₀`, `mul_le_mul_right'`, `map_mul`, `map_pow`,
`exists_topNilp_ne_zero_of_analytic`, `topNilp_vle_one_of_continuous`,
`IsPowerBounded.isTopologicallyNilpotent_mul`, `IsPowerBounded.pow` (verify).

#### Sources
Wedhorn Prop 7.41 (p.66, `wedhorn.txt:3438`); "height 1" ⟺ `MulArchimedean` value group (Prop 1.14).

#### Generality decision
`IsPowerBounded a` hypothesis (cleaner than `a ∈ powerBoundedSubring`; convert at the T-L3 call site).
`MulArchimedean (ValueGroupWithZero A)` is the faithful height-1 encoding (matches `rankOne_valueGroup_of_analytic`).

---

### [T-L4] `isPowerBounded_of_forall_vle_one_spa_of_complete` via 7.52(1) = 7.18(1) (former leaf #4)
- **Status**: 🔵 OPEN — UN-PARKED 2026-06-21 (user chose in-repo discharge). ⭐**FEASIBILITY
  VERIFIED**: all deep discharges of Huber's hypothesis-free 3.3(i) proof exist in-repo/mathlib:
  (HU-c dominating valuation) mathlib `IsLocalRing.exists_factor_valuationRing`
  (`Mathlib.RingTheory.Valuation.LocalSubring`); (HU-e continuity) project
  `Spv.isContinuous_of_isInSpvAI_of_lt_one` (SpvAI.lean:294, **lean_verify'd axiom-clean** = the
  Wedhorn 7.10 reverse direction); (HU-d restriction) mathlib `Valuation.comap`; (L-714 B⁺⊆B°)
  project `IsRingOfIntegralElements.subset_powerBounded`. Remaining = connective tissue
  (integral-closure HU-a, minimal-prime HU-b, valuation-lift bookkeeping HU-d) in the project's
  Spv encoding. See the faithful Huber-3.3(i) sub-decomposition (HU-a…e) below + `decomposition.md`.
- **Status (was)**: PARKED — cited external leaf **[Hu2] Lemma 3.3(i)**, now SOURCED (user chose (c)).
  ⚠ Adversarial round-2 finding (`decomposition.md`): the reviewer's "trivial via 7.52(1)" does
  NOT survive contact with the code — in-repo 7.18 (`isIntegral_of_forall_continuous_valuation_le_one`,
  Presheaf:1639) is `[IsDomain]`-gated (artifact of FractionRing route, FALSE for case-(b) non-domain
  `presheafValue D'`) + has a 7.22 continuity sub-`sorry`; the all-valuations form (Presheaf:1569) is
  `[IsDomain]`-gated + wrong quantifier. **ℂ_p red flag WITHDRAWN** (it is 7.18(1), not the noetherian
  density converse 7.18(3)). **[Hu2] now in hand** (`references/huber2-continuous-valuations.pdf`,
  OCR `huber2.txt`): Lemma 3.3(i), p.466 (`huber2.txt:624-627`) = the σ/τ bijection, proof
  `:633-658` **hypothesis-free (no [IsDomain]/noeth/Tate)**. Leaf stays a parked cited sorry; if an
  in-repo discharge is wanted later, follow Huber's hypothesis-free proof (≈25 lines + his (3.1)).
- **File**: FaithfulLocLift.lean (+ a `mem_plus_iff_forall_spa_vle_one` named leaf = 7.52(1))
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem
- **Progress** (2026-06-21 /beastmode):
  - ✅ Reduction PROVEN (commit ab0c53a): `isPowerBounded_of_forall_vle_one_spa_of_complete` =
    `mem_plus_of_forall_spa_vle_one` + `IsRingOfIntegralElements.subset_powerBounded`. mem_plus =
    by_contra → ONE construction sorry `x∉B⁺ ⟹ ∃w∈Spa(B,B⁺), ¬w.vle x 1`.
  - ✅ HU-a foothold (commit e3a4261): `x∉B⁺ ⟹ ¬IsIntegral B⁺ x` via `IsRingOfIntegralElements.isIntegrallyClosed`.
  - ✅ HU-b LANDED axiom-clean (commit 6a187cf): general lemma `not_isUnit_invSelf_of_not_isIntegral`
    — x not integral over R ⟹ `IsLocalization.Away.invSelf x` non-unit in `adjoin R {x⁻¹}` (via
    `isIntegral_of_isIntegral_adjoin_of_mul_eq_one` + `IsLocalization.Away.isIntegral_of_isIntegral_map`).
  - ✅ **T-L4-EXT (Chevalley ring extension) steps 1-4 WIRED + T-L4-EXT-FIELD place extension PROVEN
    axiom-clean** (2026-06-21). T-L4-EXT = 1 sorry: the IsEquiv chase, **perf-blocked** at `he2`
    (`extendToLocalization` on the heavy `FractionRing F`). **FIX (turnkey, safe — nothing calls
    T-L4-EXT yet)**: reformulate T-L4-EXT to take `F`, `L` as `IsFractionRing`-generic PARAMETERS —
    `(F : Type*) [Field F] [Algebra (R ⧸ s.supp) F] [IsFractionRing (R ⧸ s.supp) F]`,
    `(L : Type uS) [Field L] [Algebra (S ⧸ q') L] [IsFractionRing (S ⧸ q') L]` — drop the `let
    F`/`let L`; with `F` opaque, `extendToLocalization`/`he2` stay light and the (already-written)
    chase compiles. Caller (HU-d) provides `F := FractionRing (R ⧸ s.supp)`, `L := FractionRing (S ⧸ q')`.
  - ✅ **HU-c/d/e LANDED 2026-06-21 (this session) — mem_plus reduced to ONE leaf (continuity).**
    - ✅ Scaffold: localization `Bx := Localization.Away x`, `letI : Algebra ↥B⁺ Bx` (canonical
      OreLocalization instances — do NOT add a second `Algebra ↥B⁺ Bx` letI, it diamonds with
      `OreLocalization.instSMulOfIsScalarTower`), HU-b non-unit, maximal `𝔪 ∋ x⁻¹`.
    - ✅ **HU-c DOMINATION lemma `exists_dominating_valuation_of_minimalPrime_le` PROVEN axiom-clean**
      (general: prime `p`, minimal prime `q ≤ p` → valuation `s` with `supp s = q`, `s ≤ 1` on `R`,
      `s < 1` on `p`; via `Localization.AtPrime (p/q)` + `IsLocalRing.exists_factor_valuationRing` +
      `to_map_mem_maximal_iff` + local-hom). The lying-over was the feared-hard step but is a mathlib
      one-liner: `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` (Stacks 00FK).
    - ✅ HU-d assembly: minimal prime `q ⊆ 𝔪` (`Ideal.exists_minimalPrimes_le`), lying-over `q'` of
      `Bx` (Stacks 00FK), `exists_valuation_extension_of_prime_over` → `t`, `v := comap(B→Bx)(ofValuation t)`.
    - ✅ HU-e(2): `¬ v.vle x 1` (v(x)>1) — bridge `v.vle ↔ t∘(B→Bx)` via `Valuation.Compatible.vle_iff_le`,
      `t(x⁻¹)<1` (from `s(x⁻¹)<1` + `ht_equiv`), `x⁻¹·x=1` (`mul_invSelf`) ⟹ `t(x)>1`.
    - ✅ HU-e(1b): `v ≤ 1` on `B⁺` — `f∈B⁺ ⊆ R`, `s f ≤ 1` (`hs_le`) transported by `ht_equiv`.
    - ⏳ **ONE leaf left = HU-e(1a) continuity** (`v.IsContinuous`).
      ✅ **A°°-FORM CRITERION BUILT sorry-free 2026-06-21** (the key faithful piece). Source-verified
      (Huber Thm 3.1, huber2.txt:585): the faithful criterion uses `A°°` not `A₀`. The in-repo
      `Spv.isContinuous_of_isInSpvAI_of_lt_one` is the **A₀-form** (h_le_one over the ring of definition),
      STRONGER than Huber's `A°°`-form — since `A⁺⊆A₀` (Presheaf:236) and `v≤1` is known only on `A⁺`, it
      is NOT applicable here. Built the faithful replacement in SpvAI.lean (commit): `cofinalValue_principal_pow_lt`
      (the `I^n` decay for PRINCIPAL `I=(π)` via `a=π^(n-1)(πb)`, `πb∈A°°` — uses `v≤1 on A°°`, NOT `A₀`) +
      `Spv.isContinuous_of_isInSpvAI_of_lt_one_principal` (Huber 3.1 reverse, A°°-form).
      **Remaining wiring** (`P:=IsTateRing.principalPair B`; witness `restrictIdeal v (Ideal.map A₀.subtype P.I)`,
      which preserves `v(x)>1` [v(x)≥1∈cΓ] and `v≤1 on B⁺`; (c) `v≤1 on B°°` via `B°°⊆B⁺`) bottoms at
      property (d) `IsInSpvAI`, i.e. the **documented project sorry `ofValuation_restrictIdeal_isInSpvAI`**
      (SpvAITopology.lean:484 = Wedhorn 7.4(ii)/7.5(2): the `ConvexSubgroup.minContain` cofinal/microbial
      dichotomy — a deep standalone spectral-machinery leaf, one of SpvAITopology's 37 sorries). THE single
      remaining bottom of T-L4's continuity = this Wedhorn 7.4(ii) dichotomy. Faithful cited-external
      (Huber Thm 3.1). All other parts of Huber 3.3(i) ✓ proven.

#### Statement
```lean
theorem isPowerBounded_of_forall_vle_one_spa_of_complete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'), w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance x
```

#### Proof sketch (reviewer Q1 — RED FLAG WITHDRAWN)
1. State the named leaf `mem_plus_iff_forall_spa_vle_one` = **Wedhorn 7.52(1) = 7.18(1)**: for the
   affinoid ring `B = (presheafValue D', (presheafValue D')⁺)`,
   `x ∈ (presheafValue D')⁺  ⟺  ∀ w ∈ Spa B, w.vle x 1`. **Hypothesis-free** in the affinoid setting
   (any affinoid ring; NO completeness/Tate/**noetherian**). The `←` (Spa-bound ⟹ membership) is the
   substantive direction (= τ∘σ = id of the 7.18(1) bijection).
2. From `hx`, conclude `x ∈ (presheafValue D')⁺` by the leaf.
3. `x ∈ (presheafValue D')⁺ ⊆ B°` by `IsRingOfIntegralElements.subset_powerBounded` (the affinoid axiom,
   resolved via `presheafValuePlus_isRingOfIntegralElements` = T-L2). `x ∈ B° ⟹ IsPowerBounded x`.
- **DO NOT** route via Huber 3.3(iii)/density/noetherian (reviewer risk #1: that is the *different*
  converse 7.18(3)). The current docstring's "[Hu2] 3.3 external / noetherian" framing is the
  mis-citation to fix.

#### Mathlib lemmas needed
`IsRingOfIntegralElements.subset_powerBounded`, `TopologicalRing.powerBoundedSubring` membership ⟹
`IsPowerBounded` (`mem_powerBoundedSubring_iff` / `isPowerBounded_of_mem`). The 7.52(1) leaf bottoms at
[Hu2] Lemma 3.3 parts (i)/(ii) — the bijection, content in [Hu1] §3 (IN HAND); NOT part (iii).

#### Sources
Wedhorn Prop 7.52(1) (p.74, `wedhorn.txt:3619`: "|f(x)|≤1 ∀x∈Spa A iff f∈A⁺"), Prop 7.18(1) (p.60,
`:3161`, "Proof. [Hu2] Lemma 3.3"); Def 7.14(1) (`A⁺ ⊆ A°`). Reviewer reply Q1 + risk #1.
**[Hu2] = R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477 — IN HAND**
(`references/huber2-continuous-valuations.pdf`, OCR `references/huber2.txt`): **Lemma 3.3(i), p.466
(`huber2.txt:624-627`)** = the σ/τ inverse bijection; proof `:633-658` is hypothesis-free.

#### Generality decision
State the 7.52(1) leaf for a general affinoid ring `(B, B⁺)` (no Tate/complete/noetherian) for reuse;
apply at `B = presheafValue D'`.

#### FAITHFUL Huber-3.3(i) sub-decomposition (un-park 2026-06-21; transcribed from huber2.txt:633-658)
The substantive direction is **τ(σ(B⁺)) ⊆ B⁺** (`mem_plus_iff_forall_spa_vle_one` ←). Huber's proof
(p.466) is a contradiction: assume `a ∈ τ(σ(B⁺)) \ B⁺` and build `v ∈ σ(B⁺)=Spa(B,B⁺)` with `v(a)>1`,
contradicting `a ∈ τ(σ(B⁺))`. Set `G := B⁺` (open, integrally closed in `B`). Sub-lemmas, in order:

- **HU-a** `not_isUnit_inv_of_not_mem` (leaf, integral-closure): for `a ∉ G`, `a⁻¹` is NOT a unit of
  the subring `G[a⁻¹] ⊆ B_a`. Source (huber2.txt:635-637, verbatim): *"The element a⁻¹∈G[a⁻¹] is not
  a unit of G[a⁻¹] (since otherwise a∈G[a⁻¹] which implies that a is integral over G and hence a∈G)."*
  Discharge: `RingHom`/`IsIntegral` + `G` integrally closed (`IsIntegrallyClosed`-style for the ROIE
  `G=B⁺`). mathlib `isIntegral_of_mem_closure`/`Algebra.IsIntegral`. ≈ Huber 3 lines → ~40 LOC.
- **HU-b** `exists_minimalPrime_le_prime_containing_inv` (leaf, mathlib): from HU-a, `∃` prime `p ∋ a⁻¹`;
  take a minimal prime `q ⊆ p`. Source (637-639): *"there exists a prime ideal p of G[a⁻¹] with a⁻¹∈p.
  Let q be a minimal prime ideal of G[a⁻¹] with q⊆p."* Discharge: `Ideal.exists_le_maximal` /
  `Ideal.exists_minimalPrimes_le` (mathlib `Ideal.exists_minimalPrimes_le` : prime ⊇ a minimal prime).
- **HU-c** `exists_dominating_valuation` (leaf, ⭐mathlib crux): valuation ring of `Frac(G[a⁻¹]/q)`
  dominating the local ring `(G[a⁻¹]/q)_{p/q}` ⟹ valuation `s` of `G[a⁻¹]` with `q=supp(s)`, `s(g)≤1
  ∀g∈G`, `s(x)≤1 ∀x∈p` (so `s(a⁻¹)≤1`). Source (639-641). Discharge: **`IsLocalRing.exists_factor_valuationRing`**
  (`Mathlib.RingTheory.Valuation.LocalSubring`: `(f : R →+* K) → ∃ A, (∀ x, f x ∈ A) ∧ IsLocalHom …`)
  at `R := (G[a⁻¹]/q)_{p/q}`, `K := Frac(G[a⁻¹]/q)`. The local-hom property gives `s ≤ 1` on the ring
  and `< 1` (i.e. into 𝔪) on `p/q`.
- **HU-d** `exists_lifted_spv_valuation` (leaf, valuation-lift bookkeeping): lift `s` to a valuation
  `v` of `B` (via a prime of `B_a` over `q`, a valuation `t` of `B_a` over `s`, `u := t∘(B→B_a)`,
  `v := u|cΓ`) with **(a)** `v(a)>1`, **(b)** `v(g)≤1 ∀g∈G`, **(c)** `v(y)≤1 ∀y∈B°°`, **(d)**
  `v ∈ Spv(B, B°°·B)`. Source (641-655, incl. the (c) sub-argument: `y∈B°°`, `G` open ⟹ `∃n, yⁿa∈G`,
  `y∈G`, so `yⁿ=g·a⁻¹∈p` ⟹ `s(yⁿ)≤1`). Discharge: mathlib `Valuation.comap` (restriction) +
  valuation extension along `G[a⁻¹]→B_a` (`Valuation` on `Frac`); the project's `Spv`/`vle` API.
  Hardest bookkeeping leaf; may sub-split (a)/(b)/(c)/(d).
- **HU-e** `mem_spa_of_lifted` + contradiction (composition): from (c)+(d) and the **axiom-clean**
  `Spv.isContinuous_of_isInSpvAI_of_lt_one` (SpvAI:294 = Wedhorn 7.10 reverse), `v` is continuous;
  with (b), `v ∈ Spa(B,B⁺)=σ(G)`. Then `hx`/`a∈τ(σ(B⁺))` gives `v(a)≤1`, contradicting (a) `v(a)>1`.
  Source (656-658). Discharge: composition + `Spv.isContinuous_of_isInSpvAI_of_lt_one`.
- **L-714** (leaf, project, ALREADY available): `B⁺ ⊆ B°` = `IsRingOfIntegralElements.subset_powerBounded`
  (used at Cor832:1626). Final step `x∈B⁺ ⟹ IsPowerBounded x`.

**Generality:** prove HU-a…e for a general complete affinoid `(B,B⁺)` (Huber's proof needs no
noeth/domain/Tate beyond what `Spv.isContinuous_of_isInSpvAI_of_lt_one` already assumes); apply at
`B=presheafValue D'`. **File**: new `HuberLemma33.lean` (imports SpvAI + the ROIE interface), or extend
FaithfulLocLift. **First /beastmode step**: state HU-a…e as `:= by sorry` and confirm `lake build`
(skeleton), THEN fill HU-c (crux) and HU-e (continuity) first since their discharges are verified.

---

### [T-L4-EXT] Constructive valuation extension along a ring inclusion (Chevalley for rings) — sub-ticket of T-L4 (HU-d)
- **Status**: ✅ **DONE** (2026-06-21) — `exists_valuation_extension_of_prime_over` PROVEN axiom-clean
  (lean_verify, no sorryAx). Steps 1-4 (onQuot → extendToLocalization → Ideal.quotientMap field embed
  → T-L4-EXT-FIELD place extension → Spv.comap) + the IsEquiv chase all landed. KEY: `F`,`L` are
  `IsFractionRing`-generic PARAMETERS (caller passes `FractionRing`), keeping `extendToLocalization`
  light (avoids the whnf-timeout that the `let FractionRing` form hit). Depends on T-L4-EXT-FIELD ✅.
- **Status (was)**: 🔵 OPEN — **Parent**: T-L4. Spawned 2026-06-21 (/beastmode Tier-A); the gap was
  confirmed by 3 searches (leansearch + 2× loogle): mathlib's `Valuation.HasExtension` is only a
  PREDICATE + accessors (`val_map_le_one_iff` etc.) and the constructors (`mk`, `ofComapInteger`)
  require an already-existing extension `vA`; there is **no constructive `exists_extension`** that
  builds a valuation on the overring from one on the subring.
- **File**: FaithfulLocLift.lean (or a new `ValuationExtension.lean`).
- **Type**: theorem (infrastructure).
- **Why needed (Huber 3.3(i) HU-d, huber2.txt:641-643):** *"Since there exists a prime ideal of
  A_a lying over q, there exists a valuation t of A_a lying over s."* — `s` is the dominating
  valuation on the subring `R[x⁻¹] ⊆ Bx`; HU-d needs `t` on `Bx` extending `s`, then
  `Spv.comap (algebraMap B Bx)` gives `v : Spv B`.

#### Statement (Chevalley extension, the form HU-d consumes) — ⚠ lying-over hypothesis REQUIRED
```lean
theorem exists_valuation_extension_of_prime_over
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (s : Valuation R Γ)
    (q' : Ideal S) [q'.IsPrime] (hq' : Ideal.comap (algebraMap R S) q' = s.supp) :
    ∃ (Γ' : Type*) (_ : LinearOrderedCommGroupWithZero Γ') (t : Valuation S Γ'),
      s.IsEquiv (Valuation.comap (algebraMap R S) t) := by sorry
```
**Adversarial correction (2026-06-21):** the bare-injective form is FALSE (a valuation need not
extend with no prime over `supp s` — generic-fibre obstruction). The lying-over prime `q'` is a
NECESSARY hypothesis (CLAUDE.md-justified: false without it); Huber supplies it (huber2.txt:641
"a prime ideal of A_a lying over q"). HU-d must construct `q'` (prime of `Bx` over the minimal
prime of `R[x⁻¹]`) — a further sub-step (going-up/structure of the localization `Bx`).

#### Proof sketch (Chevalley/Zorn, ring case)
1. Let `q = supp(s)`; `s` factors through `R/q ↪ Frac(R/q) = F` as a valuation `s̄` with valuation
   ring `O_s̄ ⊆ F`. (mathlib: `Valuation` support, `Valuation.IsEquiv` to the induced field valuation.)
2. Choose a prime `q'` of `S` lying over `q` (Huber's "prime of A_a lying over q"; for the HU-d
   instance `q` is a minimal prime, and `R[x⁻¹] ⊆ Bx` has a prime over it). `S/q' ↪ Frac(S/q') = L`,
   and `F ↪ L` compatibly (since `R/q ↪ S/q'`).
3. Extend the valuation ring `O_s̄ ⊆ F` to a valuation ring `O ⊆ L` (Chevalley: mathlib
   `ValuationSubring`/`LocalSubring.exists_le_valuationSubring`, or `IsLocalRing.exists_factor_valuationRing`
   applied to `(O_s̄-localized-in-L)`-style). The valuation `t̄` of `L` with ring `O` restricts to
   `s̄` on `F`.
4. `t := Valuation.comap (S → S/q' → L) t̄`. Then `s.IsEquiv (comap (algebraMap R S) t)` by chasing
   the diagram `R → S → L` vs `R → F → L`.
- ⚠ This is genuine commutative-algebra infrastructure (Chevalley's valuation-extension theorem for
  rings). mathlib has the FIELD case ingredients (`LocalSubring.exists_le_valuationSubring`,
  `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`) + the `HasExtension` predicate; the
  ring-case constructor must be assembled. Moderate (standard, in mathlib's scope) — NOT research-scale.

#### Mathlib lemmas needed (ALL FOUND 2026-06-21 — turnkey)
- Step 1 ✅DONE: `Valuation.onQuot` (`s.onQuot le_rfl : Valuation (R⧸supp s) Γ`) +
  `Valuation.instIsPrimeSuppOfNontrivialOfNoZeroDivisors` (supp prime).
- Step 2 (domain → fraction field): `Valuation.extendToLocalization`
  (`(v) (hS : S ≤ v.supp.primeCompl) (B) [IsLocalization S B] : Valuation B Γ`) at
  `S = nonZeroDivisors (R⧸supp)`, `B = FractionRing (R⧸supp)`; needs `sQuot.supp = ⊥` (onQuot kills supp).
  + `extendToLocalization_apply_map_apply` / `_mk'` for value computations.
- Step 3 (embed via `hq'`): `R⧸supp ↪ S⧸q'` (Ideal.quotientMap from `hq' : comap q' = supp`);
  `IsFractionRing.lift`/`FractionRing` functoriality → `F ↪ L = FractionRing (S⧸q')`.
- Step 4 (extend valuation ring + back): `LocalSubring.exists_le_valuationSubring`
  (`(A : LocalSubring K) : ∃ V, A ≤ V.toLocalSubring`) on the image of `sQuot_F.valuationSubring` in `L`;
  `ValuationSubring.valuation (V : ValuationSubring L) : Valuation L V.ValueGroup`;
  `t := Valuation.comap (S → S⧸q' → L) V.valuation`; `Valuation.isEquiv_valuation_valuationSubring`,
  `ValuationSubring.integer_valuation`, `Valuation.IsEquiv` transitivity for the final `s.IsEquiv (comap t)`.
- Lying-over `q'` (HU-d supplies it): `Ideal.exists_minimalPrimes_le` + the localization structure of `Bx`.

---

### [T-L4-EXT-FIELD] Field-case place extension (sub-ticket of T-L4-EXT)
- **Status**: ✅ **DONE** (2026-06-21) — `exists_comap_isEquiv_of_field_hom` PROVEN axiom-clean
  (lean_verify: [propext, Classical.choice, Quot.sound], no sorryAx). Construction:
  `LocalSubring.map ι v.valuationSubring.toLocalSubring` → `LocalSubring.exists_le_valuationSubring` →
  `V`, `w := V.valuation`; IsEquiv via `isEquiv_iff_valuationSubring` + `(comap ι w).valuationSubring
  = V.comap ι` + the contraction `V.comap ι = v.valuationSubring` (`le_antisymm` via
  `isMax_toLocalSubring` + `LocalSubring.le_def`; the IsLocalHom domination transfer via
  `isUnit_iff_exists_inv` + `mul_left_cancel₀` + ι-injective pullback from `hV`). A genuine
  formalization of Chevalley's place-extension theorem for fields (not constructively in mathlib).
- **Status (was)**: 🔵 OPEN — **Parent**: T-L4-EXT. Spawned 2026-06-21 (/beastmode Tier-A). The classical
  place-extension theorem (a valuation on a field extends along a field homomorphism). mathlib has
  the `Valuation.HasExtension` predicate but no constructive existence (confirmed via leansearch).
- **File**: FaithfulLocLift.lean. **Type**: theorem.
- **Statement** (`exists_comap_isEquiv_of_field_hom`, stated + wired into T-L4-EXT):
  ```lean
  theorem exists_comap_isEquiv_of_field_hom {F L : Type*} [Field F] [Field L] (ι : F →+* L)
      {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) :
      ∃ (Γ' : Type*) (_ : LinearOrderedCommGroupWithZero Γ') (w : Valuation L Γ'),
        v.IsEquiv (Valuation.comap ι w) := by sorry
  ```
- **Proof sketch**: `O := v.valuationSubring` is a `ValuationSubring F`. `ι` injective (field hom)
  ⟹ `ι(O)` is a `LocalSubring L`. `LocalSubring.exists_le_valuationSubring` gives `V : ValuationSubring L`
  dominating `ι(O)`. Take `w := V.valuation`. `ι⁻¹(V) = O`: ⊇ since `ι(O) ⊆ V`; ⊆ since for `f ∉ O`,
  `f⁻¹ ∈ 𝔪_O` ⟹ `ι(f⁻¹) ∈ 𝔪_V` (domination) ⟹ `ι(f) ∉ V`. So `(comap ι w).valuationSubring = O =
  v.valuationSubring`, hence `v ≈ comap ι w` (same valuation subring ⟹ equiv).
- **Mathlib lemmas**: `Valuation.valuationSubring`, `LocalSubring.exists_le_valuationSubring`,
  `ValuationSubring.valuation`, `ValuationSubring.integer_valuation`, the `LocalSubring ≤`=domination
  order, `Valuation.isEquiv_iff` via valuation subring equality (`ValuationSubring.valuation` IsEquiv).
- **Generality**: stated for general fields `F`, `L` (reusable).
- **Progress** (2026-06-21 /beastmode): construction + IsEquiv reduction LANDED (commits up to the
  contraction). `exists_comap_isEquiv_of_field_hom` now bottoms at **ONE sorry**: the IsLocalHom
  (domination) goal `IsLocalHom (Subring.inclusion hsubF)` (`hsubF : O.toSubring ≤ (V.comap ι).toSubring`,
  `O := v.valuationSubring.toLocalSubring`). **Turnkey argument** (from `hV` via
  `LocalSubring.le_def.mp hV = ⟨hsub_L, hlocal_L⟩`, `hlocal_L : IsLocalHom (incl_L : ι(O) ↪ V)`):
  `refine ⟨fun a ha => ?_⟩`; from `ha : IsUnit (incl a)` get `(↑a)⁻¹ ∈ V.comap ι` ⟹ `(ι ↑a)⁻¹ = ι((↑a)⁻¹) ∈ V`;
  with `ι ↑a ∈ ι(O) ⊆ V` (`hsub_L`) ⟹ `ι ↑a` is a unit in `V`; the element `⟨ι ↑a, _⟩ : ↥ι(O)` maps
  to it, so `hlocal_L` ⟹ `ι ↑a` unit in `ι(O)` ⟹ `(ι ↑a)⁻¹ = ι((↑a)⁻¹) ∈ ι(O)` ⟹ `(↑a)⁻¹ ∈ O`
  (ι injective) ⟹ `IsUnit a`. ⚠ ~35 lines of subring-coercion unit-chasing (`Subring.equivMapOfInjective`,
  `Units`, `LocalSubring.map_toSubring`); the only remaining FaithfulLocLift field-lemma piece.

---

## T-SPVAI — Faithful principal `IsInSpvAI` (sub-dependency of T-L4 / HU-e continuity)

**Context (2026-06-22).** `ofValuation_restrictIdeal_isInSpvAI` was found **FALSE** (B2,
`b2_log.jsonl`): the general `cGammaIdeal` diverges from Wedhorn Def 7.3 (`wedhorn.txt:2942`).
User-approved faithful fix = the **principal** case (the only one HU-e uses, via
`IsTateRing.principalPair`). Already landed (commits 94e2332/1eb111e/241d352, build green):
`cGammaUnits`/`cGammaSingle`/`restrictIdealSingle`/`cGamma` + collapse identities
(`cGammaSingle_eq_cGamma_of_mem`, `cGammaSingle_eq_convexGenerated_of_subset`) + the proven generic
transfers (`cofinalValue_canon_of_restricted`, `isMicrobial_canon_of_restricted`) + the TRUE
replacement `ofValuation_restrictIdealSingle_isInSpvAI` (sorry-free **modulo** the 2 sub-lemmas
below). These tickets discharge those 2 sub-lemmas and wire the result into HU-e.

### [T-SPVAI-1] Wedhorn Prop 1.20 — `cofinal · bounded = cofinal`
- **Status**: done (2026-06-22; `IsCofinalElt` + `isCofinalElt_mul_of_mem_of_lt`, OrderedGroupConvex, axiom-clean)
- **File**: `Adic spaces/OrderedGroupConvex.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: def + lemma (INFRASTRUCTURE — general ordered-group; IS Wedhorn Prop 1.20)

#### Statement
```lean
/-- Wedhorn Def 1.16: `γ` is cofinal for the convex subgroup `H`. -/
def ConvexSubgroup.IsCofinalElt (H : ConvexSubgroup Γ) (γ : Γ) : Prop :=
  ∀ h ∈ H, ∃ n : ℕ, γ ^ n < h

/-- **Wedhorn Proposition 1.20.** `Γ' γ` cofinal, `Δ ⊊ Γ'` proper convex, `δ ∈ Δ` ⟹ `δγ`
cofinal for `Γ'`. -/
theorem ConvexSubgroup.isCofinalElt_mul_of_mem_of_lt {Γ' Δ : ConvexSubgroup Γ}
    (hlt : Δ < Γ') {γ : Γ} (hγ : Γ'.IsCofinalElt γ) {δ : Γ} (hδ : δ ∈ Δ) :
    Γ'.IsCofinalElt (δ * γ) := by sorry
```

#### Proof sketch (wedhorn.txt:351-352)
1. From `Δ ⊊ Γ'` pick `γ₀ ∈ Γ'` with `γ₀ < Δ` (i.e. `γ₀ < x` for all `x ∈ Δ`, so `Δ < γ₀⁻¹`):
   `Δ` proper-convex in `Γ'` ⟹ ∃ element of `Γ'` strictly below all of `Δ` (the cofinal
   direction). [The witness is `γ^n` for `n` large by `hγ`, see step 2 — can take `γ₀ := γ^n`.]
2. By `hγ` (cofinal): `∃ n, γ^n < γ₀`. For any target `h ∈ Γ'`, `∃ m, γ^m < h`.
3. `(δγ)^(2n) = δ^(2n) γ^(2n) < γ₀⁻¹ γ^(2n) < γ^n` — first `<` from `δ^(2n) ∈ Δ < γ₀⁻¹`
   (`Δ` subgroup), second from `γ₀⁻¹ γ^n < 1` ⟺ `γ^n < γ₀`. Iterating gives `(δγ)` cofinal.
4. Tactic realisation: `mul_lt_mul'`, `pow_lt_pow_left`-style monotonicity, `inv_lt_iff`,
   `ConvexSubgroup` membership (`mul_mem`, `inv_mem`); the convexity gives `γ₀ < Δ` witness.

#### Mathlib lemmas needed
- `mul_le_mul'` / `mul_lt_mul'` (ordered comm group), `inv_mul_lt_iff` / `lt_inv_mul_iff`
- `pow_le_pow_right'`, `mul_pow` — verify via `lean_loogle` at use time.

#### Sources
- Wedhorn, *Adic Spaces* (arXiv:1910.05934), **Proposition 1.20**, p. 6 (`wedhorn.txt:348`);
  Definition 1.16, p. 5 (`wedhorn.txt:325`); Remark 1.19, p. 6 (`wedhorn.txt:339`).

#### Generality decision
- Stated over `{Γ : Type*} [LinearOrderedCommGroup Γ]` (Wedhorn's "totally ordered group");
  applies to `Γ₀ˣ`. `ConvexSubgroup`-level, no valuation.

---

### [T-SPVAI-2] `restrictIdealSingle_cofinal_of_not_mem` (Wedhorn Lemma 7.1 + 7.2, `=∅` branch)
- **Status**: done (2026-06-22; SpvAITopology, via Prop 1.20 + convexGenerated cofinality)
- **File**: `Adic spaces/SpvAITopology.lean` (sorry at the stated decl)
- **Depends on**: T-SPVAI-1
- **Parallel**: no
- **Type**: lemma

#### Statement
```lean
theorem restrictIdealSingle_cofinal_of_not_mem (w : Valuation A Γ₀) (g : A) (hg : w g ≠ 0)
    (hmem : (Units.mk0 (w g) hg)⁻¹ ∉ Valuation.cGamma w) :
    ∀ a ∈ Ideal.span {g}, Valuation.CofinalValue (w.restrictIdealSingle g hg) a := by sorry
```

#### Proof sketch (Wedhorn Lemma 7.1 `:2904` + 7.2 `:2911`)
1. `hy : 1 < (Units.mk0 (w g) hg)⁻¹` — by_contra ⟹ `w g ≥ 1` ⟹ `mk0(w g) ∈ cGammaUnits ⊆ cGamma`
   ⟹ `(mk0 w g)⁻¹ ∈ cGamma` (inv_mem), contra `hmem`. [verified pattern; needs `one_lt_inv'`-style]
2. `hsub : cGammaUnits w ⊆ convexGenerated hy` — each char gen unit `u ≤ mk0(w b) < (mk0 w g)⁻¹`
   (the `< (mk0 w g)⁻¹` from convexity: `(mk0 w g)⁻¹ ∉ cGamma` and `>1` ⟹ above every cGamma
   element ⟹ above every char value), and `(mk0 w b)⁻¹ > (mk0 w g)` so `u ∈ [y⁻¹, y]` (`n=1`).
3. `cGammaSingle w g hg = convexGenerated hy` — `cGammaSingle_eq_convexGenerated_of_subset` (done).
4. `a ∈ Ideal.span {g}` ⟹ `a = g * c` (`Ideal.mem_span_singleton`). If `w a = 0` (⟺ `w c = 0`):
   `rs a = 0`, `CofinalValue` trivial (`0^1 = 0 < δ`). Else `rs a = w a` (preserved).
5. `CofinalValue rs (g*c)` ⟺ (plumbing) `IsCofinalElt cGammaSingle (mk0 (w(g*c)))` at `Γ₀ˣ`.
   - `w c ≤ 1`: `mk0(w(g*c)) = mk0(w c)·(mk0 w g) ≤ mk0(w g) = y⁻¹` ⟹ cofinal via
     `exists_inv_pow_lt_of_mem_convexGenerated` + `pow_le_pow_left'`.
   - `w c > 1`: `mk0(w c) ∈ cGamma w` (char value, `vUnit_mem_cGamma`); `cGamma ⊊ convexGenerated hy`
     (proper: `y ∈ cG, y ∉ cGamma`); apply **T-SPVAI-1** (Prop 1.20) with `γ := mk0(w g)`,
     `Γ' := convexGenerated hy`, `Δ := cGamma w`, `δ := mk0(w c)`.
6. Plumbing lemma (state inline or as helper): `CofinalValue (restrictToConvexBounded …) a` for
   `mk0(v a) ∈ H` ⟺ `H.IsCofinalElt (mk0 (v a))` — unfold `restrictToConvexBounded_apply_mem`,
   `WithZero`/subgroup coercions, `pow`/`<` transfer (mechanical).

#### Mathlib lemmas needed
- `Ideal.mem_span_singleton`, `map_mul`, `pow_le_pow_left'`, `one_lt_inv'`/`inv_lt_one'`,
  `WithZero.coe_lt_coe`, `Units.val_lt_val` — verify at use time.

#### Sources
- Wedhorn Lemma 7.1 (`:2904`), Lemma 7.2 (`:2911`), Lemma 7.4 (`:2948`).

#### Generality decision
- Principal `(g)` only — justified: the general statement is FALSE (B2) and the consumer is
  principal. `Γ₀` arbitrary `LinearOrderedCommGroupWithZero`, `A` the section `CommRing`.

---

### [T-SPVAI-3] `restrictIdealSingle_isMicrobial_of_mem` (`cGammaUnits` is a convex subgroup)
- **Status**: done (2026-06-22; `cGammaConvex` + `mem_cGamma_iff` in CharSubgroup + assembly in SpvAITopology)
- **File**: `Adic spaces/CharacteristicSubgroup.lean` (helper) + `SpvAITopology.lean` (assembly)
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma (+ structure helper)

#### Statement
```lean
/-- `cGammaUnits w` is already a convex subgroup: bounded-by-one-value is closed under the group
ops because `w` is multiplicative. Hence `cGamma w` membership ⟺ bounded by a single value. -/
theorem Valuation.mem_cGamma_iff (w : Valuation A Γ₀) {u : Γ₀ˣ} :
    u ∈ cGamma w ↔ u ∈ cGammaUnits w := by sorry  -- minContain of a convex subgroup = itself

theorem restrictIdealSingle_isMicrobial_of_mem (w : Valuation A Γ₀) (g : A) (hg : w g ≠ 0)
    (hmem : (Units.mk0 (w g) hg)⁻¹ ∈ Valuation.cGamma w) :
    Valuation.IsMicrobial (w.restrictIdealSingle g hg) := by sorry
```

#### Proof sketch
1. **`cGammaUnits w` is a `ConvexSubgroup`** (the key fact): for `u₁ ∈ [w(a₁)⁻¹, w(a₁)]`,
   `u₂ ∈ [w(a₂)⁻¹, w(a₂)]` (`w aᵢ ≥ 1`): `u₁u₂ ∈ [w(a₁a₂)⁻¹, w(a₁a₂)]` since
   `w(a₁a₂) = w a₁ · w a₂ ≥ 1` (`map_mul`); inverse: `u⁻¹ ∈ [w(a)⁻¹, w(a)]` (same interval);
   convex: `u₁ ≤ u ≤ u₂` ⟹ `u ∈ [w(a₁)⁻¹, w(a₂)] ⊆ [w(a₁a₂)⁻¹, w(a₁a₂)]` (both `w aᵢ ≥ 1`);
   `1 ∈` (a=1). Then `cGamma w = minContain(cGammaUnits w) = ` that subgroup (`minContain_le` both
   ways), giving `mem_cGamma_iff`.
2. `cGammaSingle w g hg = cGamma w` (`cGammaSingle_eq_cGamma_of_mem hmem`, done).
3. `IsMicrobial rs`: `∀ γ ∈ cGamma w (= value group), ∃a, 1≤rs a ∧ (rs a)⁻¹≤γ≤rs a`. From
   `mem_cGamma_iff`, `γ`'s unit `∈ cGammaUnits w` ⟹ `∃a, 1≤w a ∧ (mk0 w a)⁻¹≤γ≤mk0 w a`;
   take that `a` (`rs a = w a`, preserved since `w a ≥ 1 ⟹ mk0(w a) ∈ cGammaSingle`).
4. Plumbing: `γ : WithZero (cGammaSingle…).toSubgroup`, transfer to `Γ₀ˣ` via the identity.

#### Mathlib lemmas needed
- `map_mul`, `mul_le_mul'`, `inv_le_inv_iff`, `ConvexSubgroup.minContain_le`,
  `ConvexSubgroup.subset_minContain` — all available/used already.

#### Sources
- Wedhorn Def 4.13 (`cΓ_v`, characteristic subgroup, p. 27) — the microbial notion `cΓ_v = Γ_v`.

#### Generality decision
- `mem_cGamma_iff` is a clean general characterisation of `cGamma` (reusable). Principal for the
  microbial lemma (same justification as T-SPVAI-2).

---

### [T-SPVAI-4] Wire `restrictIdealSingle` into `mem_plus` continuity (HU-e)
- **Status**: open
- **File**: `Adic spaces/FaithfulLocLift.lean`
- **Depends on**: T-SPVAI-2, T-SPVAI-3
- **Parallel**: no
- **Type**: wiring (continuity discharge)

#### Statement / goal
Replace the HU-e reference to the **false** `ofValuation_restrictIdeal_isInSpvAI` (currently in
comments, FaithfulLocLift:398-410) with the TRUE `ofValuation_restrictIdealSingle_isInSpvAI`,
feeding `Spv.isContinuous_of_isInSpvAI_of_lt_one_principal`.

#### Proof sketch
1. `P := IsTateRing.principalPair (presheafValue D')`; `π := P` generator; `g := P.A₀.subtype π`
   (the image in `B`). The witness valuation `v` is the HU-c dominating valuation; restrict via
   `v.restrictIdealSingle g (hg)` where `hg : v g ≠ 0` (from `g ≠ 0` / `v` on the relevant point).
2. `Ideal.span {g} = Ideal.map P.A₀.subtype P.I` (since `P.I = (π)` principal; `Ideal.map_span`,
   `Set.image_singleton`).
3. Feed `ofValuation_restrictIdealSingle_isInSpvAI v g hg : IsInSpvAI (ofValuation …) (span{g})`
   to `Spv.isContinuous_of_isInSpvAI_of_lt_one_principal` (rewriting the ideal via step 2) +
   the existing `v ≤ 1 on B⁺` / `v < 1 on B°°` HU-e facts ⟹ continuity ⟹ contradiction ⟹ `mem_plus`.
4. ⚠ The HU-e/d/c construction around this is the larger T-L4 body; this ticket is the
   `restrictIdeal → restrictIdealSingle` swap + ideal-matching at the one continuity site.

#### Mathlib lemmas needed
- `Ideal.map_span`, `Set.image_singleton`, `Ideal.span_singleton_eq` (ideal-matching).

#### Sources
- Huber Thm 3.1 (`huber2.txt:585`, A°°-form continuity criterion); Wedhorn 7.10 reverse
  (`Spv.isContinuous_of_isInSpvAI_of_lt_one_principal`, already in `SpvAI.lean`).

#### Generality decision
- Principal pair (the construction's actual setting). No new hypotheses on the headline.

---

### [CLEANUP-SPVAI] Run `/cleanup` on the T-SPVAI files
- **Status**: open
- **File**: `OrderedGroupConvex.lean`, `CharacteristicSubgroup.lean`, `SpvAITopology.lean`
- **Depends on**: T-SPVAI-4
- **Parallel**: no
- **Type**: cleanup
- **Description**: Cadence cleanup after the 4 T-SPVAI proof/wiring tickets (per §1g: ≥1 cleanup
  per ~3 proof tickets + final per touched file). Golf the Prop 1.20 / convex-subgroup proofs,
  check naming (`IsCofinalElt`, `mem_cGamma_iff`), strip the superseded false-leaf docs.

---

### [T-L5] Spa-quasicompactness keystone `isClosed_image_spa_ιSpv_bool_noHArch` (gluing-leaf bottom)
- **Status**: 🔵 OPEN — tracked here for the first time (was the untracked bottom of "Leaf C gluing").
  After the γ-route 7.54 (`exists_finite_normalized_rational_refinement`, WCA:11886), the gluing leaf
  (`lemma_8_34_gluing`) bottoms at this: `isClosed_image_spa_ιSpv_bool_noHArch` (SpaCompactNoHArch.lean:310,
  bare `sorry`). = **Wedhorn 7.35(1)**: Spa A is a spectral space (hence Spa-QC), via Spv(A,I)
  pro-constructibility. ⚠DEEPEST leaf — the SpvAITopology spectral-spaces track; support lemmas
  (`cont_isClosed_in_SpvAI`, `isClosed_setOf_vle`) themselves carry `sorryAx`. Defer to its own
  `/develop --decompose` (read wedhorn.txt:3346-3370 + Lemma 7.5 + Cor 7.12 first). NOT this push.
- **Depends on**: SpvAI spectral infrastructure (separate track).
- **Type**: theorem (deep).

#### Statement
```lean
lemma isClosed_image_spa_ιSpv_bool_noHArch :
    IsClosed ((ιSpv_bool : Spv A → (A × A → Bool)) '' (Spa A A⁺)) := by sorry
```
#### Source
Wedhorn 7.35(1) (wedhorn.txt:3346-3370, verbatim): *"Spa A = Cont(A) ∩ ⋂_{a∈A⁺} Spv(A,I)(a/1) is a
pro-constructible subset of the spectral space Spv(A,I). … In particular it is a spectral space."*
(I = ideal generated by A°°.) Needs: Spv(A,I) spectral (Lemma 7.5/Cor 7.12), Cont closed in Spv(A,I)
(Huber Cor 3.2), pro-constructible ⟹ spectral.

---

### [CLEANUP-L1] Run /cleanup on StructureSheaf.lean (leaf #1 equalizer decls)
- **Status**: open
- **Depends on**: T-L1c
- **Parallel**: no
- **Type**: cleanup
- **Description**: cadence (3 proof tickets T-L1a/b/c on StructureSheaf.lean). Golf the equalizer/OMT
  assembly; confirm no `[SigmaCompactSpace]`/module-finiteness crept in.

### [CLEANUP-L2L3L4] Run /cleanup on Presheaf.lean + FaithfulLocLift.lean
- **Status**: open
- **Depends on**: T-L2, T-L3, T-L4
- **Parallel**: no
- **Type**: cleanup
- **Description**: cadence (T-L2/T-L3 on Presheaf.lean, T-L4 on FaithfulLocLift.lean). Fix the T-L4
  docstring mis-citation; remove vestigial noeth-`A₀`/[Hu2]-3.3-external notes.

### [CLEANUP-FINAL] /cleanup-all + axiom audit
- **Status**: open
- **Depends on**: T-L1c, T-L2, T-L3, T-L4, CLEANUP-L1, CLEANUP-L2L3L4
- **Parallel**: no
- **Type**: cleanup
- **Description**: `#print axioms isSheafy_of_stronglyNoetherian_828b` — confirm the residual is exactly
  the source-justified external leaves {7.47(4)=[Hu1] 2.4.3, 7.45 analytic-point, 7.52(1)=[Hu2] 3.3,
  + Leaf C R2-transport}; no `[SigmaCompactSpace]`, no noeth-`A₀`, no `[IsDomain]`, no `sorryAx` beyond
  the named leaves.
```

#### Folded tickets
- **T-ROIE-3** → **T-L2** (sharpened: openness automatic via 7.19; completion via 7.47(4)).
- **T-ROIE-4** → **T-L3** (sharpened: general 7.45 branch only + existing maximality lemma).
- The former **leaf #4 "[Hu2] 3.3 noetherian external"** framing → **T-L4** (7.52(1), red flag withdrawn).
