# Ticket Board — Thm 8.28(b) sheafiness, revised 4-leaf plan (post /expert-review 2026-06-19)

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
- **Status**: open
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
- **Status**: open — replaces the bare `sorry` at StructureSheaf.lean:1384
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
- **Status**: PARKED — cited external leaf **[Hu2] Lemma 3.3(i)**, now SOURCED (user chose (c)).
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
