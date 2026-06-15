# Wedhorn-Faithfulness Audit — Adic Spaces (target: Theorem 8.28(b))

> Source anchors below were re-read directly from `/private/tmp/wedhorn.txt` (not memory). Confirmed: Thm 8.28 lists `(a) Â has a noetherian ring of definition` and `(b) A is a strongly noetherian Tate ring` as **explicit alternatives** (wedhorn.txt:4053–4054); Remark 6.37(3) makes "(a) ⇒ strongly-noeth" **one-directional** (wedhorn.txt:2687). Props 8.30/Cor 8.32/Lemma 8.33 are each stated for a "strongly noetherian Tate affinoid ring" with **no ring of definition** (wedhorn.txt:4095, 4142, 4151); Lemma 8.34 for a "complete strongly noetherian Tate ring" (wedhorn.txt:4222). Lemma 7.45 gives `supp x ⊇ p` in general, `supp x = p` only in the noetherian-ring-of-definition sub-case (wedhorn.txt:3336–3339). 6.17 is a *Proposition* with no `[IsNoetherianRing A]` hypothesis (wedhorn.txt:2449). 6.9 is a *Proposition* (wedhorn.txt:2379), Remark 2.13 is about valuation rings of a field (wedhorn.txt:567).

## 1. Executive summary

| Verdict | Count |
|---|---|
| Total declarations | 3526 |
| FAITHFUL | 703 |
| INFRASTRUCTURE | 2316 |
| **DIVERGENT** | **477** |
| **ORPHAN** | **21** |
| **UNCITED** | **9** |
| Flagged total (DIV+ORPH+UNC) | 507 |

**Overall faithfulness.** Roughly 86% of *cited, non-infrastructure* declarations either match Wedhorn (703 FAITHFUL) or diverge only cosmetically. But the **507 flagged declarations are concentrated in the load-bearing 8.28(b) acyclicity spine** — the very theorems the project exists to prove. The headline theorems (`tateAcyclicity`, `isSheafy_ofStronglyNoetherianTate*`, `cor_8_32_*`, all `tateAcyclicity_Part2_via_*`) are DIVERGENT. So the project is faithful in its periphery and **systematically unfaithful at its summit**.

**Three dominant divergence themes**, in descending danger:

1. **Case-(a) hypothesis imported into case-(b) results** (the single most dangerous, ~300+ declarations). A `[IsNoetherianRing P.A₀]` (noetherian *ring of definition*), `[IsNoetherianRing (locSubring …)]`, or the ORPHAN lemma `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` (which *asserts* "strongly-noeth-Tate ⇒ A₀ noetherian", **false for ℂ_p**) is threaded through every flatness / injectivity / gluing / sheafy result that Wedhorn proves for case (b) alone. This is exactly the (a)/(b) confusion the source forbids: ℂ_p is strongly-noeth-Tate with **no** noetherian ring of definition, and 8.28(b) holds for it.

2. **Added hypotheses with no source counterpart**: `[IsDomain A]` (on 8.34/7.54/separation results — Spa of an affinoid is not a domain), `hArch : ∀ v, MulArchimedean …` (CLAUDE.md explicitly forbids this pattern), `[CompatiblePlusSubring A]` (built on an orphan citation), `[T2Space A]`/`[NonarchimedeanRing A]` decorations, and `HasLocLiftPowerBounded` as a parametric carrier of unproved obligations.

3. **Mis-citations / orphan numbers** (~50+): the recurring fake **"Lemma 2.13"** (real source Prop 8.2(1)/Remark 7.55), **"Definition 6.9"** for strongly-noetherian / Tate algebras (6.9 is a Proposition; real sources are Prop&Def 6.36 and Rem&Def 5.48), **"Theorem 7.30"** (→ 7.35), **"Theorem 4.9"** (→ Prop 4.7), **"Prop 8.15"** mislabelled as restriction-as-localization (it is a *stalk* statement), and **"Lemma 7.45"** mislabelled as a cover-refinement statement (it is the non-open-prime analytic-point lemma).

Several flagged declarations also carry **`sorry` bodies on false-as-stated statements** (e.g. `restrictionMapHom_injective/_surj`, `IsPowerBounded.map`, the Sierpinski-closedness chain in `SpvAITopology`, `banach_two_of_three`'s `(a)∧(c)⇒(b)` direction) — these are not merely unfaithful but **unprovable as written**.

---

## 2. Critical DIVERGENCES

### 2A. Case-(a) "noetherian ring of definition" imported into case-(b) / sheafy / acyclicity results — THE HEADLINE DEFECT

Wedhorn 8.28(b) hypothesis is **exactly** "A is a strongly noetherian Tate ring", an alternative to case-(a)'s "noetherian ring of definition". Every declaration below carries `[IsNoetherianRing P.A₀]` (P.A₀ *is* the ring of definition, HuberRings.lean:57) and/or `[IsNoetherianRing (locSubring …)]` on a case-(b) result. **All fail the ℂ_p test** (strongly-noeth-Tate, no noetherian ring of definition).

**Headline theorems (most dangerous — these are the project's deliverables):**
- `WedhornCechAcyclicity.lean :: isSheafy_ofStronglyNoetherianTate_clean` — the audit calls this "THE HEADLINE DEFECT"; adds `[IsNoetherianRing (principalPair).A₀]` + `[IsDomain A]` + redundant `[IsNoetherianRing A]` to the case-(b) sheafy theorem, with a "Wedhorn-clean" label that is inaccurate.
- `StructureSheaf.lean :: isSheafy_ofStronglyNoetherianTate_flat`, `…_flat_of_topo_inducing`
- `AuditCleanWrappers.lean :: isSheafy_ofStronglyNoetherianTate_proof`, `cor_8_32_clean_proof`, `prop_8_30_flat_clean_proof`, `tateAcyclicity_separation_via_cor832_proof`, `tateAcyclicity_gluing_via_descent_proof`
- `LaurentRefinementAcyclic.lean :: tateAcyclicity`, `tateAcyclicity_gluing`, `rationalCovering_hasSeparation`, `rationalCovering_hasGluing` (+ the `_descent_witness*` chain) — all add `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` + redundant `[IsNoetherianRing A]`.
- `TateAcyclicityResiduals.lean :: tateAcyclicityComplete (Closure 1)`, `isSheafyComplete (Closure 2)` — multiple case-(a) hyps + `[IsDomain A]`.
- `StandardCover.lean :: tateAcyclicity_via_standard_cover`.

**The entire `tateAcyclicity_Part2_via_*` family** (case-(b) gluing, but each carries `[IsNoetherianRing C.base.P.A₀]` + `[IsNoetherianRing (locSubring C.base…)]`, `[IsStronglyNoetherian A]` *absent*, plus forbidden `hArch`):
- `WedhornFinalPart2NoExtraHypThreading.lean` — `…_via_sigma_C1_and_integrated_laneB`(+`_allow_empty`), `…_via_single_t_structural_data_and_integrated_laneB`(+`_allow_empty`)
- `WedhornFinalPart2PointwiseClearingThreading.lean` — `…_via_pointwise_clearing_and_integrated_laneB`(+`_allow_empty`)
- `WedhornFinalPart2SigmaPowerThreading.lean` — `…_via_sigma_power_and_integrated_laneB`(+`_allow_empty`)
- `WedhornFinalPart2SigmaSupplierThreading.lean` — `…_via_T073_sigma_factored_supplier…`, `…_via_T073_direct_supplier…` (both +`_allow_empty`)
- `WedhornPart2LaneAInternalizedConsumer.lean` — `…_via_C1SupplierStrong_local_laneA`, `…_via_single_t_structural_data_laneA` (both +`_allow_empty`)
- `WedhornPart2LaneBIntegratedConsumer.lean` — six `…_laneA_laneB_via_separation` / `…_via_prime_extension_closed` variants; the prime-extension-closed ones add a **third** ring-of-def hyp `[IsNoetherianRing P.A₀]` and **inherit `sorryAx`**.
- `TateAcyclicityFinalAssembly.lean` — the full `tateAcyclicity_end_to_end_via_primary_laneA*` and `tateAcyclicity_via_normalizedLaurent*` families (≈25 declarations), plus `separation_via_*`, `tateAcyclicityComplete_via_*`, `hb_per_f_auto_normalizedLaurent`.
- `WedhornLaneBSeparationInterface.lean` — `laneB_supplier_via_prime_extension_closed`(+`_allow_empty`).
- `WedhornTateAcyclicityPart2C1Consumer.lean :: tateAcyclicity_Part2_via_C1SupplierStrong_local` — note this one does **not** add `[IsNoetherianRing P.A₀]`, but pins the ideal of definition to a *principal* `P.I = span{π}` with `IsUnit π` — still an added hypothesis (a Tate ideal of definition need not be principal).

**Cor 8.32 / Lemma 8.33 injectivity & flatness spine** (all "strongly-noetherian-Tate" in Wedhorn):
- `Cor832.lean` — the entire `productRestriction_injective_tate*` / `…_faithfullyFlat_*` / `flat_over_base_tate*` / `hSpa_points_*` / `coeRingHom_preserves_proper*` / `locIdeal_le_jacobson*` block (≈40 declarations) carries `[IsNoetherianRing P.A₀]` + `[IsNoetherianRing A]` (+ often `[IsNoetherianRing (locSubring …)]`). `…_of_isAdicComplete` additionally asserts `[IsAdicComplete (locIdeal) (locSubring)]` on the *uncompleted* localization (false in the Tate setting).
- `WedhornCechAcyclicity.lean` — `cor_8_32_for_2cover`, `injectivity_from_faithfullyFlat_2cover`, `wedhorn_lemma_833`, `wedhorn_lemma_833_separation*`, `…_diagram_chase`, `…_example_638_plus/minus`, `wedhorn_lemma_834*` (base/step/laurent_acyclic/restriction), `every_rational_cover_is_OXAcyclic`, `restrictToPiece_acyclic_at_D`, `laurent_cover_refines_idealgen_cover`, `laurent_cover_covers_each_idealgen_piece`.
- `StructureSheaf.lean` — `tateQuotientProductRestriction_injective(_on_algebraMap)`, `separation_ofStronglyNoetherianTate`, `presheafValue_flat_of_*`, `productRestriction_injective_of_laurentRefinement`, `productRestrictionSub_isInducing_flat`, `productRestrictionSub_injective_flat`, `cor_8_32_clean_sub_with_P`, `prop_8_30_flat_clean`, `tateAcyclicity_gluing_via_descent_with_P` (several also add `[IsDomain A]`).
- `HubnerSeparation.lean` — `laurentCover_separation_presheaf_viaBridges_of_iInf_pow_eq_bot`, `…_of_span_le_jacobson`.
- `GeometricReduction.lean` — `standardCover_gluing_induction_step_via_laurentGluing`, `hV_glue_refined_from_laurent_halves_via_primary`, `lane_A_supplier_via_primary(_canonical)`, `canonical_hcont_eval`.
- `LaurentOverlapConsumer.lean` — `V_cover_gluing_via_primary`, `laurentCover_gluing_presheaf_via_primary`, `laurentBridge_delta_eq_zero_via_primary`, `laurentAndVCover_gluing_unified_via_primary`.

**Prop 8.30 flatness via restriction** ("strongly-noetherian-Tate"):
- `RestrictionFlatness.lean` — the whole `restrictionMap_flat_via_*` / `iteratedPlus/Minus_B_flat_of_canonical` / `…_of_rational_subset_*` / `…_via_normalizedMinus` block (≈12 declarations) carries `[IsNoetherianRing P.A₀]` + `hP_A₀Noeth_B` + `hnoeth_B`; several thread the Prop-8.30 *output* (`hNoeth_B`) back in as an *input*, and add extra `hf_canonical_pb`.

**Example 6.38 bridges, iterated localization, presheaf Tate structure** (Ex 6.38 needs only strongly-noeth-Tate):
- `LaurentRefinementCore.lean` — `presheafValue_trivialPlus_fSubX_equiv`, `laurentPlusBridge`, `laurentMinusBridge`, `laurentOverlapBridge_exists_compatible(_from_bivariate_factorization)`, `laurentBridge_delta_eq_zero_of_compat`, and the full `laurentCover_gluing/isEmbedding_presheaf_via_*` tower.
- `IteratedOverlapEquiv.lean` — all ~22 `iteratedOverlap_*` helpers + `presheafValue_iteratedOverlap_equiv` carry `[IsNoetherianRing P.A₀]`.
- `PresheafTateStructure.lean` — `presheafValue_pairOfDefinition(_concrete)`, `presheafValue_isTateRing`, `presheafValue_isHuberRing`, `restrictionMap_isLocalization`, `presheafValue_isNoetherianRing_of_rationalSubset`, `mk_D₀s_isUnit`, `mk_D₀s_mem_nonZeroDivisors`.
- `TopologyComparison.lean` — `presheafValueToCanonicalQuotient*`, `presheafValueCanonicalQuotientEquiv(_isInducing/_isHomeomorph)`, `presheafValue_tateAlgebra_quotient_iso`, etc. — all carry `hnoeth : IsNoetherianRing (pairSubring (principalPair A))` = noetherian *ring of definition* A₀⟨X⟩ (Wedhorn needs A⟨X⟩ noetherian, supplied by `[IsStronglyNoetherian A]`). **Also a conclusion-shape divergence**: RHS is the 1-variable `A⟨X⟩/(1−sX)`, but Ex 6.38 for `|T|>1` is the `|T|+1`-variable quotient.
- `TateAlgebraTopology.lean` — all `tateAlgebra(₂)_isClosed_ideal` and `…Ideal_isClosed`/`_t2Space`/`_completeSpace` results take `[IsNoetherianRing (…pairOfDefinition).A₀]`; **mis-applies Prop 6.17**, which requires the Tate ring A⟨X⟩ itself noetherian, not A₀⟨X⟩.
- `Cor832.lean :: presheafValue_isAdicComplete`, `…isUnit_canonicalMap_s_via_nullstellensatz`, `…exists_spa_point_supp_ge_in_presheafValue`, the `hSpa_points_*` and `spa_point_nonOpen_*` constructions.
- `RelativeRationalLocData.lean` — all `relativeRationalLocData*` / `relativeLaurentNormalized_equiv` (also ORPHAN "Lemma 2.13", see §3).
- `EmbeddingTopo.lean` — the entire `productRestrictionSub_*_isInducing/isEmbedding` tower (T276–T292, the Lane-C closers) carries `[IsNoetherianRing P.A₀]` + `[IsDomain A]`.
- `IdealLocalization*.lean` — `Ideal.isClosed_in_*_of_isAdicComplete` / `…_of_ringOfDef_faithfullyFlat`, `locSubringToRingOfDef_faithfullyFlat_*`, `presheafValue_ringOfDef_ringEquiv_adicCompletion`.
- `PrimeExtensionClosed.lean`, `TateAcyclicityFinalAssembly.lean :: separation_via_prime_extension_closed`, `nonempty_separation_supplier_via_prime_extension_closed`.

**Lemma 8.31 (Tate-algebra flatness)** — Wedhorn 8.31 needs only "A noetherian complete Tate ring"; the genuine route is Remark 8.29 (Artin–Rees over A), which never touches A₀:
- `TateAlgebra.lean` — `tateAlgebra_flat`, `mem_ideal_map_of_forall_coeff_mem`, `fSubX_saturated`, `oneSubfX_saturated`, `flat_quotient_fSubX_general`, `flat_quotient_oneSubfX_general`, `faithfullyFlat_general` — all add `(P) [IsNoetherianRing P.A₀]`.
- `Wedhorn828.lean` — `lemma_8_31_tateAlgebra_faithfullyFlat`, `lemma_8_31_oneSubfX_flat`, `lemma_8_31_fSubX_flat` (case-(b) file, but inject case-(a) `[IsNoetherianRing P.A₀]`).

**`NoetherianTateModules.lean :: Wedhorn.isClosed_ideal_of_noetherian`** — substitutes `[IsNoetherianRing ↥P.A₀]` for 6.17's `[IsNoetherianRing A]`; the substituted hypothesis is **strictly stronger** (noeth-A₀ ⇒ noeth-A via 6.37(3), but not conversely), and false-for-ℂ_p. The faithful fix is to take `[IsNoetherianRing A]` (available from strongly-noeth-Tate) and drop the pair.

### 2B. The false "strong-noeth ⇒ noeth ring of definition" orphan lemmas (root of theme 2A)

These **assert a statement Wedhorn never makes and which is false for ℂ_p** (the converse of Rem 6.37(3)), and are `sorry`-bodied. They are the engine through which "clean-signature" theorems secretly acquire a noetherian ring of definition:
- `StructureSheaf.lean :: _aux_noeth_A0_generic_of_stronglyNoetherianTate`, `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate`, and their public wrappers `isNoetherianRing_A₀_of_stronglyNoetherianTate`, `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`.
- `WedhornStronglyNoetherian.lean :: isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`, `isNoetherianRing_A₀_of_stronglyNoetherianTate_proof` (docstrings concede Wedhorn never asserts this).

**Consequence:** the "clean-signature" theorems `StructureSheaf.lean :: cor_8_32_clean`, `cor_8_32_clean_sub`, `prop_8_30_flat_clean`, `tateAcyclicity_gluing_via_descent` have FAITHFUL *profiles* but DIVERGENT *proofs* — they supply the case-(a) hypothesis internally via these false orphans (and `prop_8_30_flat_clean` additionally routes through `restrictionMap_isLocalization`, flagged false-in-general). A clean signature whose proof depends on a false lemma is **not** a faithful proof of 8.28(b).

### 2C. `[IsDomain A]` added where Wedhorn has no domain hypothesis

`Spa A` of an affinoid is not a domain in general; Wedhorn 8.34/7.54/8.32 carry no such hypothesis. The project uses it for Krull-intersection / `iInf_pow_eq_bot` injectivity shortcuts:
- `LaurentCoverExact.lean :: epsilonHom_gen_injective`, `algebraMap_mem_span_fSubX_eq_zero`; `LaurentCoverTopology.lean :: epsilonHom_gen_inducing` (silently inherits it) — Wedhorn gets ε-injectivity from Cor 8.32, not from a domain.
- `HubnerSeparation.lean :: laurentCover_separation_presheaf_viaRow3_domain`.
- `WedhornCechAcyclicity.lean :: exists_form_a_refinement`, `exists_ideal_gen_refinement(_covers_each_D)`, `ideal_gen_refinement_covers_each_piece` (Lemma 7.54 needs only "complete affinoid ring"); `every_rational_cover_is_OXAcyclic`.
- `TateAcyclicityResiduals.lean` — the whole W1–W5 tree (`localBasisHyp_of_strongly_noetherian`, `exists_per_D_finite_cover_*`, `strengthened_cover_*`, `outside_rescue_*`, `span_top_*`, `exists_*_laurent_cover/tree*`, `balancedTree_*`, `graftAt_allNodesDisjoint`, etc.) carries `[IsDomain A]` (and the combinatorial graft lemmas carry the entire strongly-noeth-Tate + domain bracket bundle gratuitously — should be plain INFRASTRUCTURE).
- `StandardCover.lean :: refines_by_standard_cover(_per_E)` (also defers content to an explicit `hZavyalov` premise).
- `PresheafIdentification.lean :: tate_locLift_divByS_isPowerBounded_completion*`, `HasLocLiftPowerBounded.tate` — `[IsDomain A]` is a genuine narrowing of strongly-noeth-Tate.

### 2D. The forbidden `hArch : ∀ v, MulArchimedean …` pattern

CLAUDE.md explicitly names this as a prohibited work-deferral addition; it appears in no Wedhorn statement (Cor 7.32's proof uses Lemma 7.31 + the Tate axiom, neither archimedean):
- `Cor732.lean :: exists_dominating_unit`; `WedhornSigmaPowerDecay.lean :: exists_dominating_unit_strict_pair` (the audit's probe confirmed the wrapped lemma needs only `[IsLinearTopology A A]`; also drags in an unneeded `[IsNoetherianRing A]`).
- `SpaCompact.lean :: image_spa_ιSpv_bool_of_tate`, `isClosed_image_spa_ιSpv_bool_of_tate`, `isCompact_spa_of_tate_pseudouniformizer`, `instCompactSpace_spa_of_tate_pseudouniformizer` (Spa-A qc is Thm 7.35(1), routes via Spv(A,I) spectrality, no archimedean assumption).
- `WedhornNormalizedC1Assembly*.lean :: exists_per_D_finset_via_normalized_C1(Strong)_supplier`, `hZavyalov_per_E_via_normalized_C1_supplier_with_h_span`; `WedhornFinalAssemblyBridge.lean :: hZavyalov_per_E_via_normalized_C1_supplier_explicit_stage2`; `WedhornSigmaFactoredInequalityAtCor732Sigma.lean :: sigma_factored_supplier_via_cor732_direct_upper_bound_residual`.
- `ValuationContinuity.lean` — the `*_mulArchimedean` family (`pulledBackValuation_isContinuous`, `exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean`, `exists_mem_rationalOpen_supp_ge_*`, etc.) assumes `[MulArchimedean V.ValueGroup]` up front, where Lemma 7.45 obtains continuity via the retraction (Lemma 7.5(3)+Thm 7.10) with height-1 appearing only *after* passing to a vertical generization (Prop 7.41).

### 2E. Changed conclusions — claiming more than Wedhorn (exact vs. ⊇, and false-in-general)

- **`supp x = p` (exact) claimed where Wedhorn gives only `supp x ⊇ p`**: `ValuationContinuity.lean :: exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean`, `…_via_heightOne_ofPrime`, and the `exists_packaged_enlarged_domination*` reductions. Exact support is Lemma 7.45's *noetherian-ring-of-definition* case (wedhorn.txt:3338); these reach it via parametric height-1 witnesses instead of the noetherian hypothesis Wedhorn discharges by Krull–Akizuki.
- **Added openness, dropped completeness** on 7.51/7.52: `AdicSpectrum.lean :: exists_mem_spa_supp_eq` (adds `IsOpen 𝔪`, drops 7.51's completeness), `isUnit_of_forall_not_vle_zero` (adds "all maximals open", drops 7.52(2)'s completeness), and their `…_of_isOpen_topologicallyNilpotent` variants.
- **Statements false at the stated signature (`sorry`-bodied)**:
  - `Presheaf.lean :: union_translates_of_oneAdd_topNilp_subseteq_units` and `units_eq_union_translates_of_oneAdd_topNilp` — false without completeness (docstring's own ℤ_p counterexample); `maxIdeal_isClosed_of_complete_huber` routes through them.
  - `Presheaf.lean :: IsPowerBounded.map` — docstring-flagged STATEMENT BUG (ℝ_discrete→ℝ_std counterexample), uncited, `sorry`.
  - `PresheafTateStructure.lean :: restrictionMapHom_surj`, `restrictionMapHom_injective`, `restrictionMap_isLocalization` — docstring-flagged false-in-general (`A=ℚ_p⟨X⟩`, `A=k⟨T,U⟩/(TU)`), `@[deprecated]`/`sorry`. `restrictionMapHom_injective_via_iso` pushes the false injectivity onto a caller hypothesis `h_composite_inj`.
  - `BanachOMT.lean :: AddMonoidHom.banach_two_of_three` — drops the A-module/unit-sequence structure of Wedhorn 6.16 down to a bare `AddMonoidHom`; the `(a)∧(c)⇒(b)` direction is then false (2ℤ↪ℤ counterexample) and left `sorry`.
  - `ContinuousValuations.lean :: isContinuous_iff_setOf_ge_isOpen` — quantifies over Γ₀ (monoid-with-zero) instead of 7.8(3)'s value *group*; documented-false, `sorry`.
  - `SpvAITopology.lean` — the seven `isClosed_*_prop` Sierpinski sub-leaves + `isClosed_range_ιSpv` + `ιSpv_isClosedEmbedding` are false in the Sierpinski topology (project's own counterexample); `Spv.isSpectralSpace` and `SpvAI.quasiSober_topology` have faithful headlines but rest on this false route. `lemma_3_29_qcKolmogorov_oc_basis_consequences` over-claims a topological-basis conjunct (false). `SpaCompactNoHArch.lean :: isClosed_range_ιSpv_inter_vleCylinder` (and its dependents) similarly false.
  - `Wedhorn828.lean :: lemma_8_33_laurent_cover_gluing` (placeholder `hC : True` drops 8.33's defining Laurent-cover hypothesis — claims gluing for an *arbitrary* cover), `lemma_8_34_gluing` (drops `T·A=A`).
- **Vacuous placeholders** (conclusion is `∀ _, True` or a reflexivity tautology, bearing no relation to the cited theorem): `FarguesFontaine.lean :: X_FF.isNoetherian / .isRegular / .dim_one / .classicalPoints`; `WedhornStronglyNoetherian.lean :: _sub_lemma_L5_1_1_tateAlgebra_eq_adicCompletion` (proves `∃ e, e = e` for Prop 6.21(2)); `Tilting.lean :: PerfectoidField.tiltingEquiv` and `PerfectoidSpace.lean :: PerfectoidSpace.tilt` (existential trivially witnessed by X itself, not the tilting equivalence).

### 2F. Added typeclasses / parametric carriers on otherwise-correct statements

- `Presheaf.lean :: HasLocLiftPowerBounded` and `CompatiblePlusSubring` — Prop-class carriers that bundle unproved obligations (7.52(2) unit-ness, 7.41 power-boundedness, A⁺⊆A₀ per datum) and are then taken as hypotheses on `restrictionMap` and all downstream functoriality. This is the parametric-reformulation pattern CLAUDE.md warns against (project documents it as the chosen route). `CompatiblePlusSubring` additionally cites the nonexistent "Remark 7.17".
- `SpaPresheafValueEquivalence.lean` — the whole Prop-8.2 equivalence block (`_sub_lemma_C3_*`, `spa_completion_of_spa_localization`, `exists_spa_presheafValue_of_rationalOpen`, `Spa_presheafValue_eq_rationalOpen_via_subcomponents`) adds `[IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]` to **Prop 8.2, which Wedhorn states for an arbitrary affinoid ring with zero extra hypotheses**; several are also self-described circular (delegate to a `sorry`-bodied headline).
- `WedhornCechAcyclicity.lean :: propA3_part2_project_*`, `IsOXAcyclic_of_refining_acyclic_cover`, `wedhorn_lemma_834_propA3_part1_*` — **Prop A.3 is a pure presheaf-of-abelian-groups statement** with no ring/Tate/noetherian/Hausdorff/complete hypotheses; the whole strongly-noeth-Tate instance block is foreign.
- `RationalRefinement.lean :: separation_of_finer_rational`, `gluing_of_finer_rational` — labelled Prop A.3 but state concrete H⁰ separation/gluing reassembly (A.3 is about Čech-acyclicity equivalence); `gluing_of_finer_rational` takes the substantive content as hypotheses and merely re-assembles.
- `Presheaf.lean` — `isUnit_algebraMap_s_of_tate`, `isUnit_canonicalMap_s_of_tate`, `locLift_divByS_isPowerBounded(_completion)_of_tate`, `wedhorn_7_52_2_isUnit_iff_forall_not_vle_zero`, `exists_spa_point_supp_eq_maxIdeal_of_complete`, `isUnit_iff_ne_zero_on_spa_of_complete`, `prop_7_51_maxIdeal_closed_and_spa_point`, `hasLocLiftPowerBounded_of_stronglyNoetherianTate'` — add `[NonarchimedeanRing A]` and/or unused `[IsTateRing/IsNoetherianRing/T2Space]` decoration not in 7.51/7.52 ("complete affinoid ring" only); several docstrings concede the brackets are unused.
- `WedhornC1Assembly*.lean :: exists_per_D_finset_via_C1(Strong)_supplier_and_compactness`, `hZavyalov_per_E_…with_h_span` — `[T2Space A]`/`[NonarchimedeanRing A]` are foreign-to-source **and empirically inert** (audit verified single-file compile with all four stripped; compactness needs only the pseudouniformizer bundle).
- `TateAlgebra.lean :: muMap_surjective` (adds `[FirstCountableTopology A]` etc. not in Rem 8.29); `PerfectoidRing.lean :: toIsStablyUniform`, `toIsSheafy` (add `[PlusSubring]`/`[IsHuberRing]`/`HasLocLiftPowerBounded` beyond Scholze's statement, Scholze PDF absent so unverifiable).
- `AdicMorphisms.lean :: IsAdicMorphism.ringHom_isAdic` (Cor 8.40) — marks `hf` unused and instead *assumes* `hφ_analytic` (= the `f(U^a)⊆V^a` that 8.39(1) is supposed to *derive*), a parametric reformulation pushing the corollary's content to the caller. `isAdicHom_iff_preserves_analytic` (8.39(1)) restricts the unconditional adic-space iff to a complete affinoid ring (the `[IsAdicComplete]` here is faithful-necessary, binding-rule (b)).
- `CharacteristicSubgroup.lean` — `cGammaPos`, `IsMicrobial`, `cGammaIdeal*`, `coarsenIdeal*`, `restrictIdeal*` define **objects that differ from Wedhorn 4.13/7.3** (single-pair-hull instead of the generated convex subgroup; quotient instead of restriction for the 7.5(iii) retraction; cofinality replaced by a ≤1 bound). `SpvAITopology.lean :: cGammaIdeal_*`, `restrictIdeal_*`, `SpvAI.*` add `(P : PairOfDefinition A) + hIeq` (ideal-of-definition) restrictions absent from Lemma 7.4/7.5 (which hold for any √-f.g. ideal).

---

## 3. ORPHANs — citations to non-existent / wrong source statements

**The fabricated "Lemma 2.13"** (Wedhorn 2.13 is a *Remark* on valuation rings of a field; true source = Prop 8.2(1) / Remark 7.55 for iterated-rational collapse):
- `LaurentRefinementCore.lean :: presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`
- `RelativeRationalLocData.lean :: relativeRationalLocData(_hopen_proof)(_laurentNormalized)`, `relativeRationalLocData_divByS_one_mem_locSubring`, `relativeRationalLocData_hopen_proof_of_laurentNormalized`, `relativeLaurentNormalized_equiv`
- (also surfaces as a sub-citation in `IteratedOverlapEquiv.lean :: presheafValue_iteratedOverlap_equiv`, `LaneAReverseRoundTrip.lean :: laneA_τ_preBiv`, `LaurentOverlap.lean :: presheafValue_iteratedOverlap_as_minus_at_plus`, `RestrictionFlatness.lean` and `IteratedRational.lean` — listed DIVERGENT but carry the same orphan number).

**The fabricated "Definition 6.9"** (6.9 is *Proposition* 6.9; strongly-noetherian = Prop&Def 6.36, restricted power series = Rem&Def 5.48):
- `RestrictedPowerSeries.lean :: IsStronglyNoetherian` (also drops the *completion* Â that 6.36(i) requires)
- `TateAlgebra.lean :: TateAlgebra`, `TateAlgebra₂`
- `ExcellentRing.lean :: IsExcellentRing` ("excellent" appears nowhere in Wedhorn; 6.9 is the f-adic flatness Proposition)

**Other wrong/non-existent numbers:**
- `SpaCompact.lean :: isCompact_spa`, `instCompactSpace_spa` and `SpaCompactNoHArch.lean :: isClosed/image_spa_ιSpv_bool_noHArch` cite "Theorem 7.30" (no such theorem; Spa-A qc is **Theorem 7.35(1)**; 7.30 is a Remark).
- `ValuationSpectrumCompact.lean :: ιSpv_isEmbedding`, `compactSpace_of_subbasic_subcover`, `instCompactSpace` cite "Theorem 4.9" (no such theorem; Spv spectral is **Prop 4.7(1)**; 4.9 is a Prop about ring homs).
- `AnalyticPoints.lean :: IsAnalytic`, `SpaIsAnalytic` cite "Definition 8.35" (8.35 is a *Corollary*; the notion is **Def 7.39**).
- `Uniform.lean :: IsUniform`, `IsStablyUniform`, `IsUniform.discrete` cite "Definition 7.36/7.37" (those are Corollary/Example; "uniform" is not a Wedhorn notion — Kedlaya–Liu).
- `StructureSheaf.lean :: isNoetherianRing_A₀/principalPair_A₀_of_stronglyNoetherianTate` and `_aux_*` — cite "6.18 / Def 6.36 corollary" for a claim that is the **converse** of 6.37(3) and **false** (see §2B).
- `WedhornCechAcyclicity.lean :: example_638_plus_side_noeth_pairSubring` cites "6.18" (6.18 is about module topologies, says nothing about pair-subring noetherianness).

---

## 4. UNCITED substantive results — Wedhorn-level statements with no source pointer

- `WedhornCor732ChainIdentityFromLocalizedOutput.lean :: Cor732SigmaPerTauUpperBoundResidual` and `WedhornCor732DirectUpperBoundResidual.lean :: Cor732SigmaDenominatorClearingChainIdentity` — Prop-level σ-residual predicates labelled "8.34(ii)/Cor 7.32" with no statement number/line; per the acceptance test no verbatim Wedhorn passage pins them.
- `WedhornLocalizedMultiPieceLaurentRefinement.lean :: LocalizedAlphaTDBranchCoverLevelAssemblyResidual` — bespoke per-w cover-level upper-bound Prop, "Lemma 8.33 cover-level assembly" with no locatable line; project-internal reroute around a documented-false universal-lower-bound clause.
- `WedhornPerPieceLaurentCoverAssembly.lean :: LaurentCoverPresheafLemma833Assembly` — set-level union→single-target collapse Prop named for 8.33 (which is the 2-element Čech-complex *exactness*); docstring concedes "the multi-piece iteration is the missing infrastructure". The consumers in `WedhornC1CoverAssemblyClosure.lean` (`coverLevelAssemblyResidual_via_lemma833_assembly`, `C1SupplierStrong_local_clause2_via_lemma833_assembly`, `…_full_chain`) re-cite this as "Lemma 8.33" (DIVERGENT).
- `WedhornStandardCoverRefinement.lean :: WedhornStep2RefinementCarryingFactor`, `WedhornStep2FactorCarryingProvider`, `wedhorn_834_step2_factor_carrying_constructor_target` — h_struct data carriers; docstring itself flags the key `h_factor` identity as "the genuinely missing upstream content … NOT standard denominator clearing", with no Wedhorn passage.
- `GeometricReduction.lean :: noCommonZero_plusHalf_of_refines_span_top`, `noCommonZero_minusHalf_…` and `StandardCover.lean :: spanTop_iff_noCommonZero_spa` — cite "Prop 7.14" (7.14 is the *Definition* of A°); the real source is the complete-affinoid Nullstellensatz (7.52 class).
- **Mis-citations of "Lemma 7.45" for cover-refinement content** (7.45 is the non-open-prime analytic-point lemma, NOT a cover-refinement statement; the cover-refinement driver is Cor 7.32 / Lemma 8.34(ii)): `WedhornVKMaxElementComparisonDischarge.lean :: h_max_element_residual_via_base_rational_subset_comap`, `C1SupplierStrong_local_via_base_rational_subset_comap`; `WedhornBaseRationalComapResidualDischarge.lean :: WedhornCoverPieceCovPlusPieceLiftPerTBound_via_base_refinement`, `C1SupplierStrong_local_via_Wedhorn745_refinement`; `Wedhorn745PointwiseBaseRefinementDischarge.lean :: C1SupplierStrong_local_via_Wedhorn745_pointwise_refinement`; `WedhornPerWCoverPieceUpperBound.lean :: WedhornCoverPieceLocRationalBound` (these are listed DIVERGENT for the mislabel but several carry no `[IsNoetherianRing]`, so the defect is purely citation).

---

## 5. Recommended actions

**Priority 0 — Kill the false case-(a)-from-case-(b) engine (unblocks the whole spine).**
1. **Delete** `_aux_noeth_A0_generic_of_stronglyNoetherianTate`, `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate`, and their public wrappers in `StructureSheaf.lean` / `WedhornStronglyNoetherian.lean`. They assert a **false** statement (converse of Rem 6.37(3); ℂ_p counterexample) and exist only to smuggle a noetherian ring of definition into "clean" theorems.
2. Re-prove the strongly-noetherian-Tate consequences via the **faithful route**: `[IsStronglyNoetherian A] ⇒ IsNoetherianRing A⟨X⟩` (Example 6.38 / Prop 6.17 "C is noetherian"), i.e. use noetherianness of the *Tate algebra* A⟨X⟩, never of the *ring of definition* A₀⟨X⟩. This is the single fix that corrects `TateAlgebraTopology.lean`, `TopologyComparison.lean`, and the `TateAlgebra.lean` 8.31 block.

**Priority 1 — Strip `[IsNoetherianRing P.A₀]` / `[IsNoetherianRing (locSubring …)]` from every case-(b) signature.** Replace with `[IsStronglyNoetherian A]` where ring-noetherianness of a Tate localization is genuinely needed (derive it from Ex 6.38 propagation). This is mechanical across `Cor832.lean`, `RestrictionFlatness.lean`, `WedhornCechAcyclicity.lean`, `LaurentRefinementCore/Acyclic.lean`, `IteratedOverlapEquiv.lean`, `TateAcyclicityFinalAssembly.lean`, the `WedhornFinalPart2*` / `WedhornPart2*` consumers, `HubnerSeparation.lean`, `GeometricReduction.lean`, `EmbeddingTopo.lean`, `PresheafTateStructure.lean`, `IdealLocalization*.lean`, `Wedhorn828.lean`. After stripping, the headline `tateAcyclicity` / `isSheafy_ofStronglyNoetherianTate_*` must carry **exactly** `[IsStronglyNoetherian A]` (+ the genuine Tate-completion structure), matching wedhorn.txt:4054.

**Priority 2 — Remove forbidden / unjustified added hypotheses.**
- Remove every `hArch : ∀ v, MulArchimedean …` (Cor 7.32 / 7.35 / 8.34 don't use it; CLAUDE.md forbids it). Re-state `Cor732.exists_dominating_unit`, the `SpaCompact*_of_tate` lemmas, and the `WedhornNormalizedC1*` suppliers from the Tate axiom alone.
- Remove `[IsDomain A]` from `LaurentCoverExact.lean`, `LaurentCoverTopology.lean`, `HubnerSeparation.lean :: …viaRow3_domain`, `WedhornCechAcyclicity.lean` (7.54 lemmas + `every_rational_cover_is_OXAcyclic`), `TateAcyclicityResiduals.lean`, `StandardCover.lean`, `PresheafIdentification.lean`. Obtain ε-injectivity from Cor 8.32 (Wedhorn's route), not Krull-in-domains.
- Strip the foreign/inert `[T2Space A]`/`[NonarchimedeanRing A]`/unused `[IsNoetherianRing A]` decorations from `SpaPresheafValueEquivalence.lean` (Prop 8.2 = arbitrary affinoid ring), `WedhornC1Assembly*.lean`, the `Presheaf.lean :: *_of_tate` wrappers, and the `WedhornCechAcyclicity.lean` Prop A.3 lemmas (A.3 = presheaf of abelian groups).

**Priority 3 — Fix changed conclusions and false-as-stated statements.**
- `AdicSpectrum.lean :: exists_mem_spa_supp_eq`, `isUnit_of_forall_not_vle_zero`: re-state with 7.51/7.52's "complete affinoid ring" hypothesis (drop the added openness; either prove the completeness case or leave a `sorry` at the faithful signature).
- `ValuationContinuity.lean`: separate the **general** Lemma 7.45 (`supp x ⊇ p`, no archimedean assumption, via the retraction) from the **noetherian** case (`supp x = p`); do not present exact support under a `MulArchimedean` witness as "Lemma 7.45".
- `NoetherianTateModules.lean :: isClosed_ideal_of_noetherian`: replace `[IsNoetherianRing ↥P.A₀]` with `[IsNoetherianRing A]` (matches 6.17). `WedhornBanachTheorem.lean :: wedhorn_6_17`: drop the added `[IsNoetherianRing A]`.
- Repair or quarantine the genuinely-false `sorry` statements: `Presheaf.lean :: IsPowerBounded.map`, `union_translates_of_oneAdd_topNilp_subseteq_units`; `PresheafTateStructure.lean :: restrictionMapHom_surj/_injective`, `restrictionMap_isLocalization`; `BanachOMT.lean :: banach_two_of_three` (restore the A-module/unit-sequence structure of 6.16); `ContinuousValuations.lean :: isContinuous_iff_setOf_ge_isOpen` (quantify over the value *group*); the `SpvAITopology.lean` Sierpinski-closedness chain (switch to the discrete-Bool/Huber route the headline actually needs); `Wedhorn828.lean :: lemma_8_33_laurent_cover_gluing` (`hC:True` → real Laurent-cover hypothesis), `lemma_8_34_gluing` (restore `T·A=A`).
- Replace the vacuous placeholders (`FarguesFontaine.lean` four lemmas, `Tilting.lean :: tiltingEquiv`, `PerfectoidSpace.lean :: tilt`, `WedhornStronglyNoetherian.lean :: _sub_lemma_L5_1_1`) with either honest `sorry`-stubs stating the real conclusion or remove the misleading citations.

**Priority 4 — Citation fixes (low risk, high signal).** Global search-and-replace the wrong numbers:
- "Lemma 2.13" → **Proposition 8.2(1)** (or Remark 7.55) wherever it labels iterated-rational/overlap transitivity.
- "Definition 6.9" → **Prop&Def 6.36** (strongly noetherian) / **Remark&Definition 5.48** (restricted power series A⟨X⟩); for `ExcellentRing` drop the Wedhorn cross-ref entirely (EGA IV §7.8 only).
- "Theorem 7.30" → **Theorem 7.35(1/2)**; "Theorem 4.9" → **Proposition 4.7(1)**; "Definition 8.35" → **Definition 7.39**; "Definition 7.36/7.37" (uniform/stably-uniform) → Kedlaya–Liu, not Wedhorn; "Remark 7.17" → **Remark 7.15(1) + Cor 6.4(4)**; "Prop 6.4(4)/6.4(3)" → correct sub-items; "Prop 8.15" → **Example 6.38** wherever it labels restriction-as-localization or presheafValue Tate structure (8.15 is a *stalk* statement); "Lemma 7.45" → **Corollary 7.32 / Lemma 8.34(ii)** wherever it labels cover-refinement.
- Attach a real statement number + wedhorn.txt line to every UNCITED Prop in §4, or relabel them `-- INFRASTRUCTURE (not in Wedhorn)` per the project's own rule if they have no source.

**Note on the parametric carriers** (`HasLocLiftPowerBounded`, `CompatiblePlusSubring`): these are the project's documented chosen route but are exactly the "push the dependency to callers" pattern CLAUDE.md flags. They are not a citation bug to fix mechanically; treat them as a design decision to revisit once Priority 0–1 land, since they currently obscure whether the unit-ness (7.52(2)) and power-boundedness (7.41) obligations are actually discharged.
