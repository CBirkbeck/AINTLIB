All data gathered. Here is the complete scouting inventory.

---

# FJP scouting report — dev/adic-spaces, 2026-07-21

Base directory: `/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces/FJP/` (cited below as `FJP/`). Other files cited relative to `/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces/`.

## 0. Global sorry / axiom / set_option audit

`grep '\bsorry\b'` over all 12 FJP files (11 + `Milnor/StrictMilnorSquare.lean`): **zero hits in every file**. No `axiom`, no `unsafe` anywhere in FJP. Axiom probe (`lake env lean`, scratchpad, exit 0):

- `FiniteJet.finiteJet_isSheafy`, `finiteJet_not_stablyUniform`, `finiteJet_isSheafyTateRing`, `GraphKoszul.ballAdicEquiv`, `GraphKoszul.exists_d2_lift`, `GraphKoszul.syzygy_graph_restricted` — all `[propext, Classical.choice, Quot.sound]` (clean).
- `AdicCompletion.isNoetherianRing` — `[propext, sorryAx, Classical.choice, Quot.sound]` (**sorryAx**; see item 5). The FJP cone does not touch it.

`set_option` inventory (none suspicious, no `maxHeartbeats` above 6.4M):
- `FiniteJetUniformDomain.lean`: `maxHeartbeats 1000000` at 209, 252.
- `FiniteJetChart.lean`: `maxHeartbeats 800000` at 824, 1365, 1425.
- `FiniteJetGraphKoszul.lean`: `backward.isDefEq.respectTransparency false` at 1430, 1787 (v4.33 bump-repair pattern, documented in comments at 1427-1429, 1784-1786).
- `FiniteJetStrictLocalization.lean`: `backward.isDefEq.respectTransparency false` at 85, 115, 945, 1035, 1044.
- `FiniteJetFunctoriality.lean`: file-wide `backward.isDefEq.respectTransparency false` at 43 (flipped back to `true` at 2147 for one decl); `maxHeartbeats 800000` at 402, 839, 1000, 1177; `synthInstance.maxHeartbeats 800000` at 1031, 1050, 1068, 1210, 1229, 1247; `synthInstance.maxHeartbeats 400000` at 1897, 1949.
- `FiniteJetSheafTransfer.lean`: `maxHeartbeats 6400000` at 344 (the `gluing_JetA` monster), `1600000` at 631.
- All other files: none.

Note on one stale artifact: `.lake/build/lib/lean/Adic spaces/FJP/Milnor/StrictMilnorSquare.olean` currently has an **incompatible header** (probe import failed; a sibling build is churning the tree). Source is 142 lines, trivially sorry-free; tickets.md:1022 records "Interface skeleton compiled".

## 1. Declaration inventory (per file, line-numbered)

### FJP/RestrictedLaurent.lean (1452 lines) — sorry-free
Namespace `FiniteJet.RestrictedLaurent`; generic base `{R} [NormedCommRing R] [IsUltrametricDist R]` (+ `[CompleteSpace R] [NormOneClass R]` where marked).
- 42 `structure RestrictedLaurent (R)` — `coeff : ℤ → R` with `Tendsto (‖coeff ·‖) cofinite (𝓝 0)`.
- 54 `ext`; 61 `finite_setOf_le_norm_coeff` (superlevel sets finite); 69 `exists_norm_coeff_le`; 83 `tendsto_cofinite_zero_of_finite`.
- Ring structure: 103/107/114/121 `Zero/One/Add/Neg` instances; 139 `single (a : ℤ) (c : R)`; 155 `tendsto_conv_term`; 167 `summable_mul_coeff`; 173 `Mul` instance (tsum convolution); 217 `summable_conv_triple`; 255 `coeff_mul`; 260 `CommRing` instance; 338 `single_mul_single`; 353 `C : R →+* RestrictedLaurent R`; 360 `Algebra R _`; 364 `W`; 368 `Wu : (RestrictedLaurent R)ˣ` (the norm-one unit W).
- Norm: 384 `gaussNorm := ⨆ a, ‖f.coeff a‖`; 387 `norm_coeff_le_gaussNorm`; 391 `gaussNorm_nonneg`; 396 `exists_gaussNorm_eq` (norm attained, any base); 415 `isRingNorm`; 437 `NormedCommRing` instance; 442 `norm_def`; 467 `IsUltrametricDist` instance; 472 `coeff_Wu_mul`; 479 `norm_W_mul`; 491 `CompleteSpace` instance; 561 `continuous_coeff`.
- Field section (`{K} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]`): 584 `norm_tsum_lt_of_forall_lt`; **613 `norm_mul_eq`** (see item 8); 702 `coeff_C_mul`; 709 `norm_C_mul`; 714 `norm_restrictedC_mul`; 723 `mul_ne_zero_of_ne_zero`.
- 739/741 `StrongPos` instances for `fun _ : Unit => 1` and `fun _ : Fin n => 1` (needed by every `P E m` downstream).
- Nonneg subring & bridges: 749 `nonnegSubring`; 767 `isClosed_nonnegSubring`; 783 `ofPowerSeries`; 804/808 `ofPowerSeries_mem/_mul`; 867 `mk_coeff_mem_isSubring`; 880 `ofCoeffs`; 891 `nonnegEquiv` (≃+* `PowerSeries.Restricted R 1`); 925 `nonnegEquiv_norm`; 945 `ofRestricted`; 949/953 `ofRestricted_norm/_injective`; 973 `nonarchOfUltra` instance; 977 `NormOneClass` instance; 981/987/998/1009 `negateAux(_mul)/negate/norm_negate`; 1017 `norm_pow_le_one`; 1030/1043/1052/1095 `tendsto_evalLE_term/summable_evalLE/evalLE/norm_evalLE_le`; 1110/1158 `restrictedCongr(_norm)`; 1172 `foo_norm_map`; 1178/1185 `innerToSeries(_norm)` (`MvPowerSeries.Restricted R (Fin 1) ≃ PowerSeries.Restricted R 1`); 1192/1197 `negOfSeries/norm_negOfSeries`; 1203 `Wu_pow`; 1212/1218 `evalHom/evalHom_norm_le` (the presentation `K⟨W,V⟩ ↠ L`, `W ↦ Wu, V ↦ Wu⁻¹`); 1228 `truncNonpos`; 1239 `innerToSeries_symm_norm`; 1244/1249/1263/1270/1274 small compat lemmas; 1280 `coeffHom (m : ℤ)`; 1286/1299/1307/1330/1339 truncation-section lemmas; 1443 `evalHom_surjective`.

### FJP/FiniteJetRings.lean (920 lines) — sorry-free
`namespace FiniteJet`, `variable (F) [Field F]`, `local notation "K" => LaurentSeries F` (line 47).
- Rings: 49 `L := RestrictedLaurent K`; 53 `norm_K_discrete : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = 2 ^ n`; 71 `JetC := PowerSeries.Restricted (L F) 1`; 75 `JetB := DualNumber (PowerSeries.Restricted K 1)`; 79 `JetD := DualNumber (L F)`.
- Coefficients & maps: 84 `qCoeff (n) : JetC F → L F`; 86-129 `qCoeff_zero_mul/_one_mul/_add/_neg/_one/_zero/continuous_qCoeff`; 134 `rhoC : JetC →+* JetD` (2-jet truncation); 170 `rhoB : JetB →+* JetD`; 176 `sectionD` (norm-one linear section of rhoC); 189-269 `qCoeff_sectionD/sectionD_add/norm_sectionD/norm_rhoC_le/norm_rhoB/rhoB_injective/rhoC_surjective`.
- The pinching algebra: 277 `jetSupport : Subring (JetC F)` (support condition (1.8)); 302 `JetA := ↥(jetSupport F)`; 306 `isClosed_jetSupport`; 317 `CompleteSpace (JetA F)`; 320 `iotaC`; 326 `jB : JetA →+* JetB`; 383-411 norm lemmas + 411 `square_commutes`; 420/430 membership lemmas; **456 `milnorRow_exact`** (strict row existence); **478 `max_norm_eq : max ‖jB a‖ ‖iotaC a‖ = ‖a‖`** (ρ = 1); **484 `difference_strict_surjective`** (κ = 1); 491-532 `constHomC/norm_constHomC/qCoeff_constHomC/constC/norm_constC/constC_mem_jetSupport/constA/norm_constA`.
- **Uniformizer block** (see item 2): 535 `tA := constA F (LaurentSeriesExample.t F)`; 537/542 `norm_t_lt_one/norm_t_pos`; 545/549/553 `norm_tA_lt_one/norm_tA_pos/isUnit_tA`; 718/721 `norm_tA/norm_tA_mul`; 728-749 `tB/norm_tB/isUnit_tB/norm_tB_mul`; 752-776 `tD/...`; 779-789 `tC/...`.
- Generic unit-ball stack (`variable (E) [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]`, section starting 565): **572 `unitBall : Subring E`** (`{x | ‖x‖ ≤ 1}`); 584 `mem_unitBall_iff` (`Iff.rfl`); 586 `isOpen_unitBall`; 600 `norm_pow_mul_of_scale`; 609 `mem_span_unitBall_pow_iff`; 641 `unitBallPod (t htu ht1 ht0 hscale)` (pair of definition from a scaling pseudouniformizer); 674/679 `isHuberRing_of_scale/isTateRing_of_scale`; 837 `isBounded_unitBall`; 853 `unitBall_subset_powerBounded`; 868 `isRingOfIntegralElements_powerBounded`.
- Instance stack 697-918: `constHomPS`, `norm_constC_mul`, `NormOneClass (JetA F)`, `IsHuberRing`/`IsTateRing`/`PlusSubring`/`IsRingOfIntegralElements`/`IsUniformAddGroup`/right-uniformity `CompleteSpace` for all four rings.

### FJP/FiniteJetUniformDomain.lean (646 lines) — sorry-free
- 33 `norm_L_mul` (= `norm_mul_eq` at `norm_K_discrete`); 36 `norm_L_eq_zero`; 44/52/58 `finite_setOf_le_norm_psCoeff/norm_psCoeff_le/exists_norm_psCoeff_eq` (generic R); 84 `norm_restricted_mul` (generic: multiplicative base ⇒ multiplicative Gauss norm on `PowerSeries.Restricted R 1`); 150 `norm_JetC_mul`; 154 `norm_KW_mul`; 157-194 `Nontrivial/NoZeroDivisors/IsDomain` for JetC and JetA; 198/204 `norm_JetA_mul/_pow`; 214 `isPowerBounded_JetA_iff`; **255 `isUniform_JetA`**; 275/311 generic dual-number power-bound lemmas; 372/380 `isPowerBounded_JetB_iff/_JetD_iff`; **388 `not_isUniform_JetB`** (uses `t^(m+1)`, lines 403-426); 437-466 `Algebra (K⟨W⟩) (L F)` + coefficient lemmas; **471 `winv_not_integral`** (W⁻¹ not integral over K⟨W⟩, coefficient read-off at `W^{-n}`); **506 `not_moduleFinite_L`**; 512/521 `qCoeff_two_mul/qCoeff_sum`; 530 `jB_eq_zero_iff` (`ker jB = Q²𝒞`); 560/573/578 `q2elt/qCoeff_q2elt/q2elt_mem_jetSupport`; 590 `moduleFinite_of_ker_jB_fg`; 639 `ker_jB_not_fg`; **643 `not_isNoetherianRing_JetA`**.

### FJP/FiniteJetNoetherianVertices.lean (643 lines) — sorry-free
- Generic `mapRestrictedGauss` section 42-153: 47 `finsupp_prod_one`; 53 `mapRestrictedGauss (m φ hφ)`; 72 `norm_mapRestrictedGauss_le`; 88 `mapRestrictedGauss_exists_norm_le`; 124 `mapRestrictedGauss_surjective`; 131 `NormOneClass (MvPowerSeries.Restricted R (fun _ : Fin k => 1))` instance.
- 160 `isNoetherianRing_restricted_L` (via flattenings + `evalHom` surjection + `IsStronglyNoetherian K`); 193/196 `IsStronglyNoetherian (L F)` / `IsNoetherianRing (L F)`; 200 `isNoetherianRing_restricted_univariate` (generic strongly-noetherian base); 215/218 same for `JetC`; 225/240/255 `epsRestricted/fstRestricted/sndRestricted`; 275 `isNoetherianRing_restricted_dualNumber`; 312-323 `IsStronglyNoetherian/IsNoetherianRing` for `JetB`, `JetD`.
- Ball transfer (generic): 337 `isNoetherianRing_unitBall_of_section`; 349 `isNoetherianRing_unitBall_of_isometry`.
- **362 `isNoetherianRing_unitBall_gaussK (k)`** — the Laurent transposition proof (item 2); 398 `isNoetherianRing_unitBall_L`; 403 `isNoetherianRing_unitBall_KW`; 414 `isNoetherianRing_unitBall_dualNumber` (generic); 449/455/491 `..._JetB/_JetC/_JetD`; 497 `isNoetherianRing_unitBall_restricted_L (m)`; 532 `isNoetherianRing_unitBall_restricted_univariate` (generic); 549 `isNoetherianRing_unitBall_restricted_dualNumber` (generic); **634/637/640 `isSheafy_JetB/_JetC/_JetD`** (via `isSheafy_of_stronglyNoetherian_828b`).

### FJP/FiniteJetGraphKoszul.lean (1991 lines) — sorry-free, **zero Jet/Laurent mentions** — see item 4.

### FJP/FiniteJetStrictLocalization.lean (1059 lines) — sorry-free
`namespace FiniteJet.StrictLoc`, `variable (F) (m : ℕ) (g : JetA F) (f : Fin m → JetA F)` (datum-parametric; the four concrete Jet rings).
- 42-45 `PA/PB/PC/PD (m) := GraphKoszul.P (Jet• F) m`; 50-63 `extJB/extIotaC/extRhoB/extRhoC` (coefficientwise `mapRestricted`); 72 `ext_square_commutes`; 87 `extRhoC_strict_surjective`; 119 `ext_milnorRow_exact`; 165 `ext_max_norm_eq`; 178 `ext_pair_injective` — Lemma 4.1 at constants 1.
- Generators/ideals: 190-202 `rA/rB/rC/rD` (`rA i = polyToP (C g * X i − C (f i))`), `IA/IB/IC/ID := Ideal.span (range r•)`; 207-271 `span_pushed_B/C/D`, `mapRestricted_polyToP`, `rB_eq/rC_eq/rD_eq/extRhoB_rB`; 276-302 `isNoetherianRing_PB/PC/PD` + `..._unitBall_PB/PC/PD`.
- Lemma 4.3: **314 `ideal_row_surjective`** — `∃ Cs, 1 ≤ Cs ∧ ∀ y ∈ ID, ∃ xc ∈ IC, extRhoC xc = y ∧ ‖xc‖ ≤ Cs*‖y‖`; **377 `ideal_pullback_controlled`** — `∃ Cs, … ∃ xa ∈ IA, extJB xa = xb ∧ extIotaC xa = xc ∧ ‖xa‖ ≤ Cs * max ‖xb‖ ‖xc‖`; **611 `isClosed_IA`**.
- Prop 4.5: 681-684 `locA/locB/locC/locD := P• ⧸ I•`; 687-713 mem-lemmas; 723-741 `locJB/locIotaC/locRhoB/locRhoC`; 747-763 `_mk` + `loc_square_commutes`; 770 `loc_pair_injective`; **798 `loc_row_exact`** (`∃!` glue); 828/847 `locJB_lipschitz/locIotaC_lipschitz`; 868 `loc_norm_le`; **948 `loc_pair_isEmbedding`**; 975 `locRhoC_surjective`; 983/997 `extRhoC_isOpenMap/locRhoC_isOpenMap`; 1037 `locA_t2`; 1047 `locA_completeSpace`.

### FJP/FiniteJetFunctoriality.lean (2391 lines) — sorry-free
Pods 60-71 `podA/podB/podC/podD`; 83 `span_image_eq_top` (generic); pushed data 93-130 `pushDatumB/C/D(+_isRational)`; 150-158 `continuous_jB/iotaC/rhoC`; covariant maps 165-195 `presheafValueMapC/B/D` (+ continuity, canonicalMap intertwining); 207/218 `DatumEnum`/`datumEnum` (finite-enumeration of a datum); 230 generic ultrametric-quotient instance; 247 `DatumEnum.span_eq_top`; **the graph bridge for 𝓐** 255-737: `bridgeConst/bridgeBase/bridgeX/…/bridgeLocHom/bridgeFwd/bridgeToRestricted/bridgeGen/bridgeEval/bridgeRev` + continuity both ways + 636 `polyToP_denseRange` + inverses 668/702; the B/C/D copies 740-1660 (`…C` 740-899, `…B` 901-1457, `…D` 1077-1253, `bridgeEvalB/C`, `bridgeRevB/C`, `bridgeFwdB/C_injective`); 1662-1697 `continuous_rhoB`, `mapBD/mapCD` (+continuity, 1697 commuting square); 1730-1758 `norm_locRhoB_le/norm_locRhoC_le` + continuity; **1764/1820 `locRhoB_bridgeFwdB` / `locRhoC_bridgeFwdC`** (naturality of ρ against bridges); **1880 `graphBridgeA : presheafValue D ≃+* locA e.m D.s e.f`** (+ 1889/1893 continuity both ways); **1901/1956 `graphBridge_natural_B/_C`**; 2007-2011 `HasLocLiftPowerBounded` for JetB/C/D; **2020 `hasLocLiftPowerBounded_JetA`**; restriction compat 2032/2068 `presheafValueMapC_restriction/B_restriction`; 2109-2200 spectrum lemmas `plus_le_comap_of_norm_le`, `mem_rationalOpen_pushDatum•_iff`; coverings 2208-2282 `pushCoveringC/B/D (+_isRational)`; 2297/2308 generic span lemmas; 2315-2385 `interDatum(_span_eq_top)/rationalOpen_interDatum/interDatum_isRational`.

### FJP/FiniteJetSheafTransfer.lean (700 lines) — sorry-free
50 `productRestrictionSub_injective_JetA` (separation); 147/172 `pushDatumB_interOpen/pushDatumC_interOpen`; 212/258 `pushedCompatB/pushedCompatC`; 304 `pairMapBC_injective`; **347 `gluing_JetA`** (the 6.4M-heartbeat heart); 635 `productRestrictionSub_isEmbedding_JetA`; **696 `isSheafy_JetA : ValuationSpectrum.IsSheafy (JetA F)`** (fields `embedding` + `gluing`).

### FJP/FiniteJetChart.lean (1572 lines) — sorry-free
40 `Wa : JetA F` (the element W); 58 `chartDatum : RationalLocData (JetA F)` — `T = {Wa F, tA F}`, `s = tA F`; 69 `chartDatum_isRational`; 82 `rescaleRestricted (a) (ha : ‖a‖ ≤ 1)` (generic `X ↦ aX`); 108 `twistB`; 112 `thetaChart := twistB ∘ jB`; 116-267 rescale/const computations (`jB_tA` 127, `thetaChart_tA` 150, `jB_Wa_snd` 205, `thetaChart_Wa` 241, `Qa` 267); 282 `unitFinOne`; 290 `kwToTate`; 335 `Wa_val_eq`; 354/369/383 `yQ/Wa_pow_mul_yQ/norm_yQ_le` ((3.3): `Q² = ϖⁿXⁿ·(W⁻ⁿQ²)`); 407 `canonicalMap_Qa_sq` (Q² dies in the localization); 534-582 `yGen/Wa_pow_mul_yGen/norm_yGen_le/canonicalMap_eq_zero_of_qSq`; 703 `Qa_val_eq`; 720 `constNN`; 730 `jet_decomposition`; 764-849 `isUnit_thetaChart_s/chartLocHom(+lemmas)/norm_jB_Wa/chartLocHom_continuous`; 852-905 `chartFwd(+coe,continuous)/gChart(+bounded)/chartConst(+continuous)/chartEval`; 908-1178 the density argument (`coeff_kwToTate`, `chartEval_const`, `chartEval_jBWa_fst`, `chartEval_continuous` 966, `polyKW(+denseRange 1023)`, `constKW(+lemmas)`, `rho_Wa_split` 1095, `rescale_jBWa_fst` 1114, `polyKW_X/C`, `evalRescale_eq` 1145); 1180 `chartRev : JetB →+* presheafValue (chartDatum F)`; 1210-1336 chartRev computations + continuity; 1359/1368 `chartFwd_canonicalMap/chartRev_chartFwd`; 1395-1469 `jB_constKW/theta_constKW/chartFwd_chartEval/chartFwd_chartRev`; **1482 `chartEquiv : presheafValue (chartDatum F) ≃+* JetB F`** (+ 1487/1490 continuity); 1496 `chartEquiv_canonicalMap_W`; 1509/1537 generic transport `isPowerBounded_map_of_ringEquiv/isUniform_of_ringEquiv`; **1560 `not_isUniform_chart`**; **1567 `not_isStablyUniform_JetA`**.

### FJP/FiniteJetMain.lean (46 lines) / FJP/FiniteJetSheafyEndpoints.lean (212 lines) — see item 3 (quoted verbatim).

### FJP/Milnor/StrictMilnorSquare.lean (142 lines) — see item 6.

## 2. Laurent-specificity map — claims VERIFIED (with one strengthening)

The only Laurent-specific tokens are `LaurentSeriesExample.t F` (the uniformizer of `K = LaurentSeries F`, defined in `ExampleLaurentSeries.lean`, namespace at line 46; `t_ne_zero` :63, `valuation_t` :60) and the Psi transposition family (`ExampleLaurentSeries.lean`: `Psi` :286, `psi_coeff_v_le` :295, `exists_psi_eq` :327, `psiR` :434).

- **RestrictedLaurent.lean — claim "mostly generic": VERIFIED, and stronger — it is *fully* generic.** 0 occurrences of `LaurentSeriesExample`; the single `LaurentSeries` mention is docstring line 26. Everything is over abstract `R`/`K` with `[NormedCommRing/NormedField] [IsUltrametricDist] [CompleteSpace] [NormOneClass]`. The discreteness hypothesis of `norm_mul_eq` is bound as `_hd` and never used (item 8).
- **FiniteJetRings.lean — claim "mainly hard-codes the uniformizer": VERIFIED.** `K := LaurentSeries F` is a local notation (line 47). All 23 `LaurentSeriesExample` occurrences are (a) `norm_K_discrete` (53-69) — statement is the abstract "norm values are `2^ℤ`", proof uses K's `Valued`/`ValueGroup₀` normalization; and (b) the pseudouniformizer block: `tA` 535, `norm_t_lt_one` 537-541 (uses `LaurentSeriesExample.valuation_t`), `norm_t_pos` 542, `isUnit_tA` 553-555 (`t_ne_zero`), `norm_tA` 718, `norm_tA_mul` 721-722, `tB` 728 (+730, 734-736, 739, 744, 749), `tD` 752-753 (+755, 762, 766, 772, 776), `tC` 779 (+781, 784). Nothing else in the file mentions `t`; the square itself (lines 49-532) and the generic unitBall/pod stack (565-690) only need "K complete nonarch field" + eventually "∃ pseudouniformizer".
- **FiniteJetUniformDomain.lean:** 8 occurrences, all inside `not_isUniform_JetB` (403-426: `w := t^(m+1)` and `‖w⁻¹‖` computations). Needs only `0 < ‖t‖ < 1`, not discreteness. `norm_L_mul` (33-34) feeds `norm_K_discrete F` into the unused hypothesis of `norm_mul_eq`.
- **FiniteJetNoetherianVertices.lean — claim "genuinely Laurent-specific coefficient-transposition proof": VERIFIED.** The 5 `LaurentSeriesExample` occurrences (368, 371, 374, 379, 393) and the 1 `Psi` occurrence (374) all sit inside **`isNoetherianRing_unitBall_gaussK` (362-394)**: `unitBall (K⟨T₁,…,Tₖ⟩)` is exhibited as the surjective image of the noetherian `PowerSeries (MvPolynomial (Fin k) F)` under `psiR` (the transposition `F[X⃗]⟦t⟧ → 𝒪_K⟨T⃗⟩`, integrality via `psi_coeff_v_le`, surjectivity via `exists_psi_eq`). This genuinely uses `K = F((t))` (identification of the coefficient lattice with F-polynomials). Additionally `isNoetherianRing_restricted_L` (160-190) consumes `IsStronglyNoetherian K` (the ExampleLaurentSeries instance) — an abstract-K replacement needs that as a hypothesis. The rest of the file (mapRestrictedGauss 42-153, ball transfer 330-357, dual-number layers 220-323/408-447, univariate/dual arity-m chains 200-211, 532, 549) is generic.
- **FiniteJetChart.lean:** 32 occurrences (109, 132-158, 197-198, 243-257, 1115-1121, 1146-1169, 1248-1296, 1417-1422) — the chart *is* the `(W; ϖ)` chart: `chartDatum` has `s = tA F` (58-67), `twistB` rescales by `t` (108-109), and the whole density/inversion argument threads `rescaleRestricted (LaurentSeriesExample.t F)`. VERIFIED: this file is uniformizer-centric by design. Note `rescaleRestricted` itself (82) is generic in `(a : R)` with `‖a‖ ≤ 1`.
- **FiniteJetGraphKoszul.lean: ZERO** occurrences of `LaurentSeries`/`LaurentSeriesExample`/`Psi`/Jet rings. Fully generic over `E` + explicit bundle `(t : E, htu, ht1 : ‖t‖ < 1, ht0 : 0 < ‖t‖, hscale : ∀ x, ‖t*x‖ = ‖t‖*‖x‖)`. (tickets.md:1042-1043 records the same: "FiniteJetGraphKoszul, already generic — 0 Jet-mentions".)
- **FiniteJetStrictLocalization.lean:** `LaurentSeries` only at 294-295, inside `isNoetherianRing_unitBall_PB` (instantiating the vertex-ball chain). File is Jet-ring-specific (the four concrete carriers) but uniformizer-free and datum-parametric.
- **FiniteJetFunctoriality.lean:** `LaurentSeries` only as the `K` notation (line 51); no `t` usage. **FiniteJetSheafTransfer / FiniteJetSheafyEndpoints / Milnor:** zero. **FiniteJetMain:** docstring line 18 only.

## 3. The frozen endpoints — verbatim

Correction to the prompt: the five Theorem-1.3 headliners live in **`FJP/FiniteJetMain.lean`** (not SheafyEndpoints). Verbatim (lines 26-44):

```lean
/-- **[FJP] Theorem 1.3 (sheafy)**: `(𝓐, 𝓐°)` is sheafy. -/
theorem finiteJet_isSheafy : ValuationSpectrum.IsSheafy (JetA F) :=
  isSheafy_JetA F

/-- **[FJP] Theorem 1.3 (uniform)**: 𝓐 is uniform. -/
theorem finiteJet_isUniform : TopologicalRing.IsUniform (JetA F) :=
  isUniform_JetA F

/-- **[FJP] Theorem 1.3 (domain)**: 𝓐 is an integral domain. -/
theorem finiteJet_isDomain : IsDomain (JetA F) :=
  inferInstance

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: 𝓐 is not noetherian. -/
theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (JetA F) :=
  not_isNoetherianRing_JetA F

/-- **[FJP] Theorem 1.3 (not stably uniform)**: 𝓐 is not stably uniform. -/
theorem finiteJet_not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (JetA F) :=
  not_isStablyUniform_JetA F
```

(`variable (F : Type*) [Field F]`, namespace `FiniteJet`.)

**`FJP/FiniteJetSheafyEndpoints.lean`** endpoints, verbatim statements (`universe u`, `variable (F : Type u) [Field F]`):

```lean
def finiteJetPlus : RingOfIntegralElements (JetA F) :=
  ⟨((JetA F)⁺ : Subring (JetA F)), inferInstance⟩                       -- line 54

theorem finiteJet_isSheafyFor : IsSheafyFor (JetA F) (finiteJetPlus F)   -- line 60

theorem finiteJet_isSheafOfTopologicalRings :
    IsSheafOfTopologicalRings (JetA F)                                   -- line 73

theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA F))                     -- line 84

theorem finiteJet_structurePresheaf_isSheaf :
    (ValuationSpectrum.structurePresheaf (JetA F)).IsSheaf               -- line 94

def finiteJet_structureSheaf :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop (JetA F))            -- line 103

theorem finiteJet_standardSheafCondition : StandardSheafCondition (JetA F)  -- line 112

theorem finiteJet_isSheafyComplete_of_hasStandardRefinements
    (hall : ∀ Bplus : RingOfIntegralElements (JetA F),
      Bplus.HasStandardRefinements (JetA F)) :
    IsSheafyComplete (JetA F)                                            -- line 119

theorem finiteJet_isSheafyComplete : IsSheafyComplete (JetA F)           -- line 132

theorem finiteJet_isSheafyFor_all (Bplus : RingOfIntegralElements (JetA F)) :
    IsSheafyFor (JetA F) Bplus                                           -- line 136

theorem finiteJet_structurePresheaf_isSheafOfTopologicalRings_all
    (Bplus : RingOfIntegralElements (JetA F)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (JetA F))                     -- line 144

theorem finiteJet_structurePresheaf_isSheaf_all
    (Bplus : RingOfIntegralElements (JetA F)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) := Bplus.2
    haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (JetA F)).IsSheaf               -- line 156

theorem finiteJet_isSheafyTateRing : IsSheafyTateRing (JetA F)           -- line 175

theorem finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings
    (P : PairOfDefinition (JetA F))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA F) P)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements
      ((CompletionModel (JetA F) P)⁺ : Subring (CompletionModel (JetA F) P)) := Bplus.2
    haveI : HasLocLiftPowerBounded (CompletionModel (JetA F) P) :=
      hasLocLiftPowerBounded_faithful
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (ValuationSpectrum.structurePresheaf (CompletionModel (JetA F) P)) -- line 184

theorem finiteJet_completionModel_structurePresheaf_isSheaf
    (P : PairOfDefinition (JetA F))
    (Bplus : RingOfIntegralElements (CompletionModel (JetA F) P)) :
    … (ValuationSpectrum.structurePresheaf (CompletionModel (JetA F) P)).IsSheaf  -- line 200
```

All bodies are one-to-three-line discharges through the generic bridges (`isLimitSheaf_of_isSheafy`, `standardSheafCondition_of_isSheafyFor`, `isSheafyFor_iff_isSheafyComplete`, `isSheafyTateRing_iff_isSheafyComplete`) — no FJP-specific re-proofs.

## 4. FiniteJetGraphKoszul.lean deep-dive

Namespace `FiniteJet.GraphKoszul`. Two layers: a pure-`CommRing` differential/syzygy layer, and a normed layer over `E`.

**Index types and differentials** (`variable {S} [CommRing S] {m : ℕ}`):
- 56 `abbrev Pairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}` — strictly-ordered pairs subtype (not `Fin (m.choose 2)`).
- 59 `def d1 (r u : Fin m → S) : S := ∑ i, u i * r i`.
- 64 `def d2 (r : Fin m → S) (v : Pairs m → S) : Fin m → S := fun j => (∑ i, if h : i < j then v ⟨(i, j), h⟩ * r i else 0) - ∑ k, if h : j < k then v ⟨(j, k), h⟩ * r k else 0`.
  **Sign convention** (docstring, 61-63): "[FJP] p.10 sign convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`".
- 69 `d1_d2 : d1 r (d2 r v) = 0`; 78 `d1_map`, 84 `d2_map` (naturality along `φ : S →+* T`); 97 `d2_smul`; 110 `d2_unit_scale`; 123 `d2_zero`; 138 `d2_add`; 153 `d2_sum`; 170 `d2_koszul_single` (contractibility: syzygy times `r i` is a wedge image).

**Polynomial layer** (`{D} [CommRing D]`):
- 264 `syzygy_coordinate` — coordinate-sequence syzygies over any base are Koszul-generated (multidegree induction via `finSuccEquiv`).
- 363 `exists_pow_C_mul_eq_map` (denominator clearing into `Localization.Away g`); 390 `exists_pow_C_mul_eq_zero_of_map_eq_zero` (g-torsion kernel).
- 412 `translationEquiv (c : Fin m → D)` (+ 427/432 `_X/_C`); 440 `syzygy_graph_of_isUnit`.
- **504 `syzygy_graph_polynomial (g f) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤) (u) (h : d1 (fun i => C g * X i - C (f i)) u = 0) : ∃ v, d2 … v = u`** — the two-case ideal argument (`A` = ideal of Koszul-reachable multipliers; each `rᵢ ∈ A` by contractibility, `(C g)^P ∈ A` through `D_g` + translation + clearing; `A = ⊤`).

**Normed layer** (`{E} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E]`):
- 653 `mapRestricted (φ hφ c)` : coefficientwise map on `MvPowerSeries.Restricted` (generic radii `c`); 672 `norm_mapRestricted_le`.
- 701 `exists_norm_le_one_eq_pow_mul` (ball division along a scaling unit).
- 727 `pi_norm_scale`; 750 `pi_norm_add_le_max`; **759 `exists_lift_norm_le_of_closed_range {t} (htu ht1 ht0 hscale) (f : (ι → A) →+ (κ → A)) (hcont) (hequiv : t-equivariance) (hclosed : IsClosed (Set.range f)) : ∃ h, 1 ≤ h ∧ ∀ y ∈ range f, ∃ u, f u = y ∧ ‖u‖ ≤ h*‖y‖`** — the ultrametric Banach OMT with constants (Baire on the closed range, 759-1153).
- **1158 `abbrev P (E) (m) := MvPowerSeries.Restricted E (fun _ : Fin m => (1 : ℝ))`** — `P_E = E⟨T₁,…,T_m⟩`.
- 1167 `polyToP : MvPolynomial (Fin m) E →+* P E m`; 1178 `coeff_polyToP`; 1183/1195/1200 `norm_tP_mul/norm_tP/isUnit_tP`; 1205 `exists_ball_eq_tP_pow_mul`; 1215 `mem_span_C_pow_of_coeff_norm_le`; 1250 `CompleteSpace (P E m)` instance (m = 0 via `foo_isom`); 1260/1268 `norm_coeff_le_gauss/finite_setOf_le_norm_coeff`; 1281 `polyBall : MvPolynomial (Fin m) ↥(unitBall E) →+* P E m` (+ 1284/1291/1301); 1325 `trnc (n)` (degree-n polynomial truncation of a ball element); 1331/1351/1369 `coeff_polyBall_trnc/norm_sub_polyBall_trnc_le/mk_trnc_eq`.
- **AdicBridge** (section 1255-1585, `variable (t : E) (htu ht1 ht0 hscale)`): 1414 `abbrev I0 : Ideal (MvPolynomial (Fin m) ↥(unitBall E)) := Ideal.span {C ⟨t, …⟩}`; 1419 `I0_pow_smul_top`; 1432 `toAdic : ↥(unitBall (P E m)) →+* AdicCompletion (I0 t ht1) (MvPolynomial (Fin m) ↥(unitBall E))` (truncation classes); 1496 `toAdic_injective`; 1528 `toAdic_surjective` (Cauchy-limit of representatives);
  **1580 `noncomputable def ballAdicEquiv : ↥(unitBall (P E m)) ≃+* AdicCompletion (I0 (E := E) (m := m) t ht1) (MvPolynomial (Fin m) ↥(unitBall E))`** = `RingEquiv.ofBijective (toAdic …)` — the [FJP] (4.4) identification.
- 1592 `flat_polyToP (hE₀ : IsNoetherianRing (unitBall E)) (t htu ht1 ht0 hscale) : Module.Flat (MvPolynomial (Fin m) E) (P E m)` — via `ballAdicEquiv` + mathlib `AdicCompletion.flat_of_isNoetherian` + scalar-tower localization sandwich.
- **1791 `syzygy_graph_restricted (hE₀) (t htu ht1 ht0 hscale) (g f hunit) (r) (hr : ∀ i, r i = polyToP (C g * X i - C (f i))) (u) (h : d1 r u = 0) : ∃ v, d2 r v = u`** — flat base change of 504 via the equational criterion (`hflat.isTrivialRelation_of_sum_smul_eq_zero`).
- **1839 `isClosed_graphIdeal [IsNoetherianRing (P E m)] (t htu ht1 ht0 hscale) (hE₀P : IsNoetherianRing (unitBall (P E m))) (r) : IsClosed ((Ideal.span (Set.range r) : Set (P E m)))`** — via `unitBallPod` + `Wedhorn.isClosed_ideal_of_noetherian` (`NoetherianTateModules.lean:459`). Note: closedness holds for **arbitrary** `r`, not just graph sequences.
- **1860 `exists_d1_lift [IsNoetherianRing (P E m)] (t …) (hE₀P) (r) : ∃ h, 1 ≤ h ∧ ∀ x ∈ Ideal.span (Set.range r), ∃ u, d1 r u = x ∧ ‖u‖ ≤ h * ‖x‖`** ([FJP] (4.7)).
- **1929 `exists_d2_lift [IsNoetherianRing (P E m)] (hE₀) (t …) (g f hunit) (r) (hr) : ∃ z, 1 ≤ z ∧ ∀ u, d1 r u = 0 → ∃ v : Pairs m → P E m, d2 r v = u ∧ ‖v‖ ≤ z * ‖u‖`** ([FJP] (4.8); for m = 1 `Pairs 1` is empty so `ker d1 = 0`).

**`ballAdicEquiv` prerequisite chain / extraction plan.** The AdicBridge block (P … ballAdicEquiv, lines 1158-1585) uses, from outside GraphKoszul:
- from `FJP/FiniteJetRings.lean` (generic section): `unitBall` (:572), `mem_unitBall_iff` (:584), `norm_pow_mul_of_scale` (:600) — plus, only for `isClosed_graphIdeal`/`exists_d*_lift`, `unitBallPod` (:641) and `isTateRing_of_scale` (:679);
- from `FJP/FiniteJetNoetherianVertices.lean`: exactly two generic declarations — `finsupp_prod_one` (:47) and the `NormOneClass (MvPowerSeries.Restricted R (fun _ : Fin k => 1))` instance (:131);
- from `FJP/RestrictedLaurent.lean`: the `StrongPos (fun _ : Fin n => 1)` instances (:739-741);
- from the vendored stack: `MvPowerSeries.Restricted` (`Vendored/CoramMvRestricted.lean:144`), `MvRestricted.norm_eq` (`Vendored/CoramMvRestrictedNorm.lean:71`), `foo_isom` (`Vendored/CoramRestrictedIso.lean:332`);
- from mathlib: `AdicCompletion` core (only `flat_polyToP` needs `AdicCompletion.flat_of_isNoetherian`).

So `ballAdicEquiv` (and everything up through `exists_d2_lift`) can move to an upstream file that imports `FiniteJetRings` + the vendored Coram stack + `NoetherianTateModules` **without** importing `FiniteJetNoetherianVertices`, provided the two tiny generic decls (`finsupp_prod_one`, the `NormOneClass` restricted instance) are re-homed (both are base-generic and 3-20 lines). The current import of `WedhornCechAcyclicity` (which reaches `Wedhorn.isClosed_ideal_of_noetherian` transitively) comes only through `FiniteJetNoetherianVertices`; the actual home of that theorem is `NoetherianTateModules.lean:459`, importable directly. Watch the two `set_option backward.isDefEq.respectTransparency false` sites (1430, 1787) — they travel with `toAdic` and `syzygy_graph_restricted`.

## 5. AdicCompletionNoetherian.lean audit

File: `/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/projects/AdicSpaces/Adic spaces/AdicCompletionNoetherian.lean` (1735 lines, namespace `AdicCompletion`; Stacks 0316).

- **`AdicCompletion.isNoetherianRing` exists**, line 1684: `theorem isNoetherianRing [IsNoetherianRing R] (I : Ideal R) : IsNoetherianRing (AdicCompletion I R)` — full proof body present (L1 generators; `I = ⊥` case via `of_bijective`; else `MvPowerSeries.instIsNoetherianRing_fin` + `mvPowerSeriesEval_surjective` + `isNoetherianRing_of_surjective`).
- **Exactly two `sorry`s remain**, both `private`:
  - `_mvPowerSeriesEval_apply_coe` (line 976, `sorry` at 981) — `mvPowerSeriesEval I hn f hf ↑p = AdicCompletion.of I R (MvPolynomial.aeval f p)` (pending the polynomial-truncation argument);
  - `_mvPowerSeriesEval_surjective_seq_stable_value_partial` (line 1440, `sorry` at 1452) — sequence-stability of the surjectivity construction for small iteration indices.
- **Axiom probe** (ran clean): `'AdicCompletion.isNoetherianRing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]` — the sorries are on its cone (via `mvPowerSeriesEval_surjective`).
- Importers: `TateAcyclicityResiduals.lean`, `WedhornStronglyNoetherian.lean`. **The FJP chain does not depend on it** — GraphKoszul uses mathlib's `AdicCompletion.flat_of_isNoetherian`, and the FJP endpoints probed sorryAx-free. Relevant to the campaign only if the generalized development wants the *project's* Stacks-0316 (e.g. noetherian `k°` ⇒ noetherian pods for abstract K); as it stands it is not usable axiom-clean.

## 6. StrictMilnorSquare / M9 status

**Complete and sorry-free in `FJP/Milnor/`:** only `StrictMilnorSquare.lean` (142 lines):
- `structure StrictMilnorSquare (k) [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]` (line 53): four carriers `R B C D : Type u` with `NormedCommRing/IsUltrametricDist/NormedAlgebra k/CompleteSpace/NormOneClass` instance fields; norm-nonincreasing square maps `jB : R →+* B`, `iC : R →+* C`, `ρB : B →+* D`, `ρC : C →+* D` + `square_comm`; `κ : ℝ`, `one_le_κ`, `exists_lift` ((4.1): `∀ d, ∃ c, ρC c = d ∧ ‖c‖ ≤ κ*‖d‖`); `ρ : ℝ`, `one_le_ρ`, `exists_glue`, `pair_injective`, `norm_le_pair` ((4.2)); and the finiteness fields `pods_noetherian_B/C/D : ∀ m, IsNoetherianRing (FiniteJet.GraphKoszul.P _ m)` and `unitBall_pods_noetherian_B/C/D : ∀ m, IsNoetherianRing (FiniteJet.unitBall (GraphKoszul.P _ m))`.
- `StrictMilnorSquare.glue_unique` (line 135) — the only theorem.
- The docstring (29-36) lists the planned files `Milnor/Localization.lean`, `Naturality.lean`, `Transfer.lean`, `TateExtension.lean` — **none of these exist yet**, nor does `PodRow.lean` or `FiniteJetInstance.lean`. Nothing imports Milnor/ yet.

**Ticket state** (`projects/AdicSpaces/.mathlib-quality/tickets.md`, section "M9 — [FJP] Cor 5.5 + Cor 6.1" at 1019-1100; NOT in the repo-root `.mathlib-quality/` — repo-root plan.md/tickets.md have zero M9/Milnor content):
- T1001 (PodRow.lean: port extJB…ext_pair_injective to abstract S, via generic `mapRestricted`, same constants): **in_progress since 2026-07-18, file not yet created**.
- T1002/T1003 (Localization.lean: ideal_row_surjective / ideal_pullback_controlled / isClosed_IA, then `S.localize`), T1004 (Naturality.lean: graph-bridge port; note "the presheafValueMapOfHom/CovariantPush section is ALREADY generic — reuse directly"), T1005 (Transfer.lean: `S.isSheafy_R` from `IsSheafy S.B/C/D`), T1006 (`FiniteJetSquare F : StrictMilnorSquare K`, κ = ρ = 1), T1007 (milestone axiom sweep) — all open. Design notes recorded: degenerate `s = 0` handled in the transfer, not in `S.localize`; norm-nonincreasing (not merely bounded) maps are the operative class, generalizing is a recorded non-goal.
- Full architecture: `projects/AdicSpaces/.mathlib-quality/plan-m9.md` (M9a machine / M9b strong sheafiness via `restrictedTateExtension` / M9c the `A_d` family with `TruncatedJet d R`), audit in `plan-m9-preplan.md`.

**Strict-map predicate:** `IsStrictMap` (`Adic spaces/NoetherianTateModules.lean:50`, continuous + open onto image) and `IsStrictLinearMap` (`:57`). The FJP files do not use them directly — strictness is carried as explicit `∃ C, 1 ≤ C ∧ … ‖lift‖ ≤ C*‖·‖` statements.
**Closed-range bounded-lift theorem:** `FiniteJet.GraphKoszul.exists_lift_norm_le_of_closed_range` (`FJP/FiniteJetGraphKoszul.lean:759`).
**Finite-module open-mapping / closedness:** `Wedhorn.isClosed_ideal_of_noetherian` (`Adic spaces/NoetherianTateModules.lean:459`); mathlib's `ContinuousLinearMap.exists_preimage_norm_le` is the Banach-OMT-with-constants cited by DD6 (plan.md:146).

## 7. Import graph (FJP-internal edges; `X → Y` = Y imports X)

```
RestrictedLaurent ──→ FiniteJetRings ──┬─→ FiniteJetUniformDomain ──┐
 (also imports:        (also: JetDual-  ├─→ FiniteJetNoetherianVert.│
  Vendored.Coram-       NumberNorm,     │    (also: WedhornCech-    │
  RestrictedNorm/Iso,   ExampleUnitDisc)│     Acyclicity)           │
  ExampleUnitDisc)                      │        │                  │
                                        │        ▼                  │
                                        │   FiniteJetGraphKoszul    │
                                        │    (also: mathlib Adic-   │
                                        │     Completion.AsTensor-  │
                                        │     Product, Flat.Equa-   │
                                        │     tionalCriterion,      │
                                        │     LocalProperties.Sub-  │
                                        │     module)               │
                                        │        │                  │
                                        │        ▼                  │
                                        │   FiniteJetStrictLocaliz. │
                                        │        │                  │
                                        │        ▼                  │
                                        └─→ FiniteJetFunctoriality ←┘  (also: FaithfulLocLift,
                                                 │        │             PresheafFunctoriality)
                                    ┌────────────┘        └───────────┐
                                    ▼                                 ▼
                          FiniteJetSheafTransfer            FiniteJetChart (also imports
                                    │                         FiniteJetUniformDomain)
                                    └────────→ FiniteJetMain ←────────┘
                                                    │
                                                    ▼
                                        FiniteJetSheafyEndpoints
                                          (also: SheafyEndpoints, RelativeStandard-
                                           Refinement, SheafyCompletionModel)

Milnor/StrictMilnorSquare  ←  FiniteJetGraphKoszul + FiniteJetRings   (imported by nobody yet)
```

No file outside FJP imports FJP modules except the root `Adic spaces.lean` (line 94 imports `FJP.FiniteJetSheafyEndpoints`; the Milnor file is also in the build tree). `PresheafFunctoriality.lean` mentions "[FJP]" only in docstrings — no cycle (it is genuinely upstream of FiniteJetFunctoriality).

**Placement for the new files:** `FJP/KoszulFiniteFree.lean` and `FJP/RestrictedGaussAdic.lean` can sit anywhere **after `FiniteJetRings` and before `FiniteJetGraphKoszul`** with zero risk, importing `«Adic spaces».FJP.FiniteJetRings` (for `unitBall` & pods), `«Adic spaces».NoetherianTateModules` (for Wedhorn closedness/strict maps), and the `Vendored.Coram*` stack directly. If they should *not* import `FiniteJetNoetherianVertices` (to stay Laurent-free), the two generic decls `finsupp_prod_one` (NoethVert:47) and the `NormOneClass` restricted instance (NoethVert:131-152) must be re-homed upstream — those are GraphKoszul's only genuine uses of NoetherianVertices content; its import otherwise serves just the chain topology (and transitively supplies `WedhornCechAcyclicity`). Alternatively a new file placed between NoetherianVertices and GraphKoszul inherits everything with no moves. The pure-`CommRing` d1/d2/syzygy layer (GraphKoszul 51-642) has no project dependencies at all and could be extracted to a file importing only mathlib.

## 8. Norm / lattice API

- **`P E m`** (`E⟨T₁,…,T_m⟩`): `FJP/FiniteJetGraphKoszul.lean:1158`, `abbrev P E m := MvPowerSeries.Restricted E (fun _ : Fin m => (1 : ℝ))`. Jet-ring instantiations `PA/PB/PC/PD`: `FJP/FiniteJetStrictLocalization.lean:42-45`. Underlying type `MvPowerSeries.Restricted`: `Adic spaces/Vendored/CoramMvRestricted.lean:144`; univariate `PowerSeries.Restricted`: `Vendored/CoramRestrictedNorm.lean:156`. The subring-form used by `IsStronglyNoetherian` is `restrictedMvPowerSeriesSubring` (`Adic spaces/RestrictedPowerSeries.lean:78`; class at `:243`).
- **`unitBall`**: `FJP/FiniteJetRings.lean:572` (generic `Subring E` of `{‖x‖ ≤ 1}`, needs `[NormOneClass E]` — T108 signature note in the docstring), with `mem_unitBall_iff` :584 (an `Iff.rfl` — load-bearing for the v4.33 `I0` witness pattern, see GraphKoszul 1407-1413), `unitBallPod` :641.
- **The norm**: multivariate Gauss norm `MvRestricted.norm_eq` (`Vendored/CoramMvRestrictedNorm.lean:71`) over `[NormedRing R] [IsUltrametricDist R] [StrongPos c]`; univariate `NormedRing` instance `Vendored/CoramRestrictedNorm.lean:234`, `norm_eq` :243. `RestrictedLaurent`'s own norm: `gaussNorm` `FJP/RestrictedLaurent.lean:384`, `NormedCommRing` instance :437, `norm_def` :442. The `StrongPos (fun _ : Fin n => 1)` witnesses live at `RestrictedLaurent.lean:739-741`.
- **`RestrictedLaurent.norm_mul_eq`** (`FJP/RestrictedLaurent.lean:613-698`):
  ```lean
  theorem norm_mul_eq (_hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n)
      (f g : RestrictedLaurent K) : ‖f * g‖ = ‖f‖ * ‖g‖
  ```
  **The discrete-value hypothesis is NOT genuinely used**: it is bound as `_hd` (underscore, never referenced in the proof), and the docstring (609-612) says so explicitly: "the hypothesis `hd` records the discreteness of the [FJP] setting — the minimal-achiever proof below in fact works for any complete nonarchimedean field." The proof runs entirely on `exists_gaussNorm_eq` (norm attained, from coefficient decay — :396, generic) + finiteness of the achiever set + minimal-index achievers + the ultrametric dominance lemma `norm_tsum_lt_of_forall_lt` (:584). All call sites: `mul_ne_zero_of_ne_zero` (`RestrictedLaurent.lean:723`, threads its own `hd` through at :726 — equally droppable) and `norm_L_mul` (`FJP/FiniteJetUniformDomain.lean:33-34`, feeding `norm_K_discrete F` from `FiniteJetRings.lean:53`). Dropping the hypothesis is a signature-only change; the generalization campaign gets `L⟨…⟩` norm multiplicativity over any complete nonarch field for free. (The genuinely discreteness-flavoured facts elsewhere are `norm_K_discrete` itself — used *only* here — and the Psi-transposition of item 2, which needs `K = F((t))`, not just discreteness.)

Campaign-relevant plan context: `projects/AdicSpaces/.mathlib-quality/plan.md` DD1 (lines 83-87) records "Generalisation to abstract discretely-valued normed fields is a post-campaign cleanup, not scope", and Generality decisions (219-224) already committed the M3-M4 layer to "an abstract strict Milnor square of normed Tate K-algebras with noetherian-pod affinoid vertices" — the state found above matches: GraphKoszul fully abstract; StrictLocalization/Functoriality/SheafTransfer concrete-in-the-four-rings but datum-parametric; the Laurent hard-coding concentrated in FiniteJetRings' uniformizer block (535-789), norm_K_discrete (53-69), NoetherianVertices' gaussK transposition (362-394) + `IsStronglyNoetherian K` consumption (160-196), UniformDomain's `not_isUniform_JetB` witness (403-426), and the whole of FiniteJetChart.