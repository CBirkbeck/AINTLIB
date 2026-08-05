# Unused hypotheses — generalisation backlog

Generated from the `linter.unusedVariables` output of a green full build.

Each entry is a **binder the proof never uses**: the declaration is strictly stronger
than its statement claims, and the hypothesis can be dropped. This is a *statement*
change, so it is `/generalise` lane work — it stops at review, and every call site loses
an argument.

These are deliberately **not** silenced by renaming to `_h`. That marker means
"deliberately unused"; here the hypothesis is *accidentally* unused, and the warning is
the only record of it. Silencing would destroy the signal it carries.

**47 declarations, 109 unused binders.**

- `FJP/FiniteJetGraphKoszul.lean:191` **koszul_row_sum_lt** — `h`
- `FJP/FiniteJetGraphKoszul.lean:202` **koszul_row_sum_gt** — `h`
- `FJP/FiniteJetGraphKoszul.lean:1206` **exists_lift_norm_le_of_le_norm** — `hpitpow`
- `FJP/FiniteJetGraphKoszul.lean:1847` **polyBallCod** — `q`, `q`
- `FJP/FiniteJetGraphKoszul.lean:1969` **algebraMapSubmonoid_ballDenoms_surj** — `htu`, `ht0`
- `FJP/FiniteJetStrictLocalization.lean:499` **norm_d1_rA_le** — `hCrA1`
- `FJP/RestrictedLaurent.lean:1297` **coeffHom** — `f`
- `FarguesFontaine/CurveObject.lean:712` **hle3_lem** — `hct`, `hct'`
- `FarguesFontaine/CurveObject.lean:1445` **frobFixedRestrict_eq_of_germ_eq** — `y`
- `FarguesFontaine/CurveObject.lean:1756` **xPresheaf_saturated_cover** — `v`, `v`
- `FarguesFontaine/Euclidean.lean:710` **valued_eq_teichCoeffAr_forward** — `hx`
- `FarguesFontaine/Euclidean.lean:751` **valued_eq_teichCoeffAr_backward** — `hy`
- `FarguesFontaine/FrobeniusLimit.lean:325` **yFrobNat** — `V`
- `FarguesFontaine/GaussNorm.lean:854` **hlead_lem** — `hρ0`, `hρ1`
- `FarguesFontaine/IntervalRing.lean:1818` **exists_pIdeal_pow_subset_of_ball** — `y`
- `FarguesFontaine/IntervalSplitting.lean:407` **blocApprox_left** — `hq₂r`, `hmatch`, `hε`, `hd`, `hM`
- `FarguesFontaine/IntervalSplitting.lean:460` **blocApprox_right** — `hrq₁`, `hmatch`, `hε`, `hP`
- `FarguesFontaine/RobbaPresentation.lean:1707` **wIRPS_monomialSum_le** — `hσρ`, `hm`, `hgen`, `hbmem`, `hb`, `hbg`, `hWle`, `hε`
- `FarguesFontaine/RobbaPresentation.lean:1794` **evalBI_monomial_eq_BIProd** — `hρσ`, `hσρ`, `hm`, `hgen`, `hWle`, `hw1`, `hw2`, `hε`
- `FarguesFontaine/RobbaPresentation.lean:3414` **tendsto_v_fst_coeffSeq** — `n`, `n`
- `FarguesFontaine/RobbaPresentation.lean:3427` **tendsto_v_snd_coeffSeq** — `n`, `n`
- `FarguesFontaine/RobbaPresentation.lean:4843` **wIRPS_monomialSum_le₂** — `hρσ`, `hm`, `hgen`, `hbmem`, `hb`, `hbg`, `hε`
- `FarguesFontaine/RobbaPresentation.lean:4927` **evalBI_monomial_eq_BIProd₂** — `hρσ`, `hσρ`, `hm`, `hgen`, `hw1`, `hw2`, `hε`
- `LaurentCoverExact.lean:798` **hg_higher_zero_lem** — `h`
- `LaurentCoverExact.lean:823` **hh_higher_zero_lem** — `g`
- `LaurentRefinementCore.lean:1740` **iteratedMinus_forward_mem_locSubring_of_eq_s** — `ha`, `ha_A₀`, `hu_s_tgt`
- `Presheaf.lean:2035` **pairAlgebraMapToIntegralClosure** — `a`, `b`, `a`, `b`
- `RelativePieceKeystone.lean:1015` **imagePieceDatum_mem_rationalOpen_iff** — `hTateB`
- `RelativePieceKeystone.lean:1053` **imagePieceDatum_rationalOpen_mono** — `hTateB`
- `RelativePieceKeystone.lean:1073` **imagePieceDatum_rationalOpen_inter** — `hTateB`
- `RelativePieceKeystone.lean:1105` **relativePiece_restrict_square_locLevel** — `hTateB`
- `RelativePieceKeystone.lean:1174` **relativePiece_equiv_restrict_square** — `hTateB`
- `RestrictedLimitSheaf.lean:417` **isLimitSheafOn_of_isSheafyOn** — `V`, `ι`, `U`, `V`, `ι`, `U`, `V`, `ι`, `U`
- `SpvAI.lean:658` **Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO** — `h_le_AOO`
- `WedhornCechAcyclicity.lean:4523` **unitCover_F_mul_expand** — `f`
- `WedhornCechAcyclicity.lean:4613` **unitCover_witness_case_pq** — `hbb`, `haMbb`
- `WedhornCechAcyclicity.lean:4669` **unitCover_witness_case_pFq** — `hone`, `hbb`, `hinvO`, `haMbb`
- `WedhornCechAcyclicity.lean:4712` **unitCover_witness_case_pqF** — `hone`, `hbb`, `hinvO`, `haMbb`
- `WedhornCechAcyclicity.lean:4755` **unitCover_witness_case_pFqF** — `hone`, `hinvO`
- `WedhornCechAcyclicity.lean:8080` **propA3_part1_gluing_mixed_trace** — `hM_base_open`
- `WedhornCechAcyclicity.lean:9159` **genPiece_relOverlap_merge** — `hspan`
- `WedhornCechAcyclicity.lean:9187` **genPiece_relOverlap_p_decomp** — `t₂`, `EII`
- `WedhornCechAcyclicity.lean:9209` **genPiece_relOverlap_gen_mem** — `hspan`
- `WedhornCechAcyclicity.lean:9237` **genPiece_relOverlap_witness_eq** — `hspan`
- `WedhornCechAcyclicity.lean:10871` **genRestrictedCover_isOXAcyclic_of_B** — `hTateB`
- `WedhornCechAcyclicity.lean:11070` **ratio_laurent_cover_each** — `hne`
- `WedhornCechAcyclicity.lean:13266` **imageCover_gluing_transport** — `hTateB`
