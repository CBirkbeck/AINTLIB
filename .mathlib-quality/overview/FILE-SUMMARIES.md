# Per-file summaries (Phase 1 inventory returns)

## Euclidean.lean — 40 decls (4 defs, 36 lemmas), 2224 lines
Kedlaya §2 at a single radius: equips `A^r ⊆ hatK` with a coordinate degree
`degAr x = max{n : λ_ρ(x) = ρⁿ|xₙ|}` and proves Euclidean division for it.  Engine is the
Witt homogeneity estimate (2.8.1); then digit comparison (Rem 2.7), degree stability under
subdominant perturbation, additivity `deg(xy)=deg x+deg y` (Lem 2.6), approximate division
(Lem 2.8) by well-founded descent, exact division (Prop 2.9), and `A^r` is a PID (Cor 2.10).

- Key API: `degAr` (14 in-file consumers + Groebner), `convF` (8),
  `gaussTerm_teichCoeffAr_le'` (8), `divStep` (5), `degAr_spec` (4), `tendsto_convF` (4)
- **UNUSED**: `degAr_mul` (Kedlaya Lem 2.6 — stated+proved, consumed nowhere in the project);
  `isPrincipalIdealRing_ArSub` (terminal result, no consumer yet)
- sorry: none.  set_option: none.
- Proofs >30 lines: 19 of 40.  Largest: `valued_degAr_PhiHatK_convF` (155),
  `digit_sub_le` (144), `gaussTerm_sub_convF_divStep_le` (135),
  `valued_mul_sub_PhiHatK_convF_le` (134), `valued_sub_sub_PhiHatK_le` (132),
  `descent_step` (131), `exact_division` (114)

## Groebner.lean — 92 decls (13 definitional, 74 lemmas, 5 instances), 2424 lines
Kedlaya §3 at radius 1, complete and sorry-free: Gauss norm `gaussNormRPS` on the Tate
algebra `A^r⟨T₁..T_k⟩`, the bridge `isRestricted_iff_valued`, Gröbner data (leading
index/coefficient in graded-lex, Def 3.6; degree invariant `d_I` and finite index set `S`
from Dickson via a well-quasi-order, Def 3.7).  Engine: a division step resting on
`exact_division` (Prop 2.9), iterated under a well-founded colex descent `muMeasure`, giving
approximate generation (Lem 3.8) and — after ultrametric series summation — exact generation
(Lem 3.9) and `isStronglyNoetherian_ArSub` (Thm 3.2).

- Key API: `gaussNormRPS` (~50 sites), `leadIdxRPS` (15), `dIdx` (13), `leadCoeffRPS` (11)
- **UNUSED**: `coeff_frozen` (1210-1238), `coe_sub_monomialMul` (1240-1250)
- **DEAD CODE**: unused `have hrank := coeffRank_eq_of_diff_le ...` inside
  `support_step_subset` at line 1535
- sorry: none.  set_option: none (4 decls carry `open scoped Classical in`)
- Proofs >30 lines: 15.  Largest: `approx_generation_key` (109), `groebner_reduce` (89),
  `exists_rps_series_limit` (80), `groebner_step` (78), `ideal_eq_span_groebner` (67)

## ChartVObj.lean — 30 decls (5 defs, 25 lemmas), 1338 lines
Instantiates Wedhorn's generic stalk package at a Big-window chart `U_{a,b}` of 𝒴, producing
`chartVObj : VObj` by transporting Tateness / integral elements / unit ball along the ID2
comparison `presheafChartRingEquivBISub : O(U_{a,b}) ≃+* B^I`.  Payload is the plus
reconciliation (Kedlaya Def 4.5): easy inclusion by transported power-boundedness; hard
inclusion reduced to a dense-level predicate `ChartDensePlus` on `Bloc` and proved at `b = 1`
by a Teichmüller head/tail argument over three exponent zones, then a two-radius geometric
tail bound.  Conclusion `chartPlus_eq_canonical` is what YStalks consumes.

- Key API: `sPow` (9), `exists_eq_toOF_pow_mul` (4)
- **UNUSED — NOTABLE**: `chartVObj` is the file's HEADLINE object and is consumed NOWHERE in
  the project.  Either it is dead scaffolding superseded by the `spaVObjTate` route, or a
  genuine gap where the chart 𝒱-object should be feeding the capstone.  MUST resolve in Step 8.
- Also unused: `p_div_teich_pow_a_mem_chartSubring` (general-`b` sibling, off the `b=1` path)
- sorry: none.  set_option: file-level `linter.overlappingInstances false` only.
- Proofs >30 lines: 10.  Largest: `chartDensePlus_of_exact` (103), `mk_monomial_mem_of_le` (92),
  `mk_monomial_pow_a_eq` (90), `p_div_teich_pow_a_mem_chartSubring` (83)

## IntervalSplitting.lean — 35 decls (4 defs, 31 lemmas), 1029 lines
Sheaf axiom for the FF interval presheaf on a two-piece closed cover: for `q₂ ≤ r ≤ q₁`,
`B^{[q₁,q₂]}` is the fiber product `B^{[q₁,r]} ×_{hatK} B^{[r,q₂]}` — separation
(`biResQ'_split_injective`) + gluing (`biResQ'_split_surjective`).  Engine is a
Mittag-Leffler decomposition (`exists_wLoc_split`) via `WittVector.init/tail` with crossed
Gauss-norm estimates, then joint eps-approximation (`exists_blocApprox_pair`) iterated at 2^-n
to a Cauchy limit `biGlue`.  Plus `isPowerBounded_iff_wI_le_one`.
- Key API: `biFstQ`/`biSndQ` (nearly every statement after L235), `biGlue` (7), `glueSeq` (5)
- Exported (unused in-file, consumed downstream): `biSndQ_biResQ'_middle`,
  `biResQ'_split_injective`, `biResQ'_split_surjective` (-> YPresheaf),
  `isPowerBounded_iff_wI_le_one` (-> ChartVObj)
- sorry: none.  set_option: none.
- Proofs >30 lines: 5.  Largest `isPowerBounded_iff_wI_le_one` (137),
  `exists_blocApprox_pair` (128), `exists_wLoc_split` (83)

## CurveObject.lean — 100 decls (19 defs, 78 theorems, 3 instances), 1781 lines
THE CURVE. Constructs `X = Y/phi^Z` as an object of V by descending the Y-presheafed space
along the open quotient `pi`: `O_X(V) := O_Y(pi^-1 V)^{phi=1}` as the equalizer `frobFixed`
(closed, hence complete).  Heart: the stalk map of `pi` is bijective — surjectivity by gluing
the translate family over a wandering neighbourhood (compatibility vacuous off-diagonal by
proper discontinuity), injectivity by the transport-inversion toolkit with an
`Int.induction_on` piece recurrence.  Then `xStalkEquiv`, `xVPreObj`, and a `Hom_cont(T,-)`
gluing argument for the sheaf condition, giving `xVObj`.
- Key API: `curvePreimage` (30), `frobFixed` (17), `xImage` (14), `yTopToCurve` (13)
- Unused in-file: `curvePreimage_eq_opensMap`, `curveRingPresheaf_map_apply`;
  `xVObj` is the terminal export (consumed downstream)
- sorry: none.  ZERO maxHeartbeats/maxRecDepth.
- Proofs >30 lines: 9.  Largest `limitFrobHom_add` (122),
  `xPresheaf_isSheafOfTopologicalRings` (120), `ringStalkMap_piYHom_injective` (78)

## VERIFIED UNUSED (exactly 1 reference in the whole library = own definition)
- `chartVObj` (ChartVObj.lean:75) — the file's HEADLINE object
- `degAr_mul` (Euclidean.lean) — Kedlaya Lemma 2.6
- `coeff_frozen`, `coe_sub_monomialMul` (Groebner.lean)
- `p_div_teich_pow_a_mem_chartSubring` (ChartVObj.lean)
- `isPrincipalIdealRing_ArSub` (Euclidean.lean) — Kedlaya Cor 2.10, terminal

## Presentation.lean — 117 decls (15 defs, 102 lemmas), 2398 lines
Kedlaya's Robba-localization presentation of `B^I` as a quotient of a radius-one Tate algebra
over `A^{rho2}`.  Key asymmetry: the Gauss value is monotone in the radius on `A_inf[1/[w]]`
but NOT on `Bloc`.  Builds `evalArHom : A^r<T> -> B^I`, slices to `evalArMvHom` in k
variables, then proves both SURJECTIVE via a head-split of `Aloc` + successive-approximation.
- Key API: `evalAr` (23), `coeffSeq` (21), `teichPowOverP` (15), `teichPiInvAloc` (13)
- SUPERSEDED: `exists_evalAr_eq_pInv_pow` (the `exists_evalAr_lift_*` chain proves more),
  `BISub_le_topologicalClosure_evalRange` (density, subsumed by exact surjectivity)
- sorry: none.  set_option: none.
- Proofs >30 lines: 17.  Largest `exists_evalAr_lift_aloc` (89),
  `exists_correction_sequence` (84), `wI_partial_cauchy_diff` (79)

## WittF.lean — 75 decls (7 defs, 67 lemmas, 1 instance), 2058 lines
Gauss-norm theory of Witt vectors over a perfectoid field F of char p, in three movements:
Teichmuller section is uniformly (Holder) continuous; the Gauss apparatus ported from W(O_F)
to W(F) threading explicit BddAbove hypotheses; decay theory (tail values, head bounds) for
the completion A^r.
- Key API: `gaussTermF` (46), `teichCoeffF` (35), `gaussValueF` (27), `tailValueF` (9)
- **UNUSED ANYWHERE IN PROJECT (7)**: `exists_delta_teichCoeff_sub`, `twoBddSubring`,
  `tendsto_gaussTermF_of_bddAbove_gt`, `degF`, `degF_spec`,
  `tendsto_gaussTermF_add_of_tendsto`, `tendsto_gaussTermF_of_w_approx`
- 37 of 75 decls consumed outside the file (ArCompletion 30, Euclidean 16)
- sorry: none.  set_option: none.
- Proofs >30 lines: 22.  Largest `valuation_teichCoeffF_prefix_add_le` (126),
  `tailValueF_add_le` (120), `exists_delta_teichCoeffF_sub` (118)

## YSpace.lean — 57 decls (7 defs, 50 lemmas; 24 private), 963 lines
Constructs Y = Spa(A_inf,A_inf) \ V(p[w]), proves it open, uniformizer-independent, and
phi^Z-stable.  Central device: a RANK-FREE rendering of the Scholze-Weinstein radius kappa —
"kappa(v) >= a/b" encoded as `v([w]^b) <= v(p^a)` (KGE/KLE), representation-independence by
cross-multiplication in the value monoid, so no rank-1 hypothesis and no logarithm.  Then
Kedlaya's window covering with c=(p+1)/2.
- Key API: `Y` (nearly everything), `cFF` (11), `KGE` (10), `KLE` (10)
- STRAYS: `Y_subset_spa` (callers use `.1` inline), `Y_eq_spa_inter_basicOpen`
  (`isOpen_Y` re-derives inline), `KLE_mono` (unused dual of `KGE_mono`)
- **CLEANUP FLAGS**: two MISPLACED docstrings (the "The covering" block at L443-450 sits
  above `KGE_mono` but describes `Y_eq_iUnion_windows`; the "Translation" block at L603-608
  sits above private `vle_pow_iff_cross` but describes `zsmul_windowU`) — leaving
  `KGE_mono`/`KLE_mono`/`Y_eq_iUnion_windows` undocumented.  A 4-line `hbridge` idiom is
  COPY-PASTED INTO 8 PROOFS (+ duplicated hy0/hy1 in 3, hnorm1/hnorm2 in 2), ~50 lines
  extractable; `isOpen_windowV` is a near-verbatim copy of `isOpen_windowU`.  L846 = 101 chars.
- sorry: none.  set_option: none.

## UniformizerEquivariance.lean — 42 decls (9 defs, 33 lemmas), 801 lines
Bloc and B^I do not depend on the chosen pseudo-uniformizer: `blocTwistEquiv` under which
`wLoc` and `BlocToHatK` are invariant, and B^I coincides ON THE NOSE as a subring.  Then the
interval-restriction system: w^I-uniformity on Bloc, a three-circles/Hadamard 1-Lipschitz
estimate, `biRes` by dense uniform extension, packaged over rational exponents via the
irreducible `vpiQ q = |w|^q`.
- Key API: `blocToBI` (11), `vpiQ`/`vpiQ_pos`/`vpiQ_lt_one` (9 each), `biRes`/`biCongr` (6)
- **STRONGEST DEDUP TARGET IN THE FOLDER**: the `biResQ*` (L469-605) and `biResQ'*`
  (L690-797) families are NEAR-VERBATIM CLONES differing only in `hlt.ne` vs `hlt.ne'` and
  `theta_mem_unit` vs `theta_mem_unit'` — ~130 duplicated lines
- The `warn.classDefReducibility false` is needed by `blocWIUniformSpace` (a plain `def` of
  class type, deliberately neither reducible nor an instance)
- sorry: none.  Proofs >30 lines: 2.

## YStalks.lean — 49 decls (12 defs, 30 lemmas, 6 instances, 1 structure), 996 lines
Discharges Wedhorn 8.14 at every point of Y: `rationalShrink_Y` -> `stalkShrink_Y` -> local
stalks with maximal ideal = support of the stalk valuation, transported along
`restrictStalkIso` to build `yTop`, `yPresheafedSpace`, `yVPreObj`.  Second half proves the
Y-relative sheaf condition via quasi-compactness forcing any covering base into a single
"run chart".
- Key API: `yTop` (6 in-file, **207 project-wide**), `runWindow` (5), `ySpaPoint` (4)
- **DEAD CODE (0 refs anywhere)**: `windowKeystone`, `isSheafyOn_window` (subsumed by
  `isSheafyOn_runChart`)
- `yVPreObj` = headline export, 57 external refs
- sorry: none.  No maxHeartbeats.
- Proofs >30 lines: 5.  Largest `rationalShrink_Y` (83)

## YPresheaf.lean — 59 decls (13 defs + 1 structure, 33 lemmas, 12 instances), 798 lines
Structure presheaf of Y from "interval traces" (loci kappa(v) in [1/q1,1/q2]); dyadic-exponent
traces are honest rational subsets (pass to the p^s-th Frobenius-root uniformizer where
exponents become integral).  Two comparison theorems: `limitEvalTop_bijective` (crux is the
geometric bridge `dyadicTrace_subset_nested`, proved by testing at the two endpoint Gauss
points) and the sheaf axioms (two-piece split, then N-piece chain by induction).
- Key API: `DyadicIdx` + projections, `dyadicVal`, `dyadicRes`, `dyadicTrace`,
  `limitSectionsY`, `limitRestrictY`
- All 12 instances unused-by-name but consumed by typeclass inference
- sorry: none.  Proofs >30 lines: 3.  Largest `biResQ'_chain_glue` (77)

## ChartData.lean — 67 decls (15 defs, 51 lemmas, 1 instance), 1674 lines
The Big-window chart rational datum: `chartT`/`chartS`/`chartData`, the localization
`blocEquivAwayChartS`, and the chart topology/uniformity, with the two-sided comparison
between the chart subring and the interval max-norm ball.
- Key API: `chartS` (25), `chartT` (12), `blocEquivAwayChartS` (10), `chartFracP` (9),
  `podAinf` (9), `chartFracPi` (8), `chartData` (7), `chartTopology` (6)
- **NO CONSUMER ANYWHERE**: `isRational_chartData`, `windowU_zero_eq_rationalOpen`,
  `windowV_zero_eq_rationalOpen`, `chartUniformity_eq`
- (unused in-file but consumed downstream: `presheafChartToBIProd_coe` -> ChartComparison,
  `ball_le_locNhd` -> BigWindows)
- set_option: `chartUniformity` carries `warn.classDefReducibility false` (L1108) — same
  pattern as `blocWIUniformSpace` in UniformizerEquivariance: a plain `def` of class type,
  deliberately neither reducible nor an instance.  LOAD-BEARING, keep.
- sorry: none.  No maxHeartbeats.
- Proofs >30 lines: 14+.  Largest `mem_rationalOpen_chartData_iff` (80),
  `wI_le_of_mem_locIdeal_pow` (75), `exists_teichCoeff_factor_high` (73),
  `mem_chartSubring_of_wI_le` (67)

## OPERATIONAL NOTE — "agent failed" != "work lost"
Workers stall in the REPLY stream after the artifact is already written.  ChartData's worker
reported failure but its artifact was complete (773 lines, File Summary present, last entries
matching the last source decls).  RECOVERY PROCEDURE: on any worker failure, first check
`inventory/<File>.md` for entry count vs source declaration count and for a `### File Summary`
section; extract the summary from the artifact with
`sed -n '/### File Summary/,$p' <file>`.  Only relaunch (in RESUME mode, continuing from the
last covered declaration) if the artifact is genuinely partial.

## IntervalRing.lean — 99 decls (14 defs, 82 theorems, 3 instances), 1844 lines
Kedlaya's interval rings `B^I`: realized as the topological closure of the diagonal image of
`Bloc` inside `hatK rho1 x hatK rho2`, with `lambda_I = max{lambda_rho1, lambda_rho2}` induced
coordinatewise.  Core is the three-circles Lemma 4.4 (termwise on Gauss terms -> Gauss values
-> Bloc), giving Cor 4.5 and a wI-Lipschitz estimate that extends the endpoint maps to `resI`
and `resIHom` (Cor 4.6).  Endgame identifies powers of (p) in the unit ball with the
two-coordinate valuation balls, giving the pair of definition and Huber/Tate.
- Key API: `wI` (~90 sites), `BISub` (~80), `BIPlusIn` (~31), `pImage` (~30), `BIProd` (28)
- **GENUINELY DEAD (12, verified 1 ref = own defn, instances excluded)**: `BISub_fst_mem`,
  `BISub_snd_mem`, `BIProd_injective`, `mem_BIPlus_iff`, `BIPlus_le_BISub`, `wI_pow_le_one`,
  `wI_pow_eq_one_iff`, `tendsto_wI_p_pow`, `wI_le_of_approx`, `isComplete_BIPlus`,
  `wI_p_pow_mul_le`, `p_pow_smul_ball_eq`
- NOT dead despite 1 ref: `isHuberRing_BISub`, `isTateRing_BISub`,
  `instIsTopologicalRingBIPlusIn` — INSTANCES, found by resolution not by name
- sorry: none.  set_option: none.
- Proofs >30 lines: 9.  Largest `mem_pIdeal_pow_iff` (68), `wLoc_rpow_interpolate` (59),
  `resIHom` (53)

## METHOD NOTE — dead-code test must exclude instances
An `instance` with a single textual reference (its own declaration) is NOT dead: it is
consumed by typeclass resolution, never by name.  The same applies to `@[simp]` lemmas
consumed by the simp set.  Any Step-8 junk verdict must check the declaration KIND before
concluding.  Three IntervalRing instances would have been wrongly deleted by a naive count.

## ArCompletion.lean — 58 decls (13 defs, 2 abbrevs, 43 theorems), 1787 lines
Kedlaya's completed rings `A^r` (Def 2.4): the Gauss valuation on A_inf has trivial support so
extends to `K = Frac(A_inf)`; `ArSub` is the closure of `Aloc = A_inf[1/[w]]` in the valued
completion `hatK`, hence complete.  A c0-style parametrization: `PhiHatK b = sum p^n [b_n]`
converges iff `rho^n |b_n| -> 0`, `teichCoeffAr` extracts the coordinates as limits, and the
two are mutually inverse.  Payoff is Kedlaya (2.2.1) on the completion —
`valued_eq_iSup_teichCoeffAr` — plus attainment at a dominating index, so degree exists.
- Key API: `hatK` (28), `Aloc` (25), `AlocToHatK` (18), `alocToWittF` (16), `wAloc` (16),
  `ArSub` (12), `prefixAloc` (11).  Load-bearing bridges: `valued_AlocToHatK`,
  `gaussValueF_alocToWittF`, `tendsto_teichCoeffAr` — almost every later proof factors
  through one of them.
- Unused in-file (8, all exported API not dead code): `BrSub`, `gaussTerm_teichCoeffAr_le`,
  `wAloc_alocTeich`, `exists_finite_teichmuller_sum_close`, `wAr_apply`,
  `exists_valued_eq_teichCoeffAr`, `teichCoeffAr_PhiHatK`, `teichCoeffAr_zero`
- sorry: none.  set_option: none — *no heartbeat bump despite a 197-line proof*.
- Proofs >30 lines: 14 (~24% of decls).  Largest `PhiHatK_teichCoeffAr` (197),
  `exists_finite_teichmuller_sum_close` (124), `valued_PhiHatK` (106)
- ***STRONGEST API-EXTRACTION FINDING (Step 7).*** Three preambles repeat VERBATIM and
  account for most of the long-proof bulk:
  1. the `z0 = toHatK (p^N)` / `gamma = Units.mk0 ...` value-group block — **4 copies, ~25
     lines each (~100 lines)**
  2. the `u*[w]^k = a` localization-and-cancel-`c^k` preamble — **7 copies**
  3. the `B <= (c^-1)^m` value cap (2 copies) and the `BddAbove`-from-`c0` block (2 copies)
  Extracting these three helpers should remove 200+ lines AND shrink the decompose targets.
