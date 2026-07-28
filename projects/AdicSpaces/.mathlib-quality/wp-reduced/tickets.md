# Ticket Board — WP (weighted-parity rationally-stably-reduced example)

**Statements are canonical in the Lean skeleton** (`projects/AdicSpaces/Adic
spaces/WP/*.lean`, all `:= by sorry`, build green at commit `36f0f3250`): a ticket =
"fill the named sorries", statement changes forbidden (B2-stop if a statement proves
wrong — log to `../b2_log.jsonl` and stop).  Every skeleton docstring carries its
[WP] source locator; verbatim quotes in `wp-reduced/paper-extraction.md`; route
detail + verified-infrastructure citations (exact file:line) in
`wp-reduced/decomposition.md` — tickets below cite both instead of repeating them.
Base conventions: worktree `/Users/mcu22seu/Documents/GitHub/aintlib-adic-fjp`,
branch `wp/reduced-example`.  Build one target at a time
(`lake build '«Adic spaces».WP.<File>'`); verify with `#print axioms` (only
propext/Classical.choice/Quot.sound) before marking done.

## Summary
- Work tickets: 24 (W1–W24, R1–R4 folded in numbering below) + 6 cleanup/milestone
- Open: all | In progress: 0 | Done: 0
- Parallel capacity at start: W1, W2, W14, R1 (4 workers)
- Endpoint staging: E1 = {…W6}, E2 = {…W23}, E4 = {…W20} independent of E3-final;
  HRW gated behind consult (HRW-0)

## Tickets

### [W1] Weight.lean — the parity-weight combinatorics
- Status: done (2026-07-28; all 21 sorries filled + 3 helper lemmas
  `wpWeight_eq_sum_subset`/`wpWeight_update_zero`/`wpWeight_filter_split` +
  `TailIdx.prop`; build green 888 jobs; axioms clean on 4 spot-checks; Phase-6.5
  cleanup deferred by board design to CLEANUP-1)
- Progress: 2026-07-28: proofs via superset-sum normalization + split_ifs/subst_vars/
  omega pattern; gotcha: omega cannot substitute `n = 0` inside atoms `t n` —
  subst_vars required; `tailShift` fold/unfold atom alignment needed in
  headPart_of_headMem_add. | File: WP/Weight.lean | Depends: none | Parallel: yes | Type: lemmas
- Decls: all 21 sorries (`wpWeight_zero…wpWeight_shiftWeight_zero`, `WPMem.*`,
  `HeadMem.*`, `tailIdxSubmonoid`, `wpMem_tailShift`, `headPart_*`, `tailPart_*`).
- Sketch: unfold `wpWeight` as a support-sum with if-then-else; parity case analysis
  via `Nat.add_mod`/`Nat.odd_iff`; subadditivity: (s+t)ₙ odd ⇒ exactly one of sₙ,tₙ
  odd; disjoint additivity via `Finsupp.support_add_eq`/sum over disjoint union;
  splitting laws by `Finsupp.ext` + `filter_apply`/`update` case analysis (n = 0,
  n ≤ N, n > N).  Mathlib: `Finsupp.filter_apply(_pos/_neg)`, `support_filter`,
  `filter_add_filter_not` (Basic:725), `prod_filter_mul_prod_filter_not` (:710),
  `Finsupp.update`, `Finset.sum_ite_eq'`.  Sources: [WP] 687–703, 1014–1029
  (quotes in paper-extraction §6.1/§6.4).  Generality: arbitrary `w : ℕ → ℕ`.

### [W2] RestrictedComplete.lean — infinite-σ analytic base
- Status: done (2026-07-28; all 8 sorries filled + helpers `prod_one_weights`/
  `prod_weights_pos`; the ~110-line completeness port ran exactly per the recipe;
  build green incl. full WP tree; axioms clean ×3; cleanup deferred to CLEANUP-1)
- Progress: 2026-07-28: gotchas — `IsRestrictedGauss` is a def (no equation rewrites:
  use `show`/typed `have` with the Tendsto form); IsAbsoluteValue field is `abv_mul'`
  (primed); `lipschitzWith_iff_dist_le_mul` + `NNReal.coe_one`; `MvPowerSeries.mk`
  not needed — the series IS the coefficient function.
- Decls: `isCompleteSpace_general`, `normOneClass_one`, `norm_coeff_le_one_norm`,
  `lipschitzWith_coeff`, `continuous_coeff`, `finite_setOf_le_norm_coeff`,
  `isClosed_setOf_coeff_eq_zero`, `norm_restricted_mul_general`.
- Sketch: port `Restricted.isCompleteSpace` (CoramRestrictedNorm:257) — the six-step
  coefficientwise-Cauchy proof is index-uniform (decomposition.md quotes the port
  recipe; ~120 lines); NormOne: sup attained at t = 0 with weight ∏1 = 1 (generalize
  RestrictedGaussAdic:39-45 `finsupp_prod_one`); coefficient API mirrors
  RestrictedGaussAdic:199/207 via `MvPowerSeries.le_gaussNorm` +
  `MvRestricted.hasGaussNorm`; closedness: intersection of kernels of the
  continuous coefficient functionals (`isClosed_iInter`, `isClosed_eq`);
  multiplicativity: wrap `MvRestricted.isAbsoluteValue` (CoramMvRestrictedNorm:270)
  `.abv_mul` at `hnorm := norm_mul`.  Generality: arbitrary σ; c ≡ 1 where stated.

### [W3] Algebra.lean I — the support subring 𝒜 and its coefficient API
- Status: done (2026-07-28; Algebra.lean now 0 sorries — W4's instance block folded in;
  build green full WP tree; axioms clean; cleanup deferred to CLEANUP-1)
- Progress: gotchas — antidiagonal membership via `Finset.HasAntidiagonal.
  mem_antidiagonal` (export alias mismatches the instance form); `subst`-style if_neg
  proofs beat `▸`; `Real.mul_iSup_of_nonneg` needs the iSup pre-shaped by iSup_congr. | File: WP/Algebra.lean | Depends: W1, W2 | Parallel: after deps
- Decls: `wpSupport` (5 closure fields), `isClosed_wpSupport`, `coeffA` laws
  (`coeffA_of_not_wpMem`, `norm_coeffA_le`, `norm_eq_iSup_coeffA`,
  `coeffA_injective`), `wpMonomial` (+`coeffA_wpMonomial`, `norm_wpMonomial`),
  `Wa/Ya/Za` (already defined via wpMonomial), `constA`, `norm_constA`,
  `norm_constA_mul`, `mem_unitBall_iff_forall_coeffA`.
- Sketch: mul_mem' via `MvPowerSeries.coeff_mul` (antidiagonal sum; every summand
  dies unless both factors' exponents allowed, then use `WPMem.add`'s
  contrapositive); closedness by W2's `isClosed_setOf_coeff_eq_zero`; monomial =
  `⟨MvPowerSeries.monomial t c, isRestrictedGauss_monomial, support-check⟩`;
  constA = monomial at 0 (RingHom fields by `Subtype.ext` + coeff extensionality;
  the JetRings:521 `constA` route); norm lemmas coefficientwise from
  `norm_eq_iSup_coeffA` + `norm_mul` of K.  Sources: [WP] 705–730.

### [W4] Algebra.lean II — instance stack
- Status: done (2026-07-28, folded into the W3 pass: piW lemmas one-liners off constA;
  norm-window Huber/Tate instances with inlined exists_norm_window'; maximal
  PlusSubring + isRingOfIntegralElements_powerBounded verbatim from the JetA block) | File: WP/Algebra.lean | Depends: W3 | Type: instances
- Decls: `NormOneClass (WPA)`, `piW` lemmas (norm/lt_one/pos/isUnit/mul),
  unconditional `IsHuberRing/IsTateRing (WPA)`, `PlusSubring`,
  `IsRingOfIntegralElements (ringPlus)`.
- Sketch: piW lemmas from W3's constA lemmas + `Uniformizer` API (CDVFBase:98-124);
  unconditional Huber/Tate via a norm-window element (Functoriality:160-206 pattern,
  `exists_norm_window`); PlusSubring := `⟨powerBoundedSubring.toSubring _⟩` +
  `isRingOfIntegralElements_powerBounded` (FiniteJetRings:868) — copy the JetRings
  711-755 block including the rightUniformSpace CompleteSpace 4-liner (already real
  in skeleton).  Gotcha: NonarchimedeanAddGroup instance — find the
  ultrametric-normed route used by JetA (recon gotcha list).

### [CLEANUP-1] /cleanup on WP/Weight.lean + WP/RestrictedComplete.lean + WP/Algebra.lean
- Status: open | Depends: W4 (and W1, W2) | Type: cleanup

### [W5] UniformDomain.lean — uniform + domain + 𝒜° = 𝒜₀
- Status: done (2026-07-28; all 8 filled, FJP patterns adapted verbatim; endpoint
  thm 6.2(1) uniform/domain/𝒜°=𝒜₀ now fully proven; axioms clean) | File: WP/UniformDomain.lean | Depends: W3, W4 | Parallel: with W6, W7
- Decls: `norm_amb_mul`, `norm_wpa_mul`, `norm_wpa_pow`, `Nontrivial`,
  `NoZeroDivisors`, `isPowerBounded_wpa_iff`, `powerBoundedSubring_eq_unitBall`,
  `isUniform_WPA`.
- Sketch: exactly the FJP UniformDomain route (decomposition.md E1; patterns at
  FJP/Over/UniformDomain.lean:50-168 with `isPowerBounded_of_norm_le_one`
  Functoriality:325 and `pow_unbounded_of_one_lt`); expect
  `set_option maxHeartbeats 1000000` on the two heavy ones (FJP precedent).
  Sources: [WP] 789–811.

### [W6] Nonnoetherian.lean — ψ_m and the ideal chain
- Status: done (2026-07-28; all 5 filled + helpers not_wpMem_single_odd/psiCoeff/
  psiHom_apply_coeff/two_nsmul_single_eq/stage_ideal_mono; ψ multiplicativity via
  antidiagonal_single + even/odd filter + halving nbij; nonnoetherianity by
  finite-stage bounds. Endpoint thm 6.2(1) nonnoetherian PROVEN. Axioms clean.)
- Progress: gotchas — `Finset.antidiagonal`/`mem_antidiagonal` ambiguous in this
  import scope (an IsPWO-flavoured constant shadows): qualify as
  `Finset.HasAntidiagonal.antidiagonal`/`.mem_antidiagonal`; evaluate Finsupp
  equalities at the RIGHT index (j, not m+1) for the Za_of_le contradiction;
  `Submodule.mem_span_finite_of_mem_span` returns a Finset pair. | File: WP/Nonnoetherian.lean | Depends: W3 | Parallel: yes
- Decls: `psiHom`, `psiHom_Za_succ_ne_zero`, `psiHom_Za_of_le`,
  `Za_succ_notMem_span`, `not_isNoetherianRing_WPA`.
- Sketch: define ψ on coefficients (f ↦ series with n-th coefficient =
  coeffA (2n·δ_{m+1}) f); RingHom: additivity coefficientwise; multiplicativity via
  the monoid-ideal argument (decomposition.md adversarial log: odd U_{m+1}-exponent
  forces W-content via `hw`); membership: apply ψ to a span representation
  (`Ideal.mem_span_image`-style elimination, `Finsupp.total`/`Ideal.span` induction);
  conclude with the non-f.g. ideal ⋃(Za-chain) or `WellFoundedGT` violation
  (`isNoetherianRing_iff`/`monotone_stabilizes`).  Sources: [WP] 813–834.

### [W7] Heads.lean I — head subring, T_N, free normal form
- Status: done (2026-07-28; all W7 decls proven across 6 commits: subring+instances,
  even-head monoid + unhalve/halve, the halving ring iso evenSupportEquiv (ofBijective)
  + isometry, patExp/Ypat, the parity-slice decomposition sum_slice_mul_Ypat, and
  moduleFinite_head_over_even. Remaining Heads.lean sorries are W8-scope.)
- Progress: gotchas — def-alias types (Amb/Restricted) block SetLike/AddSubmonoidClass
  rewrites: route sums through explicit double-val RingHoms + map_sum; Fin-mk iota
  vs omega: obtain ⟨i, rfl⟩ reindexing beats mk-instantiation; decide-orientation:
  (decide_eq_false h).symm. | File: WP/Heads.lean | Depends: W3, W4 | Parallel: with W5, W6
- Decls: `wpHeadSupport` fields, `wpHeadSupport_le_wpSupport`, `_mono`, `headIncl`,
  `norm_headIncl`, `isClosed_wpHeadSupport`, `NormOneClass`, `constHead`, `piHead`
  lemmas, unconditional `IsHuberRing/IsTateRing`, `PlusSubring`, `IsROIE`,
  `wpEvenSupport` fields, `evenSupportEquiv`, `norm_evenSupportEquiv`,
  `moduleFinite_head_over_even`.
- Sketch: head subring/instances = W3/W4 verbatim with `HeadMem`;
  `evenSupportEquiv`: coefficient reindex along the exponent bijection
  (a,2ν) ↔ (a,ν) into `P K (N+1)` = MvRestricted (Fin (N+1)) — construct both
  directions coefficientwise, ring-hom by support convolution match, isometry by
  sup-reindex; module-finiteness: generators {Y^ε}_{ε∈{0,1}^N} =
  ∏ (Ya n)^{ε n} — every head monomial factors as even-part · Y^ε
  (eq:parity-factorization, headPart machinery from W1); `Module.Finite` via
  `Finset.span` of the 2^N basis (`Module.Finite.of_surjective` from a finite free
  cover).  Sources: [WP] 739–787 (route change documented, decomposition.md E2).

### [W8] Heads.lean II — noetherian, strongly noetherian, sheafy, dense
- Status: done (2026-07-28: Heads.lean ZERO sorries. isNoetherianRing_WPHead +
  unit-ball version (ball slices) + isStronglyNoetherian_WPHead (per-k: generalized
  scale-bundle P-noetherianity isNoetherianRing_P_of_scale + mvRestrictedCongr
  isometric transport + per-k slice module-finiteness moduleFinite_P_head_over_even)
  + isSheafy_WPHead (828b) + exists_head_approx. All axiom-clean, build 3163 green.)
- (superseded progress note: 2026-07-28: isNoetherianRing_WPHead DONE (equiv transport +
  of_finite, axiom-clean); exists_head_approx density DONE (superlevel truncation).
  REMAINING 3 sorries: isNoetherianRing_unitBall_WPHead (ball-level slice argument —
  mirror sum_slice_mul_Ypat with norm-1 generators over unitBall(even) after
  isNoetherianRing_unitBall_of_isometry transport of Uniformizer.
  isNoetherianRing_unitBall_P), isStronglyNoetherian_WPHead (per-k: restrictedGauss
  bridge + generalize CDVFNoetherian's isNoetherianRing_P to arbitrary scale-bundle
  base + MvRestricted-congr along isometric isos + coefficientwise slices), and
  isSheafy_WPHead (828b assembly: haveI IsStronglyNoetherian + the ambient letI
  ceremony per isSheafy_of_stronglyNoetherian_828b).) | File: WP/Heads.lean | Depends: W7, W5 | Type: theorems
- Decls: `IsDomain (WPHead)`, `isNoetherianRing_WPHead`,
  `isNoetherianRing_unitBall_WPHead`, `isStronglyNoetherian_WPHead`,
  `isSheafy_WPHead`, `exists_head_approx`.
- Sketch: domain by isometric-subring norm multiplicativity (W5's `norm_amb_mul`);
  noetherian: `IsNoetherianRing.of_finite` (verified, Noetherian/Basic:341) over
  `evenSupportEquiv`-transported `P K (N+1)` (noetherian:
  `Uniformizer.isNoetherianRing_P` CDVFNoetherian:77); unit ball: transfer via
  `isNoetherianRing_unitBall_of_isometry`/`_of_section`
  (FiniteJetNoetherianVertices:311/323) + `Uniformizer.isNoetherianRing_unitBall_P`;
  STRONG: for each k, `restrictedMvPowerSeriesSubring k (WPHead)` ≅
  (`restrictedGaussEquiv` ExampleUnitDisc:112) MvRestricted (Fin k) over WPHead ≅
  finite free module over MvRestricted (Fin k) over T_N ≅ (Fubini/reindex —
  `MvRestricted.finSuccEquiv` chain or a direct coefficient reindex)
  `P K (N+1+k)`-model — then `.of_finite` again; per-k, never from bare
  noetherianity (B2 guard); sheafy: `isSheafy_of_stronglyNoetherian_828b`
  (WedhornCechAcyclicity:13481) with the ambient bundle from W7 instances;
  density: ϖ-power truncation — finitely many coefficients ≥ ε := ‖ϖ‖^ℓ‖f‖ (W2's
  `finite_setOf_le_norm_coeff`), all with bounded variable-index; subtract.
  Sources: [WP] 732–787, 1131–1140.

### [CLEANUP-2] /cleanup on WP/UniformDomain.lean + WP/Nonnoetherian.lean + WP/Heads.lean
- Status: open | Depends: W5, W6, W8 | Type: cleanup

### [W9] Tail.lean I — tail coefficients on 𝒜
- Status: done | File: WP/Tail.lean | Depends: W7, W1 | Parallel: with W10
- Progress: DONE 2026-07-28.  All per sketch; `tailCoeff` built by the slice
  superlevel pattern (gate `if HeadMem` + `finite_setOf_le_norm_coeff` preimage
  along `add_left_injective (tailShift w μ)`).  Extra API: unconditional
  `coeff_tailCoeff` (rfl), `tailShift_zero`, `coeff_tailCoeff_zero`,
  `tailCoeff_zero_map/one/mul` feeding the `rhoHead` RingHom fields.  eTail laws
  via mathlib `MvPowerSeries.coeff_mul_monomial`/`coeff_add_mul_monomial`/
  `monomial_mul_monomial`/`X_pow_eq` (all exist) + the V double-subtype RingHom
  (map_pow) for `(WaHead^k).1.1`.  GOTCHAS: Finsupp-apply `show` needs the
  `( ... : ℕ →₀ ℕ) n` ascription; simp normalizes `if 0 = 0` to `if True` (use
  `if_true` not `if_pos rfl`); `headIncl_WaHead` and `rhoHead_apply` are rfl.
  Axioms clean on all 6 headliners.
- Decls: `tailCoeff` (+`coeffA_tailCoeff`, `_add`, `norm_tailCoeff_le`,
  `tendsto_norm_tailCoeff_cofinite`, `norm_eq_iSup_tailCoeff`,
  `tailCoeff_injective`), `eTail` laws (`tailCoeff_headIncl_mul_eTail`),
  `WaHead`, `headIncl_WaHead`, `eTail_mul`, `rhoHead` (+3 laws).
- Sketch: tailCoeff = the series with head coefficients read at
  `h + tailShift μ` (W1 splitting); membership/restrictedness from f's; null family:
  the map μ ↦ (sup over its head coeffs) is dominated by f's coefficient family via
  the splitting bijection + `finite_setOf_le_norm_coeff`; eTail_mul by coefficient
  comparison + `wpWeight_add_of_disjoint`; rhoHead multiplicative by the
  monoid-ideal argument (tail-content absorbs).  Sources: [WP] 1014–1034.

### [W10] Tail.lean II — the TailC0 ring
- Status: open | File: WP/Tail.lean | Depends: W1, W2 | Parallel: yes
- Decls: TailC0 `CommRing`, `NormedCommRing`, `IsUltrametricDist`, `CompleteSpace`,
  `NormOneClass`, `single` (+`coeff_single`), `single_mul_single`,
  `norm_eq_iSup_coeff`, `ofHead/toHead` (+laws).
- Sketch: convolution over `Finsupp.antidiagonal μ.1` restricted to tail pairs
  (finite); c₀-closure + submultiplicativity need `TwistElem.norm_le_one`;
  associativity via the twist cocycle (decomposition.md adversarial log);
  completeness = the W2 c₀ argument verbatim (coefficientwise Cauchy).
  Generality: any normed ultrametric commutative P.  Sources: [WP] 1021–1029.

### [W11] Tail.lean III — the Φ-embedding
- Status: open | File: WP/Tail.lean | Depends: W10, R1 | Type: def+theorems
- Decls: `tailIdxEquivFinsupp`, `tailC0ToMvPowerSeries`,
  `tailC0ToMvPowerSeries_injective`, `isReduced_tailC0`, `isDomain_tailC0`.
- Sketch [ChatGPT-5.6 review: D3/D4 confirmed; `MvPowerSeries.map_injective`
  exists vendored — use it]: reindex tails to `TailVar N →₀ ℕ`
  (`Finsupp.subtypeDomain/extendDomain`, Basic:778/1222); Φ coefficient at
  μ := ρ^{ω(μ)}·x_μ; multiplicative by twist
  absorption (Φ(xy)_τ = ρ^{ω(τ)}·(xy)_τ — expand both sides over the antidiagonal);
  injective given ρ-regularity (cancel ρ^{ω(μ)} by induction on the power);
  reduced/domain by `isReduced_of_injective` + R1 / mathlib
  `NoZeroDivisors (MvPowerSeries σ R)` (NoZeroDivisors:141).
  Sources: [WP] 1286–1297, 917–926.

### [W12] Perturbation.lean I — data, rationality, subsets
- Status: open | File: WP/Perturbation.lean | Depends: W3, W4 | Parallel: with W9-W11
- Decls: `podCongrEquiv` (+3 laws), `PerturbSetup.datum` (+`datum_T`, `datum_s`),
  `datum_isRational`, `rationalOpen_datum`, `exists_integral_bezout`.
- Sketch: podCongr — SEARCH FIRST (`CompletionModelIndependence`,
  `PresheafIdentification`, `TopologyComparison`): two pods of a Tate ring are
  commensurable ⇒ same locTopology ⇒ identity descends bicontinuously; datum :=
  ⟨unitBallPod bundle, T.image pert, pert s, genPiece_hopen (primed span-top)⟩;
  primed Bezout: ∑ a·pert = t^ℓ(1 + tH), `1 + tH` unit by geometric series
  (`IsUnit` via norm < 1 in a complete ring, ultrametric geometric series —
  Units.oneSub-style in complete normed ring); rational subset equality: pointwise
  vle estimates ([WP] 979–987 route; Spa-point calculus from
  AdicSpectrum/RationalSubsets — `Spv.vle` toolkit); Bezout existence: IsRational ⇒
  span T = ⊤ ⇒ 1 = finite combination; scale by t^ℓ to push coefficients into the
  unit ball (norm-window archimedean argument).  Sources: [WP] 949–987.

### [W13] Perturbation.lean II — the localization isomorphism
- Status: open | File: WP/Perturbation.lean | Depends: W12 | Type: def+theorems
- Decls: `PerturbSetup.equiv` (+`_continuous`, `_symm_continuous`,
  `_canonicalMap`).
- Sketch: [WP] 989–1010: q := t^ℓ/g ∈ E_α power-bounded; g'/g = 1 + t·h₀q a 1-unit
  with power-bounded inverse; `IsLocalization.Away.lift` at the unit image of the
  primed s + completion extension (`UniformSpace.Completion.extensionHom`), each
  direction; continuity via the locTopology lift criterion (the chartFwd pattern
  Chart.lean:796 — `locTopology_continuous_lift`-style lemma, search
  PresheafIdentification); composites fix the dense image of E ⇒ inverse by
  `Completion` uniqueness.  Sources: [WP] 989–1010.

### [W14] Evaluation.lean — summability + restrictedEval
- Status: open | File: WP/Evaluation.lean | Depends: none | Parallel: yes (early)
- Decls: `summable_of_tendsto_cofinite_nonarch`, `restrictedEval` (+`_C`, `_X`,
  `_continuous`, `_unique`).
- Sketch: SEARCH FIRST `Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`
  (cofinite-null ⇒ summable in complete nonarch groups; if absent: Cauchy-net
  criterion via `NonarchimedeanAddGroup.nhds_zero_basis` subgroups); eval F :=
  ∑' t, φ(c_t)·b^t — the family is null (coefficients null + {b^t} bounded via
  joint power-boundedness ∏ bounds); RingHom: multiplicativity via Cauchy-product
  rearrangement (`tsum_mul_tsum`-style for nonarch/absolute summability — search;
  fallback: prove on the dense polynomial subring + continuity); uniqueness by
  density of polynomials (`polyToP` image dense — [FJP] (4.4) trnc machinery,
  RestrictedGaussAdic:264).  Generality: complete T2 nonarch topological comm ring
  target.  Sources: [WP] 176–181; Huber (1.2).

### [CLEANUP-3] /cleanup on WP/Tail.lean + WP/Perturbation.lean + WP/Evaluation.lean
- Status: open | Depends: W9–W14 | Type: cleanup

### [W15] CoeffLocalization I — the QHead normed quotient
- Status: open | File: WP/CoeffLocalization.lean | Depends: W8 | Type: def+instances
- Decls: `datumEnum`, `TailC0.map` (+2 laws), QHead `NormedCommRing`,
  `IsUltrametricDist`, `CompleteSpace`, `rhoQ`.
- Sketch: datumEnum := `(Finset.equivFin _).symm`-flavoured choice; graph ideal
  closed at the head: `isClosed_graphIdeal` (FiniteJetGraphKoszul:1303) with
  hypotheses from W8 (`isNoetherianRing_unitBall_WPHead`, strong noetherianity ⇒
  `IsNoetherianRing (P (WPHead) m)` via the k-instance + restrictedGaussEquiv);
  quotient norm: mathlib normed-group quotient (`Mathlib.Analysis.Normed.Group.
  Quotient`) + ring submultiplicativity for the closed-ideal quotient (SEARCH
  `Mathlib.Analysis.Normed.Ring.Quotient`-flavoured; else prove the 3 axioms
  directly on `Quotient.norm`); completeness of quotient of complete by closed
  subgroup (mathlib); rhoQ := image of `polyToP (C WaHead)` with `norm ≤ 1` from
  quotient-map nonexpansiveness.  Sources: [WP] 1057–1064, eq:graph-model 172–175.

### [W16] CoeffLocalization II — the head bridge
- Status: open | File: WP/CoeffLocalization.lean | Depends: W15, W14
- Decls: `headLocEquiv` (+`_continuous`, `_symm_continuous`).
- Sketch: s is a unit in QHead ([WP] Bezout trick, lem:koszul proof 427–432:
  t^ℓ = s·(a₀ + ∑ a_i T_i) mod the graph ideal, t a unit); fwd :=
  `IsLocalization.Away.lift` into QHead + `Completion.extensionHom` (continuity via
  the locTopology criterion — chartFwd pattern); rev := W14's `restrictedEval` at
  φ := canonicalMap ∘ headIncl-of-scalars…, b_i := divByS(t_i) images (power-bounded
  by the HasLocLift layer / `isPowerBounded_of_norm_le_one`), then quotient-descend
  (relations die: s·(t_i/s) − t_i = 0 in presheafValue) via `Ideal.Quotient.lift` +
  closure (`RingHom.continuous_quotient_lift`-style); composites = id on dense
  images.  Sources: [WP] 149–181, 1057–1064.

### [W17] CoeffLocalization III — the coefficientwise model over 𝒜
- Status: open | File: WP/CoeffLocalization.lean | Depends: W16, W9, W10
- Decls: `liftDatum` (+`_T`, `_s`, `_isRational`), `coeffLocEquiv` (+`_continuous`,
  `_symm_continuous`, `coeffLocEquiv_canonicalMap_headIncl`).
- Sketch: the heart ([WP] 1054–1095; decomposition.md E2). Key steps: (i) tail
  decomposition of 𝒜⟨T⟩-analogue with head 𝒜_N⟨T⟩ (W9 machinery at the datum
  arity); (ii) graph ideal over 𝒜 closed + coefficientwise: given null (y_μ) in the
  head ideal, `exists_d1_lift_pow` (KoszulStrictClosed:254, hypotheses from W8/W15)
  gives uniform-h lifts ⇒ reassembled null lift; (iii) quotient ≅ TailC0 (QHead)
  (per-coefficient quotient + W10 norms; eq:c0-quotient); (iv) bridge to
  presheafValue (liftDatum): fwd IsLocalization lift + completion, rev via W14 at
  the TailC0 target (ofHead ∘ head-rev per coefficient + summability W14).
  Sources: [WP] 1036–1095.

### [W18] CoeffLocalization IV — every localization has finite-head form
- Status: open | File: WP/CoeffLocalization.lean | Depends: W17, W13
- Decls: `nonempty_headModelData` (via `HeadModelData`).
- Sketch: [WP] 1107–1127: scale D's entries into the unit ball (podCongr + Bezout
  scaling from W12); `exists_head_approx` (W8) at precision ℓ+1; PerturbSetup with
  pert := head approximation; ρ_N-retract the primed Bezout ⇒ head datum rational
  (`rhoHead` ring hom, W9); e := coeffLocEquiv ∘ perturb.equiv ∘ podCongrEquiv;
  hopen from `rationalOpen_datum` + `liftDatum` matching.  Sources: [WP] 1107–1127.

### [CLEANUP-4] /cleanup on WP/CoeffLocalization.lean
- Status: open | Depends: W18 | Type: cleanup

### [W19] Chart.lean I — datum, head model, domain, reduced
- Status: open | File: WP/Chart.lean | Depends: W15, W16, W17, W11
- Decls: `chartHeadDatum` (+`_T`, `_s`, `_isRational`), `chartQHeadEquiv`
  (+`_norm`), `isDomain_chartQHead`, `isDomain_chart`, `isReduced_chart`.
- Sketch: datum := ⟨unitBallPod (piHead-bundle), {WaHead, piHead}, piHead,
  genPiece_hopen⟩ (span-top from `isUnit_piHead` — [WP] 838); chartQHeadEquiv: at
  N = 0 the head is the even+head support ⇒ ≅ K⟨W⟩ (evenSupportEquiv at N = 0-ish);
  QHead = K⟨W⟩⟨X⟩/(ϖX − W) ≅ K⟨X⟩ by W ↦ ϖX (univariate rescale — FJP
  rescaleRestricted FiniteJetChart:82 + the division identity [WP] 885–905 for the
  isometry); domain: P K 1 Gauss-multiplicative (W2's
  `norm_restricted_mul_general` at σ = Fin 1) ⇒ transport; chart domain/reduced:
  `isDomain_tailC0`/domain ⇒ reduced through `coeffLocEquiv` at N = 0 + ρ ≠ 0
  regular in a domain.  Sources: [WP] 857–926.

### [W20] Chart.lean II — nonuniformity and ¬stable-uniformity
- Status: open | File: WP/Chart.lean | Depends: W17, W19
- Decls: `not_isUniform_chartModel`, `not_isUniform_chart`
  (`not_isStablyUniform_WPA` is already real in the skeleton).
- Sketch: T_n := `TailC0.single δ_n (c_n)` with c_n := (chartQHeadEquiv⁻¹ of the
  scalar ϖ^{−w n}); powers via `single_mul_single` + `chartQHeadEquiv_norm`
  (eq:Tn-power-norms — even powers norm 1, odd norm |ϖ|^{−w n}); power-bounded
  (norms ≤ |ϖ|^{−w n} uniformly in the power); family unbounded: for any candidate
  bounded V and scale, pick n with w n large (hwu) so ϖ^N·T_n ∉ unit-ball lattice
  ([WP] 939–943); transport along `coeffLocEquiv` (+continuity both ways) via
  `isUniform_of_ringEquiv` (FiniteJetChart:1537).  Sources: [WP] 928–943.

### [W21] Sheafy.lean I — the embedding field
- Status: open | File: WP/Sheafy.lean | Depends: W18 | Parallel: with W22
- Decls: `productRestrictionSub_isEmbedding_WPA`.
- Sketch: injectivity: a section vanishing on all pieces has all coefficientwise
  head restrictions vanishing on the pushed head cover (W18 models + head
  separation from `isSheafy_WPHead`.separationSub); topological-embedding upgrade
  via `sectionEqualizer_isClosed` (StructureSheaf:271) +
  `isInducing_of_closedRange_of_topNilpUnit` (WedhornBanachTheorem:437) +
  `presheafValue_uniformity_isCountablyGenerated` (StructureSheaf:309) — the FJP
  embedding assembly (SheafTransfer:667) with the c₀-model in place of the Milnor
  pair.  Sources: [WP] 1135–1218.

### [W22] Sheafy.lean II — the gluing field
- Status: open | File: WP/Sheafy.lean | Depends: W18
- Decls: `gluing_WPA`.
- Sketch: [WP] 1156–1218 (decomposition.md E2): common head for the whole cover
  (finitely many data — iterate W18's perturbation with a common M); cover transfer
  to Spa(P_M, P_M°) via the split surjection (norm-nonincreasing ρ_M/ι pair ⇒
  Spa-map section — eq:split-spectrum-map; the paper's warning about higher-rank
  points: work with the restriction of the given cover to the maximal-pair
  subspace); head Čech: `isSheafy_WPHead`.gluing + embedding give a continuous
  bijection onto the closed equalizer ⇒ bounded inverse C by the OMT bridge at the
  NORMED model (transport along headLocEquiv); glue per tail index μ with the
  C-bound (eq:coefficientwise-gluing-bound) ⇒ null glued family ⇒ TailC0 element ⇒
  pull back along coeffLocEquiv; uniqueness from W21.  Expect maxHeartbeats bumps
  (FJP gluing needed 6400000).  Sources: [WP] 1156–1218.

### [W23] Sheafy.lean III — wrappers
- Status: open | File: WP/Sheafy.lean | Depends: W21, W22 | Type: theorems
- Decls: `wp_isSheafyFor`, `wp_isSheafyComplete`, `wp_structurePresheaf_isSheaf_all`.
- Sketch: verbatim the FJP wrapper chain (SheafyEndpoints:95/175/213):
  letI/haveI prefix; `isLimitSheaf_of_isSheafy` (SheafyPair:550);
  `isSheafyFor_iff_isSheafyComplete` (RelativeStandardRefinement:201);
  `isSheafyFor_structurePresheaf_isSheaf` (SheafyEndpoints:53).

### [W24] tateExtEquiv — the Tate-extension bridge
- Status: open | File: WP/Sheafy.lean | Depends: W3 | Parallel: yes (any time)
- Decls: `tateExtEquiv` (+ its topological refinement, to be STATED during the
  ticket per the in-file note: bicontinuity for `mvTateAlgebraTopology'`).
- [ChatGPT-5.6 review]: the bridge must be a topological/normed HUBER-PAIR-level
  identification (transporting the ring of definition / plus subring), not a bare
  ring iso; the c₀-Fubini/reindex isomorphism must be proved ISOMETRIC.
- Sketch: `restrictedGaussEquiv` (ExampleUnitDisc:112) at radius 1 over WPA reduces
  to MvRestricted (Fin s) over WPA; flatten: coefficientwise reindex
  (Fin s)-exponents ⊔ ℕ-exponents ≅ ℕ-exponents under the interleaving order-iso
  realizing `shiftWeight` (variables 1..s ↦ freed slots); support condition
  transported (freed slots weight 0).  This is the campaign's one pure-plumbing
  ticket; budget the Coram-Fubini idioms (maxSynthPendingDepth 8, maxHeartbeats).

### [R1] Reduced.lean I — MvPowerSeries reducedness (mathlib-grade)
- Status: open | File: WP/Reduced.lean | Depends: none | Parallel: yes (early)
- Decls: `mvPowerSeriesPi`, `exists_injective_pi_quotient`,
  `isReduced_mvPowerSeries`.
- Sketch: pi-equiv coefficientwise (`MvPowerSeries.coeff`/`Pi.ringHom`; ring-hom
  fields by `funext` + `coeff_mul` commuting with projections);
  embedding: `Pi.ringHom (Ideal.Quotient.mk ·)`, kernel = ⋂ primes = nilradical = 0
  (`nilradical_eq_sInf` Nilpotent/Lemmas:54, `nilradical_eq_zero`:66,
  `RingHom.injective_iff_ker_eq_bot`); assemble: `MvPowerSeries.map` injective ∘
  pi-equiv ⇒ product of `MvPowerSeries J (P/𝔭)` — each `NoZeroDivisors`
  (NoZeroDivisors:141) + Nontrivial ⇒ IsReduced; product reduced
  (Nilpotent/Defs:134); `isReduced_of_injective` (twice).  Mathlib-contribution
  candidate (`/mathlibable` after landing).

### [R2] Reduced.lean II — W-regularity of head localizations
- Status: open | File: WP/Reduced.lean | Depends: W15, W16
- Decls: `rhoQ_regular`.
- Sketch [ChatGPT-5.6 review: route confirmed characteristic-free; use
  `Module.Flat.isSMulRegular_of_isRegular`]: transport to presheafValue via
  headLocEquiv; there: multiplication by
  canonicalMap(WaHead) is injective — `prop_8_30_flat_clean_proof`
  (AuditCleanWrappers:113) with D := globalLocData (Presheaf:1141), D' := DH gives
  flatness of the restriction presheafValue(global) → presheafValue(DH);
  presheafValue(global) ≅ 𝒜_N-completion (already complete ⇒ ≅ 𝒜_N — the
  CompletionModel Remark 8.3 layer / `completionModelCompare`); W a nonzerodivisor
  in the head domain (W8); `Module.Flat.rTensor_preserves_injective_linearMap` on
  `lsmul WaHead`; adapter details in decomposition.md (adversarial log item).

### [R3] Reduced.lean III — conditional single-step reducedness
- Status: open | File: WP/Reduced.lean | Depends: W18, W11, R1, R2
- Decls: `isReduced_presheafValue_WPA`.
- Sketch: W18 model e : presheafValue D ≅ TailC0 (QHead DH); hred gives
  IsReduced (presheafValue DH) ⇒ (headLocEquiv transport) IsReduced (QHead DH);
  R2 ρ-regular; W11 `isReduced_tailC0`; pull back along e
  (`isReduced_of_injective` e.injective).  Sources: [WP] 1267–1297.

### [R4] Reduced.lean IV — chains
- Status: open | File: WP/Reduced.lean | Depends: R3, W18
- Decls: `chainReduced_WPA` (+ the transport helper it needs: ChainReduced along a
  bicontinuous ring iso with datum pushforward — state during ticket as a private
  lemma; datum transport via `RationalLocData` field-wise pushforward along e).
- Sketch: induction on n; n = 0: IsReduced (WPA) from domain (W5); step: a datum on
  WPA → R3 gives reducedness AND W18 gives the model for the NEXT stage — the
  induction invariant is "bicontinuously isomorphic to TailC0 over a head-loc of
  some head", closed under localization by re-running W18's argument at level M ≥ N
  (heads of E are P_M's — [WP] cor:finite-head-presentation naturality clauses
  1044–1052, 1123–1127).  If the invariant-class bookkeeping resists, fall back to
  strengthening R3's statement to "IsReduced ∧ Nonempty (HeadModelData-successor)"
  (B2-stop if neither lands — this is the one genuinely-new induction design).

### [CLEANUP-ALL-1] /cleanup-all over WP/ (pre-milestone)
- Status: open | Depends: all W/R tickets | Type: cleanup

### [M1] Milestone — endpoint verification sweep
- Status: open | File: WP/Main.lean | Depends: CLEANUP-ALL-1
- Do: full `«Adic spaces»` umbrella build; `#print axioms` on every Main.lean
  endpoint (expect exactly {propext, Classical.choice, Quot.sound}); zero sorries in
  WP/ EXCEPT none (HeadLocsReduced is a hypothesis, not a sorry); add
  `import «Adic spaces».WP.Main` to the umbrella root `Adic spaces.lean`; record a
  final report in `wp-reduced/` (FJP K12 pattern).

### [CLEANUP-FINAL] /cleanup-all
- Status: open | Depends: M1 | Type: cleanup

### [HRW-0] Head-reducedness route adjudication — RESOLVED
- Status: done (2026-07-28: user authorized opening the BGR work; plan in
  `hrw-decomposition.md`; skeleton `WP/HeadReduced.lean` builds; chain HRW-1..6
  below replaces the gate.)

### [HRW-1] L2 — reducedness from reduced completed locals (mathlib-grade)
- Status: done | File: WP/HeadReduced.lean | Depends: none | Parallel: yes
- Progress: DONE 2026-07-28.  Proof exactly per sketch; the completion-kernel leaf
  closed by `algebraMap L (AdicCompletion I L) = AdicCompletion.of I L` (rfl, from
  `AdicCompletion/Algebra.lean:118` at S := R) + `AdicCompletion.eval_of` +
  `Submodule.Quotient.mk_eq_zero`, feeding the SMUL Krull form
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (avoids I^n•⊤-vs-I^n juggling).
  Noetherian localization: `IsLocalization.isNoetherianRing 𝔪.primeCompl`.
  Axioms [propext, Classical.choice, Quot.sound].
- Decls: `isReduced_of_forall_completedLocal_reduced`.
- Sketch: nilpotent x; per maximal 𝔪: image nilpotent in the reduced completion ⇒
  x/1 ∈ ⋂ (maxIdeal)ⁿ = ⊥ in R_𝔪 (`Ideal.iInf_pow_eq_bot_of_isLocalRing`, VERIFIED
  Filtration.lean; R_𝔪 noetherian-local via localization instances); vanishing at all
  maximals ⇒ x = 0 (`Ideal.mem_of_localization_maximal` at ⊥, VERIFIED
  LocalProperties/Basic:539).  Leaf: express "image in completion vanishes ⇒ x ∈
  every 𝔪ⁿ" via `AdicCompletion.of`'s level maps.  Sources: hrw-decomposition L2;
  reviewer proof (3 sentences).
### [HRW-2] L1.a — headToQ contraction behaviour
- Status: open | File: WP/HeadReduced.lean | Depends: W15, W16
- Decls: (headToQ is defined); new: maximality-or-primality lemmas for the
  contraction 𝔮.comap (headToQ DH) per the adversarial note in hrw-decomposition
  (do NOT silently assume the contraction maximal; L3 is stated at primes for this
  reason).
### [HRW-3] L1.b/c — finite-level graph evaluation + inverse limits
- Status: open | File: WP/HeadReduced.lean | Depends: HRW-2
- Decls: `qHead_completedLocal_comparison`.
- Sketch: mod 𝔮ⁿ the denominator s is a unit (s ∉ 𝔮 as s is a unit of QHead) and
  T_i = f_i/s is determined; surjectivity + kernel computation of the finite-level
  comparison; AdicCompletion functoriality along the tower.  Frontier flagged:
  finite-level commutative algebra, no mathlib precedent.
### [HRW-4] L3.a — the W-invertible chart (Z-elimination → Tate locals)
- Status: open | File: WP/HeadReduced.lean | Depends: none (statement-independent)
- Decls: `head_completedLocal_reduced_of_wa_notMem` (+ its sub-decomposition when
  opened: A_N[1/W] = K⟨W,U⟩[1/W] support identity; `tateAlgebra_completedLocal_
  reduced` leaf — check the 828b Nullstellensatz artifacts first).
### [HRW-5] L3.b — the singular quadratic tower (deepest leaf)
- Status: open | File: WP/HeadReduced.lean | Depends: none (statement-independent)
- Decls: `head_completedLocal_reduced_of_wa_mem`.  Requires its own decomposition
  round when opened (planned route: explicit completed support model + Φ-style
  formal-domain embedding; char-free).
### [HRW-6] L4 — assembly + unconditional endpoints
- Status: open | File: WP/HeadReduced.lean, WP/Main.lean | Depends: HRW-1..5, W16
- Decls: `headLocsReduced`; then `weightedParity_chainReduced_unconditional` (+_of_dvr)
  in Main.lean (NEW theorems; conditional forms stay).
