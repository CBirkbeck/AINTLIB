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
- Status: done | File: WP/Tail.lean | Depends: W1, W2 | Parallel: yes
- Progress: DONE 2026-07-28.  Architecture: (i) NEW `Finset.HasAntidiagonal
  (TailIdx N)` instance (attach+map from the ambient Finsupp antidiagonal — both
  components of a splitting of a tail index are automatically tail) + a local
  `sum_antidiagonal_swap` via `Finset.sum_equiv (Equiv.prodComm)`; (ii)
  AddCommGroup via `inferInstanceAs (… ↥(addSubgroup N P))`; (iii) One/Mul as
  standalone instances with `one_val`/`mul_val` rfl-lemmas; c₀-closure of the
  twisted convolution by squeeze against
  `MvPowerSeries.tendsto_sup'_antidiagonal_cofinite` (vendored) +
  `tendsto_mul_cofinite_nhds_zero` (mathlib), with the e=0/e>0 case split for
  `‖ρ^e‖ ≤ 1` (NO NormOneClass needed: `norm_pow_le'` at e>0, `pow_zero` at 0);
  (iv) mul_assoc mirrors mathlib MvPowerSeries: sum_mul/mul_sum + `sum_sigma'` +
  `sum_nbij'` with hand legs; cocycle handled by a `key` lemma
  ρ^a((ρ^b(uv))s) = ρ^c(u(ρ^d(vs))) given a+b=c+d (`rw pow_add; ring`) + omega
  on 4 subadditivity facts; (v) CommRing via `letI G := inferInstance; { G with … }`
  (the `{ inferInstanceAs … with }` and `where __ :=` forms both FAIL with
  universe-mvar errors — letI is the working idiom); (vi) norm = ⨆ via
  `AddGroupNorm.toNormedAddCommGroup` (lpSpace pattern), NormedCommRing by
  two-parent `{ _, _ with norm_mul_le }`; (vii) CompleteSpace = W2
  coefficientwise-Cauchy port (no weights).  GOTCHAS: type-ascribe the
  mem_antidiagonal.mp haves in nbij legs (unreduced Sigma projections otherwise
  poison omega/rw); `rw [← hpt]` on τ.1 breaks motive (τ in types) — rewrite
  `← Finsupp.add_apply, hpt` instead; beta-`show` before if-rewrites under dist.
  Axioms clean (instCommRing/instNormedCommRing/instCompleteSpace/
  single_mul_single/ofHead/toHead).
- Decls: TailC0 `CommRing`, `NormedCommRing`, `IsUltrametricDist`, `CompleteSpace`,
  `NormOneClass`, `single` (+`coeff_single`), `single_mul_single`,
  `norm_eq_iSup_coeff`, `ofHead/toHead` (+laws).
- Sketch: convolution over `Finsupp.antidiagonal μ.1` restricted to tail pairs
  (finite); c₀-closure + submultiplicativity need `TwistElem.norm_le_one`;
  associativity via the twist cocycle (decomposition.md adversarial log);
  completeness = the W2 c₀ argument verbatim (coefficientwise Cauchy).
  Generality: any normed ultrametric commutative P.  Sources: [WP] 1021–1029.

### [W11] Tail.lean III — the Φ-embedding
- Status: done | File: WP/Tail.lean | Depends: W10, R1 | Type: def+theorems
- Progress: DONE 2026-07-28.  ARCHITECTURE CHANGE: R1's three lemmas moved to NEW
  upstream file `WP/FormalReduced.lean` (Tail cannot import Reduced — cycle);
  Tail + Reduced both import it.  Equiv via `Finsupp.subtypeDomain`/`extendDomain`
  (membership by `support_extendDomain_subset`, NOT extendDomain_apply-dite);
  symm-additivity FREE via injectivity of the forward map (no extendDomain_add
  needed).  Φ built as bare `tailC0ToFormalFun` + rfl coeff lemma + standalone
  zero/one/add/mul laws, THEN bundled (avoids coeff-of-lambda defeq fights inside
  RingHom fields); Φ-mul by sum_nbij' along the equiv-pair map + `Nat.add_sub_cancel'`
  + pow_add + ring.  ρ-regularity upgraded to ρ^k-regularity by induction for
  injectivity.  isDomain: manual Nontrivial (coeff_zero_one) +
  `NoZeroDivisors.to_isDomain _` + `Function.Injective.isDomain`.
  Tail.lean now 0 sorries; tree 3164 green; axioms clean ×5.
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
- Status: done | File: WP/Perturbation.lean | Depends: W3, W4 | Parallel: with W9-W11
- Progress 2026-07-29: SUB-TICKET W12a (pod-independence, spawned per Tier A2)
  COMPLETE: `locTopology_pod_eq` (general-datum pod-independence — NEW math, no
  repo precedent; the global case was CompletionModelIndependence).  Route: every
  element of a `P'`-basic nbhd is a ℤ-combination of `φ(a')·τ` (a' ∈ I'-power, τ a
  T/s-monomial) — `tsMonoid` + `normalSet` + AddSubgroup-closure normal form (the
  Subring.closure-mul case via a double AddSubgroup.closure_induction);
  A-level absorption from the two `hasBasis_nhds_zero`; the strengthened
  span-induction predicate `∀ r ∈ closure(normalSet), r·d ∈ locNhd P n` makes the
  smul-case compositional (multiply r by u.val, stay in the closure).  Then
  `podCongrEquiv` + continuous/symm_continuous/canonicalMap all by the
  compareHom pattern (extensionHom across equal topologies + DenseRange.equalizer),
  with the RationalLocData-destructure/subst/iota trick for the laws (obtain both,
  dsimp at hT hs, subst — the record projections iota-reduce cleanly).
  GOTCHAS: AddSubgroup.closure_induction case names are mem/zero/add/neg (NOT
  one/mul/inv); `Submodule.mem_toAddSubgroup` doesn't exist — membership in
  `.toAddSubgroup` is accepted defeq (pass the Ideal-membership directly).
  DONE 2026-07-29 (all of W12): datum := genPieceDatum(unitBallPod, image pert,
  pert s, span-top) — datum_T/datum_s rfl; primed Bezout Σa·pert = t^ℓ(1+th) via
  ultrametric sum bound (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`) +
  ball division; unit via `Units.oneSub (−(t·h))` + `sub_neg_eq_add`;
  exists_integral_bezout via `Submodule.mem_span_finset` + t^ℓ-scaling (M := Σ‖c‖,
  `exists_pow_lt_of_lt_one` + `lt_div_iff₀`; beta-`show` before if-rewrites).
  rationalOpen_datum: STATEMENT-FAITHFULNESS FIX — added `hplus : unit ball ⊆ E⁺`
  field + [PlusSubring E] binder to PerturbSetup ([WP] line 949 "E₀ ⊆ E⁺" was
  dropped in skeletonization; without it the Spa estimates are unprovable).  Proof
  at the canonical valuation (`Valuation.Compatible.vle_iff_le` bridge, Cor732
  pattern): w(t)<1 from `not_vle_one_of_mem_spa_of_topologicallyNilpotent`
  (SpaCompact) + t topologically nilpotent (norm-powers); w(t^ℓ) ≤ w(s) via
  `Valuation.map_sum_le` over the (primed) Bezout with w(1+th)=1
  (`Valuation.map_add_eq_of_lt_left`); w(pert−x) < w(s) by ball-division +
  strict-mul helper `gv_mul_lt_of_lt_one` (b⁻¹-cancellation — NO MulRightStrictMono
  in Γ₀, and `ring` is UNAVAILABLE in Γ₀ (no addition)); w(pert s) = w(s) by
  add_eq_of_lt_left; both inclusions symmetric.  2026-mathlib renames:
  `mul_le_mul_left'`→`mul_le_mul_right` (h) (c) for c*a≤c*b, `mul_le_mul_right'`→
  `mul_le_mul_left`, `zero_le'`→`zero_le`.  Axioms clean ×5.
  NEW import: FJP.RestrictedGaussAdic (ball division).
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
- Status: done | File: WP/Perturbation.lean | Depends: W12 | Type: def+theorems
- Progress: DONE 2026-07-29.  MAJOR SIMPLIFICATION vs sketch: NO bespoke
  Away-lift/1-unit construction — the rationalOpen EQUALITY (W12) feeds the
  existing restriction-map machinery (Presheaf.lean `restrictionMapHom` +
  `restrictionMap_comp` + `restrictionMap_id`), giving equiv := restrictions both
  ways, inverses by functoriality + id-law (proof-irrelevance makes the
  ⊆-proof-args interchangeable — `restrictionMap_id S.D` is EXACT against the
  trans-proof).  The [HasLocLiftPowerBounded E] input: the faithful THEOREM-form
  `hasLocLiftPowerBounded_faithful` (FaithfulLocLift:399 — no IsNoetherianRing,
  unlike the instance-form!) with haveI-chain: isHuberRing_of_scale +
  isTateRing_of_scale + right-uniformity CompleteSpace via
  `IsUniformAddGroup.rightUniformSpace_eq` (the WPA Algebra.lean:279 pattern) —
  NonarchimedeanRing/T2 auto-synthesize for normed ultrametric E.
  SOURCE-FAITHFULNESS: added section-variable [IsRingOfIntegralElements (E⁺)]
  (the Huber-PAIR convention of [WP] §6.3 — E⁺ is a ring of integral elements by
  definition).  equiv_canonicalMap via `UniformSpace.Completion.extensionHom_coe`
  + `IsLocalization.Away.lift_eq` (NOT .AwayMap.lift_eq).  All Prop-classes →
  instance-route mismatches are proof-irrelevant (the show-forms typecheck).
  Perturbation.lean 0 sorries; axioms clean ×5.
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
- Status: done | File: WP/Evaluation.lean | Depends: none | Parallel: yes (early)
- Progress: DONE 2026-07-29.  Mathlib's SummationFilter-era names: summability =
  `(NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f).mpr`; Cauchy
  product = `tsum_mul_tsum_of_nonarchimedean` + `Summable.mul_of_nonarchimedean`;
  regroup pairs→antidiagonal by a hand-rolled `sigmaAntidiagEquiv` +
  `Equiv.summable_iff`/`Equiv.tsum_eq` + `Summable.tsum_sigma` +
  `Finset.tsum_subtype` (to_additive-generated names don't grep — PROBE with
  #check).  Monomial-set boundedness via `isBounded_closure_finset_of_isPowerBounded`
  (Bounded.lean:453) + Subring.prod_mem/pow_mem.  evalFun laws proven standalone
  then bundled (evalFun_mul needs maxHeartbeats 1000000).  Continuity: open-subgroup
  U₀ + bounded-monomials V₁ + φ-preimage δ-ball; tsum ∈ U₀ by
  `IsClosed.mem_of_tendsto` on partial sums (`sum_mem`) — `continuous_of_continuousAt_zero`
  on the AddMonoidHom.  Density: general-E port of FJP `polyToP_denseRange`
  (superlevel truncation); uniqueness via `MvPolynomial.induction_on` (cases
  C/add/mul_X) + `DenseRange.equalizer`.  hφb is UNUSED by the construction (kept:
  statement canonical).  Axioms clean ×6.
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
- Status: done | File: WP/CoeffLocalization.lean | Depends: W8 | Type: def+instances
- Progress: DONE 2026-07-29.  ARCHITECTURE AMENDMENT: `QHead` now quotients by
  `headGraphIdeal := (span graph rels).closure` (`Ideal.closure`) — the instances
  can't carry (ϖ, hK₀), and quotient-by-closure is normed UNCONDITIONALLY
  (`Ideal.Quotient.normedCommRing` [IsClosed] with `isClosed_closure`); under hK₀
  the closure collapses via `isClosed_graphIdeal` + `Ideal.closure_eq_of_isClosed`
  (W16 will use that).  Ultra on the quotient by ε-lifts
  (`Ideal.Quotient.norm_mk_lt` ×2 + `max_add_add_right`; the `rw [map_add, ha, hb]`
  does NOT auto-rfl-close — append `rfl`).  CompleteSpace: the
  `Submodule.Quotient.completeSpace` instance FAILS on the P-alias (Module (P) (P)
  diamond inside the unifier despite standalone synth!) — use mathlib's own cast
  `QuotientAddGroup.completeSpace_left M I.toAddSubgroup` directly.  rhoQ := mk
  (polyToP (C WaHead)) with `Ideal.Quotient.norm_mk_le` (NOT the Submodule-form —
  Module-diamond) + new `polyToP_C_val` (the W8 hCP fact packaged; MvPolynomial vs
  MvPowerSeries coeff_C orientations differ, and the t=0 branch auto-reduces —
  plain `rfl`) + `norm_WaHead` (via norm_headIncl + headIncl_WaHead).
  datumEnum := `(Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm`.
  TailC0.map by the mapFun+standalone-laws pattern (W11 Φ-pattern); continuity by
  LipschitzWith 1.  Axioms clean ×7.
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
- Status: done | File: WP/CoeffLocalization.lean | Depends: W15, W14
- Progress: DONE 2026-07-29 (four staged commits).  (A) `headConst` (norm ≤,
  continuous), `qX` (a WRAPPER DEF with codomain QHead — bare mk-terms break
  HMul-synthesis at the opaque alias: type-ASCRIPTION does NOT survive
  instance-search's reducible-transparency, a named def does), the closure-
  membership via `Ideal.coe_closure` + `subset_closure` (NO `Ideal.le_closure`),
  `headConst_datumEnum` (the graph relation), `isUnit_headConst_s` via
  `exists_integral_bezout'` (NEW hT1-free prime version in Perturbation — proof
  identical, the entries were never normalized) at the piHead scale-bundle +
  `Finset.sum_coe_sort` + `Equiv.sum_comp` reindex + `isUnit_of_mul_isUnit_left`.
  (B) fwd: `IsLocalization.Away.lift` + `locTopology_continuous_lift` (the
  chartFwd criterion, LocalizationTopology:360); `headLocFwdAlg_divByS` by
  `IsUnit.mul_right_cancel` off `IsLocalization.mk'_spec`; power-bounds via
  `norm_qX_le_one` + `FiniteJet.isPowerBounded_of_norm_le_one` (NEW import
  FJP.FiniteJetFunctoriality).  (C) rev: `restrictedEval` at
  `revB i := coeRingHom (divByS t_i s)` (power-bounded by the gChart pattern —
  `CompletionLocalization.coeRingHom_image_locSubring_isBounded`, NO
  HasLocLift/IsROIE needed); relations die by `mk'_spec`; kernel ⊇ closure by
  `closure_minimal` against the closed kernel; descent `Ideal.Quotient.lift`;
  continuity by ε-lifts (`Ideal.Quotient.norm_mk_lt` — NORM-INSTANCE-ATOM WARNING:
  their SeminormedCommRing-path ‖q‖ vs the ambient instance's are defeq but
  distinct atoms for linarith/rw — bridge with a CALC whose RHS you write
  yourself).  (D) equiv: roundtrips via `IsLocalization.ringHom_ext` +
  `DenseRange.equalizer` on coe/polyToP-dense images; `RingHom.congr_fun`;
  `Subtype.coe_eta` + `Equiv.symm_apply_apply` for the enum roundtrip; auto-rfl
  after rw fails on instance-path-mixed `+` — append `rfl`.  hK₀ is UNUSED
  (closure-model absorbed it) but kept (canonical statement).
  STALE-OLEAN GOTCHA: after editing an upstream file's API, `lake build` it before
  `lake env lean` on the consumer.  Axioms clean ×4.
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
- Status: done (2026-07-29) | File: WP/CoeffLocalization.lean | Depends: W16, W9, W10
- **Progress**: COMPLETE, all decls sorry-free + axiom-clean (propext/Choice/Quot.sound;
  module builds, 3155 jobs). Delivered: tailCoeff_mul keystone, wpaTailEquiv, coeffBase,
  coeffFwdAlg/coeffFwd, qToLift chain, liftE/summable_revFamily/coeffRevFun + ring laws,
  coeffRev hom + open-subgroup continuity (restrictedEval pattern), coeffFwd_qToLift
  (MvPolynomial.induction_on density chase), coeffFwd_liftE, TailC0.hasSum_single
  (metric eps/2 singles decomposition), coeffRev_coeffBase (HasSum.map along canonicalMap
  + uniqueness), both roundtrips (equalizer on Completion.denseRange_coe), the
  coeffLocEquiv record + continuities + coeffLocEquiv_canonicalMap_headIncl.
  GOTCHAS (bank): (1) coeffRevFun_mul whnf-RUNAWAY (16M heartbeats insufficient) caused
  by ASCRIBED have-types over Completion-typed tsums: my elaboration vs the lemma's
  forces an instance-path defeq descending into Completion.map2/IsDenseInducing.extend/
  Classical.epsilon (diagnostics: HMul.hMul 2.1M unfolds, Filter.sets 1.2M). FIX: bare
  `have :=` (no ascriptions) + directed Eq.trans-chain; only comp-unfold/beta defeqs
  remain. (2) Finset.sum_mul HO-pattern fails over the TailIdx def-alias: calc step with
  both sides self-written + `Finset.sum_mul _ _ _` (expected-type-driven). (3) simp
  map_mul/map_add do not fire on the ascribed `(TailC0.ofHead ... : QHead ->+* ...)`
  hom-form: finish with directed `(map_mul hom _ _).symm`. (4) mk-terms typed at the RAW
  quotient break instance search (keyed on the QHead alias): pin P via `(rho := rhoQ DH)`
  in the ofHead ascription (isUnit_coeffBase_s idiom). (5) `lake build "Adic spaces"`
  does NOT rebuild WP modules: build '<<Adic spaces>>.WP.CoeffLocalization' explicitly
  before #print axioms (stale-olean sorryAx/unknown-constant ghosts).
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

### [W17-KEYSTONE progress note 2026-07-29]
- `tailCoeff_mul` PROVEN (the full [WP] eq:tail-multiplication): route = finite
  tail-truncations (`tailTrunc` + coeff/norm laws + `exists_tailTrunc_close` off
  W9's cofinite-tendsto) → finite case by W9-algebra (`headIncl_eTail_mul` from
  eTail_mul with atom-splitting map_muls for `ring`; double-sum → `sum_product'` →
  `sum_filter` → a Finset-equality of filtered pair-sets) → density limit
  (`eq_of_forall_dist_le`, ε/M-truncations, ultrametric two-term splits).
  GOTCHAS: `ring` treats hI(x·y) vs hIx·hIy as distinct atoms — pre-split with
  map_mul-haves; `if_neg`-lambdas against ∧-conditions need `show ¬(_ ∧ _) from` 
  (bare lambdas elaborate against a whnf-reduced condition); forward-references:
  norm_WaHead had to move before the TailConv section.
  NEXT for W17-core: wpaTailEquiv (hom := tailCoeff-family, mul := tailCoeff_mul,
  inj := tailCoeff_injective; surjectivity via nonarch summation of
  headIncl·eTail-series) then coeffLocEquiv := (TailC0.map headConst) ∘ wpaTailEquiv
  route + Away.lift/extensionHom bridges (all tools in place).

### [W18] CoeffLocalization IV — every localization has finite-head form
- Status: done (2026-07-29) | File: WP/CoeffLocalization.lean | Depends: W17, W13
- **Progress**: COMPLETE sorry-free + axiom-clean (module 3155 jobs). CoeffLocalization.lean
  now has ZERO sorries. Delivered (beyond plan): generic `restrictionEquiv` +
  continuities + canonicalMap law (Perturbation.lean — the lem:small-perturbation
  restriction-map mechanism decoupled from the perturbation, needs [IsHuberRing E]
  [HasLocLiftPowerBounded E]); `rationalOpen_insert_self` and `rationalOpen_unitSMul`
  (Spa-pointwise via toValuativeRel + vle_iff_le + (hc.map w).ne_zero unit-nonvanishing
  + gv-cancellation b⁻¹-trick); `exists_head_approx_finset` (common stage via
  Finset.sup + Subring.inclusion (wpHeadSupport_mono) upcast, headIncl-compat is rfl);
  `nonempty_headModelData` = one assembly proof: window element c (SAME
  Classical.choose as wpaPod so the pod-component of the datum-match is rfl by
  proof-irrelevance), sum-of-norms scale exponent k, D1 := genPieceDatum (wpaPod)
  (insert D.s D.T scaled) , Bezout via exists_integral_bezout', precision m with
  |varpi|^m <= |t|^(l+1), PerturbSetup with pert := ite-headIncl-approx, head datum DH
  over TH := T1.image g with rationality by rhoHead-retracting the primed Bezout
  (rhoHead t = constHead c via <- headIncl_constHead + rhoHead_headIncl; 1-unit via
  ascribed-type Units.oneSub have), datum-match by RationalLocData.ext_of_fields rfl +
  Finset.image_image/image_congr + if_pos, e := (restrictionEquiv D _ hopen).trans
  (coeffLocEquiv ...) with RingEquiv.coe_trans/symm_trans continuities.
  GOTCHAS: mem_span_finset gives smul-form (show-from mul-form coercion, bezout'
  idiom); dif_pos needs simp only (beta-redex); norm_rhoHead_le K w N section-explicit;
  build the Perturbation olean BEFORE compiling the consumer (stale-olean unknowns).
- Decls: `nonempty_headModelData` (via `HeadModelData`).
- Sketch: [WP] 1107–1127: scale D's entries into the unit ball (podCongr + Bezout
  scaling from W12); `exists_head_approx` (W8) at precision ℓ+1; PerturbSetup with
  pert := head approximation; ρ_N-retract the primed Bezout ⇒ head datum rational
  (`rhoHead` ring hom, W9); e := coeffLocEquiv ∘ perturb.equiv ∘ podCongrEquiv;
  hopen from `rationalOpen_datum` + `liftDatum` matching.  Sources: [WP] 1107–1127.

### [CLEANUP-4] /cleanup on WP/CoeffLocalization.lean
- Status: open | Depends: W18 | Type: cleanup

### [W19] Chart.lean I — datum, head model, domain, reduced
- Status: done (2026-07-29) | File: WP/Chart.lean | Depends: W15, W16, W17, W11
- **Progress**: COMPLETE sorry-free + axiom-clean (module 3157 jobs; only the two W20
  decls remain sorried in the file). Delivered: chartHeadDatum block (genPieceDatum at
  the piHead unit-ball pod; span {W,pi} = top); wpHeadSupport_zero_eq_even (stage-0
  evenness vacuous) + headZeroEquiv (subringCongr.trans evenSupportEquiv) + norm;
  isDomain_P_one (multiplicative Gauss norm, W2); headZeroEquiv_WaHead/_constHead
  (unhalve-coefficient computations); chartRescale (X -> piX as restrictedEval at K),
  chartCoeff = rescale o headZeroEquiv + value laws; chartFwdP (restrictedEval with
  ite-tuple (X or 1) per datumEnum entry) + graph-kernel + chartFwd quotient-lift +
  continuity; chartRev (X -> [X_W]); BOTH roundtrips (polyToP-density equalizers;
  rev o chartCoeff = headConst by density THROUGH headZeroEquiv — the W-relation
  [W] = [pi][X_W] realizes W -> piX; the pi-entry kills by unit cancellation qX = 1);
  chartQHeadEquiv record; norm_restrictedEval_le (NEW generic nonexpansiveness in a
  Chart-local NormBound section — Evaluation.lean's B is deliberately norm-free, so
  it CANNOT live there; explicit `hone` hypothesis instead of NormOneClass B) =>
  chartQHeadEquiv_norm by the two-sided nonexpansive sandwich (NO division identity
  needed: fwd via norm_mk_lt representatives + le_of_forall_pos_le_add, rev via the
  roundtrip); isDomain_chartQHead (Injective.isDomain along toRingHom);
  isDomain_chart (rhoQ.val <> 0 by pushing to K<X> and norm-positivity;
  isDomain_tailC0 w 0 + coeffLocEquiv-transport); isReduced_chart (domain => reduced).
  GOTCHAS: `variable {K w} in` DROPS binders unused in the STATEMENT (w-free lemmas
  need w-instantiation inside proofs, e.g. (w := fun _ => 0)); Set-coercion of an
  Ideal needs the FULL Set-type spelled out (Set _ metavar blocks coercion);
  mixed alias-instance `x + x`/`x * 1` goals need explicit `rfl` (simp/rw auto-rfl
  both fail); Function.Injective.isDomain wants .toRingHom not an ascription;
  isDomain_tailC0 takes w N explicitly; long unicode heredocs to python break —
  ALWAYS use Write-tool script files.
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
- Status: done (2026-07-29) | File: WP/Chart.lean | Depends: W17, W19
- **Progress**: COMPLETE sorry-free + axiom-clean — Chart.lean has ZERO sorries; [WP]
  thm 6.2(4) (`not_isStablyUniform_WPA`) is proven. Route: norm-transfer helpers
  (norm_qHead_eq/mul/one/pow via chartQHeadEquiv_norm — the multiplicative Gauss norm
  transported to QHead kills ALL twist computations), norm_qHeadConst, norm_rhoQVal
  (= |varpi|); tailDelta n (single n 1 at stage 0); T_n := single delta_n
  (headConst-of (varpi^(w n))^{-1}); T_n*T_n collapses to norm 1 (parity weight:
  wpWeight_single at k=2 vanishes, exponent 2*w n exactly compensates the
  coefficient); powers bounded by max 1 |varpi|^{-w n} via Nat.twoStepInduction
  (case names zero/one/more!) + isPowerBounded_of_forall_norm_le (C-general mirror
  of the norm_le_one version); nonuniformity: unit ball absorption + small scalar
  (NormedField.exists_norm_lt) + hwu picks n with w n >= m0 so
  |varpi|^{w n} <= |c| makes ||T_n * v|| >= 1 inside the ball — contradiction;
  transport along coeffLocEquiv by FiniteJet.isUniform_of_ringEquiv (needed NEW
  import of FJP.FiniteJetChart in Chart.lean — not in the closure before).
  eq:Tn-power-norms realized as the T² collapse + submultiplicativity (no exact
  odd-power formula needed).
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
- Status: done | File: WP/Sheafy.lean | Depends: W18, W21a | Parallel: with W22
- **Recon note (2026-07-29)**: the FJP template
  (SheafTransfer:83 productRestrictionSub_injective_JetA + :667 embedding) pushes
  the vanishing section to the Milnor-pair components via PUSHED COVERINGS + their
  separations. The WP-analogue needs the pushed HEAD cover — shared W21/W22
  infrastructure, split out as W21a below. The embedding-half (OMT assembly:
  sectionEqualizer_isClosed + isInducing_of_closedRange_of_topNilpUnit +
  countably-generated uniformity) transfers near-verbatim at A := WPA once
  injectivity is in hand.

### [W21a] The pushed head cover (shared W21/W22 infrastructure)
- Status: done (2026-07-29; (i) done, (ii)-(iv) designed) | File: WP/Sheafy.lean | Depends: W18
- **Progress**: (i) DONE — `exists_head_approx_finset_all` (approximation at every
  stage above a threshold, inclusion-upcast), `nonempty_headModelData_all` (the
  exact-stage ∀-M primitive; W18's proof re-threaded — set-before-obtain so g is
  typed at N; original derived), `exists_common_headModel_stage` (Finset.sup of
  attached thresholds — base and every piece modeled at ONE M). All compiled
  first-try, committed.
- **Design decision for (ii)-(iii) (2026-07-29, supersedes the split-map sketch)**:
  the paper's split-surjection eq:split-spectrum-map serves ITS in-U formulation
  (E := O(U), coefficient projection E → P_M). The project's HeadModelData are
  𝒜-GLOBAL (hopen : rationalOpen (liftDatum DH).T/s = rationalOpen D.T/s in
  Spa 𝒜), which admits a DIRECT transfer: pull head-points back along
  `rhoHead : 𝒜 →+* WPHead M` (the norm-nonincreasing retraction, W9).
  For v ∈ Spa(WPHead M, °): v ∘ ρ is a Spa(𝒜, °)-point (power-bounded goes to
  power-bounded under ρ by norm_rhoHead_le), and on liftDatum-entries
  v(ρ(headIncl t)) = v(t) by rhoHead_headIncl — so membership transfers
  DEFINITIONALLY: v ∈ rationalOpen(DH_i) ↔ v∘ρ ∈ rationalOpen(liftDatum DH_i)
  = rationalOpen(D_i) (model.hopen). hsubset and hcover of the pushed covering
  both follow by this pullback + C's own hsubset/hcover. NO split surjection,
  NO maximal-pair subspace needed for the covering-data construction. (The
  split-map may still be needed for W22's Čech-equalizer boundedness transfer —
  keep the [WP] 1156–1218 reference alive there.) Remaining: (ii) build
  `pushedHeadCover (C) (models) : RationalCoveringData (WPHead K w M)` with the
  Spv-comap machinery (AdicSpectrum comap; check the project's Spv-pullback API
  for Spa-membership + vle-compat along ring homs), (iii) its IsRational (models'
  hDH), (iv) the per-piece compat squares (restriction vs coeffLocEquiv,
  [WP] eq:cover-coefficientwise naturality).
- Decls (planned): (i) `nonempty_headModelData_family` — common stage M for ALL
  data of a finite rational covering (iterate W18's perturbation at a common
  precision; alternatively upcast per-datum models along N ≤ M — needs a
  HeadModelData stage-upcast: castHead-transport of QHead/TailC0 along
  wpHeadSupport_mono, possibly easier to re-run W18 with a floor stage M);
  (ii) the pushed covering data on WPHead M (base + pieces), rationality;
  (iii) the covering property on Spa(head) via the split spectrum map
  ([WP] eq:split-spectrum-map — the isometric pair rho_M/iota gives a section of
  Spa(E,E°) → Spa(P_M,P_M°); the paper warns: work with the restriction of the
  cover to the maximal-pair subspace, do NOT identify U with it);
  (iv) per-piece model-compatibility squares (restriction maps vs coeffLocEquiv).
  Sources: [WP] 1135–1218.
- **(ii)+(iii) DONE 2026-07-29**: PushedHeadData structure + nonempty + .cover
  (RationalCoveringData on the head via the pullback) + .cover_isRational — all
  first-try compiles, committed.
- **(iv) design (2026-07-29)**: the compat square via the QHead-level restriction
  `qRestrict := headLocEquiv-i ∘ restrictionMapHom-head(P.cover.hsubset) ∘
  headLocEquiv-b.symm : QHead DHb →+* QHead (DHp D)` (nonexpansiveness for
  TailC0.map from the model isometries; twist-compat qRestrict rhoQ-b = rhoQ-i
  via the canonicalMap-laws on W-images); the naturality square
  `TailC0.map qRestrict ∘ coeffLocEquiv-b = coeffLocEquiv-i ∘ restriction` by the
  density equalizer (both continuous ring homs agree on canonicalMap-images:
  coeffLocEquiv_canonicalMap_headIncl + restrictionMapHom_canonicalMap_generic).
  **W21-injectivity walk** (needs (iv)): z vanishing on pieces → model
  coefficients q_mu ∈ QHead DHb have all P.cover-restrictions vanishing (the
  square) → transport along headLocEquiv-b.symm to presheafValue DHb →
  isSheafy_WPHead.separationSub at P.cover gives q_mu = 0 → e_base z = 0 → z = 0.
- **(iv) square — refined route (2026-07-29, after a draft round)**: the POINTWISE
  square needs fraction-handling (the mu-projection is not multiplicative, so the
  density reduction to algebraMap-generators does not close over the
  localization); the BUNDLED square (TailC0.map of qRestrict ∘ coeffLocEquiv-b =
  coeffLocEquiv-i ∘ restriction, by IsLocalization.ringHom_ext + completion
  density on RING homs) is the right carrier — but TailC0.map requires a norm-1
  coefficient hom, and qRestrict is only CONTINUOUS (headLocEquiv-general-M has
  no isometry; presheafValue carries no norm). ROUTE: (a) `bound_of_continuous`:
  a continuous additive map between the normed QHeads is C-BOUNDED for some C
  (continuity at 0 + nonarchimedean constHead-scalar scaling — mirror
  norm_bound_of_isPowerBounded's window argument); (b) `TailC0.mapC` — the
  C-bounded variant of TailC0.map (same null-preservation with a C-factor;
  same hrho twist-compat: qRestrict rhoQ-b = rhoQ-i via qRestrict_headConst at
  WaHead since rhoQ.val = headConst WaHead rfl); (c) the bundled square by
  ringHom_ext (Submonoid.powers (liftDatum-b).s) on the algebraic layer +
  DenseRange.equalizer on the completion (both sides continuous ring homs
  presheafValue(liftDatum-b) → TailC0-i; generator agreement =
  coeffBase-computations + qRestrict_headConst); the pointwise corollary by
  applying TailC0.coeff mu. All ingredients present except (a)+(b) (~150 lines).
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
- Status: done | File: WP/Sheafy.lean | Depends: W18
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
- **Progress**: DONE 2026-07-29, axiom-clean. Route DIFFERS from the ticket
  sketch in one load-bearing way: NO OMT-bounded-inverse / C-bound was needed —
  nullity of the glued family comes from the head embedding's IsInducing
  (tendsto_nhds_iff) + componentwise limits (tendsto_pi_nhds) + per-piece
  TailC0-nullity, transported through headLocEquiv/restrictionMapHom
  continuity. Infrastructure built: pair-generalized qRestrictP +
  coeffLoc_restriction_squareP (textual mirror of the P-forms), liftDatum_mono
  (via mem_liftDatum_iff, the headIncl-comap membership characterization, with
  the head norm-bound mirror norm_bound_of_isPowerBounded_head),
  interDatumHead (+ intersection formula + rationality, the FJP interDatum
  mirror at P_M), pushedCompat_head (factor arbitrary D₃ through the rational
  intersection — the pushedCompatB pattern, NO lift of D₃), pieceModel,
  and the choice/restrictionMap_cast pushed-family idiom (hgres/hgd from FJP
  gluing_JetA). Gotchas: 𝓝-notation not open (use nhds); set_option must
  precede the variable-in chain, not sit between doc-comment and theorem;
  destructuring D' : ↥P.cover.covers breaks mem_image.mp at implicit
  transparency — keep it packed; tendsto_zero_iff_norm_tendsto_zero is used
  forward.

### [W23] Sheafy.lean III — wrappers
- Status: done | File: WP/Sheafy.lean | Depends: W21, W22 | Type: theorems
- Decls: `wp_isSheafyFor`, `wp_isSheafyComplete`, `wp_structurePresheaf_isSheaf_all`.
- Sketch: verbatim the FJP wrapper chain (SheafyEndpoints:95/175/213):
  letI/haveI prefix; `isLimitSheaf_of_isSheafy` (SheafyPair:550);
  `isSheafyFor_iff_isSheafyComplete` (RelativeStandardRefinement:201);
  `isSheafyFor_structurePresheaf_isSheaf` (SheafyEndpoints:53).
- **Progress**: DONE 2026-07-29, axiom-clean — verbatim FJP SheafyEndpoints
  chain (isLimitSheaf_of_isSheafy pivot, isSheafyFor_iff_isSheafyComplete,
  isSheafyFor_structurePresheaf_isSheaf). All of [WP] thm 6.2(2) is proven:
  isSheafy_WPA + wp_isSheafyFor + wp_isSheafyComplete +
  wp_structurePresheaf_isSheaf_all, plus the strong-sheafiness shifted-weight
  statement. Sheafy.lean has ZERO sorries.

### [W24] tateExtEquiv — the Tate-extension bridge
- Status: done (2026-07-29, bare ring equiv; W24b spawned for topology) | File: WP/Sheafy.lean
- **Progress**: the BARE ring equivalence `𝒜⟨V_1,…,V_s⟩ ≅ WPA (shiftWeight w s)` is
  COMPLETE sorry-free + axiom-clean (module 3161 jobs). Full delivered chain:
  slotTo/slotInv/slotEquiv (0 ↦ inr 0, 1..s ↦ inl, >s ↦ inr shifted);
  tateExtAmbient (Xia sumAlgEquiv + mathlib renameEquiv) with coefficient law
  (embDomain identity via the mapDomain route — embDomain_apply is DITE-shaped,
  avoid); wpaVal (double subtype); tateExtToFlat + injectivity + coeff law;
  slotInr/slotInl/slot_ext/slotRecomb + roundtrip laws;
  wpWeight_shiftWeight_eq (filter-normalized sums + sum_nbij' along n ↦ n−s) and
  wpMem_shiftWeight_iff; tateExtToFlat_support (3b) and
  tateExtToFlat_isRestrictedGauss (3c joint cofiniteness: outer null + per-t inner
  Gauss-null glued along the slot split; Set.Finite.of_finite_image needs (f := ·),
  Set.mem_biUnion needs (x := ·)); tateExtToWPA (two-layer corestriction) +
  injectivity; the unflatten (unflattenCoeff per-t with fiber-null via
  Injective.tendsto_cofinite composition — value-level nullity shiftg_coeff_null
  extracted first since g.1.2 displays as subring-membership, ascribe the
  Tendsto-have; support via wpMem_shiftWeight_iff reversed;
  unflatten_isRestricted via the ε/2 fiber-witness against norm_eq_iSup_coeffA and
  the slotInl-image of the finite big-set) + the coeff-ext roundtrip
  (slotRecomb_slots); tateExtEquiv := RingEquiv.ofBijective.

### [W24b] tateExtEquiv — topological refinement (Huber-pair level)
- Status: open | File: WP/Sheafy.lean | Depends: W24
- Per the ChatGPT-5.6 review note on W24: state and prove the bicontinuity of
  `tateExtEquiv` for the project's Tate-algebra topology on
  `restrictedMvPowerSeriesSubring` (`mvTateAlgebraTopology'` letI) and the
  ring-of-definition/plus-subring transport (isometry of the flatten: the Gauss
  norm is a coefficient-sup, invariant under the slot reindex — sup-of-sup
  collapse along slot_ext/slotRecomb). Needed by the strong-sheafiness statement
  in the project's Tate-extension vocabulary at the PAIR level; the bare
  `wp_stronglySheafy`-wrapper only needs W21-23.
- **Progress (design settled 2026-07-29, implementation starting)**: route =
  ambient-first flatten, then restrict. Stage 1 (exponent/variable plumbing):
  slotEquiv : ℕ ≃ (Fin s ⊕ ℕ) sending 0 ↦ inr 0, i ∈ [1..s] ↦ inl (i-1),
  n > s ↦ inr (n-s) (realizes shiftWeight: freed slots 1..s get weight 0);
  ambient flatten `MvPowerSeries (Fin s) (MvPowerSeries ℕ K) ≃+*
  MvPowerSeries (Fin s ⊕ ℕ) K ≃+* MvPowerSeries ℕ K` via
  Vendored/XiaMvPowerSeriesEquiv.sumAlgEquiv (symm) + a rename-along-slotEquiv
  RingEquiv (check Xia for a renameEquiv; else hand-roll coeff-precompose along
  Finsupp.domCongr slotEquiv — multiplicativity via antidiagonal-image under the
  ADDITIVE equiv Finsupp.domCongr + Finsupp.sumFinsuppAddEquivProdFinsupp).
  Stage 2 (restriction/support): the composite sends
  restrictedMvPowerSeriesSubring s (WPA K w) (unfold via restrictedGaussEquiv,
  ExampleUnitDisc:111, to MvPowerSeries.Restricted at radius 1) INTO the
  wpSupport (shiftWeight w s)-subring: (i) coefficient-support conditions
  transport along slotEquiv (wpWeight-shift arithmetic: wpWeight (shiftWeight w s)
  of an interleaved exponent = wpWeight w of the u-part; slots 1..s contribute 0);
  (ii) restrictedness: nested tendsto-cofinite (outer Fin-s null with WPA-coeff
  norms) ⟺ flat tendsto-cofinite — the ε-argument: outer-null + each-coefficient
  restricted, uniformly — the joint-cofinite lemma (the one analytic step; mirror
  the tailC0ToMvPowerSeries-restrictedness proofs in Tail.lean W11). Stage 3:
  assemble the subring-restricted RingEquiv; the topological refinement
  (mvTateAlgebraTopology' bicontinuity, per the ChatGPT-5.6 note: Huber-PAIR-level
  with isometry) STATED at the end once the bare equiv compiles — isometry via
  Gauss-norm coefficient-sup invariance under reindex (sup-reindex-invariance).
  Vendored Fubini (CoramRestrictedIso.finSuccEquiv) NOT needed on this route.
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
- **Leaf plan for the TOPOLOGICAL stage (2026-07-29 late; the algebraic stage
  = W24 is done)**:
  * W24b-t1 `mem_mvTateAlgNhd_iff_norm` (at A := WPA K w, canonical
    IsTateRing.principalPair): membership in the basis nhd `mvTateAlgNhd s P₀ k`
    ⟺ every MvPowerSeries-coefficient has norm ≤ ‖t₀‖^k (t₀ = the principal
    generator). Ingredients: mvTateAlgNhd_preimage_eq +
    mvPairIdeal-power-membership ⟺ coefficientwise I₀^k (a
    mem_span_unitBall_pow_iff-analogue at the mv-pair; check what the
    isAdic-subspace proof uses), and the WPA-norm-characterization of
    I₀^k-membership (principal ⟹ ‖·‖ ≤ ‖t₀‖^k, unitBallPod-style).
  * W24b-t2: WPA-(shiftWeight)-ball ⟺ coefficient-sup bound
    (norm_eq_iSup_coeffA + Real.iSup_le-iff with BddAbove from norm_coeffA_le).
  * W24b-t3: transport t1 ⟺ t2 along the flatten's coefficient bijection
    (tateExtToFlat_coeff + the slotEquiv pair split) ⟹ continuity at 0 both
    ways ⟹ bicontinuity (additive-group topologies, translation).
  * W24b-t4: pair-level wrapper (image of mvPairSubring = unit ball / pod
    transport; the RingOfIntegralElements statement).


### [R1] Reduced.lean I — MvPowerSeries reducedness (mathlib-grade)
- Status: done | File: WP/Reduced.lean | Depends: none | Parallel: yes (early)
- Progress: DONE 2026-07-28.  KEY SIMPLIFICATION vs sketch: `mvPowerSeriesPi`'s
  forward map is `MvPowerSeries.map (Pi.evalRingHom R i)` per component — map_mul'
  free via `map_mul`, and BOTH inverse laws are literal `rfl` (kernel unfolds map).
  Raw-lambda coefficientwise route FAILED on coeff-coe opacity (show/rw stuck on
  `(coeff t X) i` vs `coeff t (fun t' => X t' i)`) — avoid.  Embedding via
  `RingHom.pi (Ideal.Quotient.mk ·)` (Pi.ringHom deprecated), kernel by
  `nilradical_eq_sInf` + `Ideal.mem_sInf` + `nilradical_eq_zero` +
  `Ideal.zero_eq_bot` (0 vs ⊥ needs the bridge).  Assembly: vendored
  `MvPowerSeries.map_injective` (XiaMvPowerSeriesEquiv — NEW import in
  Reduced.lean) + mathlib `NoZeroDivisors (MvPowerSeries σ R)` (arb σ) + Pi/quotient
  IsReduced instances + `isReduced_of_injective` on the composed RingHom.
  Axioms clean ×3.  Mathlib-contribution candidate confirmed.
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
- Status: done (2026-07-29) | File: WP/Reduced.lean | Depends: W15, W16
- **Progress**: COMPLETE. Head is a domain by inferInstance (subring of MvPowerSeries
  over K); completeRingEquivCompletionModel (SheafyCompletionModel — NEW import)
  identifies presheafValue (globalLocData DH.P) with the head, giving regularity of
  canonicalMap W upstairs by domain cancellation; prop_8_30_flat_clean_proof at
  (globalLocData DH.P, DH) with rationalOpen_singleton_one + rationalOpen_subset_spa;
  IsSMulRegular.of_flat transports; restrictionMapHom_canonicalMap_generic
  (PresheafFunctoriality — NEW import; do NOT hand-roll the Away.lift show — its
  implicit-instance elaboration gets stuck) identifies the element; headLocEquiv
  pushes to QHead. GOTCHA: state IsDomain-transport haves at the presheafValue-form
  (exact-coercion bridges the CompletionModel alias); smul-goals under
  Function.Injective beta-redexes need `simp only [smul_eq_mul]` first.
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
- Status: done (2026-07-29) | File: WP/Reduced.lean | Depends: W18, W11, R1, R2
- **Progress**: COMPLETE — exactly the planned assembly (headModelData + headLocEquiv
  transport of hred + isReduced_tailC0 w M.N + rhoQ_regular + M.e-transport).
  isReduced_tailC0/isDomain_tailC0 take w N explicitly.
- Decls: `isReduced_presheafValue_WPA`.
- Sketch: W18 model e : presheafValue D ≅ TailC0 (QHead DH); hred gives
  IsReduced (presheafValue DH) ⇒ (headLocEquiv transport) IsReduced (QHead DH);
  R2 ρ-regular; W11 `isReduced_tailC0`; pull back along e
  (`isReduced_of_injective` e.injective).  Sources: [WP] 1267–1297.

### [R4] Reduced.lean IV — chains
- Status: blocked (2026-07-29) | File: WP/Reduced.lean | Depends: R3, W18, R4a, R4b
- **Progress**: BLOCKED on new math — the paper's proof ([WP] 1267-1269) opens with
  "By transitivity of rational localization, it is enough to treat one rational
  localization", and the project deliberately has NO iterated-localization
  composition theorem (Reduced.lean docstring). The ChainReduced recursion therefore
  needs the finite-head-class closure: localizations OF the TailC0-over-head model.
  That requires either (i) the composition/transitivity theorem for rational
  localizations, or (ii) a W17-analogue over the model (sub-tickets below). The n=0
  and n=1 cases are already available (isDomain-of-W5 / R3); the sorry stays until
  R4a/R4b land.

### [R4a] Coefficientwise localization over the model (the FH-closure engine)
- Status: superseded (2026-07-29 ChatGPT-5.6-sol adjudication: ROUTE (i) — generic existential transitivity — chosen over the model re-run; see R4d) | File: WP/CoeffLocalization.lean (extension) | Depends: W17, W18
- Decls (planned): model-level analogues of exists_head_approx (density of the
  M-head images in TailC0 via canonicalMap-density + head density in the base),
  PerturbSetup instantiation at E := TailC0-model (the Perturbation machinery is
  already E-generic), and the W17-analogue: a rational localization of
  TailC0 w N (QHead DH) rho at a datum with entries in the image of the M-heads
  (M >= N) is again TailC0 w M (QHead DH') rho' — [WP]
  prop:coefficientwise-localization re-run with the base replaced by the model
  (the proof is coefficientwise-generic; the paper's transitivity shortcut
  replaced by the direct re-run). ALTERNATIVE (adjudicate first): formalize
  transitivity of rational localization (Huber-standard;
  presheafValue-composition along rationalOpen-inclusion of composed data) —
  possibly SHORTER and reusable project-wide; consult ChatGPT-5.6 before cutting
  the tree.

### [R4b] ChainReduced transport along bicontinuous ring isos
- Status: done (2026-07-29) | File: WP/Reduced.lean | Depends: none
- Decls (planned): RationalLocData pushforward along a bicontinuous e : A ≃+* B
  (pod image subring + T image + s image; hopen through bicontinuity),
  presheafValue-equivalence of a datum and its pushforward, and
  `ChainReduced.of_ringEquiv`. Mechanical but fiddly; independent of R4a.
- **Progress**: DONE — `chainReduced_of_ringEquiv` (WP/Reduced.lean) via the
  PRE-EXISTING generic transport file `RingEquivPresheafTransport.lean`
  (mapRationalRingEquiv + presheafValueRingEquivOfRingEquiv + the valid-datum
  roundtrip — discovered by the ChatGPT-5.6 codex workspace scan; no pod
  transport had to be built). Induction on n with ∀-quantified types; the
  datum-roundtrip's e.symm.symm-slot needs an explicit
  `he2 : Continuous ⇑e.symm.symm` bridge (rw [RingEquiv.symm_symm]), and the
  final transport avoids ill-typed rw-motives via generalize-then-cases
  (`key : ∀ D₂, map-map = D₂ → ChainReduced (presheafValue D₂) n`).
  IsTateRing at values: `presheafValue_isTateRing_concrete` (no noetherianity).

### [R4d] Generic existential transitivity of rational localization (ROUTE (i))
- Status: done (2026-07-29 late) | File: new `RationalTransitivity.lean` (generic, non-WP) | Depends: —
- Statement: for a complete Tate `A` with the presheaf pack and rational `D` on
  `A`, `E` on `B := presheafValue D`, there EXIST `F` rational on `A` and a
  bicontinuous `presheafValue E ≃+* presheafValue F` (existential only — no
  canonical composition, no associativity; 2026-07-29 ChatGPT-5.6-sol design).
- Sketch (Huber Lemma 1.5(ii)-(iii) / Wedhorn Prop 8.2(2)+Rem 8.4; Cont.Val.
  Prop 3.9 via perturbation Lemma 3.10):
  1. PERTURB `E`'s entries (numerators AND denominator, simultaneously) into the
     dense image of the algebraic localization `C ≃ A[1/s]`
     (`UniformSpace.Completion.denseRange_coe`), preserving the rational open
     and with equivalent completed localizations — the W18 PerturbSetup
     machinery instantiated at `B` (it is E-generic).
  2. CLEAR DENOMINATORS: common `k`, lifts `ι(h_j/s^k)`, `ι(q/s^k)`; scale by
     the unit `ι(s)^k` (`rationalOpen_unitSMul`) → datum `(ι H; ι q)`, insert q.
  3. Δ-PADDING (span-⊤ does NOT descend from B): `Δ = {π^m}`, `π` the tnu unit,
     `m` from `exists_pow_dominated_finset`/`exists_zero_nbhd_lt_on_qc`
     (Wedhorn 7.31, Cor732.lean — EXISTS) on the quasi-compact locus where `q`
     doesn't vanish; `S := H ∪ {q} ∪ Δ` spans ⊤ and the open is unchanged.
  4. F := the intersection datum of `(T̄/s)` and `(S/q)` — REUSE the generic
     `RationalLocData.interDatum` + `interDatum_rationalOpen` +
     `interTray_span_eq_top` (RationalIntersection.lean — EXISTS; my
     interDatumHead in WP/Sheafy duplicates it at the head — fleet-dedup note).
  5. UNIVERSAL PROPERTY both ways: in `𝒪_B(scaled-E)`: ι(s), ι(q) units and
     (t·h)/(s·q) = (t/s)(h/q) power-bounded → Φ : 𝒪_A(F) → 𝒪_B(Ẽ⁺); in
     `𝒪_A(F)`: s,q units (IsUnit.mul_iff), t/s = tq/sq, h/q = sh/sq with
     tq, sh ∈ F.T → Ψ backwards; density-uniqueness roundtrips
     (restrictionMapHom_canonicalMap_generic + DenseRange.equalizer).
- Then [R4-final]: invariant Q_n := ∀ D rational, ChainReduced (presheafValue D) n;
  Q_0 = R3; successor: E on 𝒪(D) → F + equivalence → reducedness from R3(F) +
  depth from Q_n(F) transported by `chainReduced_of_ringEquiv`; assemble
  `chainReduced_WPA` with IsReduced 𝒜.
- **Progress (2026-07-29 night)**: [R4-final] DONE — `chainReduced_WPA` compiles
  via the Q_n induction; the ONLY remaining sorry of the R-track is
  `exists_transitivity_WPA` (this ticket's target). REFINED FINDINGS from the
  first implementation probe:
  * The W18 `PerturbSetup` is NORMED (pseudouniformizer with exact scaling,
    norm-1 unit ball in E⁺) — instantiating it at the model TailC0 requires the
    model's SPA/HUBER STACK (PlusSubring, IsTateRing, HasLocLiftPowerBounded,
    rational-open compactness), which DOES NOT EXIST — the model was only ever a
    normed comparison object. Two options: (α) build the model Spa-stack
    (W15/W16-scale arc), or (β) build a TOPOLOGICAL perturbation variant at
    B := presheafValue D directly (B has IsTateRing via
    presheafValue_isTateRing_concrete; Huber Cont.Val. 3.10 is topological).
  * Δ-PADDING pb-dissolution trick: insert the padding numerator ϖ^m ON THE
    B-SIDE first (equal-open by Wedhorn 7.31 domination at B on the compact
    locus + generic equal-open restrictionEquiv), THEN pull down — the
    (t·ϖ^m)/(sq)-power-bounded witness for Φ then comes from the DATUM
    structure itself (numerator fractions are canonically pb), avoiding any
    Spa-pb-transfer (which is UNAVAILABLE — 𝒜 is not stably uniform!).
  * B-side compactness: `isCompact_subtype_rationalOpen` needs a PRINCIPAL
    ideal-of-definition; B's `presheafValue_concretePair` has
    I = Ideal.map (…) (locIdeal P T s) — principality UNVERIFIED (probe
    locIdeal's def; the SpaCompactNoHArch:389 consumer shows the usage shape).
  * NEXT: run a /develop --decompose-style leaf pass on this ticket (route α
    vs β adjudication with quotes from Huber Cont.Val. 3.9/3.10) before
    implementing further.

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
- **Progress FINAL**: DONE — `RationalTransitivity.lean` (generic, ValuationSpectrum
  namespace): rationalOpenEqEquiv (+continuities), imgDatum_interRational_rationalOpen,
  exists_rationalLocalization_transitivity. The perturbation/clearing/padding
  had ALREADY been implemented in the library as `exists_downstairs_rationalDatum`
  (SpaRationalSubsetCorrespondence.lean:132, sorry-free axiom-clean) — found by
  the ChatGPT-5.6 codex workspace scan; the keystone (RelativeDescent:634) is
  the Wedhorn 8.2(2)/8.4 half. `exists_transitivity_WPA` :=
  the generic theorem + hasLocLiftPowerBounded_faithful.
  `chainReduced_WPA` therefore COMPLETE — [WP] thm 6.2(3) done conditionally on
  HeadLocsReduced. Axiom caveat: the chain transitively inherits the central
  library's audit-pass-2 flatness WIP (prop_8_30_flat_clean,
  WedhornStronglyNoetherian — a pre-existing documented main-library sorry,
  consumed via R2's Wedhorn-8.30 wrapper; NOT WP-campaign work; it will clear
  when the audit lane lands). Gotchas: auto-bound universes (u_A) are rejected
  by lake-build (explicit `universe` decl BEFORE the docstring — `universe X in`
  between doc and theorem is a parse error); RingEquiv.trans-coe continuity
  goals need show-λ-forms.

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
