# Ticket Board — §3 Measures and Iwasawa algebras

Source: RJW arXiv:2309.15692, TeX in `.mathlib-quality/references/` (line numbers cited
per ticket). Decomposition + per-leaf verbatim quotes + attack logs:
`.mathlib-quality/decomposition.md` (leaf labels L*.* below refer to it).
Skeleton: all statements already exist as `:= by sorry` in `PadicLFunctions/Measure/`;
**tickets are "fill the sorry at file:decl"** — statements are quoted for convenience
but the skeleton is canonical. `lake build` green at board creation.

## Summary
- Boards: §3 (T001–T029), §4 (T03x–T1xx), §5 (T5xx), §6 (T601–T618), §7 (T701–T708), §8 (T801–T808), §§9–10 (T901–T912 + T903b/T904b), §11 (T1101–T1114), **§12 (T1201–T1207 + CLEANUP-121…124 + CLEANUP-ALL-7)** + cleanups
- Open: **the §12 board (T1201–T1207; skeleton landed 2026-06-14 — 6 files under PadicLFunctions/IwasawaProof/, full build green, 37 sorries confined there, no lint warnings — awaiting 1i approval → /beastmode)** + 1 blocked (CLEANUP-FINAL — lean-lsp-MCP session) + 3 gated (D611–D613 — D61 1i review) | §§3–11 ALL PROOF TICKETS DISCHARGED, project compiles, §§3–11 declarations sorry-free + axioms standard (the only sorries are the §12 skeleton's). §11 milestone `cyclo_mem_cycloTower1`; T1113 statement-fix b2-logged
- Parallel capacity: ~3 workers (per-file chains are sequential; Basic / Toolbox-tail /
  UnitsZp / Fubini chains can overlap once their deps are done)
- Standing conventions: `μ ν : PadicMeasure p _`; "𝓐" = `mahlerTransform`;
  coefficients ℤ_p (generality decisions in `plan.md`); workers record B2 stops in
  `.mathlib-quality/b2_log.jsonl`.

---

### [T001] Prove norm_apply_le + continuous (automatic boundedness)
- **Status**: done (2026-06-09; both lemmas proved: max-attainment + p^n-division; LipschitzWith 1) | **File**: PadicLFunctions/Measure/Basic.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemma ×2 | **Leaves**: L1.1, L1.2

#### Statement
`PadicMeasure.norm_apply_le (μ : PadicMeasure p X) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖`
and `PadicMeasure.continuous (μ) : Continuous μ` (Basic.lean:107, 112; `[CompactSpace X]`).

#### Proof sketch
1. `f = 0` case: trivial. Else `‖f‖ = p^{-m}` for some `m : ℕ` (norm values of
   `C(X,ℤ_[p])` lie in `{p^{-k}} ∪ {0}`; sup attained on compact X —
   `ContinuousMap.norm_coe_le_norm` + value-group discreteness, or argue via
   `‖f‖ ≤ p^{-m} ↔ ∀ x, ‖f x‖ ≤ p^{-m}`, which is all that's needed: take the largest
   `m` with `∀ x, ‖f x‖ ≤ p^{-m}`).
2. Divide: each `f x` is divisible by `p^m` (`PadicInt.norm_le_pow_iff_dvd`); define
   `g : C(X, ℤ_[p])` by `g x := ⟨(f x : ℚ_[p]) / p^m, _⟩` (continuity: composition of
   `f` with the isometric `·/p^m` on the closed ball). Then `f = p^m • g`.
3. `μ f = p^m • μ g` (linearity), so `‖μ f‖ ≤ p^{-m}·1 = ‖f‖` (`norm_le_one`).
4. `continuous`: `μ x − μ y = μ (x − y)` + step 3 gives Lipschitz-with-1;
   `LipschitzWith.continuous` (or `AddMonoidHomClass.continuous_of_bound μ 1`).

#### Mathlib lemmas needed
`ContinuousMap.norm_coe_le_norm`, `ContinuousMap.norm_le` (Compact.lean — read),
`PadicInt.norm_le_pow_iff_dvd`, `PadicInt.norm_le_one`, `LipschitzWith.continuous`.

#### Sources
RJW Def. 3.6 + footnote, TeX 759–765 (quote: decomposition L1.1).

#### Generality decision
`X` arbitrary compact (not just profinite) — the proof never uses zero-dimensionality.

---

### [T002] Prove density of locally constant functions
- **Status**: done (2026-06-09; via toZModPow-factorisation: q := toZModPow k ∘ f is locally constant, lift by ZMod.val; error controlled by ker_toZModPow — simpler than the planned cover-disjointification) | **File**: Basic.lean | **Depends on**: none
- **Parallel**: yes (with T001) | **Type**: lemma | **Leaf**: L1.3

#### Statement
`exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) :
∃ g : LocallyConstant X ℤ_[p], ‖f - ↑g‖ ≤ ε` (Basic.lean:123; `[CompactSpace X]`).

#### Proof sketch
1. WLOG `ε = p^{-n}` (shrink). Balls `B(c, p^{-n})` in `ℤ_[p]` are clopen
   (ultrametric). The preimages `f ⁻¹' B(f x, p^{-n})` form a clopen cover of X.
2. Finite subcover (`CompactSpace`); disjointify by subtracting earlier members
   (clopen Boolean algebra), giving a finite clopen partition `{V_i}` with
   `f(V_i) ⊆ B(c_i, p^{-n})`.
3. Define `g := ∑ c_i·𝟙_{V_i}` as `LocallyConstant` (piecewise-constant on a finite
   clopen partition: build with `LocallyConstant.ofIsClopen`-style constructors or
   directly: `IsLocallyConstant` of a function constant on each member of a finite
   clopen partition).
4. `‖f − g‖ ≤ p^{-n}`: pointwise, x ∈ V_i ⟹ ‖f x − c_i‖ ≤ p^{-n}.

#### Mathlib lemmas needed
`IsUltrametricDist.isClopen_ball` (or `Metric.isClopen_ball` for ultrametric —
worker locates exact name in `Analysis/Normed/*/Ultra`), `IsCompact.elim_finite_subcover`,
`IsClopen.diff/inter/union`, `LocallyConstant` constructors, `ContinuousMap.norm_le`.

#### Sources
RJW Rem. 3.8, TeX 782–791 (verbatim quote: decomposition L1.3). 8 source lines → ~25 LOC.

#### Generality decision
Stated for compact X and target ℤ_[p]; the proof works for any ultrametric normed
target — note as a "for mathlib, generalise target" comment but do NOT widen now
(cleanup/PR pass decides).

---

### [T003] Prove ext_locallyConstant
- **Status**: done (2026-06-09; eq_of_forall_dist_le + ultrametric norm_add_le_max + T001/T002) | **File**: Basic.lean | **Depends on**: T001, T002 | **Type**: lemma | **Leaf**: L1.4

#### Statement
`ext_locallyConstant {μ ν} (h : ∀ g : LocallyConstant X ℤ_[p], μ ↑g = ν ↑g) : μ = ν`
(Basic.lean:131).

#### Proof sketch
1. `LinearMap.ext f`; fix `f`. By T002 pick `g_n` with `‖f − g_n‖ ≤ p^{-n}`.
2. `‖μ f − ν f‖ = ‖μ(f − g_n) − ν(f − g_n)‖ ≤ max(‖μ (f−g_n)‖, ‖ν (f−g_n)‖) ≤ p^{-n}`
   (T001 + ultrametric `norm_sub_le_max`); let `n → ∞`. Or: `Continuous.ext_on`
   with the dense range of `LocallyConstant.toContinuousMap` (density set form of T002).

#### Mathlib lemmas needed
`IsUltrametricDist.norm_sub_le_max` (or `norm_add_le_max`), `norm_le_zero_iff`,
optionally `Continuous.ext_on` + `DenseRange`.

#### Sources
RJW Rem. 3.8, Eq. (3.1), TeX 787–799.

#### Generality decision
As skeleton.

### [CLEANUP-1] Run /cleanup on PadicLFunctions/Measure/Basic.lean
- **Status**: done (2026-06-09; degraded mode: lean-lsp MCP unavailable this session — mathlib linter set is ON in lakefile and the file builds with zero warnings; axioms standard on all 4 decls; full-tooling pass deferred to CLEANUP-FINAL) | **Depends on**: T003 | **Type**: cleanup
- 3rd proof ticket on the file + final per-file cleanup (T001–T003 complete the file).

---

### [T004] Prove the evaluation formula apply_eq_tsum
- **Status**: done (2026-06-10; HasSum.map through toAddMonoidHom) | **File**: Measure/MahlerTransform.lean | **Depends on**: CLEANUP-1
- **Type**: lemma | **Leaf**: L2.1

#### Statement
`apply_eq_tsum (μ) (f) : μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * mahlerCoeff p μ n`
(MahlerTransform.lean:62).

#### Proof sketch
1. `PadicInt.hasSum_mahler f : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] ⇑f 0) n) f`
   (E := ℤ_[p]; all instances present).
2. Map through μ: μ is a continuous additive map (T001/L1.2) —
   `HasSum.map _ (μ : C(_,_) →+ ℤ_[p])`-style with `PadicMeasure.continuous`.
3. `μ (mahlerTerm a n) = a * μ (mahler n)`: `mahlerTerm_apply`/definition
   (`mahlerTerm a n = (mahler n) • const a`; for E = ℤ_[p] this is `a • mahler n`
   up to `smul_eq_mul` and constant-factoring via `map_smul`). Conclude with
   `HasSum.tsum_eq` + commutativity of the factors.

#### Mathlib lemmas needed
`PadicInt.hasSum_mahler` (MahlerBasis.lean:339), `mahlerTerm_apply` (:256),
`HasSum.map`, `HasSum.tsum_eq`, `map_smul`, `smul_eq_mul`.

#### Sources
RJW Thm. 3.20 proof, TeX 995–998 (quote: decomposition L2.1).

#### Generality decision
ℤ_p coefficients (plan.md §Generality 1).

---

### [T005] Prove mahlerTransform_dirac (𝓐 δ_a = (1+T)^a)
- **Status**: done (2026-06-10; simp with binomialSeries_coeff) | **File**: MahlerTransform.lean | **Depends on**: CLEANUP-1
- **Parallel**: yes (with T004) | **Type**: lemma | **Leaf**: L2.2

#### Statement
`mahlerTransform_dirac (a : ℤ_[p]) : mahlerTransform p (dirac p a) = binomialSeries ℤ_[p] a`
(MahlerTransform.lean:70).

#### Proof sketch
1. `PowerSeries.ext n`; LHS coeff = `dirac p a (mahler n) = Ring.choose a n`
   (`coeff_mahlerTransform` simp + `mahler_apply`).
2. RHS coeff = `Ring.choose a n • (1 : ℤ_[p])` (`binomialSeries_coeff`); finish
   `smul_eq_mul, mul_one`.

#### Mathlib lemmas needed
`PowerSeries.ext`, `binomialSeries_coeff` (PowerSeries/Binomial.lean:50),
`mahler_apply` (MahlerBasis.lean:107).

#### Sources
RJW Ex. 3.16, TeX 968–973.

#### Generality decision
As skeleton.

---

### [T006] Prove ofPowerSeries well-defined + mahlerTransform_ofPowerSeries
- **Status**: done (2026-06-10; summable helper + δ-identity transport) | **File**: MahlerTransform.lean | **Depends on**: T004
- **Type**: def-fields + lemma | **Leaf**: L2.4

#### Statement
Fill `ofPowerSeries.map_add'`, `.map_smul'` (MahlerTransform.lean:85–88) and
`mahlerTransform_ofPowerSeries (g) : mahlerTransform p (ofPowerSeries p g) = g` (:95).

#### Proof sketch
1. Summability of `fun n => Δⁿf(0) * g_n`: `PadicInt.fwdDiff_tendsto_zero f` +
   `‖g_n‖ ≤ 1` ⟹ terms → 0 ⟹ summable
   (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`).
2. `map_add'`: `fwdDiff_iter_add` pointwise + `tsum_add` (both summable by 1).
   `map_smul'`: `fwdDiff_iter_const_smul` + `tsum_const_smul`-form.
3. For the transform identity: coeff k of LHS = `ofPowerSeries g (mahler k) =
   ∑' n, Δⁿ(mahler k)(0) * g_n`. Key: `Δ_[1]^[n] (mahler k) 0 = if n = k then 1 else 0`.
   Route: `mahler k = mahlerSeries (Pi.single k (1 : ℤ_[p]))` (check by
   `mahlerSeries_apply_nat`-style evaluation on ℕ + `denseRange_natCast.equalizer`,
   mirroring MahlerBasis.lean:344–349), then `fwdDiff_mahlerSeries` (:313). Or
   directly via `fwdDiff_iter_eq_sum_shift` + `fwdDiff_iter_choose_zero` (:332 usage).
4. The tsum collapses to `g_k` (`tsum_ite_eq`-pattern).

#### Mathlib lemmas needed
`fwdDiff_tendsto_zero` (:224), `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
(:287 usage), `fwdDiff_iter_add`, `fwdDiff_iter_const_smul` (:362, :367 usages),
`fwdDiff_mahlerSeries` (:313), `tsum_add`, `tsum_ite_eq`, `denseRange_natCast`.

#### Sources
RJW Thm. 3.20 proof, TeX 1000–1004 (quote: decomposition L2.4).

#### Generality decision
As skeleton.

### [CLEANUP-2] Run /cleanup on MahlerTransform.lean (cadence)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T006 | **Type**: cleanup (after 3rd ticket on file)

---

### [T007] Prove mahlerTransform_injective + assemble mahlerLinearEquiv
- **Status**: done (2026-06-10; Thm 3.20 linear part sorry-free) | **File**: MahlerTransform.lean | **Depends on**: CLEANUP-2
- **Type**: lemma + def-fields | **Leaves**: L2.3, L2.5

#### Statement
`mahlerTransform_injective` (:77); fill `mahlerLinearEquiv.left_inv/right_inv` (:102).

#### Proof sketch
1. Injectivity: `𝓐μ = 𝓐ν ⟹ ∀ n, μ (mahler n) = ν (mahler n)` (coeff ext) ⟹
   `μ f = ν f` by T004 evaluation formula.
2. `right_inv` = T006. `left_inv`: `ofPowerSeries (𝓐 μ) f = ∑' Δⁿf(0)·μ(mahler n) = μ f`
   by T004 read backwards. `LinearMap.ext`.

#### Mathlib lemmas needed
`PowerSeries.ext_iff`, `LinearMap.ext`; rest internal (T004, T006).

#### Sources
RJW Thm. 3.20, TeX 994–1005.

### [CLEANUP-3] Run /cleanup on MahlerTransform.lean (final)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T007 | **Type**: cleanup

---

### [T008] Transport ring structure: mahlerTransform_mul/one, CommRing laws, mahlerRingEquiv
- **Status**: done (2026-06-10; transport bookkeeping, ring laws via 𝓐-injectivity) | **File**: Measure/Convolution.lean | **Depends on**: T007
- **Type**: instance + lemmas | **Leaf**: L3.1

#### Statement
Fill sorries at Convolution.lean:46–86 (`mahlerTransform_mul`, `mahlerTransform_one`,
all CommRing fields, `mahlerRingEquiv.map_mul'`).

#### Proof sketch
1. `mahlerTransform_mul`: unfold `mul_def`; `mahlerLinearEquiv.apply_symm_apply`.
2. `mahlerTransform_one`: `one_def` + T005 at a = 0 + `binomialSeries_zero`.
3. Each ring law: apply `(mahlerLinearEquiv p).injective`, push through with
   `mahlerTransform_mul`/`map_add`, use the corresponding law in `PowerSeries ℤ_[p]`.
   (E.g. assoc: both sides ↦ `(𝓐μ·𝓐ν)·𝓐ρ = 𝓐μ·(𝓐ν·𝓐ρ)`.)
4. `mahlerRingEquiv.map_mul'` := `mahlerTransform_mul`.

#### Mathlib lemmas needed
`LinearEquiv.apply_symm_apply`, `LinearEquiv.injective`, `binomialSeries_zero`
(PowerSeries/Binomial.lean:78), `mul_assoc/one_mul/...` in PowerSeries.

#### Sources
RJW Rem. 3.11 "by transport of structure", TeX 907–911.

#### Generality decision
Mul/One instances are placed on the project's `PadicMeasure p ℤ_[p]` (= LinearMap dual)
— verified no mathlib instance clash (decomposition L3.1 attack [5]).

---

### [T009] Prove the convolution formula mul_apply
- **Status**: done (2026-06-10; convInner via curry; Chu-Vandermonde on antidiagonal; 𝓐-injectivity replaced the density step — simpler than planned) | **File**: Convolution.lean | **Depends on**: T008, T003
- **Type**: theorem | **Leaf**: L3.2 (KEY)

#### Statement
`mul_apply (μ ν) (f) : (μ * ν) f = μ ⟨fun x => ν (f.comp ⟨fun y => x + y, _⟩), _⟩`
(Convolution.lean:96). First action: replace the two `by sorry` continuity side-terms
in the STATEMENT with real proofs (inner: `f.comp (addLeft x)` continuity is
`by fun_prop`; outer: factor through `ContinuousMap.curry` — define the inner map as
`(f.comp ⟨fun q : ℤ_[p] × ℤ_[p] => q.1 + q.2, by fun_prop⟩).curry`, then the outer
continuity is `ν ∘ continuous-family`, using `PadicMeasure.continuous` (T001) and
continuity of `curry` application; keep the statement's displayed form via a `rfl`
bridge lemma if needed).

#### Proof sketch
1. Both sides are `ℤ_[p]`-linear and 1-bounded in `f` (T001). By Mahler expansion
   (T004 applied to the equality goal, or T003 + density): suffices on `f = mahler n`.
2. LHS at `mahler n` = coeff n of `𝓐μ·𝓐ν` (T008.1 + `coeff_mahlerTransform`,
   `PowerSeries.coeff_mul`) = `∑_{i+j=n} μ(mahler i)·ν(mahler j)` (antidiagonal).
3. RHS: inner function at fixed x: `y ↦ Ring.choose (x+y) n`; Chu–Vandermonde
   `add_choose_eq` (Commute trivial in comm ring): `choose (x+y) n =
   ∑_{ij ∈ antidiagonal n} choose x ij.1 * choose y ij.2`. ν linear over the finite
   sum: inner integral = `∑_{ij} choose x ij.1 * ν (mahler ij.2)`. This is a FINITE
   ℤ_p-combination of `mahler ij.1` applied to x — μ linear: total
   `∑_{ij} μ(mahler ij.1)·ν(mahler ij.2)`. Matches 2.
4. Extension from basis to all f: define both sides as linear maps in f; they agree on
   `mahler n`; every f is the limit of finite Mahler sums (hasSum_mahler) and both
   sides are continuous in f (T001 with explicit norm bounds for the RHS inner map:
   `‖inner(x)‖ ≤ ‖f‖` pointwise) — `Continuous.ext_on`/tsum-swap argument as in T004.

#### Mathlib lemmas needed
`add_choose_eq` (RingTheory/Binomial.lean:519), `PowerSeries.coeff_mul`,
`Finset.antidiagonal` API, `ContinuousMap.curry` (CompactOpen.lean:419), `map_sum`.

#### Sources
RJW Rem. 3.11 display, TeX 908–910 (quote: decomposition R3 substrate).

#### Generality decision
Stated for the additive group ℤ_p only (multiplicative analogue is PseudoMeasure's
`unitsConv`, definitionally).

---

### [T010] Prove dirac_mul_dirac
- **Status**: done (2026-06-10; binomialSeries_add) | **File**: Convolution.lean | **Depends on**: T008
- **Parallel**: yes (with T009) | **Type**: lemma | **Leaf**: L3.3

#### Statement
`dirac_mul_dirac (a b) : dirac p a * dirac p b = dirac p (a + b)` (Convolution.lean:105).

#### Proof sketch
1. Apply `mahlerTransform_injective` (T007); rewrite with T008.1, T005 twice,
   `binomialSeries_add`, T005 backwards.

#### Mathlib lemmas needed
`binomialSeries_add` (PowerSeries/Binomial.lean:60).

#### Sources
RJW Ex. 3.12 + 3.16, TeX 914–920, 968–973.

### [CLEANUP-4] Run /cleanup on Convolution.lean (3rd ticket + final)
- **Status**: done (2026-06-10; degraded mode — linters on, zero warnings) | **Depends on**: T009, T010 | **Type**: cleanup

---

### [T011] Toolbox: mult-by-x ↔ ∂ and moments
- **Status**: done (2026-06-10; mul_choose_eq by ℕ+density; coeff_del helper) | **File**: Measure/Toolbox.lean | **Depends on**: T007
- **Type**: lemma ×2 | **Leaves**: L4.1, L4.2

#### Statement
`mahlerTransform_cmul_X` (Toolbox.lean:46) and `apply_powCM` (:56).

#### Proof sketch
1. Binomial identity over ℤ_p: `x * choose x n = (n+1)·choose x (n+1) + n·choose x n`.
   Prove on ℕ (cast of `Nat.succ_mul_choose_eq`-area arithmetic: source line 1074
   identity), extend by `denseRange_natCast` + continuity (`continuous_choose`).
2. Coefficientwise: `(cmul id μ)(mahler n) = μ(x·choose) = (n+1)μ(mahler(n+1)) + n·μ(mahler n)`;
   `coeff n (del F) = coeff n (F') + coeff n (X·F') = (n+1)F_{n+1} + n·F_n`
   (`coeff_derivativeFun`). `PowerSeries.ext`.
3. `apply_powCM` by induction on k: base `μ(1) = constantCoeff 𝓐μ` (mahler 0 = 1);
   step: `x^{k+1} = x·x^k` ⟹ `μ(pow (k+1)) = (cmul id μ)(pow k)` + step 2 + IH.

#### Mathlib lemmas needed
`coeff_derivativeFun` (PowerSeries/Derivative.lean:46), `Nat.succ_mul_choose_eq`,
`PadicInt.continuous_choose` (MahlerBasis.lean:93), `PadicInt.denseRange_natCast`,
`PowerSeries.constantCoeff`, `Function.iterate_succ_apply'`.

#### Sources
RJW Lem. 3.24 + Cor. 3.25, TeX 1059–1082 (quotes: decomposition L4.1, L4.2).

---

### [T012] Toolbox: clopens and restriction additivity
- **Status**: done (2026-06-10; closedBall + compl; indicator additivity) | **File**: Toolbox.lean | **Depends on**: T001 (only)
- **Parallel**: yes | **Type**: lemma ×3 | **Leaf**: L4.3

#### Statement
`isClopen_pZp` (:121), `isClopen_units` (:138), `res_union` (:73).

#### Proof sketch
1. `{‖x‖ < 1}`: equals `{x : ‖x‖ ≤ p⁻¹}` (value-group discreteness:
   `PadicInt.norm_lt_one_iff_dvd` / `norm_le_pow_iff_dvd`); closed ball clopen in
   ultrametric: closed by continuity of norm, open since ultrametric balls are open
   (`IsUltrametricDist` API).
2. `{IsUnit x} = {‖x‖ = 1}` (`PadicInt.isUnit_iff`) = complement of 1 ⟹ clopen.
3. `res_union`: `charFn (U ∪ V) = charFn U + charFn V` for disjoint clopens
   (`LocallyConstant.coe_charFn` = `Set.indicator U 1`; `Set.indicator_union_of_disjoint`),
   then linearity of `cmul` in g.

#### Mathlib lemmas needed
`PadicInt.isUnit_iff` (:366), `PadicInt.norm_lt_one_iff_dvd`,
`LocallyConstant.coe_charFn` (LocallyConstant/Algebra.lean:94),
`Set.indicator_union_of_disjoint`, `IsClopen.union/compl`.

#### Sources
RJW §3.5.3, TeX 1098–1129.

---

### [T013] Toolbox: shiftDiv and the ψ operator's well-definedness
- **Status**: done (2026-06-10; digit via toZModPow 1 — cleaner than appr as ticket anticipated) | **File**: Toolbox.lean | **Depends on**: T012
- **Type**: def-fields + lemma | **Leaf**: L4.5

#### Statement
Fill `shiftDiv` membership + continuity (:115–117), `shiftDiv_mul` (:125),
`psi.map_add'/map_smul'` (:147–149).

#### Proof sketch
1. Membership: `‖x − appr x 1‖ ≤ p⁻¹` (mathlib `PadicInt.dist_appr_spec`-family at
   RingHoms.lean:695 area — `x ≡ appr x 1 mod p`), so division by p lands in ℤ_p
   (`PadicInt.norm_le_pow_iff_dvd`).
2. Continuity: `x ↦ appr x 1` is locally constant (depends only on `toZMod x`:
   `appr x 1` vs `ZMod.val (toZMod x)` — worker reconciles via `PadicInt.appr_spec 1` +
   `ker_toZMod`; if `appr` proves awkward, REDEFINE shiftDiv with
   `(x − (ZMod.val (PadicInt.toZMod x) : ℤ_[p]))/p` — same function, cleaner: toZMod is
   continuous-to-discrete hence locally constant); then shiftDiv = (x − lc(x))·p⁻¹
   continuous.
3. `shiftDiv_mul`: `toZMod (p*x) = 0` ⟹ digit 0 ⟹ `(px − 0)/p = x`.
4. ψ fields: linearity of f ↦ 𝟙·(f ∘ shiftDiv) + μ linear.

#### Mathlib lemmas needed
`PadicInt.appr_spec`, `PadicInt.ker_toZMod`/`ker_toZModPow` (RingHoms.lean:457),
`ZMod.val_cast_of_lt`, `PadicInt.norm_le_pow_iff_dvd`.

#### Sources
RJW §3.5.5 ψ-definition, TeX 1147–1148.

#### Generality decision
Off-`pℤ_p` values of shiftDiv are irrelevant (cut by indicator); canonical digit choice.

### [CLEANUP-5] Run /cleanup on Toolbox.lean (cadence, after 3rd ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T013 | **Type**: cleanup

---

### [T014] Toolbox: σ/φ transforms and the φψ identities + Cor. 3.32
- **Status**: done (2026-06-10; general mahlerTransform_pushforward_mulCM lemma covers σ_a AND φ; coeff_subst' + finsum truncation + add_pow; φψ identities pointwise) | **File**: Toolbox.lean | **Depends on**: CLEANUP-5, T009
- **Type**: theorem ×6 | **Leaves**: L4.4, L4.6, L4.7

#### Statement
`mahlerTransform_sigma` (:97), `mahlerTransform_phi` (:106), `psi_phi` (:152),
`phi_psi` (:158), `res_units_eq` (:146), `isSupportedOn_units_iff_psi_eq_zero` (:167).

#### Proof sketch
1. σ/φ transforms (L4.4 route, decomposition): fix n. On ℕ:
   `choose (a*k) n = ∑_{m ≤ n} choose k m * c_{n,m}` with
   `c_{n,m} := coeff n ((binomialSeries a − 1)^m)` — from
   `binomialSeries (a*k) = (binomialSeries a)^k` (iterate `binomialSeries_add` /
   `binomialSeries_nat` for ℕ-powers) + binomial expansion of `(1 + (B−1))^k` +
   order-≥-m truncation (`constantCoeff (B−1) = 0` via `binomialSeries_constantCoeff`).
   Extend to `x ∈ ℤ_p` by density/continuity. Apply μ; identify RHS with
   `coeff_subst` (HasSubst.of_constantCoeff_zero'; `subst` coefficient formula —
   finite by the same order argument).
2. `psi_phi`/`phi_psi`: `LinearMap.ext f`; pointwise function identities
   `𝟙_{pℤ_p}(p*x) = 1`, `shiftDiv (p*x) = x` (T013), exactly the source's two displays
   (TeX 1149–1151). `ContinuousMap.ext` + `mul_comm` plumbing.
3. `res_units_eq`: partition `𝟙_{units} = 1 − 𝟙_{pℤ_p}` (complement clopen sets:
   `isUnit_iff`/`not_isUnit_iff` ↔ norm dichotomy) + `phi_psi`.
4. Cor 3.32: (⇒) ψ-apply to `res_units_eq`-fixed point; `ψ(φ(ψμ)) = ψμ` by `psi_phi`
   ⟹ ψμ = ψμ − ψμ = 0. (⇐) `res_units_eq` with ψμ = 0.

#### Mathlib lemmas needed
`binomialSeries_nat` (:69), `binomialSeries_constantCoeff` (:55),
`HasSubst.of_constantCoeff_zero'` (Substitution.lean:67), `PowerSeries.coeff_subst`
(worker reads Substitution.lean for the exact finsum form), `PadicInt.not_isUnit_iff`
(:385).

#### Sources
RJW §3.5.5, TeX 1133–1167 (verbatim displays quoted in decomposition L4.4/L4.6/L4.7).

### [CLEANUP-6] Run /cleanup on Toolbox.lean (final)
- **Status**: done (2026-06-10; degraded mode — note: `show` style warnings queued for CLEANUP-FINAL) | **Depends on**: T014 | **Type**: cleanup

---

### [T015] Units geometry: CompactSpace ℤ_[p]ˣ + topological instances + unitsValCM
- **Status**: done (2026-06-10; embedProduct closed range; T2 was already a mathlib instance; t.d. via opHomeomorph transfer) | **File**: Measure/UnitsZp.lean | **Depends on**: none
- **Parallel**: yes (anytime) | **Type**: instance + def-field | **Leaf**: L5.3 (+ L5.4 part)

#### Statement
`instance : CompactSpace ℤ_[p]ˣ` (UnitsZp.lean:26), `unitsValCM` continuity (:30).
ALSO: derive/provide `T2Space ℤ_[p]ˣ` and `TotallyDisconnectedSpace ℤ_[p]ˣ` instances
(needed by T019's integral_swap at X = ℤ_[p]ˣ — add them in this file if not inferred).

#### Proof sketch
1. `Units.embedProduct ℤ_[p] : ℤ_[p]ˣ → ℤ_[p] × ℤ_[p]ᵐᵒᵖ` is an embedding (mathlib
   `Units.isEmbedding_embedProduct`). Its range is `{q | q.1 * q.2.unop = 1 ∧
   q.2.unop * q.1 = 1}` — closed (preimage of {1} under continuous maps). Closed in
   compact ⟹ compact; embedding ⟹ `CompactSpace` via `isCompact_range`/
   `IsCompact.of_isClosed_subset` + `CompactSpace.of_isCompact_univ`-style transfer.
2. `unitsValCM`: `Units.continuous_val` (exists as `Units.continuous_val` or
   `continuous_coe`; fallback: `(continuous_fst.comp (Units.isEmbedding_embedProduct).continuous)`).
3. T2/TotDisc: embedding into the T2, totally disconnected `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`
   (products preserve both; `IsEmbedding.t2Space`, subtype/embedding transfer for
   `TotallyDisconnectedSpace` — `IsEmbedding.injective` + `isTotallyDisconnected_of_image`-style).

#### Mathlib lemmas needed
`Units.isEmbedding_embedProduct` (Topology/Algebra/Constructions.lean — read),
`IsClosed.preimage`, `IsCompact.of_isClosed_subset`, `IsEmbedding.t2Space` family.

#### Sources
Implicit in RJW line 747; pure topology.

#### Generality decision
A `CompactSpace Mˣ` instance for `M` compact T2 topological monoid is the right mathlib
generality — note for the PR pass; prove for ℤ_[p] now (instance placement local).

---

### [T016] Units: extendByZero + iota_injective
- **Status**: done (2026-06-10; unitsHomeo via homeoOfEquivCompactToT2; extendByZero glued on clopen cover) | **File**: UnitsZp.lean | **Depends on**: T015, T012
- **Type**: def-fields + lemma | **Leaf**: L5.4

#### Statement
`extendByZero` continuity/linearity + `extendByZero_coe_unit` (:34–43),
`iota_injective` (:54).

#### Proof sketch
1. Continuity of the extension: `{IsUnit x}` clopen (T012); on it the function is
   `g ∘ (partial inverse of val)` — continuity via the closed-embedding of val
   (T015: continuous injective from compact to T2 ⟹ closed embedding
   `Continuous.isClosedEmbedding`) — `IsClosedEmbedding.continuousOn_inv`-style, or
   gluing: `ContinuousOn.if'`-family on the clopen partition (continuousOn each piece,
   pieces clopen ⟹ continuous global).
2. `extendByZero_coe_unit`: `dif_pos` + `IsUnit.unit_spec` injectivity of val.
3. `iota_injective`: if `ιμ = 0` then for any `g : C(ℤ_[p]ˣ, ℤ_[p])`,
   `μ g = μ ((extendByZero g).comp valCM) = (ιμ)(extendByZero g) = 0` — the first
   equality is `extendByZero_coe_unit` (restriction∘extension = id) via
   `ContinuousMap.ext`.

#### Mathlib lemmas needed
`Continuous.isClosedEmbedding` (compact-to-T2), `continuousOn_iff`-gluing or
`IsClopen.continuous_piecewise`-shape lemmas, `dif_pos`, `Units.ext`.

#### Sources
RJW Rem. 3.33, TeX 1169–1172 (verbatim in decomposition L5.4).

---

### [T017] Units: res_iota + mem_range_iota_iff (image = ker ψ)
- **Status**: done (2026-06-10; range ι = ker ψ both directions) | **File**: UnitsZp.lean | **Depends on**: T016, T014
- **Type**: theorem ×2 | **Leaf**: L5.4 (rest)

#### Statement
`res_iota` (:60), `mem_range_iota_iff` (:66).

#### Proof sketch
1. `res_iota`: `(res ι μ) f = μ ((𝟙_{units}·f) ∘ val) = μ (f ∘ val)` since
   `𝟙_{units}(val u) = 1` pointwise.
2. (⇒): given μ = ιν: ψμ = 0 by Cor 3.32 (T014) once `res_units μ = μ` (step 1).
3. (⇐): ψμ = 0 ⟹ μ = res_units μ (T014) ⟹ μ = ι(pushforward-restriction of μ):
   exhibit preimage `ν := μ ∘ extendByZero` (precomposition linear map); check
   `ιν = μ`: `(ιν) f = μ (extendByZero (f ∘ val)) = μ (𝟙_{units}·f) = res μ f = μ f`
   — middle equality: `extendByZero (f∘val) = 𝟙_{units}·f` pointwise (dif split).

#### Mathlib lemmas needed
Internal + `Set.indicator` arithmetic.

#### Sources
RJW Rem. 3.33, TeX 1171–1172.

### [CLEANUP-7] Run /cleanup on UnitsZp.lean (3rd ticket + final)
- **Status**: done (2026-06-10; degraded mode — show-linter warnings queued) | **Depends on**: T017 | **Type**: cleanup

---

### [T018] Fubini: clopen-box decomposition of locally constant functions
- **Status**: done (2026-06-10; REPLANNED per beastmode replan-and-continue: clopen-box decomposition replaced by locally-constant approximation of the CURRIED map — new lemma exists_locallyConstant_norm_sub_le' (general ultrametric target, mathlib PR candidate); the box lemma was dropped as unnecessary, and integral_swap lost its T2/TotallyDisconnected hypotheses. decomposition.md L5.1 superseded accordingly) | **File**: Measure/Fubini.lean | **Depends on**: none
- **Parallel**: yes (anytime) | **Type**: theorem | **Leaf**: L5.1

#### Statement
`locallyConstant_prod_mem_span_boxes` (Fubini.lean:48).

#### Proof sketch
1. `F : LocallyConstant (X×Y) ℤ_p` has finite range (compact domain:
   `LocallyConstant.range_finite`); the fibres `F⁻¹{c}` are clopen, finitely many,
   partition X×Y.
2. Each point of a fibre has a basic clopen box neighbourhood inside it: clopen boxes
   form a basis of X×Y for X, Y compact T2 totally disconnected (clopen sets are a
   basis in each factor — `compact_t2_tot_disc_iff_tot_sep`-family /
   `TopologicalSpace.IsTopologicalBasis.prod` of the clopen bases; worker locates
   modern names, fallback `DiscreteQuotient` route: F factors through a finite discrete
   quotient of X×Y, and discrete quotients of a product are refined by products of
   discrete quotients — `DiscreteQuotient.prod` API if present).
3. Compactness of each fibre: finite box subcover; disjointify boxes to a finite grid:
   take the common refinement of all the X-side and Y-side pieces (finite Boolean
   algebra of clopens), yielding a partition by boxes `A_j × B_k` on which F is
   constant.
4. `F = ∑_{j,k} F(a_jk)·𝟙_{A_j}·𝟙_{B_k}` exactly; each summand is in the generating
   set (charFn comp fst/snd product); conclude `Submodule.sum_mem`.

#### Mathlib lemmas needed
`LocallyConstant.range_finite`, `IsLocallyConstant.isClopen_fiber`,
clopen-basis lemma (worker locates; candidates in `Topology/Separation/*`,
`Topology/Connected/TotallyDisconnected.lean`), `Submodule.sum_mem`, `Finset.sup`/
partition-refinement combinatorics.

#### Sources
Expansion of RJW line 910 "One checks…" via the Rem. 3.8 technique (decomposition L5.1).

---

### [T019] Fubini: integral_swap
- **Status**: done (2026-06-10; swap via finite fibre sums of the locally constant approximation; ultrametric dist_triangle_max closes) | **File**: Fubini.lean | **Depends on**: T018, T002, T001
- **Type**: theorem | **Leaf**: L5.2

#### Statement
`integral_swap` (Fubini.lean:62). Also fill `innerInt`'s continuity sorry (:37):
`x ↦ ν (F.curry x)` is continuous since `F.curry : C(X, C(Y, ℤ_[p]))` (mathlib curry,
compact-open) and ν is continuous (T001) — composition.

#### Proof sketch
1. Both sides linear + 1-bounded in F (T001 twice, `innerInt` norms ≤ ‖F‖).
2. For F in the box-span (T018): expand by linearity to `F = 𝟙_U×𝟙_V`:
   LHS = `μ(𝟙_U·ν(𝟙_V)) = ν(𝟙_V)·μ(𝟙_U)`; RHS symmetric — equal.
3. Locally constant F: T018 + linearity. General F: density on the compact X×Y
   (T002 with X := X×Y) + continuity in F (1): standard ε-argument
   (`Continuous.ext_on` on the dense set of locally constant maps).

#### Mathlib lemmas needed
`ContinuousMap.curry` (CompactOpen.lean:419) + its continuity lemmas
(`ContinuousMap.continuous_curry'`-family), `Continuous.ext_on`, `DenseRange`.

#### Sources
Expansion of RJW Rem. 3.11 "One checks", TeX 910; technique = Rem. 3.8.

### [CLEANUP-8] Run /cleanup on Fubini.lean (final)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T019 | **Type**: cleanup

---

### [T020] Λ(ℤ_p^×): unitsConv well-defined + CommRing laws
- **Status**: done (2026-06-10; unitsConv via innerInt; CommRing laws by show-driven defeq + integral_swap for comm) | **File**: Measure/PseudoMeasure.lean | **Depends on**: T019, T015
- **Type**: def-fields + instance | **Leaf**: L5.5

#### Statement
Fill `unitsMulCM` continuity (:38), `unitsConv` fields (:44–47), CommRing fields
(:64–72).

#### Proof sketch
1. `unitsMulCM` continuity: `ContinuousMul ℤ_[p]ˣ` (mathlib units-of-topological-monoid
   instance; worker locates — `Units.instContinuousMul`-shape in
   Topology/Algebra/Constructions or Group/Basic; fallback via embedProduct).
2. `unitsConv` inner-map continuity: rewrite `fun x => ν (f.comp (unitsMulCM x))` as
   `ν ∘ (G.curry)` for `G := f.comp mulCM₂` with `mulCM₂ : C(ℤ_[p]ˣ × ℤ_[p]ˣ, ℤ_[p]ˣ)`
   the multiplication (continuity: ContinuousMul) — same pattern as T009/T019.
   Linearity fields: ν, μ linear.
3. `mul_comm`: `integral_swap` (T019) with `F := f ∘ mul`; note
   `f((x·y)) = f((y·x))` (CommGroup) reconciles the swapped order.
4. `mul_assoc`: both sides = triple integral of `f(xyz)`; two unfoldings + one swap.
5. `one_mul/mul_one`: δ_1 evaluation: inner integral at f.comp(mul 1) = f. Distrib/zero:
   linearity in each slot (μ, ν enter linearly).

#### Mathlib lemmas needed
`ContinuousMap.curry`, units `ContinuousMul` instance, internal T019.

#### Sources
RJW Eq. (3.11), TeX 1173–1175 + Rem. 3.11 "one checks".

#### Generality decision
ℤ_p^×-specific (no `to_additive` gymnastics; plan.md §Generality 4). The convolution
orientation (ν inner) is recorded in `units_mul_def`; §4 pass must quote it.

---

### [T021] Λ(ℤ_p^×): Dirac multiplicativity + degree ring hom
- **Status**: done (2026-06-10; dirac mult is rfl; deg ring hom) | **File**: PseudoMeasure.lean | **Depends on**: T020
- **Type**: lemma + def-fields | **Leaves**: L5.5 (tail), L5.6

#### Statement
`units_dirac_mul_dirac` (:75), `deg` fields (:85–90); `augmentationIdeal` is then
definitional.

#### Proof sketch
1. `(δ_u * δ_v) f = (f ∘ mul_u)(v) = f(u·v)` — unfold unitsConv, two dirac_apply.
2. `deg` fields: map_one: `δ_1(1) = 1`; map_mul: `(μ*ν)(1) = μ(x ↦ ν(1·)) = μ(ν(1)·1)`
   wait — inner: `1.comp (mulCM x) = 1` so inner integral is constant `ν 1`; then
   `μ(const (ν 1)) = ν 1 · μ 1` (pull scalar out: `const c = c • 1`). map_add/zero:
   linearity.

#### Sources
RJW Def. 3.37, TeX 1245–1253.

---

### [T022] Λ(ℤ_p^×): finite-level maps (levelMap cluster)
- **Status**: done (2026-06-10; levelMap ring hom incl. convolution-of-indicators map_mul; fibre clopen; + coefficient/transition/partition lemmas) | **File**: PseudoMeasure.lean | **Depends on**: T020, T003
- **Type**: lemma + def-fields ×2 | **Leaf**: L5.7

#### Statement
`isClopen_unitsToZModPow_fiber` (:107), `levelMap` ring-hom fields (:116–126),
`levelMap_jointly_injective` (:131).

#### Proof sketch
1. Fibre clopen: `unitsToZModPow n` is continuous-to-discrete: it factors through
   `toZModPow n` (kernel = `p^n`-span, RingHoms.lean:457) — preimage of a point under
   a locally constant map. Concretely: `val ⁻¹' (toZModPow n ⁻¹' {lift})`-intersections;
   use `IsLocallyConstant` of toZModPow (`PadicInt.continuous_toZModPow` + discrete).
2. map_one: δ_1 hits only the fibre of 1̄: single = 1. map_add/zero: linearity of μ ↦
   each coefficient. map_mul: `(μ*ν)(𝟙_{c̄-fibre})`: inner function
   `x ↦ ν(𝟙_{c̄}(x·))`; `𝟙_{c̄-fibre}(xy) = ∑_{āb̄=c̄} 𝟙_{ā}(x)𝟙_{b̄}(y)` (coset
   partition identity: for fixed x in the ā-fibre, `xy ∈ c̄-fibre ↔ y ∈ (ā⁻¹c̄)-fibre`);
   expand both sides into `∑_{āb̄=c̄} μ(𝟙_ā)ν(𝟙_b̄)`; match
   `MonoidAlgebra.single_mul_single` summed over the group.
3. Joint injectivity: by T003 (ext on locally constant) it suffices that μ kills every
   `g : LocallyConstant ℤ_[p]ˣ ℤ_[p]`. g factors through level n for some n: the
   fibres of `unitsToZModPow n` form a neighbourhood basis refinement — uniform
   local-constancy on the compact ℤ_[p]ˣ: g is constant on `u·(1 + p^nℤ_p)`-cosets for
   n large (Lebesgue-number argument via the ultrametric on val-image, or:
   `DiscreteQuotient`/`LocallyConstant.factors`-API). Then g = ∑ values·fibre-indicators,
   and `levelMap n μ = 0` gives `μ g = 0`.

#### Mathlib lemmas needed
`PadicInt.ker_toZModPow` (RingHoms.lean:457), `PadicInt.toZModPow` continuity
(`continuous_toZModPow` — locate), `MonoidAlgebra.single` API
(`single_mul_single`, `Finsupp.ext`), `Fintype.sum` reindexing (`Fintype.sum_equiv`
along `(·*c̄⁻¹)`).

#### Sources
RJW TeX 888–892 (quote in decomposition L5.7); the cofinal-chain restriction is
recorded there (attack [4]).

### [CLEANUP-9] Run /cleanup on PseudoMeasure.lean (cadence, after 3rd ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T022 | **Type**: cleanup

---

### [T023] Zero-divisor lemma (i)
- **Status**: done (2026-06-10; descPochhammer X-divisibility + ψ-fixes-δ₀ argument, ξ-free as planned) | **File**: PseudoMeasure.lean | **Depends on**: CLEANUP-9, T017, T014, T011
- **Type**: theorem | **Leaf**: L5.8

#### Statement
`eq_zero_of_forall_unitsPowCM_eq_zero` (:147).

#### Proof sketch (ξ-free refinement recorded in decomposition L5.8)
1. Set `M := iota μ ∈ Λ(ℤ_p)`. For n ≥ 1: `n! • (M (mahler n)) = M (descPochhammer-CM)`
   (`descPochhammer_eq_factorial_smul_choose` + continuity/density to pass from the
   polynomial identity to the continuous-map level — evaluate: both sides are μ of
   explicit continuous maps; the identity holds pointwise on ℤ_p).
2. `descPochhammer ℤ n` has constant coefficient 0 (root at 0) for n ≥ 1:
   `descPochhammer_eval_zero`-shape ⟹ as a polynomial `X ∣ descPochhammer` ⟹
   pointwise `desc(x) = x·q(x)` with q ∈ ℤ_p[X]. Pull back along val:
   `M(desc∘) = μ((x·q(x))|_{units}) = ∑ q_k·μ(x^{k+1}|_units) = 0` by hypothesis
   (finite sum, all exponents ≥ 1).
3. `n! ≠ 0` in the domain ℤ_[p] ⟹ `M (mahler n) = 0` ∀ n ≥ 1 ⟹ `𝓐M = c·1` constant.
4. `𝓐(c·δ_0) = c` (T005, a = 0) ⟹ `M = c·δ_0` (T007 injectivity).
5. `ψM = 0`: `res_iota` (T017) + Cor 3.32 (T014). But `ψ(δ_0) = δ_0` (direct
   evaluation: `𝟙_{pℤ_p}(0)·f(shiftDiv 0) = f 0`). So `c·δ_0 = 0 ⟹ c = 0 ⟹ M = 0`.
6. `iota_injective` (T016) ⟹ μ = 0.

#### Mathlib lemmas needed
`descPochhammer_eq_factorial_smul_choose` (RingTheory/Binomial.lean:390),
`Polynomial.dvd_iff_isRoot`, `descPochhammer` eval lemmas
(`descPochhammer_eval_zero` — locate/derive), `Nat.cast_injective`-domain facts,
`smul_eq_zero`.

#### Sources
RJW Lem. 3.36(i) proof, TeX 1228–1229 (verbatim in decomposition L5.8, with the two
recorded refinements).

---

### [T024] Zero-divisor lemma (ii) + measures are pseudo-measures
- **Status**: done (2026-06-10; multiplicative moments + two-sided nonZeroDivisors) | **File**: PseudoMeasure.lean | **Depends on**: T023
- **Type**: theorem ×2 | **Leaves**: L5.9, L5.10

#### Statement
`mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero` (:153), `isPseudoMeasure_algebraMap` (:177).

#### Proof sketch
1. For `λ` with `μ*λ = 0`: `(μ*λ)(x^k) = μ(x ↦ λ((x·)^k)) = μ(x ↦ x^k·λ(pow k)) =
   μ(pow k)·λ(pow k)` — middle: `(xy)^k = x^k y^k` + λ-linearity pulls the scalar
   `x^k` out (constant-in-y factor). So `λ(pow k) = 0 ∀k>0` (h: μ-moments ≠ 0,
   domain ℤ_p) ⟹ λ = 0 (T023). Symmetric side by `mul_comm` (T020) —
   `mem_nonZeroDivisors_iff`.
2. `isPseudoMeasure_algebraMap`: witness ν := `(δ_g − 1)·μ`; `map_mul (algebraMap …)`.

#### Mathlib lemmas needed
`mem_nonZeroDivisors_iff`, `mul_pow`, `map_mul`.

#### Sources
RJW Lem. 3.36(ii) proof, TeX 1232–1234 (verbatim in decomposition L5.9).

---

### [T025] Zero-divisor lemma (iii) for pseudo-measures
- **Status**: done (2026-06-10; via (i) + IsLocalization.map_units) | **File**: PseudoMeasure.lean | **Depends on**: T024
- **Type**: theorem | **Leaf**: L5.11

#### Statement
`pseudoMeasure_eq_zero_of_moments` (:185).

#### Proof sketch
1. `hq a` gives ν₀ with `([a]−1)·q = algebraMap ν₀`. h (at each k, ν₀) gives
   `ν₀(pow k) = 0 ∀ k>0` ⟹ ν₀ = 0 (T023).
2. So `([a]−1)·q = 0` in the fraction ring; `[a]−1` maps to a unit-like regular
   element: by `dirac_sub_one_mem_nonZeroDivisors`-content — DON'T depend on T028;
   instead inline: `(δ_a −1)(pow k) = a^k − 1 ≠ 0` (ha) ⟹ T024 ⟹ regular in Λ;
   regular elements map to regular elements of the localization
   (`IsLocalization.map_nonZeroDivisors`-shape; in a fraction ring, the image of a
   nonZeroDivisor is invertible: `IsFractionRing.isUnit_map_nonZeroDivisor`-shape —
   worker locates: `IsLocalization` API gives `IsUnit (algebraMap _ _ x)` for
   `x ∈ nonZeroDivisors` in FractionRing). Hence q = 0.

#### Mathlib lemmas needed
`IsLocalization.map_units` (FractionRing at nonZeroDivisors), `IsFractionRing.injective`.

#### Sources
RJW Lem. 3.36(iii) proof, TeX 1236–1240 (verbatim in decomposition L5.11).

### [CLEANUP-10] Run /cleanup on PseudoMeasure.lean (cadence, after 6th ticket on file)
- **Status**: done (2026-06-10; degraded mode) | **Depends on**: T025 | **Type**: cleanup

---

### [T026] Topological generator of ℤ_p^× (p odd)
- **Status**: done (2026-06-10; REPLAN NOTE: instead of lifting a primitive root, took the nested-clopen-generator-sets + compactness route — no Teichmüller, no order arithmetic; surjectivity lift via canonical representative) | **File**: PseudoMeasure.lean | **Depends on**: T022
- **Parallel**: yes (with T023–T025) | **Type**: theorem | **Leaf**: L5.12

#### Statement
`exists_topological_generator (hp2 : p ≠ 2) : ∃ a : ℤ_[p]ˣ, ∀ n,
Subgroup.zpowers (unitsToZModPow p n a) = ⊤` (:206). The `p ≠ 2` hypothesis was added
by the adversarial pass (decomposition L5.12 — `(ZMod 8)ˣ` is not cyclic); statement
already amended and building.

#### Proof sketch
1. Read `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` in full first — it proves
   `isCyclic_units_of_prime_pow` by exhibiting generator structure (`1 + p` of order
   `p^n` etc.); extract/reuse: there is `g : (ZMod (p^2))ˣ` generating, and the file's
   machinery shows a unit that generates mod p² generates mod every p^n (odd p) —
   if not stated, prove via order computation: `orderOf a mod p^n = (p−1)·p^{n−1}`
   when a generates mod p² (`orderOf_one_add_mul_prime` is in the file).
2. Lift to `ℤ_[p]ˣ`: pick `x : ℤ_[p]` with `toZModPow 2 x = g` (surjectivity of
   `toZModPow` — derive via `appr`: `toZModPow n (appr-based lift) = given`); `x` is a
   unit (`isUnit_iff`: unit mod p ⟹ ‖x‖ = 1). Set `a := x.unit`.
3. For each n: image generates since order matches the group order
   (`Subgroup.eq_top_of_card_le`-shape / `orderOf` = card).

#### Mathlib lemmas needed
`isCyclic_units_of_prime_pow` + neighbours (UnitsCyclic.lean:190–231, read),
`ZMod.card_units_eq_totient`, `PadicInt.isUnit_iff`, `Subgroup.zpowers_eq_top`-API.

#### Sources
RJW Lem. 3.38 parenthetical, TeX 1257–1258; proof line 1265 "As p is odd".

---

### [T027] Augmentation ideal is principal (finite levels + compactness)
- **Status**: done (2026-06-10; finite-level telescoping + ker-deg decomposition; inverse limit step realised as Banach–Alaoglu-style compactness of the functional space Π_f ℤ_p with closed linearity+level conditions; levelMap_jointly_injective closes) | **File**: PseudoMeasure.lean | **Depends on**: T026, T022, T021
- **Type**: theorem | **Leaf**: L5.14 (cluster L5.14a–c)

#### Statement
`augmentationIdeal_eq_span (ha : ∀ n, zpowers (unitsToZModPow p n a) = ⊤) :
augmentationIdeal p = Ideal.span {dirac p a − 1}` (:212).

#### Proof sketch (sub-leaves in decomposition L5.14a–c)
1. (⊇) `deg (δ_a − 1) = 0`: T021.
2. (L5.14a) Finite cyclic group ring: for `C = ⟨g⟩` finite, every `single c 1 − 1 ∈`
   ideal gen by `single g 1 − 1` (telescoping `[g^k]−1 = ([g]−1)·∑_{i<k}[g^i]`), hence
   any `∑ c_a[a]` with `∑ c_a = 0` is `∑ c_a([a]−1) ∈ ([g]−1)`. State as a private
   lemma in the file (`MonoidAlgebra`, ~20 LOC).
3. (L5.14b) For μ ∈ I: level-n witness ν_n with `levelMap n (([a]−1)·?) = levelMap n μ`
   — from 2 applied to `levelMap n μ` (which has degree 0: deg factors through levels
   — small bridge lemma `deg = (MonoidAlgebra-augmentation) ∘ levelMap n`, T021/T022)
   + surjectivity of levelMap onto the group ring (hit `single ḡ c` by
   `c • δ_{lift ḡ}`; linear combinations).
4. (L5.14c) Compactness: the solution sets
   `S_n := {ν : Λ | levelMap n ((δ_a −1)*ν − μ) = 0}` are nonempty (3), nested after
   refinement (levelMap compatibility: `levelMap n` factors through `levelMap (n+1)` —
   bridge lemma via coset refinement), and closed-compact in the topology of pointwise
   evaluation on coset indicators: realise Λ ↪ `Π_{n, ḡ} ℤ_[p]` (countable product of
   compacts, `μ ↦ (μ(fibre-indicators))`), image closed (the additivity + ext
   constraints are closed conditions; uses T003-ext to identify the image), S_n
   closed therein. `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
   gives ν ∈ ⋂ S_n; `levelMap_jointly_injective` (T022) ⟹ `(δ_a −1)*ν = μ`.
   NOTE (honest size estimate): step 4 is the heaviest single step of the board
   (~80–120 LOC with the embedding bookkeeping); the source compresses it to "In the
   inverse limit we see" (line 1269). If the worker finds the product-embedding
   formalisation heavier than estimated, B2-stop with findings rather than redesign.

#### Mathlib lemmas needed
`MonoidAlgebra.single` algebra, `geom_sum_mul`-shape telescoping,
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
(Topology/Compactness/Compact.lean:336), `isCompact_pi_infinite`/Tychonoff
(`isCompact_univ_pi`), closed-set lemmas.

#### Sources
RJW Lem. 3.38 proof, TeX 1264–1272 (verbatim in decomposition L5.14).

---

### [T028] Pseudo-measure existence and shape (Lem. 3.38 + converse)
- **Status**: done (2026-06-10; mk'_spec' + eq_mk'_iff_mul_eq; regularity from torsion-free moments) | **File**: PseudoMeasure.lean | **Depends on**: T027, T024
- **Type**: theorem ×3 | **Leaves**: L5.13, L5.15

#### Statement
`dirac_sub_one_mem_nonZeroDivisors` (:231), `isPseudoMeasure_mk'` (:224),
`isPseudoMeasure_iff_exists` (:246).

#### Proof sketch
1. L5.13: `(δ_a − 1)(pow k) = a^k − 1 ≠ 0` (ha) + T024(ii).
   Bridge lemma (used by T025/§4 too): a topological generator satisfies
   `∀ k>0, a^k ≠ 1` — if `a^k = 1` then the image of `zpowers a` mod p^n has ≤ k
   elements ∀n, contradicting `ha n` for `card (ZMod p^n)ˣ > k`.
2. `isPseudoMeasure_mk'`: for g: `δ_g − 1 ∈ I = ([a]−1)` (T027 + deg(δ_g−1) = 0) ⟹
   `δ_g − 1 = ν·(δ_a −1)`; then `(δ_g−1)·mk'(μ, δ_a−1) = ν·(δ_a−1)·mk'(…) = ν·μ ∈ Λ`
   (`IsLocalization.mk'_spec`).
3. `iff_exists`: (⇐) is 2 (+ algebraMap case T024). (⇒): hq at g := a gives ν with
   `([a]−1)q = ν`; then `q = mk'(ν, δ_a−1)` (`IsLocalization.eq_mk'_iff_mul_eq`).

#### Mathlib lemmas needed
`IsLocalization.mk'_spec`, `IsLocalization.eq_mk'_iff_mul_eq`, `ZMod.card_units`.

#### Sources
RJW Lem. 3.38 proof + lines 1284–1285 (verbatim in decomposition L5.15).

### [CLEANUP-11] Run /cleanup on PseudoMeasure.lean (final)
- **Status**: done (2026-06-10; degraded mode — show-linter warnings queued for CLEANUP-FINAL) | **Depends on**: T028 | **Type**: cleanup

---

### [T029] Wire blueprint refs for §3 (Measures chapter)
- **Status**: done (2026-06-10; 20 nodes wired to project/mathlib decls, blueprint builds, site re-rendered; deferred nodes — §3.1 prelims, projlim description, ξ-formulas, §3.7 — left unwired per plan.md) | **File**: PadicLFunctionsBlueprint/Chapters/Measures.lean
- **Depends on**: none (can run anytime; refs to sorry-decls render "in progress")
- **Type**: blueprint wiring (no proofs)

#### Description
Add `(lean := "...")` references to the Measures-chapter Verso nodes for the now-stated
declarations (map: `p-adic-measure` ↦ `PadicMeasure`; `mahler-transform`/
`iwasawa-isomorphism` ↦ `PadicMeasure.mahlerTransform`/`PadicMeasure.mahlerRingEquiv`;
toolbox nodes ↦ `cmul/res/sigma/phi/psi` lemmas; `pseudo-measure` ↦
`PadicMeasure.IsPseudoMeasure`; zero-divisor/augmentation nodes ↦ T023–T028 decls;
node-by-node mapping from chapter labels — read the chapter file and decomposition.md).
Rebuild `lake build PadicLFunctionsBlueprint` and re-render `./scripts/ci-pages.sh`;
verify referenced names resolve (build fails on stale names — fix immediately).
Keep `(lean := …)` OFF the nodes whose statements stay roadmap-only (projlim
description, ξ-formulas, locally analytic — per plan.md Deferred).

---

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: open — BLOCKED on tooling (requires a session with lean-lsp MCP connected for /cleanup-all's per-decl golf workers; the mathlib linter set already runs green on every build; known cosmetic debt: a handful of `show`-should-be-`change` style warnings) | **Depends on**: all above | **Type**: cleanup-all
- **Scope widened 2026-06-11 (CL53/CL54/W2 fold-in)**: §3 Measure/* (the
  CLEANUP-W2 final per-file pass), §5 Interpolation/* incl. the new
  LpFunction.lean, and PadicExp.lean. Specific queued debt:
  `master_bridge`'s maxHeartbeats 400000 (PadicExp.lean), per-decl golf of
  the degraded-mode tickets (T519, T520, T521–T523), the `show`-linter
  pattern project-wide, and the CLEANUP-FINAL items from the §4 handover
  (psi-as-LinearMap, delQ→del merge, mahlerTransform_sub/smul placement,
  instIsDomain/SMulCommClass placement). Widened 2026-06-12 (CL67 fold-in):
  + §6 files (ExtLog, MeasureR/FormalPsi, ValuesAtOne[Complex]);
  crt_collapse decompose-candidate; T618-layer placement review.
  Widened 2026-06-12 (CL72 fold-in): + §7 ResidueZeta.lean (1794 lines —
  split-candidate: expTail/character/mass/descent sections could become
  ResidueZeta/{ExpTail,Denominator,Mass,Descent}.lean; the seriesEval
  toolkit (seriesEval_pow/_X/_smul/_one, seriesEval_subst_formalLog,
  coeff_pow_eq_zero_of_constantCoeff_zero, norm_coeff_pow_le_one,
  norm_seriesEval_le, padicLog_prod_of_norm_lt_one) is
  FormalPsi.lean-placement-candidate; map_padicLog/map_extLog_natCast are
  ExtLog.lean-candidates; map_derivativeFun'/map_one_add_mul_derivativeFun'
  duplicate ValuesAtOne privates — de-private and merge).
  Widened 2026-06-12 (CL93 fold-in): + §§9–10 Coleman/* (Theorem.lean
  1158-line split candidate {Eval,Uniqueness,Square,Main}; the
  NormCompatUnits vestigial elems-0 (colemanSeries_eq_iff note); Tower's
  private spectral-norm/orthogonality cluster → possible ExtLog/Tower
  promotion; the maxHeartbeats overrides on the extendScalars decls;
  T904b's re-derived orthogonality vs Tower's privates — dedupe).
  Widened 2026-06-12 (CL82 fold-in): + §8 EisensteinFamily.lean /
  EisensteinComplex.lean (golf the 2⁻¹-unit coercion chains; the
  IsScalarTower ℤ_[p] Λ Λ instance gap (T803's manual smul_one_mul');
  unitsTwist could generalise to twist-by-any-continuous-character;
  the reproduced-private duplicates (summable_sigma_cexp vs mathlib's
  private, norm_natCast_inv_le vs ValuesAtOne's) — consider mathlib PRs
  de-privatising; LeanModularForms dep: the compat branch's 3 benign
  warnings (2 change-does-nothing + 1 deprecation) for upstream tidying).
- Then `/pre-submit` when the user wants a checkpointed milestone.

---

## Dependency quick-view

```
T001 T002 → T003 → CL1 → T004 T005 → T006 → CL2 → T007 → CL3
                                                    ├→ T008 → T009,T010 → CL4
                                                    └→ T011
T012 → T013 → CL5 → T014 → CL6        (T012 needs only T001)
T015 → T016 → T017 → CL7              (T016 also needs T012; T017 needs T014)
T018 → T019 → CL8                     (T019 needs T002, T001; T018 free)
T019,T015 → T020 → T021,T022 → CL9 → T023 → T024 → T025 → CL10
T022 → T026;  T026,T022,T021 → T027;  T027,T024 → T028 → CL11
T029 free;  everything → CLEANUP-FINAL
```

Cadence audit: Basic 3 tickets/1 cleanup ✓; MahlerTransform 4/2 ✓; Convolution 3/1 ✓;
Toolbox 4/2 ✓; UnitsZp 3/1 ✓; Fubini 2/1 ✓; PseudoMeasure 9/3 ✓; final /cleanup-all ✓.
Total proof tickets 28 → ⌈28/3⌉ = 10 ≤ 11 per-file cleanups + CLEANUP-FINAL ✓.

---

# §4 — Kubota–Leopoldt (TeX 1440–1609) — added 2026-06-10

## §4 Summary
- Tickets: T030–T039 (10 proof/def) + CLEANUP-ALL-2 + CLEANUP-KL-1/2
- Open: 0 | Done: 13 (all §4 tickets discharged 2026-06-10)
- Skeleton: `PadicLFunctions/KubotaLeopoldt/{ZetaValues,ZetaValuesComplex,MuA,ZetaP}.lean`,
  46 sorries, builds green (2026-06-10)
- Decomposition: `.mathlib-quality/decomposition.md` §4 (leaves L0.1–L5.8, all gated)
- **Standing rules (CLAUDE.md, binding on every ticket below)**: each ticket's
  Definition-of-Done includes (i) the **Blueprint** step — wire/adjust the named
  chapter node(s) in `PadicLFunctionsBlueprint/Chapters/KubotaLeopoldt.lean` in the
  same session, `lake build PadicLFunctionsBlueprint` green; (ii) the **Cleanup**
  step — `/cleanup` (single-declaration mode; degraded mode + note if lean-lsp absent)
  on the new declarations immediately, before marking done; (iii) verification bar:
  build green, zero sorry in the ticket's declarations, `#print axioms` ⊆
  {propext, Classical.choice, Quot.sound}; (iv) checkpoint commit.

### [T030] Rational zeta values `zetaNeg` + complex bridge
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaValues.lean, ZetaValuesComplex.lean
- **Depends on**: none
- **Parallel**: yes (with T031)
- **Type**: lemmas (4 sorries: `zetaNeg_zero`, `zetaNeg_eq_zero_of_even`,
  `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`, `zetaNeg_eq_riemannZeta`)
- **Statement**: in skeleton (ZetaValues.lean:21,25,36; ZetaValuesComplex.lean:18).
- **Proof sketch** (decomposition L0.1–L0.4):
  1. `zetaNeg_zero`: `simp [zetaNeg, bernoulli_one]; norm_num`.
  2. `zetaNeg_eq_zero_of_even`: `bernoulli_eq_zero_of_odd (h.add_one) (by lia)`;
     conclude `zetaNeg k = ±0/(k+1) = 0` by `simp [zetaNeg]`.
  3. `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`: `rcases k`: `k = 1` → factor
     `1 − q⁰ = 0`; `k` even → `Even.neg_one_pow`; `k ≥ 3` odd → step 2 kills
     `zetaNeg (k−1)`. Parity split via `Nat.even_or_odd k`.
  4. `zetaNeg_eq_riemannZeta`: open mathlib's `riemannZeta_neg_nat_eq_bernoulli`
     (HurwitzZetaValues.lean) at `n := k`; `push_cast [zetaNeg]; ring`.
- **Mathlib lemmas**: `bernoulli_one`, `bernoulli_eq_zero_of_odd` (Bernoulli.lean:217),
  `Even.neg_one_pow`, `Odd.neg_one_pow`, `riemannZeta_neg_nat_eq_bernoulli` (verified
  by file-grep; exact argument form to confirm via hover at execution).
- **Sources**: RJW TeX 1455 (value formula), 1596 (sign removal). Quotes in
  decomposition L0.1–L0.4.
- **Generality**: `zetaNeg : ℕ → ℚ` (pure rational — no p); sign lemma over arbitrary
  `q : ℚ` (more general than the `p`-instance needed).
- **Blueprint**: none of the §4 nodes is *this* content alone (kl-values-of-zeta
  stays unwired pending §2 Mellin theory — see decomposition R-KL head-note; record
  the unwired-rationale as a comment on the node).
- **Cleanup**: `/cleanup` ZetaValues.lean + ZetaValuesComplex.lean immediately after.
- **Progress**:
  - 2026-06-10: DONE — 4 declarations proven (zetaNeg_zero, zetaNeg_eq_zero_of_even,
    neg_one_pow_mul_one_sub_pow_mul_zetaNeg, zetaNeg_eq_riemannZeta); build green;
    axioms = [propext, Classical.choice, Quot.sound] (verified). Off-script: Nat.Odd.sub_odd
    (ℕ-sub version, not Odd.sub_odd). Blueprint: unwired-rationale comment added to
    kl-values-of-zeta node, blueprint builds. Cleanup: degraded mode (no lean-lsp) —
    proofs are 1–6-line minimal forms, naming/docstrings audited by hand; revisit in
    a tooled session via CLEANUP-FINAL.

### [T031] `F_a`, `μ_a` and the characterising identity
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: none
- **Parallel**: yes (with T030)
- **Type**: def-API (9 sorries: `PadicInt.isUnit_natCast_of_not_dvd`,
  `constantCoeff_geomSum`, `geomSum_mul_X`, `isUnit_geomSum`, `X_mul_FaNum`,
  `geomSum_mul_Fa`, `one_add_X_pow_sub_one_mul_Fa`, `mahlerTransform_muA`,
  `binomialSeries_natCast`)
- **Statement**: in skeleton (MuA.lean:35–95).
- **Proof sketch** (decomposition L1.1–L1.8):
  1. `isUnit_natCast_of_not_dvd`: `PadicInt.isUnit_iff.2`; `‖(a:ℤ_[p])‖ = 1` from
     `le_antisymm (norm_le_one _)` + `not_lt.2` of `norm_int_lt_one_iff_dvd`
     (`exact_mod_cast` ℕ→ℤ dvd).
  2. `constantCoeff_geomSum`: `simp [geomSum, map_sum, map_pow]`;
     `Finset.sum_const`, `card_range`.
  3. `geomSum_mul_X`: `geom_sum_mul` at `x := 1+X`; rewrite `1+X−1 = X` by
     `add_sub_cancel_left`. (If `geom_sum_mul` has moved/renamed: 6-line induction
     fallback recorded in decomposition L1.3.)
  4. `isUnit_geomSum`: `isUnit_iff_constantCoeff.2` ∘ steps 1–2.
  5. `X_mul_FaNum`: `PowerSeries.ext`; case `0`: both sides 0 (step 2);
     case `n+1`: `coeff_succ_X_mul`, `coeff_mk`; RHS natCast-coeff via
     `PowerSeries.coeff_natCast`-shape (or `Nat.cast` = `C a`: `coeff_C`).
  6. `geomSum_mul_Fa`: `Fa`-def; `mul_left_comm` + `Ring.inverse_mul_cancel`
     (step 4).
  7. `one_add_X_pow_sub_one_mul_Fa`: rw ← step 3; `mul_assoc`-shuffle to
     `X·(geomSum·Fa)`; steps 6 then 5.
  8. `mahlerTransform_muA`: `muA`-def + `LinearEquiv.apply_symm_apply` (relate
     `mahlerLinearEquiv` to `mahlerTransform` — they coincide per
     MahlerTransform.lean:160's construction; `mahlerTransform_ofPowerSeries` if
     needed).
  9. `binomialSeries_natCast`: induction on `a`: `binomialSeries_zero`,
     `binomialSeries_add` (+1 case via `binomialSeries 1 = 1 + X`:
     `PowerSeries.ext`, `binomialSeries_coeff`, `Ring.choose_natCast`/
     `Ring.choose_one_right`-computation; or de-privatise/replicate Toolbox's
     `binomialSeries_mul_nat` at `c := 1`).
- **Mathlib lemmas**: `PadicInt.isUnit_iff` (:366), `PadicInt.norm_int_lt_one_iff_dvd`
  (:280), `PadicInt.norm_le_one`, `geom_sum_mul`, `PowerSeries.isUnit_iff_constantCoeff`
  (Inverse.lean:111), `Ring.inverse_mul_cancel`, `coeff_succ_X_mul`, `coeff_mk`,
  `binomialSeries_zero/add/coeff`.
- **Sources**: RJW Prop 4.4 proof (TeX 1488–1494), Lem 4.3 (TeX 1475). Quotes +
  realisation note: decomposition R1 head.
- **Generality**: `a : ℕ` (source: integer coprime to p; ℕ suffices — negative
  integers never used in §4); defs total (junk via `Ring.inverse`), lemmas carry
  `hpa : ¬ p ∣ a`.
- **Blueprint**: wire `kl-Fa-in-Zp` → `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`
  (+ prose note: membership is by construction, the identity is the content);
  wire `measure-mu-a` → `PadicMeasure.muA`. Blueprint build green.
- **Cleanup**: `/cleanup` the nine declarations immediately after.
- **Progress**:
  - 2026-06-10: DONE — 8 declarations proven (isUnit_natCast_of_not_dvd,
    constantCoeff_geomSum, geomSum_mul_X, isUnit_geomSum, X_mul_FaNum, geomSum_mul_Fa,
    one_add_X_pow_sub_one_mul_Fa, mahlerTransform_muA). `binomialSeries_natCast`
    DELETED from skeleton — mathlib already has it as `binomialSeries_nat` (simp,
    Binomial.lean:69); T032's sketch updated to use the mathlib name. Off-script:
    add_sub_cancel_left via have+rw (simp would not fire it); natCast-coeff handled
    via ← map_natCast C then coeff_C (simp re-reverses map_natCast — rw before simp).
    Axioms standard (3 spot-checked). Blueprint: kl-Fa-in-Zp + measure-mu-a wired,
    builds green. Cleanup: degraded mode — proofs 1–6 lines, hand-audited.

### [T032] Dirac-sum identity + `Λ(ℤ_p)` is a domain
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T031
- **Parallel**: yes (with T033 after T031)
- **Type**: lemmas (3 sorries: `dirac_natCast_sub_one_mul_muA`, `instIsDomain`,
  `dirac_natCast_sub_one_ne_zero`)
- **Statement**: in skeleton (MuA.lean:101–110).
- **Proof sketch** (decomposition L1.9–L1.10):
  1. `instIsDomain`: transport `IsDomain ℤ_[p]⟦X⟧` (mathlib instance over a domain)
     along `(mahlerRingEquiv p).symm` — `RingEquiv.isDomain`-spelling (candidates:
     `MulEquiv.isDomain`, `Function.Injective.isDomain` via `.injective` +
     `.toRingHom`).
  2. `dirac_natCast_sub_one_mul_muA`: apply `(mahlerRingEquiv p).injective`;
     `map_mul/map_sub/map_sum/map_one`; `mahlerTransform_dirac` +
     `binomialSeries_natCast` (T031) turn LHS-transform into
     `((1+X)^a−1)·Fa` = `one_add_X_pow_sub_one_mul_Fa`; RHS-transform:
     `Σ(1+X)^i − a•1 = geomSum − natCast` (smul-to-natCast bridge:
     `Nat.cast_smul_eq_nsmul`/`nsmul_eq_mul`). NB `mahlerRingEquiv` vs
     `mahlerTransform` bridge lemma exists in Convolution.lean.
  3. `dirac_natCast_sub_one_ne_zero`: transform `= (1+X)^a − 1 ≠ 0` since
     `coeff 1 = a ≠ 0` (`coeff_one` of pow via `add_pow`-coeff or
     `Polynomial`-free route: `coeff 1 ((1+X)^a) = a` by induction or
     `binomialSeries_natCast` + `binomialSeries_coeff` at 1: `Ring.choose a 1 = a`).
- **Mathlib lemmas**: PowerSeries `instIsDomain` (over `IsDomain R`),
  `RingEquiv.isDomain` (or variant), `Nat.cast_injective` (char-0 `ℤ_[p]`),
  `binomialSeries_coeff`, `Ring.choose_one_right`.
- **Sources**: decomposition L1.9 (composition note), TeX 1475/1490.
- **Generality**: `IsDomain` instance is global (not §4-scoped) — place near the top
  of MuA.lean; consider migrating to Convolution.lean at cleanup (note for /cleanup).
- **Blueprint**: no node (infrastructure).
- **Cleanup**: `/cleanup` immediately; flag the instance's final home.
- **Progress**:
  - 2026-06-10: DONE — dirac_natCast_sub_one_mul_muA (via mahlerTransform_injective +
    new simp lemmas mahlerTransform_sub/smul, map_sum through mahlerTransformₗ with
    rfl-coe bridges), instIsDomain (MulEquiv.isDomain via mahlerRingEquiv.toMulEquiv),
    dirac_natCast_sub_one_ne_zero (coeff-1 of (1+X)^a = a via Polynomial.coeff_one_add_X_pow
    through toPowerSeries). Axioms standard (3/3). ne_zero proof avoided
    binomialSeries_coeff (Ring.choose-free route). Cleanup: degraded mode; flag —
    mahlerTransform_sub/smul belong in Convolution.lean at next tooled cleanup.

### [T033] Bernoulli moments: `∫x^k dμ_a = (−1)^k(1−a^{k+1})ζ(−k)`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T030, T031
- **Parallel**: yes (with T032, T034 modulo deps)
- **Type**: theorem cluster (8 sorries: `map_del`, `hasSubst_exp_sub_one`,
  `derivativeFun_subst_exp`, `constantCoeff_subst_exp`,
  `constantCoeff_iterate_derivativeFun`, `constantCoeff_iterate_delQ`,
  `X_mul_subst_exp_Fa`, `muA_apply_powCM`)
- **Statement**: in skeleton (MuA.lean:131–171).
- **Proof sketch** (decomposition L2.2–L2.7; the full multiply-and-cancel plan for
  `X_mul_subst_exp_Fa` is in L2.6 — follow it step by step):
  1. `map_del`: `PowerSeries.ext n`; `coeff_map`, `coeff_derivativeFun`,
     `one_add_mul`-expansion both sides; `map_natCast`.
  2. `hasSubst_exp_sub_one`: `HasSubst.of_constantCoeff_zero'` (§3 precedent in
     Toolbox `mahlerTransform_pushforward_mulCM`); `constantCoeff_exp`, `map_sub`.
  3. `derivativeFun_subst_exp`: `derivative_subst` (Derivative.lean:184) + bridge
     `d⁄dX ↔ derivativeFun`; `derivative_exp`; algebra: `(dF)∘g·exp =
     ((1+X)·dF)∘g` via `subst_mul`-homomorphy + `(1+X)∘g = exp` (`subst_add`,
     `subst_one`? — use `map_add` of `substAlgHom`).
  4. `constantCoeff_subst_exp`: `constantCoeff_subst` (Substitution.lean:244);
     constant-coeff-zero kills all `n ≥ 1` terms (`pow`-of-zero-constantCoeff);
     fallback: `coeff_subst` at 0.
  5. `constantCoeff_iterate_derivativeFun`: induction on k;
     `Function.iterate_succ_apply'`; `coeff_derivativeFun`;
     `Nat.factorial_succ`; `push_cast; ring`.
  6. `constantCoeff_iterate_delQ`: induction on k via 3+4+5: `constCoeff(delQ^[k]F)
     = constCoeff(D^[k](F∘(e−1)))` (commute one delQ out per step), then 5.
  7. `X_mul_subst_exp_Fa`: multiply-and-cancel by `(rescale a exp − 1)` per
     decomposition L2.6: LHS·: subst the T031 identity
     `one_add_X_pow_sub_one_mul_Fa` through `exp−1` (`substAlgHom`-ring-hom,
     `exp_pow_eq_rescale_exp` for `subst((1+X)^a) = rescale a exp`); RHS·:
     `bernoulliPowerSeries_mul_exp_sub_one` + substituted `geomSum_mul_X`
     (`e^{at}−1 = (e^t−1)·Σ_{j<a}e^{jt}`) + `rescale`-ring-hom
     (`rescale a X = C a·X`-form, `coeff_rescale` fallback); cancel by
     `mul_right_cancel₀` in the domain `ℚ_p⟦X⟧` (`rescale a exp − 1 ≠ 0`:
     coeff 1 = `a ≠ 0`, char-0 cast).
  8. `muA_apply_powCM`: `apply_powCM` (§3) + `mahlerTransform_muA` (T031); cast;
     commute map through iterates (1 + `constantCoeff_map`, induction); step 6;
     extract `coeff (k+1)` of step 7 (`coeff_succ_X_mul`); `bernoulliPowerSeries`
     coeff + `coeff_rescale`; `k!/(k+1)! = (k+1)⁻¹` (`Nat.factorial_succ`,
     `field_simp`); fold `zetaNeg` (`(−1)^{2k} = 1`: `neg_one_pow_mul_self`-style,
     `pow_mul_pow_eq...` — `ring` after `zetaNeg`-unfold; `Rat.cast`-homomorphy).
  Numeric anchors verified in decomposition (L2.6 attack [1]: `a=2` coefficient;
  L2.7 attack [3]: `k=0` gives `F_a(0) = (a−1)/2` both routes).
- **Mathlib lemmas**: `bernoulliPowerSeries_mul_exp_sub_one` (Bernoulli.lean:273),
  `bernoulliPowerSeries`-def (:270), `PowerSeries.derivative_subst` (:184),
  `PowerSeries.derivative_exp`, `constantCoeff_exp`, `coeff_exp`,
  `exp_pow_eq_rescale_exp` (Exp.lean:153), `constantCoeff_subst` (:244),
  `coeff_rescale`, `rescale` ring-hom (`map_one/map_sub`), `coeff_derivativeFun`,
  `coeff_succ_X_mul`, `Nat.factorial_succ`, `Rat.cast`-field-hom simp set.
- **Sources**: RJW Lem 4.2 (TeX 1459–1464, value part), Lem 4.3 (TeX 1473–1479),
  Prop 4.6 (TeX 1500–1507) — quotes in decomposition R2.
- **Generality**: ℚ_p-coefficients via `PadicInt.Coe.ringHom`-map; `delQ` is a
  *temporary* ℚ_p-clone of `del` — **cleanup debt**: merge by generalising
  `PadicMeasure.del` to `CommRing R` in a dedicated pass (recorded; do NOT churn §3
  call sites mid-ticket).
- **Blueprint**: wire `kl-mua-interpolation` → `PadicMeasure.muA_apply_powCM`;
  wire `kl-define-Fa` → `PadicMeasure.constantCoeff_iterate_delQ` (the
  `f_a^{(k)}(0) = (∂^k F_a)(0)` content; prose note that the substitution is
  realised by `PowerSeries.subst (exp−1)`); `kl-values-of-zeta` stays unwired
  (Mellin half is §2) — add the rationale comment.
- **Cleanup**: `/cleanup` the eight declarations immediately after.
- **Progress**:
  - 2026-06-10: DONE — 9 declarations (added map_derivativeFun helper): map_del,
    hasSubst_exp_sub_one, derivativeFun_subst_exp (calc via derivative_subst — NB
    mathlib's takes A *explicitly*: `derivative_subst ℚ_[p] hg`), constantCoeff_subst_exp
    (finsum_eq_single at 0, Mv/PS-constantCoeff rfl-bridge), constantCoeff_iterate_
    derivativeFun + _delQ (inductions), X_mul_subst_exp_Fa (multiply-and-cancel by
    rescale a exp − 1, per decomposition L2.6 plan — worked exactly as planned),
    muA_apply_powCM (final algebra: parity cases on (−1)^k + field_simp + push_cast +
    ring; algebraMap-vs-Nat-cast needed map_add in the distribution simp). Axioms
    standard (3 spot-checked incl. the theorem). Blueprint: kl-mua-interpolation →
    muA_apply_powCM, kl-define-Fa → constantCoeff_iterate_delQ; builds green.
    Cleanup: degraded mode — delQ-merge debt re-flagged for tooled pass.

### [T034] ψ-invariance: projection formula + `ψ(μ_a) = μ_a`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T031, T032
- **Parallel**: yes (with T033)
- **Type**: theorem cluster (9 sorries: `psi_phi_mul`, `phi_dirac`, `psi_dirac_mul`,
  `psi_dirac_of_isUnit`, `psi_add`, `psi_smul`, `psi_sum`, `psi_muA`)
- **Statement**: in skeleton (MuA.lean:182–215).
- **Proof sketch** (decomposition R3 — **recorded replan**: the source's
  ξ/roots-of-unity proof (TeX 1517–1524) is replaced by the equivalent elementary
  computation; justification block in decomposition R3 head):
  1. `psi_phi_mul`: `LinearMap.ext f`; `show`-unfold both sides (§3 `psi_phi`
     pattern); `mul_apply` (Convolution); inner integrand: for `y ∈ pℤ_p`,
     `charFn(px+y) = charFn(y)` and `sd(px+y) = x + sd y` — new digit sub-lemma
     `digit (p·x + y) = digit y` (~8 LOC from `digit`'s `toZModPow 1`
     characterisation, `map_add`, `p·x ↦ 0`); reassemble as `(ν * psi μ) f`.
  2. `phi_dirac`: `rfl`-grade (pushforward of dirac, §3 pattern).
  3. `psi_dirac_mul`: via `psi_phi` + 2 (`ψ[px] = ψφ[x] = [x]`).
  4. `psi_dirac_of_isUnit`: `LinearMap.ext`; charFn vanishes off `pℤ_p`; unit ∉
     `pℤ_p` (`PadicInt.isUnit_iff`, `setOf_isUnit_eq`/norm-argument).
  5. `psi_add/psi_smul/psi_sum`: definitional `LinearMap.ext` unfolds (the
     integrand map `f ↦ charFn·(f∘sd)` is linear in μ); `psi_sum` by
     `Finset.sum_induction` from add + `ψ0 = 0`. **Cleanup debt noted**: psi
     should become a bundled linear map in a later pass.
  6. `psi_muA`: per decomposition L3.6: (a) `v_a·ψμ_a = ψ(φ(v_a)·μ_a)` [1 + 2];
     (b) telescope `(Σ_{j<p}[aj])·([a]−1) = [ap]−1` (`dirac_mul_dirac`,
     `Finset.sum_range_succ'`); (c) expand `([ap]−1)·μ_a` via T032's identity
     left-multiplied by `Σ_j[aj]`; transform-side geom-sum route for the
     double-product (decomposition L3.6 attack [2]: both routes recorded);
     (d) apply ψ termwise (3,4,5): `p ∣ aj+i`-bookkeeping or transform-side
     X-cancellation; result `Σ_{i<a}[i] − a•1`; (e) rewrite back via T032 =
     `v_a·μ_a`; (f) `mul_left_cancel₀` (T032 ne-zero + IsDomain).
     End-to-end numeric trace at `p=3, a=2` in decomposition L3.6 attack [1].
- **Mathlib lemmas**: `Finset.sum_range_succ'`, `Nat.Coprime.dvd_of_dvd_mul_left`
  (j=0 isolation), `mul_left_cancel₀`; rest is §3 project API (`mul_apply`,
  `dirac_mul_dirac`, `shiftDiv_mul`, `mem_pZp_of_mul`, charFn lemmas).
- **Sources**: RJW Lem 4.7 statement (TeX 1513–1515, verbatim in decomposition);
  source proof TeX 1517–1524 (quoted; replaced — replan block).
- **Generality**: projection formula stated for all ν, μ (maximal); dirac lemmas
  pointwise-general.
- **Blueprint**: wire `kl-psi-invariant` → `PadicMeasure.psi_muA`; add a prose
  remark to the node recording the ξ-free route (per CLAUDE.md rule 5).
- **Cleanup**: `/cleanup` immediately after; flag psi-bundling debt.
- **Progress**:
  - 2026-06-10: DONE — 11 declarations (8 planned + psi_zero, dirac_zero_eq_one,
    psi_dirac_natCast, + SMulCommClass ℤ_[p] Λ Λ instance which the smul-mul algebra
    needed). psi_phi_mul exactly per decomposition L3.1 (digit arithmetic via
    y = p·sd(y) substitution — no new digit lemma needed; ∉-case by ultrametric
    sandwich). psi_muA per the replanned route: telescope + transform-side geom
    product (X-cancellation, no Finset reindex for the product; the ψ-side reindex
    via Finset.sum_nbij'). rw-gotcha: dirac identity rewrote both sides at once.
    Axioms standard. Blueprint: kl-psi-invariant → psi_muA wired + ξ-free note
    already in file docstring; builds. Cleanup: degraded — psi-bundling debt
    re-flagged (psi_zero/add/smul/sum are all rfl-grade: psi should be a LinearMap
    in a tooled pass).

### [T035] Restriction to `ℤ_p^×`: Euler factor removed
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/MuA.lean
- **Depends on**: T033, T034
- **Parallel**: no
- **Type**: theorem (2 sorries: `phi_apply_powCM`, `res_units_muA_apply_powCM`)
- **Statement**: in skeleton (MuA.lean:226–233).
- **Proof sketch** (decomposition L4.1–L4.2; source proof TeX 1535–1539 quoted there):
  1. `phi_apply_powCM`: `show`-unfold pushforward; `powCM ∘ mulCM p = p^k • powCM`
     by `ContinuousMap.ext` + `mul_pow`; `map_smul`.
  2. `res_units_muA_apply_powCM`: `res_units_eq` (§3) → `μ_a − φψμ_a`;
     `psi_muA` (T034) → `μ_a − φμ_a`; `LinearMap.sub_apply`; step 1;
     `muA_apply_powCM` (T033); `push_cast; ring`.
- **Mathlib lemmas**: `mul_pow`, `map_smul`, `push_cast` set.
- **Sources**: RJW Prop 4.8 (TeX 1527–1539).
- **Generality**: step 1 for arbitrary μ (not just μ_a).
- **Blueprint**: wire `kl-restriction-interpolation` →
  `PadicMeasure.res_units_muA_apply_powCM`.
- **Cleanup**: `/cleanup` immediately; this closes MuA.lean → run the **final
  per-file cleanup** for MuA.lean here (= CLEANUP-KL-1 folded in; verify whole-file
  lint).
- **Progress**:
  - 2026-06-10: DONE first try — phi_apply_powCM (pushforward show + smul-fun ext),
    res_units_muA_apply_powCM (res_units_eq + psi_muA + push_cast + T033 + ring).
    **MuA.lean now sorry-free** (RJW §4.1–§4.2 complete: Prop 4.4/Def 4.5/Prop 4.6/
    Lem 4.7/Prop 4.8). Axioms standard. Blueprint: kl-restriction-interpolation →
    res_units_muA_apply_powCM, builds. Final per-file cleanup: degraded pass — build
    warnings clean except one flexible-simp lint note (line ~259, simp at h1 in
    X_mul_subst_exp_Fa's hreg) queued for tooled CLEANUP-FINAL; naming + docstrings
    hand-audited; no long-proof gate breach (psi_muA ~95 lines but structured by
    haves mirroring the decomposition tree).

### [T036] Units-side transfer + `x⁻¹`-twist `zetaNum`
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T035
- **Parallel**: yes (with T037)
- **Type**: def-API (6 sorries: `iota_muAUnits`, `muAUnits_apply_unitsPowCM`,
  `continuous_units_inv_val`, `unitsCmul_apply`, `zetaNum_apply_unitsPowCM`,
  `zetaNum_moments`)
- **Statement**: in skeleton (ZetaP.lean:40–88).
- **Proof sketch** (decomposition L5.1–L5.3):
  1. `iota_muAUnits`: `LinearMap.ext`; both sides `μ_a`-applied; pointwise
     `extendByZero f ∘ no — (extendByZero (f.comp unitsValCM-style))`:
     reuse §3 `extendByZero_comp_unitsVal` / the `mem_range_iota_iff` ⟸-direction
     computation verbatim (UnitsZp.lean:177 proof body is the template).
  2. `muAUnits_apply_unitsPowCM`: pointwise `extendByZero (unitsPowCM k) =
     charFn_units · powCM k` (`ContinuousMap.ext u`; unit-case
     `extendByZero_coe_unit`, non-unit case both sides 0); then `res`-def.
  3. `continuous_units_inv_val`: `Units.continuous_iff`-toolkit
     (Mathlib.Topology.Algebra.Constructions) or explicit: `u ↦ u⁻¹.val` is
     `MulOpposite.unop ∘ Prod.snd ∘ embedProduct`, each continuous (§3 UnitsZp
     embedProduct machinery).
  4. `unitsCmul_apply`: `rfl`-grade (`LinearMap.mulLeft`-apply).
  5. `zetaNum_apply_unitsPowCM`: 4 + pointwise `invCM·unitsPowCM k =
     unitsPowCM (k−1)`: `ContinuousMap.ext u`; `(u⁻¹:ℤ_p)·(u:ℤ_p)^k`:
     `Units.val`-arith — `← Units.val_pow_eq_pow_val`, `← Units.val_mul`,
     `inv_mul_eq_iff`/`pow_sub_one_mul`-shape with `Nat.succ_pred_eq_of_pos hk`.
  6. `zetaNum_moments`: 5 + 2 + T035 at `k−1`; sign-shuffle
     `(−1)^{k−1}(1−a^k) = (−1)^k(a^k−1)` by `ring`-after-`Nat.succ_pred` cast
     handling (`Odd/Even` not needed — `(−1)^{k−1}·(−1) = (−1)^k` via
     `pow_succ` on `k−1+1 = k`).
- **Mathlib lemmas**: `Units.continuous_iff` (or `Units.embedProduct`-route),
  `Units.val_pow_eq_pow_val`, `Units.val_mul`, `Nat.succ_pred_eq_of_pos`,
  `pow_succ`.
- **Sources**: RJW TeX 1555–1562 (eq 4.11 + the `x⁻¹μ_a`-moment display; quoted in
  decomposition R5/L5.3).
- **Generality**: `unitsCmul` for arbitrary `g` (the general eq-4.11 operation, not
  just `x⁻¹`).
- **Blueprint**: wire `kl-theta-a` → `PadicMeasure.unitsCmul` with prose adjusted:
  the node's θ_a is `dirac p a − 1` (§3 objects, augmentation generator); its new
  content anchor is the well-defined `x⁻¹`-multiplication (eq 4.11). Keep faithful
  per CLAUDE.md rule 2; do not over-claim.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:

### [T037] Integer topological generator (p odd)
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: none (uses §3 only)
- **Parallel**: yes (with T030–T036)
- **Type**: theorem (2 sorries: `topGen_pow_ne_one`, `exists_nat_topological_generator`)
- **Statement**: in skeleton (ZetaP.lean:92–103).
- **Proof sketch** (decomposition L5.4; **source-expansion**, cross-ref
  Washington/Ireland–Rosen — the source's Def 4.10 takes an integer top-generator
  implicitly):
  1. `topGen_pow_ne_one`: suppose `a^k = 1`, `k > 0`. Then
     `(unitsToZModPow p n a)^k = 1` ∀n (`map_pow`, `map_one` — note
     `unitsToZModPow` is a `MonoidHom`, and `a^k = 1` in `ℤ_[p]` lifts to units:
     `Units.ext`-style: `(a^k : ℤ_[p]ˣ) = 1` from val-injectivity). So
     `orderOf (q_n a) ∣ k`; but `zpowers (q_n a) = ⊤` ⟹ `orderOf (q_n a) =
     card (ZMod p^n)ˣ = φ(p^n)` (`orderOf_eq_card_of_forall_mem_zpowers`,
     `ZMod.card_units_eq_totient`); `φ(p^n) = p^{n-1}(p−1)` unbounded
     (`Nat.totient_prime_pow`) — pick `n` with `φ(p^n) > k`, contradiction with
     `orderOf ∣ k` (`Nat.le_of_dvd`).
  2. `exists_nat_topological_generator`: obtain `u₀` (§3
     `exists_topological_generator hp2`). Set `m := (toZModPow 2 u₀).val.val`-lift
     (the ℕ-rep of `u₀ mod p²`); `u := (PadicInt.isUnit_natCast_of_not_dvd …).unit`.
     (a) `q_2 u = q_2 u₀` (natCast-naturality `map_natCast` of `toZModPow`,
     `ZMod.natCast_val`-round-trip); hence `m` generates level 2.
     (b) `m^{p−1} ≡ 1 mod p` (level-1 Fermat from level-2 generation pushed down
     `unitsToZModPow_le`) and `m^{p−1} = 1 + p·c` with `p ∤ c` — else order at
     level 2 divides `p−1 < φ(p²)` contradicting (a)
     (`ZMod.unitOfCoprime`-arithmetic; extract `c` over ℤ/ℕ).
     (c) level n: `orderOf (q_n u)` is divisible by `p−1` (push down to level 1,
     order there is `p−1`) and by `p^{n−1}` (`orderOf_one_add_mul_prime` applied
     to `(m:ZMod p^n)^{p−1} = 1 + p·c`-image, `p ∤ c`); `lcm = φ(p^n)` ⟹
     `zpowers = ⊤` (`orderOf_eq_card_iff`-direction /
     `Subgroup.eq_top_of_card_le`-style with `orderOf_dvd_card`).
     (d) levels 0,1: from level 2 by transition-surjectivity
     (`unitsToZModPow_le` + `Subgroup.map`-zpowers-⊤ pushforward; level 0 trivial
     group). §3's `exists_topological_generator` proof structure (PseudoMeasure:857)
     is the template for the level-bookkeeping.
- **Mathlib lemmas**: `orderOf_eq_card_of_forall_mem_zpowers`,
  `ZMod.card_units_eq_totient`, `Nat.totient_prime_pow`, `orderOf_one_add_mul_prime`
  (ZMod-side, located during §3 work), `Nat.le_of_dvd`, `Nat.lcm_dvd`/`dvd`-algebra,
  `ZMod.natCast_val`, `map_natCast`.
- **Sources**: RJW TeX 1566 (the gloss) + decomposition R5 head-note
  (cross-references). LOC ~60–80 (the board's largest single leaf — bounded,
  toolkit proven in §3 T026).
- **Generality**: stated for this p (no further generality available — p=2 false).
- **Blueprint**: no §4 node (supporting lemma); mention in `kubota-leopoldt`
  def-node prose when T038 wires it.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:
  - 2026-06-10: DONE — topGen_pow_ne_one (level-(k+1) order vs totient growth;
    Nat.card vs Fintype.card bridge needed) and exists_nat_topological_generator
    (~110 LOC: integer lift of u₀ mod p² via ZMod.natCast_rightInverse; p∤m by the
    p²∣p contradiction; descent along surjective unitsMap via MonoidHom.map_zpowers +
    Subgroup.map_top_of_surjective; Fermat split m^{p−1} = 1+pc with p∤c from the
    level-2 order p(p−1); ascent: orderOf bounds via ZMod.orderOf_one_add_mul_prime
    (n = n'+1 destructuring to align types) + coprime lcm + eq_top_of_card_eq).
    Names found: ZMod.natCast_eq_zero_iff (not the old natCast_zmod_…), orderOf_units,
    Nat.card_zpowers. Axioms standard. Cleanup: degraded.

### [T038] `ζ_p`: definition, pseudo-measure property, interpolation
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T036, T037
- **Parallel**: no
- **Type**: def + theorems (3 sorries: `IsPseudoMeasure.sub`,
  `padicZeta_isPseudoMeasure`, `padicZeta_moments`)
- **Statement**: in skeleton (ZetaP.lean:110–151). `padicZeta` def already compiles.
- **Proof sketch** (decomposition L5.5–L5.7):
  1. `IsPseudoMeasure.sub`: `intro g`; witnesses `ν₁, ν₂`; `⟨ν₁ − ν₂, by
     rw [map_sub, mul_sub, hν₁, hν₂]⟩`.
  2. `padicZeta_isPseudoMeasure`: unfold `padicZeta`; `isPseudoMeasure_mk'` (§3,
     PseudoMeasure:1024) at the `choose_spec` generator-property.
  3. `padicZeta_moments`: from `IsLocalization.mk'_spec`:
     `([u]−1)·ζ_p = alg(zetaNum m)`; multiply `hν` by `alg([u]−1)` and the spec by
     `alg([b]−1)`; equate, pull back along `IsFractionRing.injective`
     (`NoZeroDivisors` ✓): `([u]−1)·ν = ([b]−1)·zetaNum m` in Λ;
     `units_mul_apply_unitsPowCM` (§3 :753) + dirac/one moments
     (`dirac`-apply `= u^k`; `1`-apply `= 1`):
     `(u^k−1)·ν(x^k) = (b^k−1)·zetaNum(x^k)`; cast to ℚ_p; divide by
     `(u^k−1) ≠ 0` (T037 `topGen_pow_ne_one` + `PadicInt.coe_injective`-cast,
     `sub_ne_zero`); insert `zetaNum_moments` (T036); sign removal:
     `neg_one_pow_mul_one_sub_pow_mul_zetaNeg` (T030) after `push_cast`
     (the ℚ-lemma casts to ℚ_p: `Rat.cast`-hom on the identity).
- **Mathlib lemmas**: `IsLocalization.mk'_spec`, `IsFractionRing.injective`,
  `sub_ne_zero`, field algebra (`div_eq_iff`, `mul_comm`-shuffles).
- **Sources**: RJW Def 4.10 (TeX 1565–1570), Prop 4.11 + proof (TeX 1581–1597) —
  quotes in decomposition R5.
- **Generality**: `padicZeta_moments` quantifies over ALL `b` and ALL witnesses
  (the strongest faithful form; gives a-independence content of zero-divisor(iii)
  for free at T039).
- **Blueprint**: wire `kubota-leopoldt` (def-node) → `PadicMeasure.padicZeta`
  (prose: mention the fixed integer-generator choice + L5.4);
  wire `kl-zetap-interpolation` → `PadicMeasure.padicZeta_moments`.
- **Cleanup**: `/cleanup` immediately after.
- **Progress**:
  - 2026-06-10: DONE — IsPseudoMeasure.sub (mul_sub then ← map_sub: order matters),
    padicZeta_isPseudoMeasure (exact isPseudoMeasure_mk' at the choice-spec),
    padicZeta_moments (mk'_spec' for the defining relation; witness pullback via
    IsFractionRing.injective; moments via units_mul_apply_unitsPowCM + dirac_apply
    rfl + units_one_def; division by u^k−1 via Subtype.coe_injective-torsion-freeness;
    final algebra: linear_combination (b^k−1)(u^k−1)·hsign — rw [← hsign] fails on
    associativity, linear_combination is the right tool). Axioms standard.
    Blueprint: kubota-leopoldt → padicZeta, kl-zetap-interpolation →
    padicZeta_moments; builds green. Cleanup: degraded.

### [CLEANUP-ALL-2] Pre-milestone `/cleanup-all` (§4)
- **Status**: done (2026-06-10, degraded mode — no lean-lsp). Swept all four
  KubotaLeopoldt files + §3: fixed the `finsum_eq_finsetSum_of_support_subset`
  deprecation in Toolbox.lean; remaining warnings are the standing cosmetic
  `show`-linter items (§3-pattern, queued for tooled CLEANUP-FINAL) + one
  flexible-simp note (MuA.lean:260) queued likewise. Blueprint re-render deferred
  to post-T039 (single render).
- **Depends on**: T030–T038
- **Type**: cleanup
- **Description**: project-wide cleanup before the §4 milestone theorem, per the
  cadence rule. Sweep the four KubotaLeopoldt files + any §3 files touched
  (Toolbox if psi-lemmas land there); verify linter set; re-render blueprint site
  (`./scripts/ci-pages.sh`).

### [T039] **MILESTONE** — Kubota–Leopoldt: existence and uniqueness
- **Status**: done (2026-06-10)
- **File**: PadicLFunctions/KubotaLeopoldt/ZetaP.lean
- **Depends on**: T038, CLEANUP-ALL-2
- **Parallel**: no
- **Type**: theorem (1 sorry: `kubotaLeopoldt`)
- **Statement**: in skeleton (ZetaP.lean:154).
- **Proof sketch** (decomposition L5.8; source TeX 1599):
  1. Existence: `⟨padicZeta p hp2, ⟨padicZeta_isPseudoMeasure …, fun b k hk ν hν =>
     padicZeta_moments …⟩, ?uniq⟩`.
  2. Uniqueness: `q` with the property; show `q = padicZeta`: set `d := q −
     padicZeta`; `IsPseudoMeasure.sub` (T038); apply
     `pseudoMeasure_eq_zero_of_moments` (§3 :829) at `a := u` (the T037 generator,
     torsion-free via `topGen_pow_ne_one`): given a witness `ν` of `([u]−1)·d`,
     produce witnesses `ν₁` of `([u]−1)q` (from `hq.2`-side: `q`'s
     IsPseudoMeasure at `u`) and `ν₂ := ν₁ − ν` for padicZeta — or symmetrically;
     both interpolation values equal (the property at `b := u`) ⟹
     `ν(x^k)`-cast `= 0` ⟹ `ν(x^k) = 0` (`PadicInt`-cast injective +
     `Rat`-cast arith); conclude `d = 0`; `sub_eq_zero`.
     (Witness bookkeeping: `alg([u]−1)·d = alg(ν)` with `alg` injective makes all
     witness-identifications unique — `IsFractionRing.injective` once.)
- **Mathlib lemmas**: `sub_eq_zero`, `ExistsUnique`-intro shape; rest §3/§4 project.
- **Sources**: RJW Thm 4.1 (TeX 1444–1447) + proof line (TeX 1599) — quoted at
  decomposition R-KL head.
- **Generality**: statement quantifies moments over all `b` (decomposition R-KL
  "moment encoding" note).
- **Blueprint**: wire `kl-existence-uniqueness` → `PadicMeasure.kubotaLeopoldt`.
  This completes the §4 chapter except `kl-values-of-zeta` (unwired, §2-pending —
  rationale comment in place from T033). Re-render site.
- **Cleanup**: `/cleanup` immediately after (= final per-file cleanup for
  ZetaP.lean, CLEANUP-KL-2 folded in). Then update CLEANUP-FINAL's scope to include
  the §4 files.
- **Progress**:
  - 2026-06-10: **DONE — RJW Theorem 4.1 proven.** Existence: padicZeta +
    padicZeta_isPseudoMeasure + padicZeta_moments. Uniqueness: difference is a
    pseudo-measure (IsPseudoMeasure.sub) with vanishing witness-moments (witness
    split via IsFractionRing.injective; both interpolations at b := u subtract to 0;
    Subtype.coe_injective with a beta-reducing `show` for the ℤ_p-level conclusion),
    killed by pseudoMeasure_eq_zero_of_moments at the integer generator.
    `lake build PadicLFunctions` green, ZERO sorries project-wide,
    #print axioms kubotaLeopoldt = [propext, Classical.choice, Quot.sound].
    Blueprint: kl-existence-uniqueness → kubotaLeopoldt wired; chapter now 10/11
    nodes green (kl-values-of-zeta deliberately unwired pending §2 Mellin theory);
    site re-rendered (ci-pages OK). Final per-file cleanup ZetaP.lean: degraded
    pass done (show-linter cosmetics queued for tooled CLEANUP-FINAL).

### CLEANUP-FINAL scope note (updated 2026-06-10)
CLEANUP-FINAL (§3 board) now covers the §4 files too:
PadicLFunctions/KubotaLeopoldt/{ZetaValues,ZetaValuesComplex,MuA,ZetaP}.lean.
Queued degraded-mode items: show-linter cosmetics (project-wide pattern),
flexible-simp at MuA.lean:260, psi-bundling (psi → LinearMap), delQ/del merge
(generalise del to CommRing), mahlerTransform_sub/smul → Convolution.lean,
instIsDomain + SMulCommClass placement review. Blocked on a lean-lsp-tooled session.

## §4 dependency quick-view

```
T030 (zeta values)──────────────┐
T031 (F_a, μ_a)──┬─ T032 (dirac/domain) ─┬─ T034 (ψ) ─┐
                 └─ T033 (moments) ←T030 ┘            ├─ T035 (Res moments)
T037 (integer generator) [independent]                │
T036 (units/x⁻¹) ←─────────────────────────────────────┘
T038 (ζ_p) ← T036, T037
CLEANUP-ALL-2 ← T030..T038
T039 MILESTONE ← T038, CLEANUP-ALL-2
```
Parallel capacity: 3 workers at peak (T030/T031/T037 start immediately).
Cleanup cadence: per-ticket immediate cleanup (standing rule) ⊇ 3-ticket cadence;
final per-file cleanups folded into T035 (MuA.lean) and T039 (ZetaP.lean);
CLEANUP-ALL-2 guards the milestone; CLEANUP-FINAL (§3 board) extended to §4 files.

---

# §5 — Interpolation at Dirichlet characters (TeX 1610–1979) — added 2026-06-10

## §5 Summary
- Tickets: TW1–TW6 (widening) + T501–T523 (§5 proper + exp/log cluster,
  user-added at board approval) + cleanups per cadence
- Open: all | Done: 0
- Decomposition: `.mathlib-quality/decomposition.md` §5 (W*, L5.1.*, L5.2.*, L5.3.*;
  gate PASSED 2026-06-10 with 3 recorded replan/design notes: R5-CLEAR,
  L5.2.4-route, L5.2.8/L5.3.3 statement designs)
- Skeleton: `Coefficients.lean` + `Interpolation/{Characters,GenBernoulli,
  GenBernoulliComplex,Branches}.lean` skeletonised NOW; the Λ_R-dependent
  statements (Twist/TameConductor/NonTame) are skeletonised by TW6 (refactor
  exception, decomposition §5 "Skeleton location")
- Coefficients: `L` normed field, `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
  [CompleteSpace L]`, `R := integerRing L` (plan.md §5 design decision 1)
- **Standing rules (CLAUDE.md) bind every ticket**: blueprint node wiring in-session
  (chapter: `Interpolation.lean`; node labels listed per ticket), /cleanup
  (FULL tooled mode — lean-lsp present) before done, axioms ⊆ standard, checkpoint
  commit + push.
- **Parallel capacity**: 3 chains independent at the start — (A) TW-chain,
  (B) T501/T503/T504/T505 (Gauss/Bernoulli, no W dependency), (C) T517/T518
  (Branches, no W dependency). §5.1/§5.2 assembly tickets need (A).

### [TW1] Coefficients: integerRing + instances + root-of-unity norms
- **Status**: done (2026-06-10T17:05Z)
- **Progress**: 2026-06-10: all 8 skeleton sorries discharged. W1 integerRing +
  4 instances (ultrametric/complete/Algebra ℤ_[p]/IsLinearTopology via ballIdeal +
  mk_of_hasBasis'); helper norm_natCast_self_lt_one; W2 norm_sub_one_lt
  (binomial + Nat.Prime.dvd_choose_pow + exists_norm_finsetSum_le_of_nonempty);
  W2' tendsto; W3 norm_pow_sub_one_eq_one (prod_one_sub_pow_eq_order +
  Padic.norm_natCast_eq_one_iff + erase-product argument). VERIFICATION: zero
  diagnostics; #print axioms = {propext, Classical.choice, Quot.sound} on both
  headline theorems (lean_verify); lake build green project-wide (3517 jobs).
  CLEANUP: tooled-inline at authoring (zero linter warnings incl. show/push_neg/
  longLine/unusedSectionVars all fixed; import order corrected); formal 10-phase
  file pass runs at CLEANUP-W1 per board placement. Mathlib-gap notes: no
  norm-unit-ball subring in mathlib (integerRing is a PR candidate, as are W2/W3). | **File**: PadicLFunctions/Coefficients.lean | **Depends on**: none
- **Parallel**: yes (chain A head) | **Type**: def + instances + lemmas
- **Statement**: fill the skeleton sorries at Coefficients.lean (integerRing
  subring fields; IsUltrametricDist/CompleteSpace/Algebra ℤ_[p]/IsLinearTopology
  instances; `IsPrimitiveRoot.norm_sub_one_lt`, `.tendsto_pow_sub_one`,
  `.norm_pow_sub_one_eq_one`).
- **Proof sketch**: decomposition W1/W2/W3 + L5.1.6a entries (routes + attack
  logs there). W1 closure: `IsUltrametricDist.norm_add_le_max` (mathlib, exact
  name verify via lean_local_search) + `norm_mul_le`. Completeness:
  `IsClosed.completeSpace_coe` on the closed ball. Algebra: `‖algebraMap ℚ_[p] L
  q‖ = ‖q‖` from `NormedAlgebra` (norm_algebraMap') restricted to ℤ_[p].
  IsLinearTopology: `IsLinearTopology.mk_of_hasBasis`-style with the ideal basis
  `{x | ‖x‖ ≤ ε}` (ideals by ultrametric + ‖unit-ball·x‖ ≤ ‖x‖). W2: binomial
  expansion of (1+x)^{p^n} = 1 + Kummer `Nat.Prime.dvd_choose` (mathlib name:
  `Nat.Prime.dvd_choose_pow`?? verify) + norm contradiction. W3: evaluate
  `∏_{0<j<D}(X − ζ^j)` at 1 via `IsPrimitiveRoot` cyclotomic-product lemmas
  (search `IsPrimitiveRoot` `geom_sum`/`prod_X_sub`-family) ⟹ ∏(1−ζ^j) = D;
  norms multiply (NormedField), all ≤ 1, ‖D‖ = 1 (p ∤ D + algebra-norm).
- **Mathlib lemmas**: `IsUltrametricDist.norm_add_le_max`(-shape),
  `IsClosed.completeSpace_coe`, `norm_algebraMap'`, `Nat.Prime.dvd_choose`
  (Kummer-direction), `IsPrimitiveRoot.pow_eq_one`, cyclotomic product (verify
  candidates: `IsPrimitiveRoot.prod_one_sub_pow`-shape; fallback 8-line direct).
- **Sources**: RJW TeX 690 (O_L), 1798 (W3 verbatim quote in decomposition);
  Washington §1 for W2 (classical).
- **Generality**: maximal — any nonarch complete normed ℚ_[p]-algebra field;
  no finiteness over ℚ_p (plan.md §5 decision 1).
- **Blueprint**: none yet (infrastructure; Measures-chapter prose already wired).
- **Sizing**: W1 ~60 LOC, W2 ~25, W3 ~20, instances ~40 (source spans cited in
  decomposition; the instance pack has no source-lines — infrastructure).

### [TW2] Widen Measure/Basic.lean to coefficient ring R
- **Status**: done (2026-06-10T17:45Z)
- **REPLAN NOTE (route, 2026-06-10T17:20Z)**: in-place parameter swap rejected
  after measurement: ~420 call sites, and `ℤ_[p]` is definitionally-but-not-
  syntactically `↥(integerRing ℚ_[p])` (PadicInt is its own subtype with its own
  instance tower) — an in-place swap breaks every §4 call site with instance-
  diamond repairs, violating the "§4 unaffected" DoD. ROUTE: parallel general
  layer `PadicLFunctions/MeasureR/*.lean` over `(K : NormedField, ultrametric,
  complete; R := integerRing K)` mirroring Measure/* — the ambient field makes
  the W-r1 division/continuity argument work exactly as in the ℤ_p case; §3/§4
  stay frozen; TW6's baseChange bridges `PadicMeasure p X → MeasureR ℚ_[p]-…`
  via the TW1 algebra map. TW2 := MeasureR/Basic.lean; TW3–TW5 scope updated
  to the corresponding MeasureR files. plan.md "parameter-insertion" promise
  superseded by this recorded note (same lemmas+proof routes, new placement).
- **Progress**: 2026-06-10: MeasureR/Basic.lean complete, zero sorries —
  `MeasureR K X` (abbrev, LinearMap-transparent like §3), dirac/compRight/
  pushforward + simp API, `norm_apply_le` (field-division route per W-r1:
  attained sup + divide-by-scalar in K, integrality from ball-valuedness),
  `continuous`, `ext_locallyConstant` (reuses §3 Fubini general approximation
  lemma per W-r2). VERIFICATION: zero diagnostics; axioms standard
  (lean_verify on norm_apply_le); lake build green (3518 jobs). CLEANUP:
  tooled-inline at authoring (abbrev-not-def lesson recorded; rfl-bridge for
  subtype-norm). Formal file pass at CLEANUP-W1. | **File**: Measure/Basic.lean | **Depends on**: TW1 | **Type**: refactor
- **Contract**: re-parametrise `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`
  to `PadicMeasure R X := C(X, R) →ₗ[R] R` over
  `variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]`
  + per-lemma extras; keep an `abbrev`/notation so §3/§4 ℤ_[p]-call-sites stay
  green (`PadicMeasure p X` ↦ instantiation at `R := ℤ_[p]`; choose the spelling
  that minimises §4 churn — worker decides, records). `norm_apply_le` per
  decomposition W-r1 (division-by-attained-value; needs the codomain-ball
  argument — for abstract R state as `‖μ f‖ ≤ ‖f‖` PROVABLE when R is a ball
  ring: take the hypothesis spelling `[NormMulClass R]` + norm-≤-1-of-values…
  worker follows W-r1's resolution: values in R have ‖·‖ ≤ ?? — for abstract R
  the values are R itself: the W-r1 proof shape needs `‖μ g‖ ≤ 1`-from-
  R-valuedness only when R IS the ball of L. State the lemma over
  `integerRing L` directly if the abstract form fights — both forms recorded,
  decomposition W-r1). Density: rebase on Fubini.lean's
  `exists_locallyConstant_norm_sub_le'` (W-r2).
- **DoD**: `lake build PadicLFunctions` green project-wide, zero sorries in file,
  axioms standard, §4 unaffected, /cleanup, checkpoint commit.
- **Sources**: RJW Def 3.6 TeX 755–765 (§3 tree quotes).

### [TW3] Widen MahlerTransform.lean + Convolution.lean
- **Status**: done (2026-06-10T18:35Z)
- **Progress**: 2026-06-10: MeasureR/MahlerTransform.lean + MeasureR/Convolution.lean
  complete, ZERO sorries. mahlerCM basis through the isometric algebra map (new
  Coefficients lemmas: norm_algebraMap_eq, isometry_algebraMap, IsBoundedSMul);
  full Thm 3.20 over R: mahlerLinearEquiv + CommRing transport + mahlerRingEquiv +
  mul_apply (Chu-Vandermonde via algebraMap, congrArg-Subtype.val bridges) +
  dirac_mul_dirac. mahlerTransform_dirac restated as mapped binomialSeries
  (avoids BinomialRing on R — recorded). De-privated
  PadicMeasure.fwdDiff_iter_mahler_zero. VERIFICATION: zero diagnostics both
  files; axioms standard (lean_verify mul_apply); lake build green (3520).
  CLEANUP: tooled-inline at authoring; formal pass at CLEANUP-W1. | **Depends on**: TW2 | **Type**: refactor
- **Contract**: W-r3 — mathlib `mahlerEquiv` is already E-general; re-parametrise
  `mahlerCoeff/mahlerTransform/ofPowerSeries/mahlerLinearEquiv/mahlerRingEquiv`
  and the convolution transport to R. Re-check each `PadicInt.*`-specific call
  site (decomposition W-r3 attack note); `binomialSeries` acts through
  `algebraMap ℤ_[p] R`.
- **DoD**: as TW2.

### [CLEANUP-W1] /cleanup on Coefficients.lean + Basic.lean + MahlerTransform.lean + Convolution.lean
- **Status**: done (2026-06-10T18:50Z) | **Depends on**: TW3 | **Type**: cleanup (cadence: 3 tickets)
- **Progress**: scope = the new W-layer (Coefficients + MeasureR/{Basic,
  MahlerTransform,Convolution}). Full-severity diagnostic audit via lean-lsp:
  9 findings (1 unused simp arg, 4 show-changed-goal -> change, 4 unused
  section vars -> omit) — all fixed; build green, new files zero-warning.
  Per-decl golf was applied inline at authoring (same session, live linter);
  worker-per-decl ceremony recorded as not-redispatched for just-authored
  lint-clean decls (deviation note; the §3-files' standing show-warnings
  remain CLEANUP-FINAL scope).

### [TW4] Widen Toolbox.lean + UnitsZp.lean + Fubini.lean
- **Status**: done (2026-06-10T19:40Z)
- **Progress**: MeasureR/{Toolbox,UnitsZp,Fubini}.lean complete, ZERO sorries.
  Toolbox: cmul/del/powCM + mahlerTransform_cmul_X + apply_powCM (Cor 3.25
  over R; reuses de-privated PadicMeasure.mul_choose_eq through algebraMap),
  charFnCM (moved to Basic, p-FREE — mathlib charFn is value-ring-parametric,
  design improvement over the algebraMap detour), res/IsSupportedOn,
  sigma/phi/psi + psi_phi/phi_psi/res_units_eq/Cor 3.32 (space-side digit/
  shiftDiv/clopens reused from §3 — zero duplication). UnitsZp: extendByZero,
  iota, iota_injective, res_iota, mem_range_iota_iff (= ker ψ). Fubini:
  innerInt + integral_swap (the §3 approximation argument verbatim over R).
  VERIFICATION: zero diagnostics all files; axioms standard (lean_verify
  integral_swap); lake build green project-wide. CLEANUP: tooled-inline;
  formal pass folded into CLEANUP-W2. | **Depends on**: CLEANUP-W1 | **Type**: refactor
- **Contract**: W-r4 — space-side constructions re-parametrise mechanically
  (res/σ/φ/ψ/shiftDiv, units geometry, integral_swap). The §4-needed toolbox
  lemmas (φ-moment scaling, psi_phi_mul-projection formula in MuA.lean —
  actually relocate-or-widen: psi_phi_mul lives in MuA.lean (§4); widen its
  STATEMENT to R here or in TW5, worker picks placement, records).
- **DoD**: as TW2.

### [TW5] Widen PseudoMeasure.lean's Λ(ℤ_p^×)-ring section; §4 call-site repair
- **Status**: done (2026-06-10T20:10Z)
- **Progress**: MeasureR/UnitsRing.lean complete, ZERO sorries: unitsConv +
  CommRing (comm via integral_swap, assoc via triple-integral changes with
  Subtype.val bridges), units_dirac_mul_dirac, deg ring hom. innerInt API
  (add/smul/measure_add/measure_zero) added to MeasureR/Fubini. §4 call-site
  repair: NOT NEEDED under the parallel-layer route (§4 untouched — the
  route's purpose). Pseudo-measure theory stays ℤ_p per scope note.
  psi_phi_mul widening deferred to T513 (per TW4's "worker picks placement"
  note — T513 is its only §5 consumer). VERIFICATION: zero diagnostics,
  axioms standard, build green. | **Depends on**: TW4 | **Type**: refactor
- **Contract**: the units-convolution ring (unitsConv, CommRing laws, diracs,
  degree) over R; the pseudo-measure/zero-divisor/augmentation/QuotientField
  sections STAY at ℤ_[p] (decomposition W-r4 scope note). All §4 files compile
  unchanged-or-mechanically-repaired (W-r5).
- **DoD**: as TW2 + `#print axioms PadicMeasure.kubotaLeopoldt` still standard.

### [TW6] baseChange + skeletonise Λ_R-dependent §5 statements
- **Status**: done (2026-06-10T21:05Z)
- **Progress**: MeasureR/BaseChange.lean SORRY-FREE: baseChange ring hom
  (transform-side coefficient inclusion), mahlerTransform_baseChange,
  baseChange_dirac, algCM + baseChange_algCM (the characterising property,
  via tsum-mapping through the isometric algebra map). Naturality lemmas
  (psi/res/twist-compat) deferred to their §5 consumers per the loc-const
  strategy recorded in this ticket's notes. SKELETON GATE: Interpolation/
  {Twist,TameConductor,NonTame}.lean created with the Λ_R-dependent
  statements (16 sorries; charCM helper; toFieldChar bridge; statements per
  decomposition with the L5.1.8-trace-pinned form, R5-CLEAR clearing, and
  the L5.2.8 determinacy design). Support: CharZero-of-ℚ_p-algebra lemma;
  isClopen_toZModPow_fiber skeleton. Build green project-wide. W-CLUSTER
  CRITICAL PATH COMPLETE — all three §5 chains unblocked. | **Depends on**: TW5 | **Type**: def + skeleton gate
- **Statement** (key new decl): `PadicMeasure.baseChange : PadicMeasure p X →
  PadicMeasureR R X`-shape (W4: transform-side coefficient inclusion for
  X = ℤ_p; density-extension for general profinite X; ring hom on Λ(ℤ_p);
  `baseChange_dirac`, naturality w.r.t. res/φ/ψ/twist as API lemmas).
  THEN: create `Interpolation/Twist.lean`, `Interpolation/TameConductor.lean`,
  `Interpolation/NonTame.lean` with ALL the Λ_R-dependent leaf statements from
  decomposition §5 (L5.1.2/3/6/7/8/10/12, L5.2.1–L5.2.8) as `:= by sorry`,
  imports wired into PadicLFunctions.lean; `lake build` green (THE deferred
  Step-2.5 gate — decomposition "Refactor-cluster exception").
- **DoD**: build green (sorries allowed in the three new files ONLY), /cleanup
  on baseChange, commit.

### [CLEANUP-W2] /cleanup-all-lite on the widened Measure/* (final per-file)
- **Status**: done (degraded — subsumed by CLEANUP-FINAL, 2026-06-11)
- **Depends on**: TW6 | **Type**: cleanup (final per-file ×6)
- **Progress**:
  - 2026-06-11: sequenced with the final cleanup block (CL53/CL54/
    CLEANUP-FINAL): §5 consumers were still adding to Measure/* through T516
    (extendByZero factorisation in Basic.lean), and the per-decl golf needs a
    lean-lsp-tooled session. Linter-set is green on Measure/* as of the
    ALL-5 sweep (2026-06-11). Not a mainline blocker.

### [T501] Gauss sums: product formula at general level + norm-one
- **Status**: done (2026-06-10T21:40Z)
- **Progress**: BOTH lemmas proven, zero sorries in their section.
  gaussSum_mul_gaussSum_inv (Rem 5.3(i) at general level N, domain target —
  the planned 4-sum collapse: mulShift-of-primitive backwards, sum swap,
  AddChar.sum_mulShift orthogonality; MATHLIB-PR CANDIDATE).
  norm_gaussSum_eq_one (torsion-values ultrametric bound + product formula +
  ‖D‖=1; helper norm_eq_one_of_pow_eq_one for normed fields, also PR-shape).
  BLUEPRINT: interp-gauss-sum → mathlib gaussSum; interp-gauss-sum-properties
  → {PadicLFunctions.gaussSum_mul_gaussSum_inv, gaussSum_mulShift_of_isPrimitive}
  with prose note on the cleared form; blueprint builds. VERIFICATION:
  axioms standard (lean_verify), build green. | **File**: Interpolation/Characters.lean | **Depends on**: none
- **Parallel**: yes (chain B head) | **Type**: lemmas (mathlib-PR candidates)
- **Statement**: skeleton `gaussSum_mul_gaussSum_inv` (L5.1.5),
  `norm_gaussSum_eq_one`, + any zmodChar-primitivity bridge sub-lemmas needed.
- **Proof sketch**: decomposition L5.1.5 (the 4-sum collapse; attack-verified);
  norm-one via ≤1 (ultrametric sum of root-of-unity terms — values χ(c)ζ^c with
  ‖·‖ ≤ 1… careful: χ values in L: roots of unity have norm 1 — NormedField +
  finite order ⟹ ‖χ(c)‖ = 1; sub-lemma) then product = ±D with ‖D‖ = 1 splits.
- **Mathlib lemmas**: `gaussSum_mulShift_of_isPrimitive`,
  `gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`, `AddChar.sum_mulShift`-
  orthogonality ingredient (verify generality — field proof's `sum_mulShift`),
  `ZMod.zmodChar`, `IsPrimitiveRoot.pow_eq_one`.
- **Sources**: Rem 5.3 TeX 1653–1659 (verbatim in decomposition L5.1.4); DS05
  §4.3 (cross-ref); TeX 1798 for norm-one.
- **Generality**: general level N, domain target; norm-form over the §5 L.
- **Blueprint**: wire `interp-gauss-sum` → mathlib `gaussSum` and
  `interp-gauss-sum-properties` → the pair {mathlib mulShift lemma,
  `PadicLFunctions.gaussSum_mul_gaussSum_inv`} per the new linking policy.
- **Sizing**: L5.1.5 ~35 LOC (source proof 6 lines, TeX 1685–1691-adjacent);
  norm lemma ~20.

### [T502] χ as a locally constant function on ℤ_p
- **Status**: done (2026-06-10T22:05Z)
- **Progress**: all 5 sorries discharged: continuity via locally-constant
  fibres (reusing §3 isOpen_toZModPow_fiber), vanishing on pℤ_p (p∣x +
  isUnit_of_mul_isUnit_left + coprime-self contradiction), multiplicativity
  (REPLAN: hypothesis-free — MulChars are unconditionally multiplicative;
  the skeleton's 1 ≤ n dropped), isLocallyConstant, norm ≤ 1 (REPLAN:
  specialised to ball-valued characters where it is the subtype bound; the
  general-R form was unprovable-or-vacuous — recorded). Characters.lean now
  fully sorry-free. Axioms standard, build green. | **File**: Interpolation/Characters.lean | **Depends on**: none
- **Parallel**: yes | **Type**: def API
- **Statement**: skeleton `DirichletCharacter.toContinuousMapZp` continuity +
  4 API sorries (L5.1.1).
- **Proof sketch**: decomposition L5.1.1 (toZModPow fibres clopen — §3
  Basic.lean pattern `isLocallyConstant_toZModPow_val`; vanishing via
  `MulChar.map_nonunit` + unit-reduction bridge `PadicInt.isUnit_toZModPow_iff`-
  shape (verify; else 6-line norm argument)).
- **Mathlib lemmas**: `MulChar.map_nonunit`, `IsLocallyConstant.continuous`,
  `ZMod.isUnit_iff`-family.
- **Sources**: TeX 1620 (quote at L5.1.1).
- **Blueprint**: contributes to `interp-twist` prose (wired at T506).
- **Sizing**: ~50 LOC total (5 lemmas).

### [T503] genBernoulli: trivial character + parity + cyclotomic product
- **Status**: done (2026-06-10T22:55Z)
- **Progress**: all three proven. genBernoulli_one (B_{k,1} = bernoulli' k via
  bernoulli_eval_one). genBernoulli_eq_zero (parity): level-one branch via
  bernoulli'_odd_eq_zero; main branch via the ZMod-indexed sum (image-bijection
  a ↦ a+1 with boundary terms killed by χ(0)=0), Equiv.neg reflection with
  ZMod.val_neg_of_ne_zero, and the mapped reflection identity
  bernoulli_eval_one_sub through algebraMap ℚ L; factor 2 ≠ 0 (CharZero).
  prod_primitiveRoot_mul_sub_one: STATEMENT CORRECTED at proof time — the
  skeleton form was FALSE for even M ((Y−1)(−Y−1) = 1−Y²); hypothesis Odd M
  added (faithful: used only at M = p^n, p odd); proof via Kummer
  X_pow_sub_C_eq_prod evaluated at 1 + Finset.prod_neg + Odd.neg_one_pow.
  Recorded as a decomposition-attack miss (L5.1.10c didn't try even M).
  VERIFICATION: build green, axioms standard. | **File**: Interpolation/GenBernoulli.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `genBernoulli_one`, `genBernoulli_eq_zero`,
  `prod_primitiveRoot_mul_sub_one` (L5.1.9/L5.1.11/L5.1.10c).
- **Proof sketch**: decomposition entries (a-range 1..N pinned; involution
  c ↦ N−c + `bernoulli_eval_one_sub`; product via `IsPrimitiveRoot`).
- **Mathlib lemmas**: `Polynomial.bernoulli_eval_one_sub` (verify name),
  `Polynomial.bernoulli_eval_one`, `bernoulli'`-bridges,
  `IsPrimitiveRoot.prod_X_sub_pow`-family (verify; else direct).
- **Sources**: Washington §4.1 Prop 4.1 (cross-ref recorded); TeX 1744–1746.
- **Blueprint**: none directly (value infrastructure).
- **Sizing**: ~30+35+20 LOC.

### [T504] genBernoulli generating function (L5.1.10a)
- **Status**: done | **File**: GenBernoulli.lean | **Depends on**: T503 | **Type**: lemma
- **Progress**: DONE 2026-06-10. Route refined at execution: instead of
  per-coefficient bernoulliPowerSeries bookkeeping, used mathlib's
  `Polynomial.bernoulli_generating_function (t)` directly at `t = (a+1)/N`,
  hit with the ring hom `rescale (N : L)` (rescale_rescale +
  div_mul_cancel₀ collapses `rescale N ∘ rescale ((a+1)/N) = rescale (a+1)`;
  rescale_X gives the `C N` factor), then χ-weighted sum over `a ∈ range N`
  and cancellation of `C N` (domain, `mul_left_cancel₀`). The coefficient
  identification `C N · mk(B_{k,χ}/k!) = Σ_a χ(a+1) • rescale N (GF_a)` is
  `ext k` + zpow collapse `N^k = N·N^{(k:ℤ)−1}` (`zpow_sub_one₀`) +
  aeval→eval-of-map conversion (`map_smul`, `Algebra.smul_def`, targeted
  `map_natCast (algebraMap ℚ L) k.factorial` — the untargeted form matched
  χ↑(a+1) and stuck on a RingHomClass goal) + `ring`. GenBernoulli.lean now
  SORRY-FREE; also fixed deprecated `bernoulli'_odd_eq_zero` →
  `bernoulli'_eq_zero_of_odd` in T503's proof. Verification: zero
  diagnostics; axioms = {propext, Classical.choice, Quot.sound} on
  genBernoulliPowerSeries_mul (scan_source clean). No blueprint node
  (Washington-sourced internal identity).
- **Statement**: skeleton `genBernoulliPowerSeries_mul`.
- **Proof sketch**: decomposition L5.1.10a — expand both sides; mathlib
  `bernoulliPowerSeries_mul_exp_sub_one` per-a after rescale-bookkeeping
  (`exp_pow_eq_rescale_exp`, `rescale_comp`-laws); T031's clearing pattern.
- **Mathlib lemmas**: `bernoulliPowerSeries_mul_exp_sub_one`,
  `PowerSeries.exp`, `rescale`, `Polynomial.bernoulli_generating_function`-
  variant (exact mathlib relating bernoulli POLYNOMIALS: `Polynomial.sum_range_pow`-
  family — survey at execution; the §4 T031–T033 files are the template).
- **Sources**: Washington §4.1 defining identity (cross-ref recorded).
- **Sizing**: source's manipulation ~10 lines ⟹ ~80 LOC Lean (T031 analogue
  ran ~70).

### [T505a] Sawtooth boundary: sinZeta(x,1) = π(1/2−x) and hurwitzZeta at s=0
- **Status**: done | **File**: Interpolation/Sawtooth.lean (new) | **Depends on**: none
- **Progress**: DONE 2026-06-10. Sawtooth.lean (~740 lines): port compiled with
  only 3 cast-juggling fixes (Tendsto.comp eta-mismatch → plain `exact`;
  push_cast before ring in the ζ_O(x,0) endgame; `map_inv₀` not `map_div₀` for
  algebraMap ℚ ℂ 2⁻¹). All four mathlib dependencies present in pin
  (tendsto_tsum_powerSeries_nhdsWithin_lt, hasSum_taylorSeries_neg_log,
  Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded,
  hasSum_nat_sinZeta). New beyond the port: `unitAddCircle_coe_ne_zero`,
  `hurwitzZetaOdd_apply_zero_of_mem_Ioo` (ζ_O(x,0) = 1/2−x via
  hurwitzZetaOdd_one_sub at s=1 + Gamma_one + cpow_neg_one + sin π/2),
  `hurwitzZeta_neg_nat_of_mem_Ioo` (all k ≥ 0; docstring records the genuine
  x=0 boundary failure ζ(0) = −1/2 ≠ −B₁(0)). 13 over-length lines repacked;
  lake build green. Axioms = {propext, Classical.choice, Quot.sound} on
  sinZeta_one_eq_boundary (scan clean) and hurwitzZeta_neg_nat_of_mem_Ioo.
  Mathlib PR candidate alongside T505.
- **Spawned by**: T505 (beastmode A1, 2026-06-10) — mathlib gap: `hurwitzZeta_neg_nat`
  requires `k ≠ 0` (mathlib's own TODO: "formula also correct for k = 0; current
  proof does not work"); the missing ingredient is the conditionally-convergent
  sawtooth value `sinZeta x 1 = π(1/2 − x)` on `(0,1)` (Dirichlet-test/Abel
  boundary argument, no absolutely-convergent route).
- **Statement**: port of flt-regular-bernoulli `LValueAtOne/{DirichletBounds,
  ComplexBounds-general-part,Sine}.lean` (user's own repo, sorry-free, same
  author/licence): Dirichlet-test partial-sum bounds; `sinZeta_one_eq_boundary
  {x} (0<x) (x<1) : sinZeta x 1 = π(1/2−x)`; NEW composition lemmas
  `hurwitzZetaOdd_apply_zero_of_mem_Ioo : hurwitzZetaOdd x 0 = 1/2 − x` (via
  `hurwitzZetaOdd_one_sub` at s=1: ζ_O(x,0) = 2(2π)⁻¹Γ(1)sin(π/2)·sinZeta x 1)
  and `hurwitzZeta_apply_zero_of_mem_Ioo : hurwitzZeta x 0 =
  −((bernoulli 1).map (algebraMap ℚ ℂ)).eval x` (even part 0 on (0,1) by
  `hurwitzZetaEven_apply_zero`) — closing mathlib's k=0 TODO for interior x.
- **Mathlib lemmas**: `HurwitzZeta.hasSum_nat_sinZeta`,
  `differentiableAt_sinZeta`, `hurwitzZetaOdd_one_sub`,
  `hurwitzZetaEven_apply_zero`, `geom_sum_eq`, `UniformCauchySeqOn` API.
- **Sources**: port provenance flt-regular-bernoulli (survey addendum,
  plan.md); the mathematical content is the classical Abel-limit evaluation of
  Σ sin(2πnx)/n (Washington Ch. 4 territory).
- **Sizing**: ~700 LOC port + ~60 new.

### [T505] Complex bridge: L(χ,−k) = −B_{k+1,χ}/(k+1)
- **Status**: done | **File**: GenBernoulliComplex.lean | **Depends on**: T503, T505a
- **Progress**: DONE 2026-06-10. `LFunction_neg_nat` proven for ALL k ≥ 0
  (the planned statement, unrestricted — the k=0 gap that spawned T505a is
  closed). N=1 branch: level_one + LFunction_modOne_eq +
  riemannZeta_neg_nat_eq_bernoulli' + genBernoulli_one + eq_ratCast. N>1
  branch: unfold LFunction/ZMod.LFunction (simp only with def names),
  cpow_natCast; termwise hurwitzZeta values (j = 0 killed by χ(0) = 0 — this
  is what confines to the OPEN interval where T505a applies; j ≠ 0 via
  toAddCircle_apply + hurwitzZeta_neg_nat_of_mem_Ioo); NEW REUSABLE LEMMA
  `genBernoulli_eq_zmod_sum` extracted from T503's hsum_eq block (range-sum =
  ZMod-sum bijection; genBernoulli_eq_zero refactored to consume it — net
  ~35 lines saved, both compile); endgame eq_div_iff + sum_mul +
  sum_neg_distrib + per-term field_simp. Verification: lake build green
  (full PadicLFunctions incl. new Sawtooth import in root); axioms =
  {propext, Classical.choice, Quot.sound} on LFunction_neg_nat (scan clean).
  Blueprint: `interp-dirichlet-integral` left unwired with the
  kl-values-of-zeta-pattern rationale comment naming LvalNeg /
  LFunction_neg_nat / sinZeta_one_eq_boundary (no chapter node states the
  bare value identity). PR candidate.
- **Parallel**: yes | **Type**: theorem (quarantined complex; PR candidate)
- **Statement**: skeleton `LFunction_neg_nat`.
- **Proof sketch**: unfold `DirichletCharacter.LFunction` = `ZMod.LFunction` =
  `N^{−s}Σ_j χ(j)·hurwitzZeta(j/N)`; at s = −k apply `hurwitzZeta_neg_nat`
  (j/N ∈ [0,1]); collect into genBernoulli's polynomial sum (a-range shift
  0..N−1 ↦ 1..N: j = 0 term has χ(0) = 0 for N > 1; N = 1 separately via
  `riemannZeta_neg_nat_eq_bernoulli'` + `LFunction_modOne_eq`).
- **Mathlib lemmas**: `hurwitzZeta_neg_nat`, `ZMod.toAddCircle`-coercions,
  `riemannZeta_neg_nat_eq_bernoulli'`, `DirichletCharacter.LFunction`.
- **Sources**: TeX 1702–1740 (Lem 5.5 — its L-value content), Washington Thm 4.2.
- **Blueprint**: wire `interp-dirichlet-integral`'s VALUE half? — NO: that node
  states the full Mellin lemma (complex f_{χ,a}); stays unwired with rationale
  (§2-Mellin pending, kl-values-of-zeta pattern). This theorem is the §5
  analogue of `zetaNeg`'s complex bridge — wire INTO the chapter where the
  L-values are introduced via a remark node if present (worker checks chapter).
- **Sizing**: ~60 LOC.

### [T506] Twist by χ + z-twist transform formula
- **Status**: done | **File**: Interpolation/Twist.lean (TW6 skeleton) | **Depends on**: TW6, T502
- **Type**: def + lemmas
- **Statement** (from TW6 skeleton; signatures fixed there per decomposition
  L5.1.2/L5.1.6): `PadicMeasure.twist`, `twist_apply`, `twist_powCM`,
  `twist_res_units`-integral-form (L5.1.3), `mahlerTransform_charTwist`
  (L5.1.6, eval₂ form).
- **Proof sketch**: decomposition L5.1.2/3/6 (Dirac sanity + coefficientwise
  Chu–Vandermonde; the §3 T009/T014 proof patterns; eval₂ instance stack from
  TW1's IsLinearTopology).
- **Mathlib lemmas**: `PowerSeries.eval₂`/`aeval` + `WithPiTopology` instances;
  `PadicInt.addChar_of_value_at_one` + `mahlerSeries`-API.
- **Sources**: TeX 1637–1641 (verbatim at L5.1.2), TeX 1084–1090 (z-twist).
- **Blueprint**: wire `interp-twist` → `PadicMeasure.twist`.
- **Sizing**: twist API ~40; charTwist ~90 (T014 ran ~80).
- **Progress**: DONE 2026-06-10. `isClopen_toZModPow_fiber` delegated to the
  pre-existing `PadicMeasure.isClopen_toZModPow_fiber` (PseudoMeasure.lean —
  planner had restated it). `twist_res_units` via χ̃·1_{units} = χ̃ pointwise
  (unit: indicator 1; non-unit: `toContinuousMapZp_eq_zero`), with the
  congrArg-Subtype.val bridge after `ext`. `mahlerTransform_charTwist`
  (coefficientwise z-twist formula): apply_eq_tsum + per-m finite identity
  Δ^m[κ_r·binom(·,n)](0) = [X^n]((1+X)(1+r)−1)^m — both sides expanded to
  Σ_{i≤m} (−1)^{m−i}·C(m,i)·(1+r)^i·C(i,n) via fwdDiff_iter_eq_sum_shift and
  Commute.add_pow; new API `charCM_natCast` (κ_r(↑k) = (1+r)^k, the
  onePAdicPow_natCast pattern); coeff of (1+X)^i via Polynomial-cast
  (binomialSeries route blocked: no BinomialRing instance on integerRing K).
  Linter clean (omits added, show→change). Verification: zero errors, only
  T507/T508 sorries remain in the file; axioms = {propext, Classical.choice,
  Quot.sound} on mahlerTransform_charTwist. Blueprint: `interp-twist` wired to
  {MeasureR.twist, MeasureR.twist_res_units} with prose note; build green.

### [T507] Cleared restriction formula (EqRestrictionFormula)
- **Status**: done | **File**: Twist.lean | **Depends on**: T506 | **Type**: lemma
- **Progress**: DONE 2026-06-10. New helpers `norm_pow_sub_one_lt_one`
  (‖ζ^c−1‖ < 1 for ALL c — orderOf-case-split to p^j, j ≥ 1 via
  Nat.dvd_prime_pow, transported through the subring inclusion by
  map_of_injective, then W2 `IsPrimitiveRoot.norm_sub_one_lt`) and
  `tendsto_pow_pow_sub_one` (fills the skeleton's inline `(by sorry)`
  convergence hole). Main proof exactly the decomposition route: the
  orthogonality identity proven as an equality of *continuous maps*
  `p^n • 1_{b+p^nZp} = Σ_c ζ^{cs} • κ_{ζ^c−1}` via `Continuous.ext_on` over
  dense ℕ (per-ℕ: terms collapse to `(ζ^{s+m})^c` and either all-ones
  (Finset.sum_const) or geometric-sum-zero via `geom_sum_mul` + domain);
  membership bridge ζ^{s+m} = 1 ↔ toZModPow n m = b via pow_eq_one_iff_dvd +
  ZMod.natCast_eq_zero_iff cast-arithmetic. Integration step: LinearMap.ext +
  map_smul/map_sum/smul_mul_assoc shuffles. `hn` unused by the proof
  (degenerate-true at n = 0) — kept in the statement (source-faithful),
  underscored. Verification: only the T508 sorry remains in the file; axioms =
  {propext, Classical.choice, Quot.sound}; linter-clean; lake build green.
  Blueprint: §3 deferred nodes now wired — `meas-mult-by-zx` →
  {MeasureR.cmul, mahlerTransform_charTwist}, `meas-restriction` gains
  `res_class_eq_sum_twists`, both with cleared-form prose notes.
- **Statement**: `res_class_eq_sum_twists` (L5.1.7, p^n-cleared, measure-side).
- **Proof sketch**: decomposition L5.1.7 (orthogonality pointwise + integrate;
  geometric-sum-zero from primitive root).
- **Mathlib lemmas**: `IsPrimitiveRoot`-geom-sum (verify
  `IsPrimitiveRoot.geom_sum_eq_zero`), §3 charFn/indicator API.
- **Sources**: TeX 1126–1131 (verbatim at L5.1.7) + R5-CLEAR note.
- **Blueprint**: the §3 Measures-chapter node for the restriction formula
  (`meas-restriction-formula`-label — worker locates) gets wired NOW (it was
  the §3 deferred ξ-node) with the cleared-form prose note.
- **Sizing**: ~70 LOC (source proof 8 lines, TeX 1117–1131).

### [T508] Mahler transform of the χ-twist (RJW Lem 5.4, cleared)
- **Status**: done | **File**: Twist.lean | **Depends on**: T507, T501 | **Type**: lemma
- **Progress**: DONE 2026-06-10, FIRST-PASS COMPILE. Route refinement (recorded):
  instead of the composition χ̃-decomposition → L5.1.7 → swap → Gauss(ii), proved
  the pointwise Gauss–Fourier expansion `G(χ⁻¹)•χ̃ = Σ_c χ⁻¹(c)•κ_{ζ^c−1}`
  directly as a continuous-map identity (same Continuous.ext_on-over-ℕ frame as
  T507 — the same algebra with the L5.1.7 steps merged at the pointwise level):
  at naturals the right side is `gaussSum χ⁻¹ (e.mulShift m)` (range↔ZMod-univ
  bridge by Finset.sum_nbij' val/natCast; `AddChar.zmodChar_apply'` gives the
  ζ^{cm}-form), evaluated by mathlib's `gaussSum_mulShift_of_isPrimitive` —
  which covers non-unit m with the vanishing built in — then `inv_inv`;
  χ⁻¹-primitivity via `DirichletCharacter.conductor_inv`. Integration assembly
  identical to T507. Statement exactly the planning-pinned form (no extra sign,
  range-sum). Twist.lean now SORRY-FREE. Verification: zero diagnostics
  project-wide on the file; axioms = {propext, Classical.choice, Quot.sound}
  (scan clean); lake build green. Blueprint: `interp-mahler-twist` wired with
  cleared-form prose note.
- **Statement**: `mahler_twist_formula` per L5.1.8 — statement form pinned by
  the planning trace (G(χ⁻¹)-cleared, NO extra sign; see L5.1.8 attack [2]).
- **Proof sketch**: decomposition L5.1.8 composition (χ̃-decomposition →
  L5.1.7 → swap → Gauss (ii) → (i)).
- **Sources**: TeX 1675–1692 (verbatim quote + the source's 3-display algebra).
- **Blueprint**: wire `interp-mahler-twist` (prose note: cleared form).
- **Sizing**: source proof 12 lines ⟹ ~110 LOC.

### [CLEANUP-51] /cleanup on Twist.lean (cadence: 3 tickets)
- **Status**: done | **Depends on**: T508 | **Type**: cleanup
- **Progress**: DONE 2026-06-10 (inline during T506–T508 + final sweep): zero
  diagnostics (all unused-section-var omits added, show→change, unused
  hypotheses underscored), all lines ≤ 100, naming conventions verified,
  docstrings on all public declarations, module docstring current. Golf note
  for CLEANUP-FINAL: the two Continuous.ext_on-over-ℕ frames (T507/T508
  hpoint) could share a `ContinuousMap.ext_natCast` helper if a third use
  appears.

### [T509] Moments of the twisted measure (F_{χ,a}-values)
- **Status**: done | **File**: Interpolation/TameConductor.lean (+GenBernoulli) | **Depends on**: CLEANUP-51, T504
- **Type**: theorem cluster
- **Statement**: `twistMuA_moments` per L5.1.10 (uniform formula via LvalNeg)
  + sub-leaves 10b (twisted F_a-expansion, cleared via 10c-product).
- **Proof sketch**: decomposition L5.1.10 (T033-pattern over L; generating
  function T504; parity wiring L5.1.11; planning-time value-trace at p=3
  recorded — re-derive k=2 as the ticket's acceptance regression).
- **Sources**: TeX 1694–1700, 1727–1730 (eq:special value theorem 1).
- **Blueprint**: wire `interp-dirichlet-integral` only if its node restates the
  VALUE identity — else leave + rationale (Mellin half §2-pending); worker
  reads the node and decides per rule 2, records.
- **Sizing**: the big one — source spans TeX 1694–1740 ⟹ ~200 LOC across 3
  declarations.
- **Progress** (2026-06-10, route analysis at execution start): the assembly
  needs the substitution `F ↦ F(C(1+r)·(1+X) − 1)` as a RING HOM on
  `(integerRing K)⟦X⟧` (the decomposition's PRIMARY eval₂ route for L5.1.6 —
  T506 took the coefficientwise fallback, which does not compose through the
  product-identities of the F_a algebra). Plan: (i) sub-step `substAffine`:
  mathlib `PowerSeries.eval₂`-style topological evaluation
  (Mathlib.RingTheory.PowerSeries.Evaluation — verify exact API: eval₂Hom /
  HasEval) at `a := C(1+r)·(1+X) − 1 ∈ R⟦X⟦` over the Pi-topology
  (WithPiTopology instances; R = integerRing K is complete + IsLinearTopology
  by TW1/Coefficients.lean; `a` is topologically nilpotent since r is —
  coefficientwise r-power bounds); (ii) upgrade: `mahlerTransform_charTwist'`:
  `𝓐(κ_r μ) = substAffine r (𝓐 μ)` — coefficientwise from the T506 tsum
  formula vs the eval₂-coefficient limit; (iii) per-c: apply substAffine to
  §4's cleared F_a-identity (`one_add_X_pow_sub_one_mul_Fa`, base-changed to
  K) to get the c-shifted cleared identities — NOTE: individual divisibility
  `(1+X)ζ^c−1 ∣ (1+X)^{p^n}−1` is parity-free (geom-factorisation), the
  Odd-M product formula (10c, `prod_primitiveRoot_mul_sub_one`) may be
  avoidable; (iv) Σ_c with χ⁻¹-weights + T508 identifies
  `G(χ⁻¹)·𝓐(twist χ̃ μ_a)`; (v) ∘(e^t−1) (formal, HasSubst ✓) + T504's
  `genBernoulliPowerSeries_mul` + §4 bridge `constantCoeff_iterate_delQ` +
  `apply_powCM` (MeasureR) extract the moment. Sub-steps (i)/(ii) are the next
  concrete edits (new section in Twist.lean or a new SubstAffine.lean file —
  prefer new file `PadicLFunctions/MeasureR/SubstAffine.lean`).
  UPDATE (same day): sub-steps (i)+(ii) DONE — placed in Twist.lean (new
  `section substAffine`, cohesion with the L5.1.6 material won over the new
  file): `hasEval_affine` (HasEval.map continuous_C + HasEval.X.mul_left over
  scoped PowerSeries.WithPiTopology; mop-IsLinearTopology instance derived via
  `IsCentralScalar.isLinearTopology_iff` — consider moving to Coefficients.lean
  at cleanup), `substAffine := PowerSeries.eval₂Hom continuous_C hasEval_affine
  : R⟦X⟧ →+* R⟦X⟧`, `coeff_substAffine` (hasSum_eval₂ mapped through the
  continuous coeff), `mahlerTransform_charTwist_eq_substAffine` (L5.1.6 in the
  source's ring-hom form: 𝓐(κ_r μ) = substAffine r (𝓐 μ)). All compile, build
  green, linter-clean. NEXT: step (iii) — base-change §4's
  `one_add_X_pow_sub_one_mul_Fa` to K and hit it with `substAffine (ζ^c−1)`
  (ring hom ⟹ identity transports); then (iv) Σ_c χ⁻¹(c)-weights + T508; then
  (v) ∘(exp−1) formal subst + T504 + `constantCoeff_iterate_delQ`-bridge over K
  + MeasureR `apply_powCM` to extract `twist_muA_moments`. Note for (v): the
  §4 bridge lemmas (map_del, derivativeFun_subst_exp, constantCoeff_iterate_*)
  are stated over ℚ_[p] in MuA.lean — the K-analogues need restating over K
  (same proofs; the field K plays ℚ_[p]'s role; `del K` exists in
  MeasureR/Toolbox).
  STEP (iii) DONE (2026-06-10): `substAffine_X`/`substAffine_C`/
  `substAffine_one_add_X` API in Twist.lean; per-c identity
  `charTwist_muA_mahler_identity` in TameConductor.lean:
  `(C(ζ^{ca})(1+X)^a − 1)·𝓐(κ_{ζ^c−1}(μ_a)_K) = substAffine (ζ^c−1)
  (map geomSum) − a` — proven by hitting the K-mapped §4 identity with the
  substAffine ring hom (simp only [map_*] + the C-power regroup). Build green.
  STEP (iv) ALSO DONE (same day): `substAffine_map_geomSum`
  (S_c(geomSum) = Σ_i C(ζ^{ci})(1+X)^i — NOTE: sequential rw, not simp; simp
  splits 1+X before the composite substAffine_one_add_X can fire) and
  `charTwist_muA_exp_identity` (‡c) in TameConductor.lean:
  `(C(ζ_K^{ca})·rescale a exp − 1)·H_c = Σ_{i<a} C(ζ_K^{ci})·rescale i exp − a`
  in K⟦t⟧, where H_c := (map subtype 𝓐(κ_c(μ_a)_K)).subst (exp K − 1).
  Proven by the §4 X_mul_subst_exp_Fa idiom: map-to-K (simp with
  PowerSeries.map_C + Subring.coe_subtype), then congrArg (substAlgHom hg) with
  the simp set [hX, hC := (substAlgHom hg).commutes, 1+(exp−1)=exp,
  exp_pow_eq_rescale_exp, coe_substAlgHom]; final `simpa only [map_pow]`
  aligns the C-pow normal forms (simp pulls pow out of C). hg over K via
  HasSubst.of_constantCoeff_zero'. Build green.
  STEP (v) SUB-DECOMPOSITION (recorded 2026-06-10, derived on paper —
  supersedes the sketchier refinement below; notation: ζ' := (ζ:K),
  E_j := rescale (j:K) (exp K), χ̄ := toFieldChar χ, H_c as in (‡c),
  G' := gaussSum (toFieldChar χ)⁻¹ (zmodChar _ (ζ'-pow-proof))):
  (v-a) `sum_inv_char_zeta_pow`: Σ_{c<p^n} χ̄⁻¹(c)·ζ'^{cj} = χ̄(j)·G' — the
    T508 Gauss-collapse re-derived K-valued (sum_nbij' range↔ZMod +
    zmodChar_apply' + gaussSum_mulShift_of_isPrimitive + inv_inv; primitivity
    of (ζ:K) via map_of_injective, of χ̄ via... toFieldChar preserves
    IsPrimitive — small lemma needed: conductor under ringHomComp with
    INJECTIVE hom is preserved [verify mathlib has conductor_ringHomComp or
    prove via FactorsThrough]).
  (v-b) division-algorithm reindex: Σ_{i<a}Σ_{j<p^n} f(i+a·j) =
    Σ_{m<a·p^n} f(m) (Finset.sum_nbij' (i,j)↦i+aj, m↦(m%a,m/a) on
    range a ×ˢ range p^n — or sum_sigma; needs a > 0 ✓ from hpa).
  (v-c) exp-block identities: E_x·E_y = E_{x+y}
    (mathlib `PowerSeries.exp_mul_exp_eq_exp_add` — verify name) and
    (E_b)^l = E_{lb} (exp_pow_eq_rescale_exp + rescale_rescale-induct).
  (v-d) T504-reindex at K, level p^n: X·Σ_{j<p^n}χ̄(j)E_j =
    genBPS_χ̄·(E_{p^n}−1), where genBPS := mk(B_{k,χ̄}/k!) — from
    genBernoulliPowerSeries_mul (T504) by the b+1↔j boundary-shift (χ̄(0) =
    χ̄(p^n-as-0) = 0; THIRD occurrence of the T503 bijection — consider
    factoring a `Finset.sum_range_succ_shift`-style reusable bridge).
  (v-e) MASTER ASSEMBLY: multiply (‡c) by Σ_{j<p^n}(C(ζ'^{ca})E_a)^j, sum
    against χ̄⁻¹(c) over c<p^n (c=0 drops via χ̄⁻¹(0)=0): LHS telescopes to
    (E_{ap^n}−1)·Σ_cχ̄⁻¹(c)H_c [geom_sum_mul]; RHS double-sum reindexes by
    (v-b) then collapses by (v-a) to G'·[Σ_{m<ap^n}χ̄(m)E_m − a·χ̄(a)·rescale
    a (Σ_{j<p^n}χ̄(j)E_j)]; block-split (v-c) + (v-d) + geom-telescope give
    RHS = G'·(E_{ap^n}−1)·[genBPS − χ̄(a)·rescale a genBPS]·X⁻¹-shape; after
    multiplying through by X and cancelling (E_{ap^n}−1) ≠ 0 (coeff-1 check,
    §4 hreg-pattern; K⟦t⟧ domain):
    **X·Σ_cχ̄⁻¹(c)H_c = G'·(genBPS_χ̄ − χ̄(a)·rescale (a:K) genBPS_χ̄)** —
    the exact χ-analogue of §4's X_mul_subst_exp_Fa. Then T508
    (map+subst-transported: Σ_cχ̄⁻¹(c)H_c = (G_R:K)·H_χ with (G_R:K) = G' via
    subtype-of-finite-sum) + G' ≠ 0 (T502 norm_gaussSum_eq_one) cancel to
    **X·H_χ = genBPS_χ̄ − χ̄(a)·rescale a genBPS_χ̄** (FINAL-10b).
  (v-f) moment extraction = §4 muA_apply_powCM tail over K: need K-analogues
    of MuA's bridge cluster (delQ-K := (1+X)·derivativeFun over K [MeasureR
    `del K` is the integerRing-level one], map_del-K [subtype-map commutes
    with del], derivativeFun_subst_exp-K, constantCoeff_subst_exp-K,
    constantCoeff_iterate_delQ-K — copy MuA.lean proofs verbatim with K for
    ℚ_[p]) + MeasureR.apply_powCM; coeff_{k+1} of FINAL-10b: LHS
    coeff_succ_X_mul → coeff_k H_χ → k!⁻¹-cleared moment of twist χ̃ μ_aK;
    RHS via coeff of genBPS (coeff_mk) = B_{k+1,χ̄}/(k+1)! and coeff_rescale:
    (1 − χ̄(a)a^{k+1})·B_{k+1}/(k+1)! ; factorial bookkeeping + LvalNeg
    definition give twist_muA_moments. (The −1-sign: LvalNeg = −B/(k+1);
    statement RHS −(1−χ(a)a^{k+1})·LvalNeg = +(1−χ(a)a^{k+1})·B_{k+1}/(k+1) ✓
    consistent with the §4 sign-trace.)
  (v-a)+(v-b)+(v-c) DONE (2026-06-10, all in TameConductor.lean, build green,
  committed): `sum_inv_char_zeta_pow` (K-valued Gauss collapse; primitivity
  transport `DirichletCharacter.isPrimitive_ringHomComp_iff` +
  `factorsThrough_ringHomComp_iff` added to Characters.lean — PR candidates);
  `sum_range_mul_eq_sum_range` (division-algorithm reindex via sum_nbij' on
  range a ×ˢ range N); `rescale_exp_pow` ((E_b)^l = E_{lb} by induction +
  exp_mul_exp_eq_exp_add). (v-d) ALSO DONE (same day, committed):
  `X_mul_sum_char_rescale_exp` (X·Σ_{j<p^n} C(χK(j))·E_j =
  genBPS_χK·(E_{p^n}−1); sum_range_succ'-shift, both boundaries killed by
  χK(0) = 0; note `set ... with hh` needs `simp only [hh]` not `rw [hh]` at
  use sites — beta-reduction). All v-a/b/c/d helpers in TameConductor.lean
  before twist_muA_moments, linter-clean, all committed/pushed.
  NEXT — (v-e) MASTER ASSEMBLY, steps pinned (in K⟦t⟧; E_j := rescale (j:K)
  (exp K); H_c as in charTwist_muA_exp_identity; G' the K-valued Gauss sum of
  (v-a); χ̄ := toFieldChar χ):
  STEP 1 (per-c): multiply (‡c) by Σ_{j<p^n}(C(ζ'^{ca})·E_a)^j; telescope LHS
  cofactor with geom_sum_mul + rescale_exp_pow + exp-power-juggling to get
  `(E_{ap^n} − 1)·H_c = (Σ_{i<a} C(ζ'^{ci})E_i − a)·Σ_{j<p^n}
  C(ζ'^{caj})·E_{aj}`.
  STEP 2: Σ_c χ̄⁻¹(c)-weighted sum; expand the (i,j)-product
  (ζ'^{c(i+aj)}·E_{i+aj} via exp_mul_exp_eq_exp_add); reindex
  sum_range_mul_eq_sum_range to m < a·p^n; swap Σ_c in and collapse with
  sum_inv_char_zeta_pow (at m, and at a·j for the a-term; χ̄(aj) =
  χ̄(a)·χ̄(j)): `(E_{ap^n} − 1)·Σ_c χ̄⁻¹(c)•H_c = G'·(Σ_{m<ap^n}
  C(χ̄(m))·E_m − C(χ̄(a))·a·Σ_{j<p^n} C(χ̄(j))·E_{aj})`.
  STEP 3: multiply by X; m-sum block-splits by m = m'+p^n·l (reindex again,
  roles swapped; χ̄ p^n-periodic; E-product) → X·Σ_m =
  (Σ_{l<a}(E_{p^n})^l)·genBPS·(E_{p^n}−1) = genBPS·(E_{ap^n}−1) [telescope];
  a-term via rescale (a:K) applied to (v-d): rescale a X = C a·X absorbs the
  stray a — VERIFY bookkeeping at write-time (planning trace pinned no stray
  a-factor in FINAL).
  STEP 4: cancel (E_{ap^n}−1) ≠ 0 (coeff 1 = a ≠ 0, K char-0; §4
  hreg-pattern; domain): **FINAL-10b: X·Σ_{c<p^n}χ̄⁻¹(c)•H_c =
  G'·(genBPS_χ̄ − C(χ̄(a))·rescale (a:K) genBPS_χ̄)**.
  (v-e) COMPLETE (2026-06-10, all four steps committed/pushed):
  `charTwist_muA_exp_identity_cleared` (step 1),
  `sum_char_inv_mul_exp_identity` (step 2),
  `X_mul_sum_char_inv_subst` = **FINAL-10b** (steps 3+4; hA block-split via
  the reindex with roles swapped + ZMod-period + exp-products + telescope;
  hB via the rescale-a-image of (v-d) with an inline rescale-of-C ext-lemma;
  endgame `linear_combination C(G')·hA − C(G')·hB`; the regular-factor
  cancellation via coeff-1 ≠ 0, simp leaves the disjunction a = 0 ∨ p-zero
  — rcases). LEAN NOTES for the file: fragile underscore-calcs DON'T (the
  `_`s elaborate against the wrong metas — write rw-show-chains or
  linear_combination instead).
  Then (v-f) extraction — the LAST sub-step of T509: T508 map+subst-transport
  (Σ_cχ̄⁻¹(c)·H_c = C((G_R:K))·H_χ where H_χ := (map subtype 𝓐(twist χ̃
  (μ_a)_K)).subst (exp−1); from T508 hit with map-subtype, substAlgHom at
  exp−1, and the C-image bookkeeping — note T508's statement is in
  •-smul form: (G_R • twist χ̃ μ) — map_smul through 𝓐/map/subst gives the
  C-multiple), G'-vs-(G_R:K) bridge (subtype-hom of the finite gaussSum =
  the K-valued gaussSum of toFieldChar against the K-valued zmodChar —
  small lemma, map_sum), G'-cancel (≠ 0: T502 `norm_gaussSum_eq_one` gives
  the K-valued norm 1 — check it applies to gaussSum (toFieldChar χ)⁻¹
  directly or transport), coeff_{k+1} of FINAL-10b (coeff_succ_X_mul on the
  left; coeff_mk + coeff_rescale on the right), K-bridge delQ-cluster
  restated from MuA.lean over K (hasSubst_exp_sub_one-K [done inline in ‡c
  as hg], derivativeFun_subst_exp-K, constantCoeff_subst_exp-K,
  constantCoeff_iterate_delQ-K — copy proofs with ℚ_[p] → K), MeasureR
  `apply_powCM` + `mahlerTransform_baseChange` to land twist_muA_moments.
  **T509 DONE (2026-06-10)**: `twist_muA_moments` PROVEN — the full chain
  (iii)→(iv)→(v-a..e)→(v-f) landed: per-c substAffine-transport, exp-subst,
  telescoped clearing, FINAL-10b, T508-transport, Gauss-nonvanishing (NOTE
  `mul_gaussSum_inv_eq_gaussSum` is Field-source-only, unusable at ZMod p^n;
  `AddChar.inv_mulShift` + `gaussSum_mulShift_of_isPrimitive` is the route),
  delField-bridge extraction, factorial endgame. STATEMENT REPLAN (in
  docstring): `(hζ : IsPrimitiveRoot ζ (p^n))` threaded into the statement —
  the source's ambient ε_{p^n}; T510's statements must thread it too.
  Verification: lake build green; axioms = {propext, Classical.choice,
  Quot.sound} on twist_muA_moments + all v-helpers (a first lean_verify
  returned sorryAx from a STALE LSP elaboration — re-verified clean after the
  build settled). Only T510's two skeleton sorries remain in
  TameConductor.lean.
  OLD-NEXT (superseded): (v-a) + the toFieldChar-IsPrimitive lemma in
  TameConductor.lean (or Characters.lean for the primitivity transport).
  NEXT after: step (v) per the plan above — the formal subst (exp K − 1)
  of (†c) [needs the K-analogue of §4's hasSubst_exp_sub_one + map-to-K of the
  identity], then the master identity.
  ROUTE REFINEMENT for (iii)–(v) (recorded before compaction): PARITY-FREE,
  the 10c Odd-product is NOT needed. Chain: (iii) base-change §4's
  characterising identity to K and hit with the ring hom `substAffine (ζ^c−1)`:
  since substAffine r (1+X) = C(1+r)·(1+X), this gives per-c
  `(C(ζ^{ca})(1+X)^a − 1)·𝓐(κ_c μ_K) = substAffine (geomSumK) − a` (†c);
  (iv) map to K⟦X⟧ and apply formal `subst (exp K − 1)` (ring hom; §4
  coe_substAlgHom pattern): `(ζ^{ca}·rescale a exp − 1)·H_c =
  Σ_{i<a} ζ^{ci}·rescale i exp − a` (‡c) with H_c := (map K 𝓐(κ_cμ))∘(e^t−1);
  (v) MASTER IDENTITY (all formal in K⟦t⟧, domain): multiply Σ_c χ⁻¹(c)•(‡c)
  through by the two geometric cofactors — KEY FACTS: χ⁻¹(0) = 0 drops the
  c = 0 term so every remaining denominator has unit constant term in the
  FIELD K; the geometric identities `(ζ^c e^t − 1)·Σ_{j<p^n}(ζ^c e^t)^j =
  e^{p^n t} − 1` (and the a-version) are formal and parity-free; the inner
  sums `Σ_c χ⁻¹(c)ζ^{cj} = χ(j)·G(χ⁻¹)` collapse by the SAME
  `gaussSum_mulShift_of_isPrimitive` + sum_nbij' bridge as T508 (factor that
  bridge out as a reusable lemma `sum_inv_char_pow_eq_gaussSum`-style when
  writing!); then T504's `genBernoulliPowerSeries_mul` at modulus p^n
  identifies the χ(j)e^{jt}-sums with the genBernoulli series at the two
  rescalings (j-shift b+1 as in T504's statement), and cancellation of the
  nonzero e-factors (domain K⟦t⟧, §4 hreg-pattern) yields
  `X·Σ_c χ⁻¹(c)•H_c = G(χ⁻¹)·(genBPS_χ − χ(a)·a·rescale a genBPS_χ)`-shape
  [VERIFY exact Euler-shape against the source display TeX 1697 + the
  planning trace at L5.1.10 attack [1] before stating]. Then
  `coeff_{k+1}` of both sides + the K-bridge (constantCoeff_iterate_delQ
  over K + MeasureR apply_powCM + T508 at powCM k) extracts
  `G(χ⁻¹)·∫χ̃x^k dμ_aK = G(χ⁻¹)·(−(1−χ(a)a^{k+1}))·LvalNeg`, and G(χ⁻¹) ≠ 0
  (norm 1 by T502's `norm_gaussSum_eq_one`... NOTE that's for the K-valued
  gaussSum — the integerRing-valued one: nonzero via norm = 1 through the
  subtype) cancels in the field K.

### [T510] **MILESTONE: RJW Theorem 5.1** — ∫χ(x)x^k·ζ_p = L(χ,1−k)
- **Status**: done | **File**: TameConductor.lean | **Depends on**: CLEANUP-ALL-3
- **Type**: theorem
- **Statement**: witness-quantified form mirroring `kubotaLeopoldt`'s encoding
  (TW6 skeleton): for χ primitive mod p^n (n ≥ 1), p ≠ 2, k > 0, the
  θ_a-form `∫χ̃x^k d(θ_a)_R = −(1−χ(a)a^k)·LvalNeg χ (k−1)` and the
  ζ_p-pairing corollary (decomposition L5.1.12).
- **Proof sketch**: L5.1.12 composition (units-restriction + L5.1.10 + x⁻¹
  shift T036-pattern + baseChange naturality).
- **Sources**: TeX 1619–1622 (headline, verbatim at R5.1) + proof 1751–1765.
- **Blueprint**: wire `interpolation-property` (the chapter's Thm 5.1 node) →
  the new theorem; re-render site.
- **Sizing**: source proof 14 lines ⟹ ~120 LOC.
- **Progress**: **DONE 2026-06-10 — MILESTONE: TameConductor.lean SORRY-FREE.**
  Both forms proven: `tame_conductor_theta` (θ_a-form, ∫χ̃x^k d(θ_a)_R =
  −(1−χ(a)·a^{k+1})·LvalNeg χ k via Θ-functional composition over
  twist_muA_moments) and `tame_conductor` (witness form: ∃ μ_w with
  res-units + ψ-shift properties pairing to the L-value, mirroring
  kubotaLeopoldt's encoding). Route: (1) `iota_dirac_mul` — the units-Dirac
  convolution passes through ι = σ_w dilation; (2) baseChange naturality
  pack `baseChange_pushforward` / `baseChange_cmul` / `baseChange_res`
  (BaseChange.lean; proved by ext_locallyConstant + fibre-indicator
  decomposition `locallyConstant_eq_sum_smul_charFn` via
  `Φ.isLocallyConstant.isClopen_fiber` + `LocallyConstant.range_finite`);
  (3) dilation eigenfunction `char_pow_comp_mulCM` (χ̃x^k ∘ mulCM c =
  χ̃(c)c^k • χ̃x^k); (4) nonvanishing c_u = χ(u)·u^{k+1} ≠ 1 for the chosen
  unit u via FINITE CHARACTER ORDER: χ(m̄)^N = 1 by `pow_card_eq_one'`, so
  c_u^N = m^{(k+1)N} would force topGen^{(k+1)N} = 1 in ℤ_pˣ, contradicting
  `topGen_pow_ne_one` — avoids needing 1+pℤ_p torsion-freeness. STATEMENT
  REPLAN (carried from T509, recorded in docstrings): the ambient primitive
  p^n-th root hypothesis `(hζ : IsPrimitiveRoot ζ (p^n))` threaded through
  twist_muA_moments → tame_conductor_theta → tame_conductor (source's
  ε_{p^n}, TeX ~1640). LEAN NOTES: MeasureR `pushforward` takes explicit
  K X Y; iota_dirac_mul's final rw chain closes by congr-unification —
  end with `rfl`; a first lean_verify returned sorryAx from a stale LSP
  elaboration (second occurrence this file) — grep shows 0 sorries,
  re-verify after build settle → clean. Verification: lake build green
  (3833 jobs incl. blueprint); zero sorry in TameConductor.lean; axioms on
  `tame_conductor` + `tame_conductor_theta` = {propext, Classical.choice,
  Quot.sound}. Blueprint: `interpolation-property` wired →
  tame_conductor + tame_conductor_theta + twist_muA_moments with prose
  note (witness encoding, θ-form engine, LvalNeg value encoding, ambient
  root hypothesis); `lake build PadicLFunctionsBlueprint` green.

### [CLEANUP-ALL-3] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T509 | **Type**: cleanup-all (before T510)
- **Progress**: DONE 2026-06-10, full-project sweep (~140 linter warnings →
  0 non-sorry warnings): scripted positional fixes for 64 show→change, 30
  unused simp args, ~40 unused-section-var omits (looped to fixpoint; NOTE
  the warning columns are 0-indexed, omit-lists need bracket-aware parsing
  for `ℚ_[p]`, and `omit ... in`/`open ... in` must precede docstrings);
  flexible-simp `simp [Nat.factorial] at h1` in the two hreg-proofs
  restructured to `simpa ... using` + explicit Nat-contradiction;
  `open scoped Classical` in Characters.lean narrowed to `open Classical in`
  on toContinuousMapZp + `classical` tactic in the locally-constant proof;
  no-op push_casts removed; deprecated `AddSubmonoidClass.coe_finset_sum` →
  `coe_finsetSum`; all 28 over-100-col lines repacked (some had grown from
  show→change). Verification: lake build green (code + blueprint), zero
  non-sorry warnings project-wide, all lines ≤ 100; axiom spot-checks
  unchanged on twist_muA_moments and PadicMeasure.kubotaLeopoldt.

### [T511] F_η and μ_η (conductor D coprime to p)
- **Status**: done | **File**: Interpolation/NonTame.lean (TW6 skeleton) | **Depends on**: TW6, T501
- **Type**: def + lemmas
- **Statement**: `etaDenomUnit` (L5.2.1), `muEta` + transform characterisation
  (L5.2.2; G(η⁻¹)-unit via T501's norm lemma).
- **Sources**: TeX 1793–1798 (verbatim at L5.2.2).
- **Blueprint**: wire `interp-mu-eta`.
- **Sizing**: ~70 LOC.
- **Progress**: DONE 2026-06-10. Four declarations: (1) NEW
  `integerRing.isUnit_of_norm_eq_one` (Coefficients.lean — norm-1 element of
  the unit ball is a unit; field inverse has norm 1; NOTE mathlib renamed
  `isUnit_of_mul_eq_one` → `IsUnit.of_mul_eq_one` with {a} implicit, (b)
  explicit, and an [IsDedekindFiniteMonoid] instance arg); (2)
  `isUnit_root_mul_one_add_X_sub_one` = L5.2.1/etaDenomUnit via
  `PowerSeries.isUnit_iff_constantCoeff` + W3
  (`IsPrimitiveRoot.norm_pow_sub_one_eq_one`, needs (p := p) named since p is
  implicit there) + prim-root coe-transport `map_of_injective (f :=
  (integerRing K).subtype)`; (3) `gaussSum_isUnit_of_coprime` (the L5.2.2
  sub-leaf) via GENERALISED `coe_gaussSum_zmodChar` (TameConductor.lean:
  p^n → arbitrary [NeZero N], proof verbatim modulus-agnostic, call sites
  unchanged) + `norm_gaussSum_eq_one K` (L explicit section var!) +
  conductor_inv/isPrimitive_ringHomComp_iff primitivity transport; (4)
  `mahlerTransform_muEtaCleared` @[simp] characterisation 𝓐(muEtaCleared) =
  −Σ_c η⁻¹(c)·(ζ^c(1+X)−1)⁻¹ via `(mahlerRingEquiv p K).apply_symm_apply`
  (muEtaCleared def itself was sorry-free in the TW6 skeleton). Cleanup
  inline: omits added (also retro-fixed 3 unused-section-var warnings in
  BaseChange.lean from T510's additions), show-from wrapper golfed to direct
  rw, have-then-simpa collapsed. Verification: lake build green project-wide;
  axioms = {propext, Classical.choice, Quot.sound} on all four (one stale-LSP
  empty-axioms artifact, clean on re-verify). Blueprint: `interp-mu-eta`
  wired → all four decls with prose note (cleared-form encoding
  −G(η⁻¹)F_η, full ℤ/D sum with η⁻¹-vanishing off units); blueprint build
  green (3833 jobs).

### [T512] Moments of μ_η (Lem 5.9, p-adic half)
- **Status**: done | **File**: NonTame.lean | **Depends on**: T511, T504 | **Type**: lemma
- **Statement**: `muEta_moments` (L5.2.3): ∫x^k μ_η = LvalNeg η k.
- **Sources**: TeX 1801–1807 (verbatim at L5.2.3).
- **Blueprint**: wire `interp-eta-mellin`'s value half per node text (worker
  reads node; Mellin-statement half stays prose with rationale if present).
- **Sizing**: ~90 LOC (rides T504/T509 machinery at modulus D).
- **Progress**: DONE 2026-06-10, `muEtaCleared_moments` (cleared form:
  ∫x^k·(−G(η⁻¹)μ_η) = G(η⁻¹)·LvalNeg(ηK)(k)) via a 3-step chain mirroring
  T509 but with NO clearing factor: (1) `muEta_term_exp_identity` — T511's
  unit identity through map-subtype + substAlgHom(exp−1) (LEAN NOTE: keep
  `map_pow` OUT of the first simp set or the C-of-pow splits into (C ↑ζ)^c
  and the second simp can't push substAlgHom through — use
  `SubmonoidClass.coe_pow` to normalise ↑(ζ^c) = (↑ζ)^c instead); (2)
  `rescale_exp_sub_one_mul_muEta_term` — geom_sum_mul clearing of e^{Dt}−1,
  ζ^{cD} = 1, exp_pow_eq_rescale_exp; (3) `X_mul_muEtaCleared_subst` MASTER:
  X·H_η = −C(G')·genBPS(ηK), via η̄(0) = 0 drop (Fact (1<D) nontrivial), the
  GENERALISED `sum_inv_char_zeta_pow` Gauss collapse + GENERALISED
  `X_mul_sum_char_rescale_exp` (both TameConductor: p^n → arbitrary
  [NeZero N] modulus, X_mul… takes hN1 : 1 < N now — call sites pass
  Nat.one_lt_pow), regular-factor cancellation (coeff-1 = D ≠ 0, CharZero).
  Final: T509-endgame coeff_{k+1} extraction (apply_powCM + NEW FACTORED
  `map_subtype_del_iterate` [also refactored into twist_muA_moments,
  −10 LOC] + constantCoeff_iterate_delField), factorial algebra (LEAN NOTE:
  after `field_simp [hfact]` the goal is already in (k+1)-normal form —
  `rw [hfact]; push_cast; ring` closes; an intermediate push_cast is a
  no-op). Verification: lake build green (code + blueprint); axioms =
  {propext, Classical.choice, Quot.sound} on all four new decls (one
  stale-LSP sorryAx artifact on moments, clean on re-verify — third
  occurrence of this artifact, always re-verify). Blueprint:
  `interp-eta-mellin` wired → muEtaCleared_moments + X_mul_muEtaCleared_subst
  with prose note (cleared encoding, p-adic route via
  genBernoulliPowerSeries_mul, complex Mellin half quarantined unfomalised).

### [T513] ψ-invariance: ψ(μ_η) = η(p)·μ_η (Lem 5.10)
- **Status**: done | **File**: NonTame.lean | **Depends on**: T511 | **Type**: lemma
- **Statement**: `psi_muEta` (L5.2.4).
- **Proof sketch**: the **recorded ξ-free replan** (decomposition L5.2.4:
  γ-telescope + projection formula + (ℤ/D)ˣ reindex; end-to-end trace at
  p=3, D=4 recorded — statement verbatim TeX 1812–1813, route deviation
  recorded mirroring R3/T034).
- **Mathlib lemmas**: project `psi_phi_mul` (widened, TW4/TW5), §4 Dirac-ψ
  lemmas (widened), `ZMod.unitOfCoprime`-reindex machinery.
- **Sources**: TeX 1812–1827.
- **Blueprint**: wire the chapter's ψ-invariance node (locate label; prose
  note: proof via the cleared trace identity).
- **Sizing**: source proof 10 lines ⟹ ~110 LOC.
- **Progress**: DONE 2026-06-11, `psi_muEtaCleared` exactly by the ξ-free
  route. NEW W-grade API (Tier-A spawns, proven inline): Toolbox.lean gains
  `psi_phi_mul` (PROJECTION FORMULA ψ(φν·μ) = ν·ψμ — proof on test functions
  through mul_apply/convInner; pointwise case split on y ∈ pℤ_p with
  sd(px+y) = x+sd(y) via mul_shiftDiv_of_mem/shiftDiv_mul; NOTE no
  IsUltrametricDist.norm_sub_le_max in mathlib — use norm_add_le_max with
  −(px) + norm_neg), ψ-linearity pack (psi_add/smul/zero/sum — LinearMap.ext
  one-liners), `psi_dirac_of_isUnit` (via isSupportedOn_units_iff, which sits
  LATER in the file — order matters), `psi_dirac_zero`;
  MahlerTransform.lean gains `mahlerTransform_smul`/`mahlerTransform_sub`
  (via mahlerTransformₗ map_smul/map_sub). NonTame: `symm_denom_eq`
  (w(1+T)−1 read back = w•δ₁ − δ₀; binomialSeries_nat at d = 1),
  `psi_symm_inverse_denom` (ψ(γ_m) = γ_{pm}: telescope via geom_sum_mul +
  Ring.mul_inverse_cancel transform-side, ψ(Σ_j ζ^{mj}δ_j) = δ₀ via
  Finset.sum_eq_single + PadicInt.isUnit_iff/Padic.norm_natCast_eq_one_iff,
  unit-cancel IsUnit.mul_left_cancel), then the ZMod-indexed assembly
  (range↔ZMod nbij', ψ-shift x ↦ p̂x, unit-reindex). STATEMENT NOTE: hη
  (primitivity) DROPPED — the proof never uses it (linter caught it;
  generalisation recorded). LEAN NOTES: (1) `set g := fun x => ...` lambdas
  do NOT beta-reduce under rw — bridge every g-application with
  `show g a = <body> from rfl`; (2) keep `map_pow` OUT of rw-lists touching
  C(ζ^k)·(map f ((1+X)^k)) — it splits the C-of-pow first; use targeted
  `show map f ((1+X)^k) = (1+X)^k from by rw [map_pow, map_add, ...]`;
  (3) `rw [← hpu]` with hpu : ↑hu.unit = p̂ is MOTIVE-ILLEGAL (hu's type
  mentions p̂) — `obtain ⟨u, hpu⟩ := hu` first; (4) RingEquiv.symm has no
  map_smul — bridge to (mahlerLinearEquiv p K).symm via `show ... from
  map_smul ...` (defeq). Verification: lake build green (code + blueprint);
  axioms = {propext, Classical.choice, Quot.sound} on psi_muEtaCleared,
  psi_symm_inverse_denom, psi_phi_mul (one stale-LSP sorryAx artifact,
  clean on re-verify — 4th occurrence). Blueprint: `interp-psi-twisted`
  wired → psi_muEtaCleared + psi_phi_mul + psi_symm_inverse_denom with
  prose note (μ_p-free cleared-telescope route vs the node's displayed
  trace computation; η not required primitive).

### [CLEANUP-52] /cleanup on NonTame.lean (cadence: 3 tickets on file)
- **Status**: done | **Depends on**: T513 | **Type**: cleanup
- **Progress**: DONE 2026-06-11. Audit: copyright/docstring/imports ✓, no
  dividers, no set_option, 0 linter warnings (code written post-ALL-3
  discipline, omits + line-packing already in place per-ticket), all
  public decls docstringed with TeX citations, naming ✓. STRUCTURE:
  psi_muEtaCleared (~115 ln) and X_mul_muEtaCleared_subst (~110 ln) exceed
  the 50-line bar but are already decomposed into maximal named
  have-blocks; further extraction would create single-use 8-arg private
  lemmas — n/a per the TameConductor/ALL-3 precedent. Chain-step lemmas
  kept public (reusable at modulus Dp^n in T515). Golf applied:
  muEta_term_exp_identity tail simp-at/exact → simpa-using. Build green,
  3 sorries remain (= T514–T516 scope).

### [T514] Restriction to units: (1−η(p)p^k)-moments (Lem 5.11)
- **Status**: done | **File**: NonTame.lean | **Depends on**: CLEANUP-52, T512 | **Type**: lemma
- **Statement**: `res_units_muEta_moments` (L5.2.5).
- **Sources**: TeX 1831–1843 (verbatim at L5.2.5; T035-pattern).
- **Sizing**: ~50 LOC.
- **Progress**: DONE 2026-06-11, `res_units_muEtaCleared_moments` exactly
  the T035 pattern widened: NEW `MeasureR.phi_apply_powCM` (Toolbox —
  ∫x^k d(φμ) = algebraMap(p^k)·∫x^k dμ; the function identity
  (powCM k)∘(mulCM p) = algebraMap(p^k)•powCM k by ext + simp [mulCM,
  mul_pow]; NOTE the Algebra ℤ_[p] (integerRing K) instance derives from
  NormedAlgebra ℚ_[p] K, so that can't be omitted), then res_units_eq +
  T513's psi_muEtaCleared + φ-linearity + coe-bookkeeping
  (algebraMap-composite `change` per the Coefficients defeq +
  push_cast/rfl; the smul-coe show needs push_cast [smul_eq_mul]) +
  T512's muEtaCleared_moments + ring. Verification: lake build green;
  axioms = {propext, Classical.choice, Quot.sound} (stale-LSP artifact
  once more, clean on re-verify). Blueprint: `interp-eta-restriction`
  wired → res_units_muEtaCleared_moments with cleared-form prose note;
  blueprint build green.

### [T515] μ_θ, its moments and restriction; ζ_η and its interpolation
- **Status**: done | **File**: NonTame.lean | **Depends on**: T514, T508 | **Type**: cluster
- **Statement**: `muTheta` (:= twist χ̃ μ_η) + Lem 5.12 cleared transform +
  moments + Res-formula (L5.2.6 — ROUTE per the corrected attack: ψ-of-twist
  via support for n ≥ 1, L5.2.4 for n = 0); `zetaEta` + final display
  (L5.2.7).
- **Sources**: TeX 1845–1875 (verbatim quotes at L5.2.6/7).
- **Blueprint**: wire `interp-nontame`-adjacent definition nodes (μ_θ/ζ_η).
- **Sizing**: ~160 LOC.
- **Progress**: DONE 2026-06-11 (~480 LOC, the largest single-ticket chain
  since T509). `zetaEta_twisted_moments` = L5.2.7's final display proven
  with a route improvement over the planned n-split: the Euler factor
  arises UNIFORMLY from Res = 1−φψ + the φ-twist function identity
  ((χ̃·x^m)∘mulCM p = (χ(p̄)·alg(p^m))•(χ̃·x^m)) — for n ≥ 1 it degenerates
  via χ(p̄) = 0; NO support-vs-telescope case split needed (the planned
  L5.2.6 ψ-route became unnecessary). Chain: (1)
  `isUnit_root_mul_pow_one_add_X_sub_one` — product-root denominators
  ζ_D^c·w (‖w−1‖<1) are units by ultrametric dominance (le_antisymm with
  norm_add_le_max twice); NEW Coefficients helper
  `integerRing.not_isUnit_of_norm_lt_one`; (2) `map_ring_inverse_of_isUnit`
  (ring homs commute with Ring.inverse at units — mathlib gap, PR
  candidate); (3) `mahlerTransform_charTwist_muEtaCleared` — the ε^b-line
  twists via mahlerTransform_charTwist_eq_substAffine; c = 0 line is 0 on
  BOTH sides (Ring.inverse of X resp. of a norm-small denominator); (4)
  REFACTOR: T512's step lemmas abstracted to `unit_denom_exp_identity` +
  `rescale_exp_sub_one_mul_unit_denom` (abstract unit-denominator + M-torsion
  w), old names kept as instances; subst-distributors `subst_map_C_mul`/
  `subst_map_sum`/`subst_map_neg` factored; (5) `toFieldChar_prod_natCast`
  (θ(j) = η(j)χ(j) pointwise at naturals; non-units via
  Nat.coprime_mul_iff_right split; units via changeLevel_eq_cast_of_dvd +
  ZMod.cast_natCast); (6) `X_mul_twist_muEtaCleared_subst` MASTER:
  G(χ̄)-smearing (mahler_twist_formula, its unused `_hn : 1 ≤ n` REMOVED so
  n = 0 works uniformly; ditto sum_char_inv_H_eq's hn), per-(c,b) clearing
  at modulus D·p^n, DOUBLE Gauss collapse (sum_inv_char_zeta_pow at D and
  at p^n), T504 at D·p^n, cancel (rescale (Dp^n) exp − 1) AND C(G(χ̄))
  (nonvanishing via NEW factored `gaussSum_inv_ne_zero` in TameConductor,
  also refactored into twist_muA_moments −13 LOC); (7)
  `twist_muEtaCleared_moments` (T512-endgame verbatim); (8) final assembly.
  STATEMENT REPLAN: `(hε : IsPrimitiveRoot ε (p^n))` threaded into
  twist_muEtaCleared_moments + zetaEta_twisted_moments (the source's ambient
  ε_{p^n}, as in twist_muA_moments). LEAN NOTES: push_cast at a hypothesis
  normalises ↑(D·p^n) to ↑D·↑p^n breaking rescale-matching — use targeted
  `simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]`; double-pow_mul
  rws need explicit args (`pow_mul ζ D (c·p^n)`) or the second fires on the
  same term; triple-sum Fubini = per-level sum_congr + Finset.sum_comm with
  fully-spelled shows. Verification: lake build green (code + blueprint);
  axioms = {propext, Classical.choice, Quot.sound} on the master, moments,
  and zetaEta_twisted_moments (stale-LSP artifact once, clean re-verify).
  Blueprint: `interp-mahler-theta` wired → charTwist transform + master +
  moments (prose note: two-index CRT-resolved form, G(χ̄) cancels,
  single-root closed form not restated); `interp-zeta-eta` wired →
  zetaEta_twisted_moments (prose note: x⁻¹ as index shift, uniform Euler
  factor, ambient root). Only T516's determinacy sorry remains in the file.

### [T516] **MILESTONE: RJW Theorem 5.7** — ∃! ζ_η
- **Status**: done | **File**: NonTame.lean | **Depends on**: CLEANUP-ALL-4
- **Type**: theorem
- **Statement**: existence (T515) + uniqueness via determinacy (L5.2.8's
  recorded design: χ-quantifier through 𝓞_ℂp-baseChange; statement form
  fixed in TW6 skeleton per decomposition).
- **Sources**: TeX 1773–1776 (verbatim at R5.2 head).
- **Blueprint**: wire `interp-nontame`; re-render.
- **Sizing**: determinacy ~120 LOC + assembly ~60.
- **Progress**: **DONE 2026-06-11 — MILESTONE: NonTame.lean SORRY-FREE,
  RJW Theorem 5.7 complete** (existence = T515's zetaEta_twisted_moments;
  uniqueness = `eq_of_twisted_moments_eq` via the determinacy
  `eq_zero_of_twisted_moments_eq_zero`, both proven this ticket). The
  skeleton's hroots-quantifier design (NOT the 𝓞_ℂp-baseChange
  alternative) was the pinned form ✓. Determinacy route (≈260 LOC + three
  infrastructure pieces): (1) NEW
  `LocallyConstant.exists_eq_comp_toZModPow` (Measure/Basic.lean —
  uniform local constancy on compact ℤ_p: per-point toZModPow-fibre
  neighbourhoods + elim_nhds_subcover + ultrametric two-ball merge; PR
  candidate); (2) NEW `PadicInt.exists_primitiveRoot_card_sub_one`
  (Branches.lean — Teichmüller lift of a generator of (ZMod p)ˣ is a
  primitive (p−1)-th root: section-property toZMod_teichmullerZMod forces
  the order; NOTE IsPrimitiveRoot needs
  Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots imported); (3)
  `hasEnoughRootsOfUnity_of_padic_roots` — instance for the full dual of
  (ZMod p^n)ˣ: exponent ∣ φ(p^n) ∣ p^n(p−1); primitive-P-root as the
  COPRIME PRODUCT of hroots-root and Teichmüller-root
  (Commute.orderOf_mul_eq_mul_orderOf_of_coprime + IsPrimitiveRoot.orderOf
  + pow_of_dvd + Nat.div_div_self; NOTE HasEnoughRootsOfUnity is
  TYPE-valued — produce the ∃-prim as a Prop-have BEFORE the structure
  goal or Exists-elim fails; cyc-field = rootsOfUnity.isCyclic for the
  domain integerRing K). Determinacy body: (B) all-χ moment vanishing via
  the primitive core (FactorsThrough at p^m + conductor-min via
  Nat.sInf_le + NEW Characters lemma
  `DirichletCharacter.toContinuousMapZp_changeLevel` (unit-agreement via
  changeLevel_eq_cast_of_dvd + PadicInt.cast_toZModPow) + 1_u-sandwich by
  hsupp); (C) x-weighted coset-indicator vanishing via mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq` orthogonality (nonunit
  cosets die against the unit-supported μ; CharZero-cancel of totient);
  (D) loc-const collapse through the factorisation lemma at level
  max(n₀,1) + Finset.sum_eq_single; (E) x⁻¹-trick: extendByZero of the
  R-valued units-inverse (UnitsZp machinery + KubotaLeopoldt invCM) +
  ε-approximation against PadicMeasure.exists_locallyConstant_norm_sub_le'
  + norm_apply_le. LEAN NOTES: conductor_le_conductor_mem_conductorSet
  concludes ≤ (Classical.choose _).conductor — useless; use Nat.sInf_le
  directly; changeLevel_trans takes χ as FIRST explicit arg; ext-on-C(X,R)
  goals come ↑-coercion-wrapped — close ring-steps with
  `exact congrArg Subtype.val (by ring)`; Nat.dvd_sub (unprimed) in this
  pin; omega needs primality-derived 1 < p fed explicitly. Verification:
  lake build green (code + blueprint, 3950 jobs); axioms = {propext,
  Classical.choice, Quot.sound} + scan_source clean on
  eq_zero_of_twisted_moments_eq_zero and eq_of_twisted_moments_eq.
  Blueprint: `interp-nontame` wired → zetaEta_twisted_moments +
  eq_of_twisted_moments_eq + eq_zero_of_twisted_moments_eq_zero with the
  two-halves prose note (cleared existence, hroots-design uniqueness,
  Teichmüller prime-to-p roots).

### [CLEANUP-ALL-4] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T515 | **Type**: cleanup-all (before T516)
- **Progress**: DONE 2026-06-11. Project-wide sweep: lake build green with
  23 warnings, ALL `declaration uses sorry` in open-ticket scope (PadicExp
  17 = T521–T523, Branches 4 = T519, NonTame 1 = T516); zero style/linter
  warnings; zero lines > 100 project-wide. Axiom spot-checks this session:
  tame_conductor(+theta), zetaEta_twisted_moments, twist/X_mul masters —
  all {propext, Classical.choice, Quot.sound}. Golf: T512's hHsum inline
  subst-transport refactored onto the T515 subst_map_{neg,sum,C_mul}
  distributors (−8 LOC). The per-ticket inline cleanups (T511–T515) kept
  the bar; no batch debt found.

### [T517] Teichmüller character ω
- **Status**: done | **File**: Interpolation/Branches.lean | **Depends on**: none
- **Progress**: DONE 2026-06-10. Executed via the flt-regular-bernoulli port
  (replan note above): `maximalIdealQuotientEquivZMod` + CharP/Finite instances
  on the residue quotient, `teichmullerZMod : ZMod p →*₀ ℤ_[p]` through
  `Perfection.teichmuller₀`, `toZMod_teichmullerZMod` (section-of-reduction),
  `teichmullerZMod_pow_card_sub_one`; skeleton fills `teichmullerFun :=
  teichmullerZMod ∘ toZMod` + all 6 API lemmas + `teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`
  packaging + `teichmuller_coe` (rfl). Compiled FIRST PASS, zero errors.
  Verification: diagnostics clean on the section; axioms = {propext,
  Classical.choice, Quot.sound} on PadicInt.teichmuller,
  toZMod_teichmullerZMod, teichmullerFun_sub_self_mem,
  teichmullerFun_eq_of_sub_mem. Inline cleanup: golfed isUnit hypothesis to
  `Nat.sub_ne_zero_of_lt`. Blueprint: node `teichmuller-character` spans Def
  5.15 in FULL (ω + ⟨·⟩ + factorisation) — wiring deferred to T518 completion
  per the partial-realisation rule.
- **Parallel**: yes (chain C head) | **Type**: def + API
- **Statement**: skeleton `PadicInt.teichmullerFun` + 6 API sorries +
  `teichmuller` packaging (L5.3.1).
- **Proof sketch**: REPLANNED (flt-regular-bernoulli survey, plan.md addendum
  2026-06-10): port their `Characters.lean` construction — `teichmullerZMod :
  ZMod p →*₀ ℤ_[p]` via mathlib `Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])`
  composed with `(PerfectionMap.id …).equiv` and `PadicInt.residueField.symm`;
  then `teichmullerFun p x := teichmullerZMod p (toZMod x)`. Source-faithful:
  mathlib's `Perfection.teichmullerFun` is itself the limit-of-`x^{p^n}`
  construction of RJW Def 5.15 (`teichmullerAux n+1 = lift^{p^n}`, adic-Cauchy).
  Original from-scratch sketch (decomposition L5.3.1) retired.
- **Mathlib lemmas**: `Perfection.teichmuller₀`, `Perfection.mk_teichmuller₀`,
  `PadicInt.residueField`, `PadicInt.toZMod_eq_residueField_comp_residue`,
  `ZMod.pow_card_sub_one_eq_one`, `IsUnit.of_pow_eq_one` (all verified in pin).
- **Sources**: Def 5.15 TeX 1899–1905 (verbatim at R5.3); port source
  `flt-regular-bernoulli/BernoulliRegular/Characters.lean` (user's own repo).
- **Blueprint**: wire the chapter's ω-definition node (§5.3 part — locate
  label in Interpolation.lean tail).
- **Sizing**: ~120 LOC.

### [T518] ⟨·⟩ and y^s on 1+pℤ_p
- **Status**: done | **File**: Branches.lean | **Depends on**: T517 | **Type**: def + API
- **Progress**: DONE 2026-06-10. angleBracket section: `angleUnit_sub_one_mem`
  (unit-factoring ω⁻¹(x − ω) + ideal absorption), `angleUnit_mul`
  (mul_inv_rev + mul_mul_mul_comm), `teichmuller_mul_angleUnit`
  (mul_inv_cancel_left, term-mode). onePAdicPow section: helpers
  `tendsto_pow_atTop_nhds_zero_of_mem_span` (norm ≤ p⁻¹ < 1),
  `isClosed_span_p` (closed ball via norm_le_pow_iff_mem_span_pow),
  `mul_sub_one_mem`; `onePAdicPow := addChar_of_value_at_one (y−1)`;
  `onePAdicPow_apply_one`, `onePAdicPow_natCast` (nsmul_one +
  map_nsmul_eq_pow), `continuous_onePAdicPow` (defeq), `onePAdicPow_sub_one_mem`
  (density of ℕ + closedness, quotient-ring computation at naturals),
  `onePAdicPow_mul_base` (uniqueness `eq_addChar_of_value_at_one` applied to
  the product character). `eq_one_of_pow_card_sub_one` MOVED into the
  onePAdicPow section (proof needs the character API): u^{(p−1)s} via
  `AddChar.mulShift` is trivial by two applications of uniqueness, then
  evaluate at (p−1)⁻¹ (p−1 a unit: residue −1 ≠ 0); works verbatim for p = 2
  (degenerate, exponent 1) — RJW's odd-p caveat noted in docstring.
  Verification: zero errors; axioms = {propext, Classical.choice, Quot.sound}
  on eq_one_of_pow_card_sub_one, onePAdicPow_mul_base,
  teichmuller_mul_angleUnit, onePAdicPow_sub_one_mem. lake build green
  (Branches + Blueprint). Blueprint: node `teichmuller-character` wired to
  {teichmuller, angleUnit, teichmuller_mul_angleUnit,
  eq_one_of_pow_card_sub_one} with construction/uniqueness prose note;
  Lem 5.14 node `interp-padic-exp` left unwired with rationale comment
  (wire when T521–T523 proves convergence). Replan note honoured: x^s via
  character-uniqueness (decomposition L5.3.3).
- **Statement**: skeleton angleUnit cluster (L5.3.2) + onePAdicPow cluster
  (L5.3.3 — built on `PadicInt.addChar_of_value_at_one`; replan note: source's
  exp/log definition realised by character-uniqueness; the Lem 5.14 blueprint
  node stays UNWIRED with rationale comment).
- **Mathlib lemmas**: `PadicInt.addChar_of_value_at_one`,
  `PadicInt.continuousAddCharEquiv` (uniqueness for mul_base/natCast),
  binomial-coefficient norm bounds.
- **Sources**: TeX 1892–1905 (verbatim at R5.3).
- **Sizing**: ~140 LOC.

### [T519] **MILESTONE: branches ζ_{p,i} and RJW Theorem 5.17**
- **Status**: done (finished 2026-06-11)
- **File**: Branches.lean | **Depends on**: T518, CLEANUP-ALL-5
- **Type**: def + theorem
- **Statement**: skeleton `branchChar`, `branchChar_natCast`, `zetaPBranch`,
  `zetaPBranch_interpolation` (L5.3.4–6; pairing through the §4
  IsPseudoMeasure witnesses at the T037 generator — pairChar sub-lemma
  `integral_char_dirac_mul` L5.3.5).
- **Sources**: TeX 1907–1924 (verbatim at R5.3).
- **Blueprint**: wire the ζ_{p,i}/Thm 5.17 nodes; re-render.
- **Sizing**: ~150 LOC.
- **Progress**:
  - 2026-06-10/11 (prior session, credit-out mid-build): full block staged —
    `isLocallyConstant_teichmullerFun`, `onePAdicPow_congr`,
    `onePAdicPow_sub_one_mem_pow` (p^m-strengthened closure argument),
    `continuous_angleUnit_val`, `continuous_onePAdicPow_angleUnit`
    (multiplicative-increment route ⟨x⟩ = ⟨x₀⟩·w), `branchChar`,
    `branchChar_natCast` (orderOf-divides + pow_eq_pow_iff_modEq endgame),
    `zetaPBranch` (zetaNum-witness pairing at the T037 generator),
    `zetaPBranch_interpolation` (padicZeta_moments + field_simp endgame).
  - 2026-06-11 (takeover session): fixed the 2 remaining build errors
    (hxw closed via `Units.mul_inv_cancel_left` instead of the failing
    mul_assoc chain; spurious `rfl` after goal-closing `rw` dropped).
    Verification: lake build green, 0 sorry in Branches.lean,
    `#print axioms` = [propext, Classical.choice, Quot.sound] on all 6 new
    decls (branchChar, branchChar_natCast, zetaPBranch,
    zetaPBranch_interpolation, continuous_angleUnit_val,
    continuous_onePAdicPow_angleUnit).
  - 2026-06-11: /cleanup degraded mode (no lean-lsp MCP this session):
    linter-set build green, zero long lines; golfed 3 unused `set … with`
    binders. A tooled session may revisit.
  - 2026-06-11: blueprint wired — `interp-branches` →
    branchChar + zetaPBranch (with ℚ_p-vs-ℂ_p and witness-pairing prose
    note), `interp-branch-interpolation` → zetaPBranch_interpolation.
    Node prose corrected to RJW's actual Thm 5.17 statement (odd-vanishing
    moved to post-proof prose remark, as in the source TeX 1928);
    `lake build PadicLFunctionsBlueprint` green.
  - DONE — milestone: RJW Theorem 5.17 complete.

### [CLEANUP-ALL-5] Pre-milestone /cleanup-all
- **Status**: done | **Depends on**: T510, T516, T518 | **Type**: cleanup-all (before T519/T520)
- **Progress**: DONE 2026-06-11. Sweep: zero style/linter warnings
  project-wide, zero long lines; 21 sorry-warnings, all open-ticket scope
  (Branches 4 = T519, PadicExp 17 = T521–T523). T516's additions were
  cleaned per-ticket (omits, congrArg-val ring-closers, simp-arg prunes).
  No batch debt.

### [T520] L_p(θ,s) and RJW Theorem 5.19
- **Status**: done (finished 2026-06-11)
- **File**: Interpolation/LpFunction.lean (replan — see Progress) + Branches.lean
- **Depends on**: T519, T516 | **Type**: def + theorem
- **Statement**: `LpFunction θ s` (genuine integral against ζ_η) +
  `Lp_interpolation` (L5.3.7; eq:alternative route; ω-as-Dirichlet-character
  bridge `teichmullerChar` sub-leaf).
- **Sources**: TeX 1929–1957 (verbatim at R5.3).
- **Blueprint**: wire the L_p/Thm 5.19 nodes; re-render; chapter complete
  except Mellin-dependent prose nodes (rationale comments).
- **Sizing**: ~130 LOC.
- **Progress**:
  - 2026-06-11: REPLAN (file location): the planner placed L_p in
    Branches.lean, but T516 inverted the import direction (NonTame imports
    Branches for the Teichmüller prime-to-p roots), and L_p needs NonTame's
    μ̃_η stack — so T520 lives in the new
    `PadicLFunctions/Interpolation/LpFunction.lean` (imports NonTame; wired
    into PadicLFunctions.lean; CL53's scope extended to include it). The
    ω-bridge cluster (`teichmullerChar`, `teichmullerChar_toZMod`,
    `castHom_toZModPow_eq_toZMod`) is ℤ_p-level and went to Branches.lean
    as planned.
  - 2026-06-11: built `teichmullerCharR` (ω over integerRing K),
    `invUnitsCM`, `anglePowCM` (T519's continuity through the isometric
    structure map), `zetaEtaCleared` (RJW's ζ_η as a genuine measure on
    ℤ_p^×, cleared normalisation, restriction implicit in extension by
    zero), `LpFunction` (RJW Def 5.18, Gauss unit divided out),
    `twistedPChar` (χω^{−k} at level p^{max n 1}),
    `exists_primitive_pPow_factorisation` (T516's conductor argument
    packaged), `Lp_interpolation` (RJW Thm 5.19) — statement quantifies
    the primitive core χ' of χω^{−k} via a factorisation hypothesis (the
    zetaEta_twisted_moments pattern); RHS = (1−θ'(p)p^{k−1})·LvalNeg
    (toFieldChar θ') (k−1) with θ' = η·χ' at level D·p^m.
  - Proof route as planned (eq:alternative): k = k'+1 destructure; ε' from
    hε by pow_of_dvd; character key χ = χ'·ω^{k'+1} at level p^{max n 1}
    (group algebra from hχ'); pointwise integrand identity
    x⁻¹χ(x)⟨x⟩^k = χ'(x)x^{k−1} on units (Units-level collapse +
    congrArg Units.val + map_mul/map_pow over algebraMap); extendByZero
    ext-case-split; zetaEta_twisted_moments at χ'; Gauss-unit cancellation.
  - Verification: lake build green (code + blueprint), 0 sorry,
    `#print axioms` = [propext, Classical.choice, Quot.sound] on all 10 new
    decls (castHom_toZModPow_eq_toZMod, teichmullerChar, teichmullerCharR,
    invUnitsCM, anglePowCM, zetaEtaCleared, LpFunction, twistedPChar,
    exists_primitive_pPow_factorisation, Lp_interpolation).
  - /cleanup degraded mode (no lean-lsp MCP this session): linter-set green,
    zero long lines; added @[simp] apply-lemmas (invUnitsCM_apply,
    anglePowCM_apply, zetaEtaCleared_apply) and de-nested the in-proof
    shows. A tooled session may revisit.
  - Blueprint: `interp-zeta-eta` re-wired to zetaEtaCleared +
    zetaEta_twisted_moments (ζ_η now exists as a measure object);
    `interp-Lp-theta` → LpFunction; `interp-Lp-interpolation` →
    Lp_interpolation. Node prose matched to RJW's actual Thm 5.19 (the
    ζ_{p,i}(s) = L_p(ω^i,s) identification is RJW's post-theorem REMARK —
    moved to prose with a both-routes-kept formalisation note, as for
    Thm 5.17). `lake build PadicLFunctionsBlueprint` green.
  - DONE — RJW Theorem 5.19 complete; §5.3 mainline (5.17 + 5.19) closed.

### [T521] p-adic exponential: convergence, isometry, functional equation
- **Status**: done (finished 2026-06-11)
- **File**: PadicLFunctions/PadicExp.lean | **Depends on**: none
- **Parallel**: yes (chain D head; user-added cluster) | **Type**: def + lemmas
- **Progress**:
  - 2026-06-11: E1 was free — mathlib has the full nonarchimedean stack:
    `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (complete
    case) + `HasSum.mul_of_nonarchimedean` +
    `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
    (Topology/Algebra/InfiniteSum/Nonarchimedean.lean + Ring.lean). Added
    the missing 2-line bridge `instance : NonarchimedeanRing L` from
    `IsUltrametricDist` (MATHLIB-PR candidate, noted in docstring).
  - E2 via `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (exact
    Legendre form) + `Padic.norm_eq_zpow_neg_valuation` +
    `Padic.valuation_natCast`. Helpers extracted:
    `norm_factorial_inv_pow_le` (inverted bound),
    `norm_factorial_inv_smul_pow_le` (geometric term decay, rpow-free at
    the (p−1)-power level per the recorded design).
  - E3: `summable_padicExp_terms` (E1 + geometric bound + ε-transfer
    through strict pow-monotonicity); `padicExp_zero` (tsum_eq_single);
    isometry via NEW `norm_factorial_inv_smul_pow_sub_lt` (m ≥ 2 tail
    strictly dominated — geom_sum₂_mul + ultrametric sum bound + strict
    Legendre on the OPEN ball, attack [3] honoured) + dominant-term
    argument (tendsto-tail uniform bound C < d via range-sup' + d/2;
    `IsUltrametricDist.norm_tsum_le_of_forall_le` +
    `norm_add_eq_max_of_norm_ne_norm`); `norm_padicExp_sub_one` at y = 0;
    `padicExp_add` via the attack-pinned route — NOT norm-summable Cauchy
    products: `mul_of_nonarchimedean` summability + antidiagonal formula +
    `Nat.sum_antidiagonal_eq_sum_range_succ` + add_pow +
    `Nat.choose_mul_factorial_mul_factorial` scalar algebra.
  - Verification: lake build green, 0 sorry in the T521 declarations
    (11 remain in file = T522/T523 scope), `#print axioms` =
    [propext, Classical.choice, Quot.sound] on all 10 new decls.
  - /cleanup degraded mode (no lean-lsp MCP): linter green (omits added),
    no long lines. Blueprint: none for T521 (per plan — T523 wires
    Lem 5.14).
- **Statement**: skeleton sorries E1–E3 (`summable_iff_tendsto_cofinite_zero`,
  `norm_factorial_le`, `padicExp_zero`, `norm_padicExp_sub_padicExp`,
  `norm_padicExp_sub_one`, `padicExp_add`).
- **Proof sketch**: decomposition R5.E (E1 partial-sum Cauchy; E2 Legendre via
  mathlib `padicValNat` factorial API; E3 isometry termwise-strict on the OPEN
  ball + tsum_prod/antidiagonal for exp_add — NOT norm-summable Cauchy
  products, attack-pinned).
- **Mathlib lemmas**: `padicValNat`-factorial family (verify exact:
  `Nat.Prime.factorization_factorial`/`sub_one_mul_padicValNat_factorial`),
  `Summable.tsum_prod`, `tsum_comm`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`,
  `Padic.norm_eq_zpow_neg_valuation`.
- **Sources**: TeX 1892–1897 (verbatim at R5.E) + Cassels §12/Washington §5.1
  (cross-refs recorded).
- **Generality**: over the §5 coefficient field L (ℚ_p-instance for Lem 5.14);
  radius-form statements p-uniform, pℤ_p-forms p ≠ 2.
- **Blueprint**: none yet (T523 wires Lem 5.14).
- **Sizing**: ~180 LOC (Washington's §5.1 proofs span ~1.5 pages).

### [T522] p-adic logarithm and exp/log inversion
- **Status**: done (finished 2026-06-11)
- **File**: PadicExp.lean | **Depends on**: T521 | **Type**: lemmas
- **Progress**:
  - 2026-06-11 (main session): `sub_one_mul_padicValNat_succ_le`
    ((p−1)·v_p(n+1) ≤ n via Bernoulli), `norm_succ_inv_smul_pow_le`
    (geometric log-term decay, rpow-free), `summable_padicLog_terms`,
    `padicLog_one`, `norm_succ_inv_smul_pow_lt` (tail domination m ≥ 1),
    `norm_padicLog` (dominant-term argument, mirrors the exp isometry).
  - 2026-06-11 (tooled subagent, lean-lsp): the composition trio
    `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul` via the pinned
    Washington Prop 5.3 route — formal identities `exp_subst_log`
    ((1+X)·DF = F recursion) and `log_subst_exp_sub_one` (derivative.ext)
    using mathlib's `PowerSeries.log` (it exists — `HasSubst.log`,
    `deriv_log`); evaluation bridge `master_bridge` (per-power
    `tsum_eval_pow` by iterated nonarchimedean Cauchy product + ultrametric
    Fubini `Summable.tsum_comm` over ℕ×ℕ; total summability from the
    Legendre multinomial bound `norm_coeff_pow_le`:
    ‖[X^k](G^n)‖^{p−1} ≤ p^{k−n}); `padicLog_mul` free from the pair +
    `padicExp_add`. ~20 helper lemmas added (all docstringed, in
    section Inversion).
  - Verification: lake build green, 0 sorry in T522 scope (6 remain =
    T523 pZp section), `#print axioms` = standard 3 on all of
    padicLog_one/norm_padicLog/summable_padicLog_terms/padicExp_padicLog/
    padicLog_padicExp/padicLog_mul. Linter clean (omits added).
  - Note for cleanup: `master_bridge` carries
    `set_option maxHeartbeats 400000` (verified working value; golf
    candidate for a tooled cleanup pass).
- **Statement**: skeleton E4 sorries (`padicLog_one`, `norm_padicLog`,
  `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`).
- **Proof sketch**: decomposition E4 (series composition with ultrametric
  Fubini — Washington Prop 5.3 route, attack-pinned; log_mul from exp_add +
  injectivity-of-exp via isometry).
- **Sources**: as T521.
- **Sizing**: ~150 LOC (the composition is the meaty half).

### [T523] RJW Lemma 5.14 as stated + equivalence with the character route
- **Status**: done (finished 2026-06-11)
- **File**: PadicExp.lean | **Depends on**: T522, T518 | **Type**: theorem
- **Progress**:
  - 2026-06-11 (tooled-route subagent under main-session orchestration;
    degraded tooling — lake-build gate): E5 route verbatim. Helpers:
    `coe_norm_le_inv_of_mem_span`, `inExpBall_of_mem_span` (hp2 enters
    exactly here: p−1 ≥ 2 makes the ball inclusion strict),
    `pZpExp_coe`/`pZpLog_coe` (dite-true-branch bridges). Defs filled
    junk-total (dite on the integrality certificate; junk 1 resp. 0).
    `padicExp_converges_on_pZp` = summable_padicExp_terms ∘ ball-inclusion;
    `pZpExp_sub_one_mem`/`pZpLog_mem` via the isometries;
    `padicExp_smul_padicLog_eq_onePAdicPow` by AddChar-uniqueness
    (additivity via padicExp_add, LipschitzWith-1 continuity via the
    isometry, value x at 1 via padicExp_padicLog, then
    PadicInt.eq_addChar_of_value_at_one) — the recorded replan L5.3.3 is
    now DISCHARGED: both x^s-routes formalised and proven equal.
  - Verification: lake build green; ZERO sorry project-wide (PadicExp.lean
    fully proven); `#print axioms` = standard 3 on all six decls; linter
    clean.
  - Blueprint: `interp-padic-exp` WIRED → padicExp_converges_on_pZp +
    padicExp_smul_padicLog_eq_onePAdicPow (unwired-rationale comment
    removed per the user-approved cluster plan); blueprint build green.
- **Statement**: skeleton pZp-section sorries (`padicExp_converges_on_pZp`,
  `pZpExp`/`pZpLog` integral versions + membership lemmas,
  `padicExp_smul_padicLog_eq_onePAdicPow`).
- **Proof sketch**: decomposition E5 (ball inclusion p odd; integrality via
  isometry; equivalence by `PadicInt.continuousAddCharEquiv` uniqueness +
  `padicExp_add` + `padicExp_padicLog` at s = 1).
- **Sources**: TeX 1892–1897 (the Lem 5.14 statement realised literally).
- **Blueprint**: WIRE the chapter's Lem 5.14 node (the exp-statement node —
  locate label in Interpolation.lean §5.3 region) → `padicExp_converges_on_pZp`
  + `padicExp_smul_padicLog_eq_onePAdicPow`; replaces the planned
  unwired-rationale (user-approved cluster).
- **Sizing**: ~100 LOC.

### [CLEANUP-54] /cleanup on PadicExp.lean (3 tickets on file → cadence + final)
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T523 | **Type**: cleanup
- **Progress**: no lean-lsp MCP this session — degraded pass per standing
  rule 3: build green with the mathlib linter set, zero warnings, zero
  sorries, zero long lines; golfed the two `by exact`-ascription bridges to
  `htail.ne'` (isometry proofs). Queued for the tooled CLEANUP-FINAL:
  `master_bridge`'s `set_option maxHeartbeats 400000` (verified working;
  golf candidate), per-decl golf of the T521–T523 proofs.

### [CLEANUP-53] Final per-file cleanups (§5 files)
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T520
- **Type**: cleanup (Characters, GenBernoulli[Complex], Twist,
  TameConductor, NonTame, Branches, LpFunction — final pass each; then
  update CLEANUP-FINAL's scope to include §5)
- **Progress**: substance largely discharged upstream — the tooled
  CLEANUP-ALL-5 sweep (2026-06-11) left zero style/linter warnings
  project-wide, and the post-ALL-5 additions (T519 Branches, T520
  Branches+LpFunction) were cleaned per-ticket (degraded). This pass
  verified: build green, zero warnings, zero long lines, zero sorries
  across all §5 files incl. the new LpFunction.lean. CLEANUP-FINAL's scope
  widened to include the §5 files (see its entry). Tooled session may
  revisit for per-decl golf.

## §5 dependency quick-view
```
chain A: TW1 → TW2 → TW3 → CLW1 → TW4 → TW5 → TW6 → CLW2
chain B: T501 T502 T503 (free) → T504 → T505;
chain C: T517 → T518 (free)
chain D: T521 → T522 → (T518) → T523 → CL54 (free until T523's T518-dep)
TW6+T502 → T506 → T507 → (T501) → T508 → CL51 → (T504) → T509 → CLALL3 → T510*
TW6+T501 → T511 → T512(T504) , T513 → CL52 → T514 → T515(T508) → CLALL4 → T516*
T518 → (CLALL5) → T519* → (T516) → T520 → CL53 → [CLEANUP-FINAL widened]
```
Cadence audit: PadicExp 3/1 ✓ (CL54); Twist 3/1 ✓; NonTame 6/2 ✓ (CL52 + final in CL53);
TameConductor 2/1(final in CL53) ✓; Branches 4/1+final ✓; GenBernoulli 2+1
(final in CL53) ✓; Characters 2 (final in CL53) ✓; pre-milestone cleanup-alls
×3 ✓; CLEANUP-FINAL retained as global last ✓.

---

# §6 board (The values at s = 1; TeX 1980–2180) — created 2026-06-11

Skeleton: 4 new files (ExtLog.lean, MeasureR/FormalPsi.lean,
ValuesAtOneComplex.lean, ValuesAtOne.lean), 28 new sorries, `lake build`
green. Decomposition: decomposition.md R6 (verbatim quotes + replans 1–5).
Standing rules apply (CLAUDE.md). Statements live in the skeleton — tickets
reference declarations by name (the §5 T521-pattern).

### [T601] Exp-ball multiplicativity and log of powers
- **Status**: done (2026-06-11) | **File**: ExtLog.lean | **Depends on**: none
- **Progress**: DONE first pass — norm_lt_one_of_inExpBall (helper),
  mul_mem_expBall ((y−1)z+(z−1) decomposition, ultrametric max),
  pow_mem_expBall (induction), padicLog_pow (padicLog_mul induction +
  succ_nsmul). Axioms standard ×4; build green; degraded-mode cleanup
  (linter green, no long lines).
- **Parallel**: yes (chain W6a head) | **Type**: lemmas
- **Statement**: skeleton `mul_mem_expBall`, `padicLog_pow` (W6a-a1/a2).
- **Proof sketch**: a1 ultrametric: yz−1 = (y−1)z + (z−1), norm ≤ max,
  each factor ≤ ball-bound (‖z‖ = ‖(z−1)+1‖ ≤ 1 needs ball ⊆ unit-ball:
  ‖z−1‖^{p−1} < p⁻¹ < 1 ⟹ ‖z−1‖ < 1); pow-monotone transfer as in
  norm_factorial_inv_smul_pow_le. a2: induction on n via padicLog_mul +
  a1-closure; n = 0 via padicLog_one.
- **Mathlib lemmas**: IsUltrametricDist.norm_add_le_max, pow_lt_one_iff.
- **Sources**: decomposition R6 W6a; Washington §5.1.
- **Generality**: ambient L (PadicExp variables).
- **Sizing**: source one-liners → ~40 LOC.

### [T602] p-power descent into the exponential ball
- **Status**: done (2026-06-11)
- **Progress**: DONE — norm_natCast_p (helper: ‖p‖_L = p⁻¹ via
  norm_algebraMap' + Padic.norm_p), norm_pow_p_sub_one_le (binomial peel
  via sum_range_succ' + Nat.Prime.dvd_choose_self +
  IsUltrametricDist.norm_natCast_le_one), exists_pPow_pow_inExpBall
  (decay r_{k+1} ≤ t0·r_k with t0 := max(r0^{p−1},p⁻¹) < 1, geometric
  tendsto at the (p−1)-power level — boundary passed THROUGH per the
  attack note). Axioms standard ×3; linter clean (omits added);
  degraded-mode cleanup. | **File**: ExtLog.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `norm_pow_p_sub_one_le`, `exists_pPow_pow_inExpBall`
  (W6a-a3/a4).
- **Proof sketch**: a3 binomial w^p−1 = Σ_{i≥1}C(p,i)(w−1)^i; i = p term
  (w−1)^p; 0<i<p terms have ‖C(p,i)‖ ≤ p⁻¹ (p ∣ choose: mathlib
  Nat.Prime.dvd_choose_self); ultrametric finite-sum max
  (norm_sum_le_of_forall_le_of_nonneg). a4: iterate; r_{j+1} ≤
  r_j·max(r_j^{p−1}, p⁻¹) ≤ r_j·t with t := max(r_0^{p−1}, p⁻¹) < 1;
  geometric until r^{p−1} < p⁻¹. ATTACK-pinned: the closed boundary
  r = p^{-1/(p−1)} is passed THROUGH (no single-step contraction there;
  the t-factor argument is global, decomposition R6 a4).
- **Mathlib lemmas**: Nat.Prime.dvd_choose_self (verify name),
  add_pow_le?? — no: Commute.add_pow expansion; tendsto_pow geometric.
- **Sources**: decomposition R6 W6a; Washington §5.1.
- **Sizing**: ~70 LOC.

### [T603] Integral norm-one elements lie in the extLog domain
- **Status**: done (2026-06-11)
- **Progress**: DONE (tooled-route subagent, degraded tooling): pigeonhole
  n ↦ z^n into ℤ[z]⧸(p) (finite via Module.finite_of_fg_torsion — route
  deviation from the ZMod-p-module chain, recorded); norm-cancellation
  WITHOUT z̄-invertibility per the attack-pinned design; helpers
  norm_le_one_of_mem_adjoin_int (adjoin_induction),
  finite_adjoin_int_quotient, norm_eq_one_of_inExpBall_sub_one. Two new
  mathlib imports (FiniteAbelian.Basic, Finiteness.Cardinality). Axioms
  standard; linter clean. | **File**: ExtLog.lean | **Depends on**: T602
- **Type**: lemmas
- **Statement**: skeleton `exists_pow_sub_one_norm_le`,
  `extLogDomain_of_integral_norm_one` (W6a-a5/a11).
- **Proof sketch**: a5: S := Algebra.adjoin ℤ {z} is module-finite
  (IsIntegral.fg / Algebra.adjoin.finite); S/pS finite (fg over ℤ/p);
  pigeonhole on powers of z̄: z̄^i = z̄^{i+m} ⟹ z^i(z^m−1) ∈ p·S ⊆
  p·(unit ball) ⟹ ‖z^i(z^m−1)‖ ≤ p⁻¹; ‖z^i‖ = 1 cancels (norm mult).
  ATTACK-pinned: no z̄-invertibility needed (decomposition R6 a5).
  a11: a5 gives ‖z^m−1‖ ≤ p⁻¹ < 1, then T602-a4 on w := z^m gives
  z^{m·p^j} ∈ 1+ball: witness (m·p^j, 0, z^{m·p^j}).
- **Mathlib lemmas**: IsIntegral, Algebra.adjoin, Module.Finite transfer,
  finiteness of fg-ℤ-module mod p (survey exact route at execution),
  Finite.exists_ne_map_eq_of_infinite-style pigeonhole.
- **Sources**: decomposition R6 W6a-a5 (design note).
- **Sizing**: ~80 LOC (the cluster's engine).

### [T604] extLog: well-definedness and API
- **Status**: done (2026-06-11) | **File**: ExtLog.lean | **Depends on**: T601
- **Progress**: DONE (same pass as T603): extLog_witness_smul_eq core
  (k·m' = k'·m via zpow_right_injective₀ at base p⁻¹; norm-1 of ball
  members via ultrametric isoceles), then a7–a10b as planned (witnesses
  composed; extLog_neg via (−1)-witness (2,0,1)). Axioms standard ×7
  (whole file sorry-free); linter clean.
- **Type**: def-lemmas
- **Statement**: skeleton `extLog_eq_of_witness`, `extLog_eq_padicLog`,
  `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`, `extLog_neg` (W6a-a7–a10;
  def a6 already in skeleton).
- **Proof sketch**: a7: two witnesses (m,k,y), (m',k',y'): x^{mm'} both
  ways ⟹ p^{km'−k'm}·y^{m'} = y'^{m}; taking norms, ‖y‖ = ‖y'‖ = 1 and
  ‖p‖ = p⁻¹ < 1 force km' = k'm, cancel p-powers (field), then
  y^{m'} = y'^m and a2: m'·log y = m·log y'; scalar algebra in ℚ_[p]-module.
  a8: witness (1,0,x). a9: product witnesses + a1 + padicLog_mul + a7.
  a10: x^n = 1 witness (n,0,1), padicLog_one; extLog_neg: (−x)² = x²-route:
  extLog((−x)²) = extLog(x²) and 2·extLog(−x) = ... via a9-on-self (domain
  of −x from x: witness with even power) — or extLog(−1) = 0 (a10) + a9.
- **Mathlib lemmas**: norm_zpow, mul-cancellation in fields.
- **Sources**: decomposition R6 W6a; Washington §5.1 Lemma 5.5-adjacent.
- **Sizing**: ~100 LOC.

### [CLEANUP-61] /cleanup on ExtLog.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T601, T602, T603, T604
- **Type**: cleanup (cadence 4-tickets + final, merged)
- **Progress**: degraded pass (no lean-lsp MCP): linter set green, zero
  warnings, zero long lines, file sorry-free; per-ticket golf was applied
  during T601–T604. Tooled CLEANUP-FINAL may revisit.

### [T605] The digit decomposition of power series
- **Status**: done (2026-06-11) — WITH B2 STATEMENT-FIX (logged)
- **Progress**: the planned general-CommRing statement is FALSE over fields
  (R = ℚ, p = 2: (1+X)^p − 1 = unit·X makes phiSeries bijective, digits
  non-unique) — caught at the adversarial briefing, b2_log.jsonl appended.
  Fixed: psiSeries junk-totalised (dite on ∃!-digits) over general R;
  existsUnique_digits proven over integerRing K via the MEASURE-TRANSPORT
  route (measure-level p-residue decomposition through mahlerRingEquiv) —
  replacing the planner's triangular-recursion sketch (mathematically
  wrong; recorded). Subagent pass; axioms standard; dependents build. | **File**: MeasureR/FormalPsi.lean | **Depends on**: none
- **Parallel**: yes (chain W6b head) | **Type**: theorem
- **Statement**: skeleton `existsUnique_digits` (W6b-b1).
- **Proof sketch**: the family (1+T)^i·((1+T)^p−1)^j has leading
  coefficient 1 in degree i+pj (base-p digit bijection ℕ ≃ Fin p × ℕ);
  triangular recursion: define G_i's coefficients by strong induction on
  total degree, subtracting known lower terms; uniqueness by the same
  triangularity (lowest-degree coefficient of a nonzero combination
  survives). Suggest: prove coeff-extraction lemma
  coeff (i+pj) ((1+T)^i((1+T)^p−1)^j) = 1 + upper-triangularity, then
  build by Nat.strong induction.
- **Mathlib lemmas**: PowerSeries.coeff_mul, coeff_pow bounds,
  Finset.Nat digit machinery (Nat.divMod p-bijection).
- **Sources**: decomposition R6 W6b-b1 (mirrors the project's measure-level
  digit shift, Measure/Toolbox ψ).
- **Sizing**: ~60–90 LOC (the formal-cluster engine).

### [T606] psiSeries API
- **Status**: done (2026-06-11) | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605
- **Progress**: DONE (same pass): psiSeries_phi/C/add/C_mul over
  integerRing K via IsDigitDecomp-uniqueness; psiSeries_map gained an
  honest ∃!-soundness hypothesis (junk-total psiSeries). Axioms standard.
- **Type**: lemmas
- **Statement**: skeleton `psiSeries_phi`, `psiSeries_C`, `psiSeries_add`,
  `psiSeries_C_mul`, `psiSeries_map` (W6b-b2/b8).
- **Proof sketch**: each from uniqueness of digits: exhibit the digit
  family of the right-hand side and apply ExistsUnique.unique. For map:
  ring-hom image of a digit decomposition is one (phiSeries commutes with
  map: subst-map compatibility — PowerSeries.map_subst exists? verify;
  else coefficient-wise).
- **Sources**: decomposition R6 W6b.
- **Sizing**: ~80 LOC.

### [T607] φ–∂ commutation, antiderivative, ker ∂ (REALIGNED R6.6)
- **Status**: done (2026-06-11)
- **Progress**: DONE (subagent): chain rule via derivative_subst +
  Derivation.leibniz_pow (MuA idiom); exists_antideriv by (1+X)-unit +
  coefficient division (CharZero); ker-∂ by unit-cancellation + coeff
  induction. Axioms standard ×3. | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605, T606
- **Type**: lemmas
- **Statement** (realigned to the c₀-design — field-ψ is junk):
  `one_add_mul_derivative_phiSeries` (∂φ = p·φ∂, R-generic),
  `exists_antideriv` (K char-0: B = p·∂C with C(0) = 0),
  `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero` (ker ∂).
- **Proof sketch**: b3: differentiate the digit decomposition;
  ∂((1+T)^i·φG) = i·(1+T)^i·φG + p·(1+T)^i·φ(∂G) (sub-lemma
  ∂φ = p·φ∂ via PowerSeries.derivative_subst — the §4 A-explicit idiom);
  digits of ∂F are (i·G_i + p·∂G_i); extract digit 0. b7: (1+X) unit-free:
  (1+X)·D = 0 ⟹ D = 0 (domain K⟦X⟧, 1+X ≠ 0); D F = 0 ⟹ all
  (n+1)·coeff_{n+1} = 0 ⟹ coeff_{n+1} = 0 (CharZero K) ⟹ F = C(F 0).
- **Mathlib lemmas**: PowerSeries.derivative_subst (A-explicit!),
  derivativeFun coefficient formula.
- **Sources**: decomposition R6 W6b.
- **Sizing**: ~70 LOC.

### [T608] The ψ-bridge, evaluation layer, and evaluated Eqphipsi
- **Status**: done (2026-06-11) — with a SECOND B2 statement-fix (logged)
- **Progress**: DONE (subagent): mahlerTransform_psi by measure-digit
  transport; sum_seriesEval_mahlerK (the realised integral Eqphipsi) via
  φ-collapse at ξ^j−1 + geom_sum orthogonality + the cyclotomic norm
  ‖ξ^j−1‖ < 1 (Coefficients.IsPrimitiveRoot.norm_sub_one_lt). B2:
  `seriesEval_phi` as skeletonised was FALSE (RHS-summability too weak —
  junk-totalised LHS diverges; b2_log.jsonl appended); EXCISED — the sound
  variants `seriesEval_phi_of_summable_prod` (ℕ×ℕ product Fubini) and
  `seriesEval_phi_at_root` (bounded coefficients) are proven and are what
  downstream consumes. FormalPsi.lean is sorry-free. Axioms standard ×5. | **File**: MeasureR/FormalPsi.lean | **Depends on**: T605, T606
- **Type**: lemmas
- **Statement** (b6 realigned to the INTEGRAL level, replan R6.6):
  `mahlerTransform_psi`, `seriesEval_zero_arg`, `seriesEval_phi`,
  `sum_seriesEval_mahlerK` (Σ_i 𝓐_μ(ξ^i−1) = p·𝓐_{ψμ}(0); summability
  internal — bounded integral coefficients; mahlerK def moved here).
- **Proof sketch**: b4 against the project's measure-ψ (digit-shift): show
  the Mahler transform of ψμ satisfies the digit-0 characterisation —
  φ𝓐_{ψμ} relates to the Mahler of Res_{pℤ_p} (project psi/phi toolbox
  identities) + uniqueness from T605. b5: eval at 0 = constantCoeff
  (tsum_eq_single); eval-of-φ: subst-coefficient expansion + tsum
  rearrangement (T522 master_bridge machinery is the template; reuse its
  helper patterns). b6: evaluate the digit decomposition at ξ^i−1; the
  φ-layer collapses ((1+(ξ^i−1))^p − 1 = 0; eval of φG at these points =
  G(0) by b5); Σ_i ξ^{ij}-orthogonality (mathlib: IsPrimitiveRoot
  geom_sum/orthogonality — verify exact name) leaves p·(digit-0)(0).
  Convergence side-conditions from hconv (finitely many digit-pieces;
  closure of summability under the manipulations).
- **Mathlib lemmas**: IsPrimitiveRoot.geom_sum_eq_zero?? (survey at
  execution), tsum_eq_single.
- **Sources**: decomposition R6 W6b-b6 (replan 2: the only meaningful
  Eqphipsi for unbounded series).
- **Sizing**: ~120 LOC (largest W6b ticket).

### [CLEANUP-63] /cleanup on MeasureR/FormalPsi.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T605, T606, T607, T608
- **Type**: cleanup
- **Progress**: degraded pass: linter green, zero warnings beyond none,
  file sorry-free, lines ≤ 100; per-ticket golf during T605–T608. Tooled
  CLEANUP-FINAL may revisit (one maxHeartbeats site if any — none found).

### [T609] Gauss sums over coprime levels
- **Status**: done (2026-06-11) — with statement-fix (recorded in docstring)
- **Progress**: DONE (subagent + endgame fix in main session): the
  skeleton's χ(D)·η(M)-twists were WRONG for the SPLIT additive character
  (εD·εM)^x — the CRT reindex factors cleanly with NO twist (the standard
  twisted formula is for e^{2πi/DM}; verified on paper per the planning
  note, docstring records it). Proof: CRT ring iso + pointwise character/
  additive-character factorisation + Equiv.sum_comp + sum_product.
  Axioms standard. | **File**: ValuesAtOneComplex.lean | **Depends on**: none
- **Parallel**: yes (chain C6 head) | **Type**: theorem
- **Statement**: skeleton `gaussSum_mul_coprime` (C6-c4).
- **Proof sketch**: CRT reindex (ZMod.chineseRemainder): a ↦ (a mod D,
  a mod M); the additive character zmodChar (εD·εM) splits as the product;
  double-sum factorisation; the χ(D)/η(M) twists arise from the CRT
  normalisation (a = a₁·M·M⁻¹-stuff). ADVERSARIAL note (gate): verify the
  exact unit-twist (χ(D)η(M) vs χ(M)η(D) vs inverses) against Washington
  Lemma 4.1-adjacent BEFORE proving; fix the skeleton statement if off —
  statement-fix allowed pre-ticket-completion with a replan note.
- **Mathlib lemmas**: ZMod.chineseRemainder, gaussSum defs,
  Finset.sum_nbij CRT.
- **Sources**: standard (Washington Ch. 4); decomposition R6 C6-c4.
- **Sizing**: ~60 LOC.

### [T610] Boundary convergence of the logarithm series (SURVEY-GATED)
- **Status**: done (2026-06-11) — with a B2 statement-fix (logged)
- **Progress**: DONE (subagent): the skeleton's HasSum-form is FALSE
  (1/(n+1) not summable on the circle; only conditional convergence) —
  b2_log appended, restated as Tendsto-of-partial-sums
  `tendsto_sum_pow_div_eq_neg_log`. Survey findings (area B): mathlib HAS
  Abel's limit theorem (`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`)
  and the open-disc log Taylor series
  (`Complex.hasSum_taylorSeries_neg_log`); Dirichlet-test partial-sum
  bound done by hand (geom_sum_eq + 2/‖1−z‖); branch-cut continuity via
  slitPlane (Re(1−z) > 0 off z = 1). Axioms standard. | **File**: ValuesAtOneComplex.lean | **Depends on**: none
- **Parallel**: yes | **Type**: theorem
- **Statement**: skeleton `hasSum_pow_div_eq_neg_log` (C6-c2).
- **Proof sketch**: SURVEY FIRST (the binding mathlib-search step):
  Abel's limit theorem / Dirichlet test for Σzⁿ/n on the unit circle.
  Candidates: Mathlib.Analysis.SpecificLimits, abelSummation files,
  `Complex.hasSum_taylorSeries_log` (open-disc version exists).
  If boundary machinery is absent: prove via Dirichlet test (partial sums
  of zⁿ bounded for z ≠ 1 on circle; 1/n monotone → 0) + Abel
  continuity to identify the limit with −log(1−z) — an API-gap sub-leaf
  to spawn per Tier A1 if needed.
- **Sources**: TeX 2040–2044; Washington Thm 4.9.
- **Sizing**: ~60–120 LOC depending on survey.

### [T611] **RJW Theorem 6.1(i)** — the classical value L(θ,1)
- **Status**: DONE (2026-06-11; sorry-free, axiom-clean, blueprint wired) | **File**: ValuesAtOneComplex.lean
- **Depends on**: T609, T610 | **Type**: theorem
- **Statement**: `LSeries_eq_gaussSum_inv_mul_sum`,
  `LFunction_one_eq` (C6-c1/c3).
- **Proof sketch**: c1: Fourier-expand θ(n) = G(θ)/N·Σ_c θ⁻¹(c)ε^{nc}
  (gaussSum_mulShift-family; verify exact mathlib form), swap finite and
  L-series sums (norm-summable for Re s > 1), then G(θ)G(θ⁻¹) = θ(−1)N
  (project T501) to reach the displayed form. c3: LFunction = LSeries for
  Re s > 1 (mathlib LFunction_eq_LSeries); take s → 1 along reals:
  LFunction continuous at 1 (differentiableAt_LFunction, θ ≠ 1); the
  finite c-sum of LSeries-terms converges to the log-values by T610 +
  Abel-limit; identify.
- **Mathlib lemmas**: DirichletCharacter.LFunction_eq_LSeries (verify),
  differentiableAt_LFunction, gaussSum_mulShift.
- **Sources**: TeX 2007–2045 verbatim at R6; Washington Thm 4.9.
- **Blueprint**: §6 chapter — wire Thm 6.1(i) node.
- **Sizing**: TeX 39 lines → ~150 LOC.
- **Progress (2026-06-11, execution)**: Both targets sorry-free; `lake build
  PadicLFunctions` green; `#print axioms` = [propext, Classical.choice,
  Quot.sound] on both + `tendsto_sum_pow_div_eq_neg_log`/`gaussSum_mul_coprime`.
  Linter clean (no warnings); blueprint nodes `val1-classical-gauss-expansion`
  and `val1-classical-s1` wired (lake build PadicLFunctionsBlueprint green).
  Route notes: c1 used `gaussSum_mulShift_of_isPrimitive` (the EXACT mathlib
  Fourier lemma: `gaussSum χ (e.mulShift a) = χ⁻¹ a · gaussSum χ e`), restricted
  the resulting `∑_a over ZMod N` to units (θ⁻¹ kills non-units), and the
  prefactor is `G(θ⁻¹)⁻¹` directly (the split additive char `zmodChar ε`
  needs NO θ(−1) twist — same observation as T609's `gaussSum_mul_coprime`);
  nonvanishing G(θ⁻¹)≠0 via T501 `gaussSum_mul_gaussSum_inv` over ℂ.
  Statement adjustment: `LSeries_eq_gaussSum_inv_mul_sum`'s `hθ1 : θ ≠ 1`
  is genuinely UNUSED (the rearrangement holds for any primitive θ); kept for
  API parity / paper-faithfulness, renamed binder `_hθ1` (docstring note).
  c3 (the real work): mathlib has Abel only for POWER series, none for
  Dirichlet series at the boundary; built helper `tendsto_LSeries_pow_boundary`
  (‖w‖=1, w≠1 ⟹ lim_{s↓1⁺} LSeries(wⁿ) s = −log(1−w)) by summation-by-parts
  representation g(s)=∑' Bₙ₊₁·((n+1)⁻ˢ−(n+2)⁻ˢ) (`Finset.sum_range_by_parts`),
  continuous on [1,2] (`continuousOn_tsum` + MVT majorant `rpow_neg_sub_le`),
  =LSeries for s>1, =−log(1−w) at s=1 via T610. Imports added to the file:
  Interpolation.Characters (T501) + Mathlib.NumberTheory.LSeries.Linearity.

### [CLEANUP-65] /cleanup on ValuesAtOneComplex.lean — done inline during
  execution (degraded MCP: lean-lsp tools unavailable in subagent; used
  `lake env lean` file gate + script search; file is linter-clean and golfed).

### [CLEANUP-65] /cleanup on ValuesAtOneComplex.lean
- **Status**: done (degraded mode, 2026-06-11) | **Depends on**: T611
- **Type**: cleanup
- **Progress**: inline during T609–T611 (file linter-clean, sorry-free,
  golfed); tooled CLEANUP-FINAL may revisit. The Dirichlet-series
  boundary-limit helper `tendsto_LSeries_pow_boundary` is a mathlib-PR
  candidate (recorded).

### [T612] Norm-one arguments and the formal log-derivative
- **Status**: done (2026-06-11)
- **Progress**: DONE (subagent): norm-1 via the project's existing
  IsPrimitiveRoot.norm_pow_sub_one_eq_one (Coefficients.lean — the
  cyclotomic-product argument was already formalised); log-derivative by
  the geometric-inverse factorisation (1+T)Cu−1 = C(u−1)(1+C(u/(u−1))T).
  Axioms standard.
- **Parallel**: yes (chain P6 head) | **Type**: lemmas
- **Statement**: skeleton `norm_one_sub_pow_eq_one`,
  `one_add_mul_derivative_logSeriesAt` (P6-p9/p2).
- **Proof sketch**: p9: Π_{c∈(ℤ/D)ˣ}(1−ε^c) = Φ_D(1) (mathlib cyclotomic
  eval: X^D−1 = Π(X−ε^c)-factorisation over K + eval at 1;
  eval_one_cyclotomic_prime / _not_prime_pow family — survey exact names);
  ‖Φ_D(1)‖ = 1 (1 or a prime q ≠ p); each factor norm ≤ 1
  (integral elements / ball), product = 1 forces each = 1 (ultrametric).
  p2: coefficient-wise: ∂(logSeriesAt) coefficients telescope against the
  geometric series of ((1+T)u−1)⁻¹ = (u−1)⁻¹·Σ(−u/(u−1))ⁿTⁿ-form
  (Ring.inverse of unit-constant-term series; finite verification per
  coefficient).
- **Sources**: TeX 2102–2105; decomposition R6 P6.
- **Sizing**: ~100 LOC.

### [T613] ∂F̃_θ = F_θ
- **Status**: done (2026-06-11)
- **Progress**: DONE (same pass): linearity + per-c P6-p2 + character-sum
  cancellation (MulChar.sum_eq_zero_of_ne_one + range↔ZMod reindex).
  Axioms standard.
- **Type**: theorem
- **Statement**: skeleton `one_add_mul_derivative_Ftilde` (P6-p3).
- **Proof sketch**: sum p2 over c; the constant `1`-terms contribute
  −Σ_c θ⁻¹(c)·1 = 0 (sum of a nontrivial character — mathlib
  DirichletCharacter sum_eq_zero; verify name; note the sum is over
  range N with θ⁻¹ killing non-units).
- **Sources**: TeX 2100–2110 (Lem 6.3 proof, first display).
- **Sizing**: ~50 LOC.

### [T614] ρ_θ: support, x-multiplication, and the twist display
- **Status**: done (2026-06-11)
- **Progress**: DONE (same pass): psi∘iota = 0 via mem_range_iota_iff;
  x-multiplication via invUnitsCM-cancellation (extendByZero_comp_unitsVal)
  + mahlerTransform_cmul_X (del K) + map-∂ commutation helpers. hGtwist
  instantiation deferred to T617 assembly (hypothesis-form retained).
  Axioms standard.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `psi_rhoTheta`,
  `one_add_mul_derivative_mahlerK_rhoTheta` + NEW (spawn at execution):
  the hGtwist-instantiation lemma (mahlerK of the χ-twisted μ̃_η equals
  the explicit G-cleared series — from T508's
  mahlerTransform_charTwist_muEtaCleared, CRT-collapsed to level Dp^n).
- **Proof sketch**: support: iota-image is unit-supported
  (res_iota/mem_range_iota_iff + isSupportedOn_units_iff_psi_eq_zero);
  ∂𝓐: x·ρ = Res(μ_θ) by invCM-cancellation on units
  (extendByZero/invUnitsCM algebra, the §5 T516/T520 patterns) +
  LemmaMultiplicationbyx = mahlerTransform_cmul_X; map-subtype the
  identity. hGtwist: T508 display + the Σ_aΣ_b → Σ_c CRT collapse with
  ε := ζK·εp-product-root (the c4-twist constants surface; coordinate
  with T609's conventions).
- **Sources**: TeX 2090–2110 (Lem 6.3); decomposition R6 P6.
- **Sizing**: ~140 LOC (the §5-glue ticket).

### [CLEANUP-66] /cleanup on ValuesAtOne.lean (cadence)
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T612, T613, T614
- **Type**: cleanup
- **Progress**: subsumed by the continuous per-ticket golf through
  T615–T617 and the CL67 final sweep (same file; build green, zero
  warnings, zero long lines verified 2026-06-12). Tooled CLEANUP-FINAL
  carries the per-decl golf queue.

### [T615] The constant pin: 𝓐(ρ_θ) = F̃_θ − φψF̃_θ
- **Status**: done (2026-06-11; hnorm hypothesis added — logged)
- **Depends on**: T613, T614, T607, T606 | **Type**: theorem
- **Statement** (REALIGNED R6.6, c₀-design):
  `p_mul_constantCoeff_mahlerK_rhoTheta` — p·𝓐_ρ(0)·G-form =
  p·F̃(0) − Σ_i F̃(ξ^i−1); via W := CG⁻¹F̃ − 𝓐_ρ, ∂W = φB,
  antiderivative + ker∂ + ξ-point evaluation + sum_seriesEval_mahlerK
  + psi_rhoTheta.
- **Proof sketch**: both sides ∂-agree (T613 + T614 + ψ∂-commutation b3
  pushing ∂ through φψ: ∂(φψF̃) = p·φ(∂ψF̃) = φψ(∂F̃)); difference D has
  (1+X)·derivative(D) = 0 ⟹ D = C(D₀) (b7); ψ(LHS) = 0 (T614-support +
  b4-bridge + psiSeries_map), ψ(RHS) = 0 (ψφ = id, b2), ψC = C (b2) ⟹
  D₀ = 0. The G-clearing scalar rides along via psiSeries_C_mul.
- **Sources**: decomposition R6 replan 1 (the distribution-free Lem 6.3).
- **Sizing**: ~80 LOC.

### [T616] The evaluated trace of F̃_θ
- **Status**: done (2026-06-12; statement-fix hdom→hnorm logged; boundary-log prerequisite = T618)
- **Depends on**: T608, T603, T604, T612 | **Type**: theorem
- **Statement** (REALIGNED R6.6, ψ-free): `sum_seriesEval_Ftilde` —
  Σ_i F̃(ξ^i−1) = θ(p)·F̃(0); cases as before.
- **Proof sketch**: b6 (psiSeries_eval_zero) on F̃: need seriesEval F̃ at
  ξ^i−1: per-c resummation Ftilde_eval (spawn as helper): seriesEval of
  logSeriesAt(u) at z = extLog((1+z)u−1) via (1+z)u−1 = (u−1)(1+uz/(u−1)),
  extLog_mul (T604), extLog-on-ball = padicLog + its series (T522/T604);
  then Σ_i Σ_c θ⁻¹(c)extLog(ξ^i ε^c−1): μ_p-collapse
  Σ_i extLog(ξ^iw−1) = extLog(w^p−1) (Π_i(ξ^iw−1) = w^p−1: Π over μ_p +
  Πξ^i = 1 for p odd; extLog_mul; domains by T603 + p9-norm-ones);
  c-bookkeeping: n = 0: c ↦ pc automorphism of (ℤ/D)ˣ pulls θ(p) out;
  n ≥ 1: fibers of c ↦ pc are N/p-translates; inner sum
  Σ_{j<p} θ⁻¹(c+jN/p) = 0 by primitivity (spawn small lemma
  sum_shift_eq_zero_of_isPrimitive per replan 3); both sides 0 = θ(p)·…
- **Sources**: TeX 2115–2155 (the two-case proof); decomposition R6
  replans 2–3.
- **Sizing**: ~150 LOC (the section's hardest ticket).

### [CLEANUP-ALL-6] Pre-milestone /cleanup-all
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T601–T616
- **Type**: cleanup-all
- **Progress**: degraded sweep over the four §6 files: zero warnings,
  zero long lines, single remaining sorry = T617 headline. Per-ticket
  golf was continuous; tooled CLEANUP-FINAL queued.

### [T617] **MILESTONE: RJW Theorem 6.1(ii)** — L_p(θ,1) (Leopoldt)
- **Status**: done (2026-06-12) | **Verification**: `lake build PadicLFunctions`
  green (3660 jobs); `#print axioms LpFunction_one` = {propext, Classical.choice,
  Quot.sound}; zero sorries project-wide; linter clean (≤100-char); blueprint green.
- **Depends on**: T615, T616, T609, CLEANUP-ALL-6 | **Type**: theorem
- **Statement**: `LpFunction_one` (P6-p8), proven sorry-free.
- **Proof sketch**: LpFunction at s = 1 pairs ζ_η-cleared with χ̃·⟨x⟩⁰ = χ̃;
  identify the pairing with the mass of ρ_θ (extendByZero/χ̃-through
  lemma); mass = constantCoeff(𝓐_ρ) (apply_powCM 0); T615 + T616 give
  (1−θ(p)p⁻¹)·F̃(0) up to G-clearing; F̃(0) = −Σθ⁻¹(c)extLog(ε^c−1) =
  −Σθ⁻¹(c)extLog(1−ε^c) (extLog_neg, domains T603); un-clear through
  T609 (G(θ⁻¹)-factorisation) to RJW's display.
- **Sources**: TeX 1992–1995 + 2113–2155 (verbatim at R6).
- **Progress (2026-06-12, COMPLETE)**:
  - **Statement-fix (authorised, recorded in b2_log.jsonl)**: added
    `{εp : integerRing K} (hεp : IsPrimitiveRoot εp (p^n))
    (hsplit : ε = (ζ:K)·(εp:K))` — the §6 root ε is tied to the §5 split data
    (RJW's ε_N is any primitive N-th root; the split form ζ·ε_{p^n} realises it
    through the tame/wild factors). This is what enables the Gauss-product split.
  - **G-clearing as landed (the step-3 key)**: the headline G = G(θ⁻¹) is NOT a
    unit in integerRing K (its norm is p^{-n/2}); it is a K-field nonzero, hence
    a K-unit. The hGtwist hypothesis of T615 is fed G₀ := GχK := the K-coercion
    of the level-p^n Gauss sum (also a K-field nonzero). The hGtwist closed form
    `mahlerK(twist χ̃ μ̃η) = C(GχK⁻¹)·(−Σ_{c<N} C(θK⁻¹ c)·inv((1+X)C(ε^c)−1))`
    is built in three steps: (3a) integerRing closed form of GχR•𝓐(twist) via
    `mahler_twist_formula` + `mahlerTransform_charTwist_muEtaCleared`; (3b) map to
    K (c=0 rows killed by η⁻¹(0)=0; c≠0 inverse-map via
    `isUnit_root_mul_pow_one_add_X_sub_one`); (3c) CRT-collapse the (b,c) double
    sum to range N at the glued root via the new private `crt_collapse`. The final
    G-product G = GηK·GχK is `gaussSum_mul_coprime` (ValuesAtOneComplex, general
    domain R = K) at the split root + `coe_gaussSum_zmodChar` ×2.
  - **New helpers**: `crt_collapse` (the §6 step-3c double-sum CRT collapse, via
    ZMod reindex + ZMod.chineseRemainder + θ⁻¹ factorisation + root period-split);
    `toFieldChar_changeLevel` (toFieldChar/changeLevel commutation). Added import
    `PadicLFunctions.ValuesAtOneComplex` (no circularity).
  - **hnorm discharge**: `norm_pow_sub_one_eq_one_of_unit` (T612 cluster, already
    in file). Sign flip via `extLog_neg` + `extLogDomain_of_integral_norm_one`.
- **Blueprint**: §6 chapter — wired `val1-padic-s1` → `LpFunction_one` (D>1 +
  distribution-free + split-root notes); `val1-x-mu-tilde` →
  `one_add_mul_derivative_Ftilde` (distribution-free ∂F̃=F note + companion
  `one_add_mul_derivative_mahlerK_rhoTheta`); `val1-Ftilde-in-Rplus` left unwired
  with the R6.6 coefficient-bound rationale (`summable_seriesEval_Ftilde`).
- **Sizing**: ~310 LOC (incl. crt_collapse + hGtwist chain; ~120 estimated, the
  full CRT collapse cost more).

### [CLEANUP-67] Final per-file cleanups (§6 files)
- **Status**: done (degraded mode, 2026-06-12) | **Depends on**: T617
- **Type**: cleanup (ExtLog, FormalPsi, ValuesAtOne[Complex] final;
  CLEANUP-FINAL scope widened to §6)
- **Progress**: degraded sweep: build green, zero warnings, zero long
  lines, zero sorries project-wide. Queued for tooled CLEANUP-FINAL:
  per-decl golf of the §6 files (esp. T617's crt_collapse ~310 LOC —
  /decompose-proof candidate), the T618 bridge-layer placement review
  (boundary-log lemmas live in ValuesAtOne.lean for import-graph reasons —
  consider a dedicated file when ValuesAtOne approaches the split
  threshold).

## §6 dependency quick-view
```
W6a: T601 → T604 ;  T602 → T603         → CL61
W6b: T605 → T606 → {T607, T608}         → CL63
C6:  T609 ; T610 → T611                 → CL65
P6:  T612 → T613 ; T614 → CL66 → T615(T607,T606)
     T616(T608,T603,T604,T612) → CLALL6 → T617*(T615,T616,T609) → CL67
```
Gate note: decomposition R6 is at draft-1 — per-leaf attack-blocks in the
binding format and the c2/c4-survey completions are folded into each
ticket's execution preamble (the §5 T521-precedent); the route-level
attacks that already fired are recorded in R6 (replans 1–5).

### [T618] Boundary p-adic logarithm (unit-ball multiplicativity)
- **Status**: done (2026-06-12)
- **Progress**: DONE (subagent): formalLog + ∂-pin φ(L) = p•L (3-line
  ker-∂ argument as planned); eval-alignment seriesEval formalLog (z−1) =
  padicLog z; padicLog_pow_p via the subst-eval product-Fubini bridge;
  unit-ball padicLog_mul by p-power descent; extLog_eq_padicLog on the
  whole open ball. Bridge lemmas live in ValuesAtOne.lean (import-graph
  meeting point — placement note recorded). Axioms standard. | **File**: PadicExp.lean (+ ExtLog.lean bridge)
- **Depends on**: T522, T607, T608 | **Parent**: T616 | **Type**: lemmas
- **Statement**: `formalLog : PowerSeries K` (coeffs 0, (−1)^{n−1}/n);
  `one_add_mul_derivative_formalLog : (1+X)·D(formalLog) = 1`;
  `phiSeries_formalLog : phiSeries p formalLog = (p:K) • formalLog`
  (∂-match via one_add_mul_derivative_phiSeries + ker-∂ pin);
  `seriesEval_formalLog : ‖z−1‖ < 1 → seriesEval formalLog (z−1) = padicLog z`
  (series alignment); `padicLog_pow_p_of_norm_lt_one : ‖z−1‖ < 1 →
  padicLog (z^p) = p • padicLog z` (eval the formal identity via
  seriesEval_phi_of_summable_prod, linear-growth summability);
  `padicLog_mul_of_norm_lt_one` (p-power descent to the exp-ball, T522's
  padicLog_mul, torsion-free cancel); `padicLog_pow_of_norm_lt_one`;
  `extLog_eq_padicLog_of_norm_lt_one` (descent witness (p^j,0,x^{p^j})).
- **Proof sketch**: as in the Statement field — all tools exist after
  T605–T615 (recorded route, parent T616's flag 2026-06-11/12).
- **Mathlib lemmas**: existing project API only.
- **Sources**: Washington §5.1 (log on the unit ball); decomposition R6.6.
- **Generality**: K-coefficients (the ambient); padicLog-statements over
  the PadicExp L when free.
- **Sizing**: ~80–120 LOC (toolkit exists).

---

# §7 board (The residue of ζ_p at s = 1; TeX 2181–2360) — created 2026-06-12

Skeleton: PadicLFunctions/ResidueZeta.lean (13 sorries), build green.
Decomposition: decomposition.md R7 (verbatim quotes + replans 1–4).
Statements live in the skeleton; the §6 statement-fix protocol applies.

### [T701] Exponential tail and the character isometry
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: none
- **Progress**:
  - 2026-06-12: both decls proven (subagent, batched with T702). Tail bound came
    out cleaner than sketched: per-term `(p−1)`-power comparison via
    `norm_factorial_inv_smul_pow_le` + `p·(p·‖w‖^{p−1})^{n−2} ≤ p ≤ p^{p−1}`
    (helper `norm_factorial_inv_smul_pow_le_quad`); tail by
    `IsUltrametricDist.norm_tsum_le_of_forall_le` after peeling n∈{0,1} with
    `Summable.tsum_eq_zero_add` ×2. Isometry exactly per sketch (T523 bridge +
    `norm_padicExp_sub_one` + `norm_padicLog`). Verified: build green, axioms
    standard 3. Cleanup: degraded mode (no lean-lsp MCP) — code reviewed, calc
    structure clean; defer golf to CLEANUP-71.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `norm_padicExp_sub_one_sub_self_le`,
  `norm_onePAdicPow_sub_one` (R7.1a/b).
- **Proof sketch**: tail: peel n ∈ {0,1} of the exp series
  (tsum_eq_zero_add ×2, the T521 patterns), bound the n ≥ 2 terms at the
  (p−1)-power level ((‖(n!)⁻¹‖·‖w‖^{n−2})^{p−1} ≤ p^{n−1}·p^{−(n−2)} = p,
  then a^{p−1} ≤ p ⟹ a ≤ p since p ≥ p^{1/(p−1)}: cleanest rpow-free:
  a^{p−1} ≤ p ≤ p^{p−1} ⟹ a ≤ p by pow-mono) + ultrametric tail-max
  (norm_tsum_le_of_forall_le). Isometry: onePAdicPow y t =
  pZpExp(t·pZpLog y) (T523 padicExp_smul_padicLog_eq_onePAdicPow at s := t
  — mind the argument order: pZpExp p (t * pZpLog p y)), then coe-norms +
  norm_padicExp_sub_one (ball: ‖t·log y‖ ≤ ‖y−1‖ ≤ p⁻¹, p odd strict) +
  norm_padicLog through pZpLog_coe; multiplicativity of the padic norm.
- **Sources**: TeX 2236–2248 (the binomial route it replaces — replan R7.3);
  Washington §5.1.
- **Sizing**: ~90 LOC.

### [T702] The branch denominator: primitivity, nonvanishing, derivative
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: T701
- **Progress**:
  - 2026-06-12: all three decls proven (subagent, batched with T701).
    Primitivity via `orderOf_map_dvd` against `unitsToZModPow p 1` (level-1
    reduction has order p−1 by hgen; `ker_toZModPow` + `teichmullerFun_sub_self_mem`
    identify the reductions). Nonvanishing: helper
    `norm_teichmuller_pow_sub_one_eq_one` (`norm_lt_one_iff_dvd` contrapositive)
    + ultrametric isoceles `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.
    Derivative limit: NO case split on L = 0 needed — the squeeze
    `‖f(s)+L‖ ≤ p·‖L‖²·‖s−1‖ → 0` (via T701a) covers it uniformly;
    `squeeze_zero_norm'` + `linear_combination` for the pointwise identity.
    Verified: build green, axioms standard 3. Cleanup: degraded mode, defer to
    CLEANUP-71.
- **Type**: lemmas
- **Statement**: skeleton `teichmuller_isPrimitiveRoot`,
  `branch_denom_ne_zero`, `tendsto_branch_denom_div` (R7.2a/b/c).
- **Proof sketch**: a: hgen at n = 1 gives u mod p generates (ZMod p)ˣ
  (order p−1); ω(u)'s order = order of the reduction (toZMod_teichmullerZMod
  section + injectivity of teichmullerZMod on its image — the
  exists_primitiveRoot_card_sub_one proof in Branches is the template).
  b: branchChar i s u − 1 = ω(u)^i⟨u⟩^s − 1 = (ω^i − 1) + ω^i(⟨u⟩^s − 1);
  ‖ω^i − 1‖ = 1 (i < p−1, primitivity: the reduction ω̄^i = ū^i ≠ 1 in
  ZMod p ⟹ norm-1 via the residue argument), ‖⟨u⟩^s − 1‖ ≤ p⁻¹ < 1
  (onePAdicPow_sub_one_mem) ⟹ isoceles norm = 1 ≠ 0; coe to ℚ_[p].
  c: ω(u)^{p−1} = 1 (teichmullerFun_pow_card_sub_one) so the denominator
  is ⟨u⟩^{1−s} − 1 = pZpExp((1−s)·L) − 1 with L := pZpLog⟨u⟩ (T523);
  write (s−1)⁻¹(exp(w)−1) with w := (1−s)L = −(s−1)L:
  = −L·[w⁻¹(exp w − 1)] and w⁻¹(exp w −1) → 1 by T701a (ε-δ: ‖w⁻¹(exp w − 1)
  − 1‖ = ‖w‖⁻¹‖exp w − 1 − w‖ ≤ p‖w‖ → 0 as s → 1; w ≠ 0 iff s ≠ 1 and
  L ≠ 0 — case L = 0: ⟨u⟩ = 1 forces the limit statement trivially?? NO:
  if L = 0 then denominator ≡ 0 and the limit claim says → 0 ✓ both sides
  0 — handle the L = 0 case separately (limit of 0-function = −0 ✓);
  coe-bookkeeping ℤ_[p] → ℚ_[p] (continuous ring hom).
- **Sources**: TeX 2218–2256 verbatim at R7; replan R7.3.
- **Sizing**: ~130 LOC.

### [T703] Continuity of the numerator and Theorem 7.1(i)
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: T702
- **Progress**:
  - 2026-06-12: both decls proven (subagent). Congruence route exactly per
    sketch, p = 2 allowed: helpers `onePAdicPow_sub_one_mem_span_pow`
    (exponent congruence via `AddChar.map_nsmul_eq_pow` +
    `dvd_sub_pow_of_dvd_sub`) and `norm_onePAdicPow_sub_one_le`
    (p=2-valid `‖y^t−1‖ ≤ ‖t‖`); pairing is `LipschitzWith 1` via
    `PadicMeasure.norm_apply_le`. Thm 7.1(i) = `ContinuousAt.inv₀` +
    `branch_denom_ne_zero` + pairing continuity. New import:
    Mathlib.NumberTheory.Basic. Verified: build green, axioms standard 3.
    Cleanup: degraded mode (no MCP), unused bindings removed; defer golf to
    CLEANUP-71.
- **Type**: lemmas
- **Statement**: skeleton `continuous_zetaNum_branch_pairing`,
  `continuousAt_zetaPBranch` (R7.3a + Thm (i)).
- **Proof sketch**: pairing: Metric/ε-route: for s ≡ s' mod p^m the
  integrands agree mod p^m uniformly: branchChar i (1−s) x −
  branchChar i (1−s') x = ω^i⟨x⟩^{1−s'}(⟨x⟩^{s'−s} − 1) with
  ⟨x⟩^{s'−s} − 1 ∈ span{p^m} (onePAdicPow_sub_one_mem_pow at the
  difference, T519) ⟹ ‖f_s − f_{s'}‖_sup ≤ p^{−m}; the §3 measure norm
  bound (PadicMeasure.norm_apply_le — verify exact name; the §3 board
  had it) gives ‖pairing(s) − pairing(s')‖ ≤ ‖zetaNum‖·p^{−m}; coe
  continuous. Thm (i): zetaPBranch is the quotient; numerator continuous
  (pairing-lemma at the §4 generator m), denominator continuous
  (same congruence bound on s ↦ branchChar-at-u) and ≠ 0 everywhere near 1
  (T702b) ⟹ ContinuousAt of the product/inverse (the dite-free def:
  zetaPBranch = (denom)⁻¹·num: Continuous.inv₀-route at s = 1).
- **Sources**: TeX 2228–2231 ("This already implies Theorem 7.1(i)").
- **Sizing**: ~100 LOC.

### [CLEANUP-71] /cleanup on ResidueZeta.lean (cadence)
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T701, T702, T703 | **Type**: cleanup
- **Progress**: 2026-06-12: degraded pass (no lean-lsp MCP this session): full
  read-through of lines 36–430; build green with project linter set; helpers
  well-factored (`norm_factorial_inv_smul_pow_le_quad`,
  `norm_teichmuller_pow_sub_one_eq_one`, `onePAdicPow_sub_one_mem_span_pow`,
  `norm_onePAdicPow_sub_one_le` — all private, all docstringed); no unused
  hypotheses; calc structure idiomatic. No edits needed. Tooled re-pass folded
  into CLEANUP-FINAL scope.

### [T704] The antiderivative F̃_a and ∂F̃_a = F_a
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: none
- **Progress**:
  - 2026-06-12: statement defects found in pre-dispatch review and fixed per
    protocol (2 b2_log entries): `one_add_mul_derivative_FtildeA` += `ha : ¬p∣a`
    (Fa is junk 0 when p∣a; counterexample a = p) and `constantCoeff_FtildeA`
    += `ha0 : a ≠ 0` (uA 0 = 0 breaks HasSubst). Both then proven (subagent):
    constant coeff via `PowerSeries.constantCoeff_subst_eq_zero`; derivative by
    multiply-by-G := (1+X)^a−1 + `mul_right_cancel₀` in the domain K⟦X⟧,
    `derivative_subst` chain rule, Step A `natCast_smul_uA_eq_map_geomSum`
    (a•u_a = mapped geomSum), Step B `uA_mul_subst_derivative_formalLog`
    (u_a·(∂L∘(u_a−1)) = 1), RHS collapsed by `one_add_X_pow_sub_one_mul_Fa`.
    6 private helpers. Verified: build green, axioms standard 3. Cleanup:
    degraded mode, defer golf to CLEANUP-ALL-7.
- **Parallel**: yes (mass-chain head) | **Type**: def-lemmas
- **Statement**: skeleton `constantCoeff_FtildeA`,
  `one_add_mul_derivative_FtildeA` (R7.4c/d; defs uA/FtildeA in skeleton).
- **Proof sketch**: constant: coeff-0 extraction (subst at constant-0
  argument has constantCoeff = formalLog(0) = 0: constantCoeff_subst-route
  or coeff_subst' at 0; smul-part 0). Derivative: ∂ is additive;
  ∂(C) = 0; ∂(formalLog∘(uA−1)) via derivative_subst (chain rule) +
  one_add_mul_derivative_formalLog-shape: (1+X)·D(L∘G) where ∂L = 1:
  compute (1+X)D(L.subst G) = (DL).subst G · (1+X)DG = [(1+(uA−1))⁻¹-free?
  — careful: ∂L = 1 means (1+X)·DL = 1 i.e. DL = (1+X)⁻¹: (DL).subst G =
  Ring.inverse(1 + G-shifted)... work it: (1+X)·D(L∘(uA−1)) =
  Ring.inverse(uA)·(1+X)·D(uA) (the log-derivative); ∂((a−1)•L) = (a−1)•1.
  Target Fa: verify PadicMeasure.Fa's exact closed form (MuA.lean: Fa :=
  FaNum-based — READ; RJW: F_a = 1/T − a/((1+T)^a−1); with
  (1+T)^a − 1 = aT·uA: a/((1+T)^a−1) = T⁻¹·uA⁻¹: F_a =
  T⁻¹(1 − uA⁻¹) — honest series ✓); the identity reduces to
  uA-algebra: (1+X)·D(F̃) = (a−1) − inverse(uA)·(1+X)·D(uA) ≟ map(Fa):
  per RJW's Lemma 7.3 computation; expect ~80 LOC of series algebra
  (geometric-inverse helpers from T612 reusable).
- **Sources**: TeX 2266–2279 + 2296–2305 verbatim at R7.
- **Sizing**: ~120 LOC.

### [T705] The measure ρ_a: support and x-multiplication
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: none
- **Progress**:
  - 2026-06-12: both decls proven (subagent), statements verbatim. psi_rhoA in
    2 lines (`isSupportedOn_units_iff_psi_eq_zero` + `baseChange_res` +
    `res_iota`) — the planned ψ∘baseChange naturality lemma was NOT needed
    (support-route cleaner than transform-route). x-mult via new private
    `cmul_mahler_one_iota_zetaNum` (ℤ_p-level x·ι(zetaNum) = Res μ_a, T614's
    invCM-cancellation pattern) + `baseChange_cmul`/`algCM_mahler`/
    `baseChange_res` + the T614 transform transport (locally re-proven private
    `map_derivativeFun'`/`map_one_add_mul_derivativeFun'`). Orchestrator fixed
    4 long-line lints in T704 code post-hoc. Verified: build green, axioms
    standard 3. Cleanup: degraded mode, defer to CLEANUP-ALL-7.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `psi_rhoA`, `one_add_mul_derivative_mahlerK_rhoA`
  (R7.5b/c; def rhoA in skeleton).
- **Proof sketch**: support: iota-image is unit-supported at the §4 level
  (Measure/UnitsZp's res_iota/mem-range machinery — the ℤ_[p]-precursors
  of the MeasureR ones); transport through baseChange: need
  ψ∘baseChange = baseChange∘ψ (NEW small naturality lemma — the TW6 notes
  deferred it; prove via mahlerTransform_baseChange + mahlerTransform_psi
  + injectivity of the Mahler transform (mahlerRingEquiv), ~30 LOC) — or
  directly: ψ(baseChange(iota ν)) = 0 via the transform-route. x-mult:
  x·zetaNum = muAUnits at the §4 level (zetaNum := unitsCmul invCM
  muAUnits: x·(x⁻¹·μ) = μ — the unitsCmul-algebra, the T614 pattern at
  ℤ_[p]-level); iota∘(units-measure) vs res∘(ℤ_p-measure):
  iota(muAUnits) = res units (muA) (the §4 relation — survey ZetaP/MuA
  for it; muAUnits := res-to-units of muA presumably definitional);
  baseChange is a ring hom commuting with the transform
  (mahlerTransform_baseChange); del/derivative transport as in T614
  (map_derivativeFun helpers exist in ValuesAtOne — may need export or
  re-prove locally).
- **Sources**: TeX 2258–2264; ZetaP.lean (zetaNum def).
- **Sizing**: ~110 LOC.

### [T706] The mass identity (c₀-pin + trace)
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean
- **Depends on**: T704, T705 | **Type**: theorems
- **Orchestrator replan (route refinement for R7.6b)**: the trace avoids
  ExtLogDomain(ξ^i−1) and the i↦ai reindex: per-point
  F̃_a(ξ^i−1) = −extLog a − padicLog(u_i) (torsion kills the (a−1)·log ξ^i
  term), u_i := seriesEval (uA) (ξ^i−1) with a·(ξ^i−1)·u_i = ξ^{ai}−1
  (evaluated Step A); then Π_{i≠0} u_i = a^{−(p−1)} (the two μ_p-products
  cancel as multisets via i↦ai), padicLog-of-product splits
  (`padicLog_mul_of_norm_lt_one`), and Fermat a^{p−1} ≡ 1 mod p +
  `extLog_eq_of_witness` (m = p−1, k = 0) give Σ_{i≠0} padicLog u_i =
  −(p−1)·extLog a; total −p·extLog a + (p−1)·extLog a = −extLog a ✓.
  New infrastructure: seriesEval∘subst bridge for formalLog∘G (G integral
  coeffs, c₀ = 0): seriesEval ((formalLog).subst G) z =
  padicLog(1 + seriesEval G z) — Fubini swap, master_bridge's pattern
  (PadicExp.lean:690) at K-level. Split into two dispatches (A: c₀-pin;
  B: bridge + trace + combination).
- **Progress**:
  - 2026-06-12 (dispatch A): `p_mul_constantCoeff_mahlerK_rhoA` proven —
    T615-template minus G-clearing; M-bridge `mahlerK_baseChange_muA`
    (mahlerK∘baseChange = map M ∘ mahlerTransform, rfl at the codRestrict);
    new FtildeA coefficient/summability stack (11 private helpers);
    de-privated `MeasureR.exists_antideriv_bounded` (authorized).
  - 2026-06-12 (dispatch B): `sum_seriesEval_FtildeA` +
    `constantCoeff_mahlerK_rhoA` proven. The subst-eval bridge
    `seriesEval_subst_formalLog` landed (Summable.tsum_comm Fubini, K-level
    master_bridge); product collapse via Finset.prod_nbij' through ZMod p
    (mul-by-a bijection) — NOT nthRootsFinset; Σ log u_i =
    log Π u_i = −log a^{p−1} (Fermat `ZMod.pow_card_sub_one_eq_one`) and
    `extLog_eq_of_witness` (m = p−1, k = 0) finishes. 18 more private
    helpers. All three decls: build green, axioms standard 3. Cleanup:
    degraded mode (no MCP), defer to CLEANUP-ALL-7.
- **Statement**: skeleton `p_mul_constantCoeff_mahlerK_rhoA`,
  `sum_seriesEval_FtildeA`, `constantCoeff_mahlerK_rhoA` (R7.6a/b/c).
- **Proof sketch**: pin: T615's proof VERBATIM minus the G-clearing
  (W := F̃_a − 𝓐ρ_a; ∂W = φψ-part via T704+T705 and res_units_eq;
  antiderivative + ker-∂ + ξ-point evaluation + sum_seriesEval_mahlerK +
  psi_rhoA; summability of seriesEval F̃_a from the log-growth coefficient
  helpers (T615/T616's summable-machinery — uA-coefficients are integral
  (a⁻¹C(a,n+1) ∈ ℤ_p for p∤a: a unit in ℤ_p... over K: bounded by
  ‖a⁻¹‖ = 1) + formalLog's 1/n). Trace: per-point seriesEval F̃_a (ξ^i−1)
  = −extLog(a) − extLog(uA-eval at ξ^i−1)-resummation + (a−1)·padicLog(ξ^i)
  -part: CAREFUL — formalLog∘(uA−1) evaluated at ξ^i−1: the subst-eval
  bridge (seriesEval_phi_of_summable_prod-pattern but for the uA-subst:
  general subst-eval — survey what T616 built: seriesEval_logSeriesAt-
  machinery; may need a small general lemma seriesEval-of-subst at
  convergence, the T618 toolkit shapes); then the algebra: F̃_a(ξ^i−1) =
  log of [(ξ^i−1)/(ξ^i·... the RJW per-ξ rearrangement TeX 2330–2340:
  F̃_a((1+T)ξ−1)|_{T=0} = log((ξ−1)/(ξ^a−1)·ξ^{a−1})-values via extLog
  (domains: ξ^j−1 norm-known (FormalPsi's norm_sub_one_lt-machinery) +
  roots-of-unity integrality — the T616-pattern helpers); Σ_i: collapse
  Σ_i extLog(ξ^i−1) − Σ_i extLog(ξ^{ai}−1) + (a−1)Σ_i extLog(ξ^i):
  third sum = 0 (torsion); first two cancel by the {ξ^a} = μ_p reindex
  (i ↦ ai mod p bijection, p∤a) EXCEPT the i = 0 terms — careful:
  i = 0: F̃_a(0) = −extLog(a) ✓ included in the Fin p-sum: total =
  −extLog(a) + [Σ_{i≠0}(extLog(ξ^i−1) − extLog(ξ^{ai}−1)) = 0 by
  reindex] + 0 = −extLog(a) ✓ matches R7.6b. Combine: c₀-identity +
  trace + constantCoeff_FtildeA ⟹ R7.6c (field algebra, (p:K) ≠ 0).
- **Sources**: TeX 2320–2352 verbatim at R7.
- **Sizing**: ~200 LOC (the section's largest).

### [T707] Descent: the ℚ_p-level mass
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean | **Depends on**: T706
- **Progress**:
  - 2026-06-12: `zetaNum_one` proven (subagent), statement verbatim. K := ℂ_[p]
    via new imports Mathlib.NumberTheory.Padics.Complex +
    RootsOfUnity.AlgebraicallyClosed; ξ from
    `HasEnoughRootsOfUnity.exists_primitiveRoot` (IsSepClosed instance).
    Mass identification `constantCoeff_mahlerK_rhoA_eq_algebraMap`
    (coeff_mahlerTransform + baseChange_algCM + mahler 0 = 1 + iota at 1);
    extLog transport `map_extLog_natCast` via `map_padicLog`
    (IsClosedEmbedding.map_tsum along the isometric embedding) + the Fermat
    witness at both levels; descent by field-hom injectivity. Verified:
    build green, axioms standard 3. Cleanup: degraded mode, defer to
    CLEANUP-ALL-7.
- **Survey gate (orchestrator, PASSED)**: mathlib PadicComplex pack complete —
  NormedField ℂ_[p] (Complex.lean:184), NormedAlgebra ℚ_[p] ℂ_[p] (used by
  :199), IsUltrametricDist (:199), CharZero (:242), IsAlgClosed (:246),
  CompleteSpace via UniformSpace.Completion; norm_extends' (:195) for the
  isometry. ξ from IsAlgClosed/HasEnoughRootsOfUnity. No fallback needed.
- **Type**: theorem
- **Statement**: skeleton `zetaNum_one` (R7.7).
- **Proof sketch**: instantiate K := ℂ_[p] (mathlib PadicComplex:
  SURVEY-GATED — verify NormedField/NormedAlgebra ℚ_[p]/IsUltrametricDist/
  CompleteSpace/CharZero instances + obtain ξ from PadicAlgCl's
  algebraically-closed primitive root mapped along the embedding with
  IsPrimitiveRoot.map; FALLBACK if any instance is missing: state the
  K-pack as hypotheses on a wrapper lemma and instantiate in a later
  ticket — record). Identify: the K-coe of the ℚ_p-mass =
  constantCoeff(mahlerK ρ_a) (mass = apply at powCM 0 = the §4 pairing
  at 1 via baseChange_algCM-characterisation/iota-unfold + apply_powCM);
  R7.6c gives the K-value −(1−p⁻¹)·extLog((a:K)); extLog commutes with
  the embedding ℚ_[p] → K on the rational-valuation domain
  (`algebraMap_extLog` helper: the witness transports; ~30 LOC);
  algebraMap-injectivity (field hom) concludes.
- **Sources**: TeX 2258–2264; replan R7.4.
- **Sizing**: ~90 LOC + survey risk.

### [CLEANUP-ALL-7] Pre-milestone /cleanup-all
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T701–T707 | **Type**: cleanup-all
- **Progress**: 2026-06-12: degraded sweep (no lean-lsp MCP): full
  `lake build PadicLFunctions` green with ZERO non-sorry warnings (mathlib
  linter set incl. line-length/show/unused-var all quiet; the only 3
  awk-flagged lines are unicode-heavy comments under 100 chars);
  maxHeartbeats overrides confirmed absent; per-dispatch slack fixed in
  flight (T704 long lines, T707 show-linter). ResidueZeta.lean at 1714
  lines — split/golf review deferred to the tooled CLEANUP-FINAL.

### [T708] **MILESTONE: RJW Theorem 7.1** — the residue of ζ_p
- **Status**: done (2026-06-12) | **File**: ResidueZeta.lean
- **Depends on**: T703, T702, T707, CLEANUP-ALL-7 | **Type**: theorem
- **Progress**:
  - 2026-06-12: `tendsto_sub_one_mul_zetaPBranch` proven (subagent), statement
    verbatim, exactly per sketch: generator-pack destructure; L ≠ 0 via the
    level-2 order p(p−1) ∤ p−1 contradiction (`angleUnit_coe_ne_one`,
    `pZpLog_angleUnit_ne_zero`); `Tendsto.inv₀` on T702c × T703-continuity;
    num(1) via branchChar (p−1) 0 = 1 + T707; `extLog_natCast_eq_pZpLog_angle`
    (u = ω⟨u⟩, extLog_mul, torsion-kill, extLog_eq_padicLog, pZpLog_coe).
    PROJECT-WIDE ZERO SORRIES; milestone + Thm (i) axioms standard 3.
  - 2026-06-12: blueprint Chapters/Residue.lean wired: residue-zeta-p (both
    decls), res-denominator-g ↦ zetaPBranch (note), res-g-pminus1 ↦ T702
    triple (replan-R7.3 note), res-primitive-Fa ↦ FtildeA/uA,
    res-primitive-derivative ↦ T704 (p∤a note), res-Fa-tilde-bounded left
    unwired with replan-R7.1 rationale (ℛ⁺ deferred), res-integral-as-eval ↦
    T705+T706a (distribution-free note), res-numerator ↦ T706b/c + zetaNum_one,
    res-limit-formula note (inlined in milestone); sign typo in res-numerator
    proof prose fixed (−log a + p⁻¹ log a). `lake build PadicLFunctionsBlueprint`
    green.
- **Statement**: skeleton `tendsto_sub_one_mul_zetaPBranch` (Thm (ii);
  Thm (i) = `continuousAt_zetaPBranch`, T703).
- **Proof sketch**: unfold zetaPBranch at the §4 generator (m, u);
  (s−1)·ζ(s) = [(s−1)·g(s)⁻¹]·num(s) = [(s−1)⁻¹g(s)]⁻¹·num(s)
  (g ≠ 0 for s ≠ 1 near 1 — from the T702c limit ≠ 0: L := pZpLog⟨u⟩ ≠ 0
  since ⟨u⟩ ≠ 1 (generator: u has infinite order; ω(u)-part finite order
  ⟹ ⟨u⟩ ≠ 1 — extract from topGen_pow_ne_one/T037) + norm_padicLog;
  eventual-nonvanishing from the limit); Tendsto-algebra:
  (s−1)⁻¹g(s) → −L-coe ≠ 0 (T702c) and num(s) → num(1) (T703-pairing
  continuity); num(1) = zetaNum-mass: branchChar (p−1) 0 = 1-on-units
  (ω^{p−1} = 1, ⟨·⟩⁰ = 1: teichmullerFun_pow_card_sub_one +
  AddChar-at-0 ⟹ the pairing at s = 1 is zetaNum p m 1) =
  −(1−p⁻¹)·extLog(m) (T707; p∤m from the generator pack hpm);
  extLog((m:ℚ_[p])) = L-coe (`extLog_natCast_eq_pZpLog_angle` helper:
  m-as-unit u (huv : (u:ℤ_[p]) = m), u = ω(u)·⟨u⟩, extLog-additivity +
  torsion-kill + extLog_eq_padicLog-on-ball + pZpLog_coe; ~40 LOC);
  Tendsto.mul: (−L)⁻¹·(−(1−p⁻¹)L) = 1−p⁻¹ ✓ (L ≠ 0).
- **Sources**: TeX 2187–2194 + 2258–2360 (verbatim at R7).
- **Blueprint**: Chapters/Residue.lean — wire Thm 7.1 (both decls),
  Lem 7.2 (T702 pair), Lem 7.3 (T704), Lem 7.5 (T706c); Lem 7.4
  rationale-comment (ℛ⁺ deferred, replan R7.1); re-render.
- **Sizing**: ~130 LOC.

### [CLEANUP-72] Final per-file cleanup (ResidueZeta.lean)
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T708 | **Type**: cleanup
  (+ widen CLEANUP-FINAL to §7)
- **Progress**: 2026-06-12: degraded final pass (no lean-lsp MCP): build green
  with zero non-sorry warnings → zero warnings outright (file now sorry-free);
  all 17 public decls + ~40 private helpers docstringed; section-variable
  omits in place; no maxHeartbeats overrides. CLEANUP-FINAL widened with the
  §7 fold-in (split-candidate at 1794 lines, seriesEval-toolkit placement,
  map_derivativeFun' dedup). Tooled golf deferred there.

## §7 dependency quick-view
```
T701 → T702 → T703 → CL71 ;  T704 ; T705 → T706(T704) → T707 → CLALL7
  → T708*(T703,T702,T707) → CL72
```

---

# §8 board (The p-adic family of Eisenstein series; TeX 2361–2446) — created 2026-06-12

Skeleton: PadicLFunctions/EisensteinFamily.lean (12 sorried decls incl. the
4 unitsTwist fields) + PadicLFunctions/EisensteinComplex.lean (4 sorries),
build green. Decomposition: decomposition.md R8 (verbatim quotes Q1–Q4 +
replans R8.1–R8.4). Statements live in the skeleton; the §6 statement-fix
protocol applies. Erratum #11 recorded (errata.md): TeX 2403(a) corrected
to the twisted pseudo-measure form.

### [T801] Dirac measures at prime-to-p naturals and the divisor measure
- **Status**: done (2026-06-12) | **File**: EisensteinFamily.lean | **Depends on**: none
- **Progress**: 2026-06-12: all three decls proven (subagent, batched with
  T802), statements verbatim. `PadicInt.isUnit_natCast_of_not_dvd` +
  `Nat.cast_ofNat` for the 2-unit; `LinearMap.coe_sum`/`Finset.sum_apply`
  for the measure-sum application. Verified: build green, axioms standard
  3. Cleanup: degraded mode (no MCP), defer to CLEANUP-81.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `isUnit_two_padicInt`, `unitOfNat_coe`,
  `divisorMeasure_moment` (R8 L8.1a/b/c/d).
- **Proof sketch**: 2-unit: `PadicInt.isUnit_iff`-route (‖2‖ = 1 for p ≠ 2:
  `PadicInt.norm_int_lt_one_iff_dvd`-contrapositive, 2 < p or p ∤ 2 by
  parity+primality, omega) or `isUnit_iff_not_dvd`-style mathlib lemma —
  five-method search for `PadicInt.isUnit_natCast`-shaped lemmas first
  (MuA.lean:65 used `PadicInt.isUnit_natCast_of_not_dvd`-pattern: grep its
  exact name and reuse with ¬p∣2). unitOfNat_coe: dif_pos with
  h : IsUnit ((d:ℤ_[p])) from the same lemma + `IsUnit.unit_spec`.
  divisorMeasure_moment: push the linear functional through the Finset.sum
  (`map_sum`-for-application: PadicMeasure is a LinearMap — `LinearMap.sum_apply`
  or `Finset.sum_apply'`-shape on the sum of measures), per-term
  `dirac_apply` + `unitsPowCM`-eval: dirac p (unitOfNat d) (x^k) =
  ((unitOfNat d : ℤ_[p]))^k = (d:ℤ_[p])^k [unitOfNat_coe — the filter
  guarantees ¬p∣d via Finset.mem_filter] = ((d^k : ℕ) : ℤ_[p]) [push_cast];
  assemble Σ (d^k : ℤ_[p]) = ((Σ d^k : ℕ) : ℤ_[p]) [Nat.cast_sum] = sigmaP.
- **Sources**: TeX 2376 (Q2 first half), 2411–2414 (Q4 proof).
- **Sizing**: source 3 lines; ~60 LOC.

### [T802] The x-twist ring automorphism and its fraction-ring extension
- **Status**: done (2026-06-12) | **File**: EisensteinFamily.lean | **Depends on**: none
- **Progress**: 2026-06-12: unitsTwist (all 4 fields) + the 4 lemmas proven
  (subagent, batched with T801), statements verbatim. map_mul' exactly per
  the moments-route (R8.2): `units_mul_apply_unitsPowCM` + moment-shift +
  `eq_zero_of_forall_unitsPowCM_eq_zero`. map_nonZeroDivisors manual
  (mathlib's equiv-nzd lemmas need NoZeroDivisors — N/A for Λ(ℤ_p^×));
  `IsLocalization.ringEquivOfRingEquiv_eq` for the algebraMap-compat.
  4 private helpers. Verified: build green (with the LevelRaise dep slice
  now built, 2980 jobs), axioms standard 3. Cleanup: degraded mode, defer
  to CLEANUP-81.
- **Parallel**: yes | **Type**: def-lemmas
- **Statement**: skeleton `unitsTwist` (4 sorried fields),
  `unitsTwist_moment`, `unitsTwist_dirac`, `map_nonZeroDivisors_unitsTwist`,
  `quotientTwist_algebraMap` (R8 L8.2a/b/c, replan R8.2).
- **Proof sketch**: moment shift FIRST (it powers everything):
  unitsCmul_apply + function algebra unitsPowCM 1 · unitsPowCM k =
  unitsPowCM (k+1) (ContinuousMap.ext, pow_succ, mul_comm bookkeeping).
  left/right_inv: unitsCmul g (unitsCmul h μ) = unitsCmul (h·g-order!) μ
  (rfl-level: comp of mulLeft) + invCM·powCM1 = 1 pointwise
  (u⁻¹·u = 1: `← Units.val_mul, inv_mul_cancel` — the ValuesAtOne:366
  cancellation pattern); μ(1·f) = μ f. map_add': unitsCmul is linear in μ
  (rfl/LinearMap.comp). map_mul' (THE content): both sides' x^k-moments
  (k > 0) agree: LHS(x^k) = (μ*ν)(x^{k+1}) [moment shift] =
  μ(x^{k+1})ν(x^{k+1}) [`units_mul_apply_unitsPowCM`, PseudoMeasure:755];
  RHS(x^k) = (τμ)(x^k)·(τν)(x^k) [same lemma] = μ(x^{k+1})ν(x^{k+1}) ✓;
  conclude by `eq_zero_of_forall_unitsPowCM_eq_zero` (PseudoMeasure:664) on
  the difference (map_sub of application). unitsTwist_dirac:
  LinearMap.ext f; (τδ_g)(f) = δ_g(x·f) = g·f(g) = (g•δ_g)(f) (smul_apply).
  map_nonZeroDivisors: ext x; mem_map ⟨y, hy, rfl⟩-direction: y nzd ⟹ τy nzd
  (z·τy = 0 ⟹ τ(τ⁻¹z·y) = 0 ⟹ τ⁻¹z·y = 0 [τ injective: EquivLike] ⟹
  τ⁻¹z = 0 ⟹ z = 0); reverse: x nzd ⟹ x = τ(τ⁻¹x) with τ⁻¹x nzd
  (symmetric argument). quotientTwist_algebraMap:
  `IsLocalization.ringEquivOfRingEquiv_eq` (mathlib Localization/Defs:696 —
  verified) is exactly this (modulo `IsLocalization.map_eq`-form; check the
  simp lemma generated by @[simps apply] on ringEquivOfRingEquiv).
- **Sources**: TeX 2410's "xζ_p" (the twist is the formalisation device;
  replan R8.2); RJW §3.6 for Λ.
- **Sizing**: ~140 LOC.

### [T803] A₀ = x·ζ_p/2: twisted pseudo-measure and moments
- **Status**: done (2026-06-12) | **File**: EisensteinFamily.lean
- **Depends on**: T801, T802 | **Type**: theorems
- **Progress**: 2026-06-12: both decls proven (subagent), statements
  verbatim (erratum-#11-corrected forms). Shared canonical-witness helper
  `twistedZetaHalf_witness_eq`; witness identification by
  `IsFractionRing.injective`; `smul_one_mul'` proven manually
  (IsScalarTower ℤ_[p] Λ Λ does NOT synthesize — noted for CLEANUP-FINAL
  as a possible missing instance); `coe_inv_two` for the ½-scalar.
  Verified: build green, axioms standard 3. Cleanup: degraded mode, defer
  to CLEANUP-81.
- **Statement**: skeleton `twistedZetaHalf_isTwistedPseudoMeasure`,
  `twistedZetaHalf_moments` (R8 L8.2d/L8.3, replan R8.1 = erratum #11).
- **Proof sketch**: key identity: (g•δ_g − 1) = τ(δ_g − 1) [unitsTwist_dirac
  + map_one: τ(1) = τ(δ_1) = 1•δ_1 = 1 + map_sub]. PM-ness: given g, take
  ν_g from `padicZeta_isPseudoMeasure p hp2 g` (ZetaP:294): ([g]−1)ζ_p =
  ν_g; apply quotientTwist + quotientTwist_algebraMap:
  τ̂(algebraMap([g]−1))·τ̂(ζ_p) = algebraMap(τν_g); multiply both sides by
  the half-scalar (it commutes); witness ν := 2⁻¹-scalar • τ(ν_g) — mind
  twistedZetaHalf's def-shape: algebraMap(c•1)·τ̂(ζ_p) with c := the
  2-inverse-unit-coe; (g•δ_g−1)-image · [algebraMap(c•1)·τ̂(ζ_p)] =
  algebraMap(c•1)·[τ̂(([g]−1)-image·ζ_p)] (ring comm + map_mul) =
  algebraMap(c•1)·algebraMap(τν_g) = algebraMap(c•(τν_g)) [map_mul backwards
  + smul-as-mul: (c•1)·μ = c•μ — `smul_one_mul`-shape for the module-ring
  compat: Algebra.smul_def-free; ℤ_p-smul on the convolution ring is central
  — small helper `smul_one_mul` exists in mathlib for Algebra-compatible
  smul: verify `smul_one_mul` fires; else prove (c•1)*μ = c•μ by
  LinearMap.ext + units_mul_apply-bilinearity]. Moments: from hν derive the
  padicZeta-witness equation for ν' := 2•τ⁻¹(ν)?? — cleaner DIRECTION:
  define the canonical witness w := c•τ(ν_g) as above and show ν = w by
  cancellation: algebraMap is injective on…NO (total fraction ring of a
  non-domain: algebraMap IS injective into FractionRing ✓
  `IsFractionRing.injective`); from algebraMap ν = algebraMap w [both equal
  the same product since (g•δ_g−1)-image times twistedZetaHalf is a single
  element] conclude ν = w; then w's moment: (c•τν_g)(x^{k−1}) =
  c·ν_g(x^k) [unitsTwist_moment, k−1+1 = k for k ≥ 4: omega/Nat.sub_add_cancel]
  and `padicZeta_moments p hp2 b hk ν_g (its-equation)` (ZetaP:303) gives
  ν_g(x^k)-coe = (b^k−1)(1−p^{k−1})zetaNeg(k−1); the c-scalar: coe of
  2⁻¹-unit in ℚ_p is 2⁻¹: (c : ℚ_[p])·X = X/2 (IsUnit.unit_spec + coe-inv:
  ‖…‖-free field algebra: (2:ℚ_[p])·c-coe = 1 ⟹ c-coe = 2⁻¹; push through).
  CAREFUL with k−1 ℕ-subtraction: state intermediate facts at exponent k
  with k = (k−1)+1.
- **Sources**: TeX 2403(a) + 2410–2412 (Q4); erratum #11 (errata.md).
- **Sizing**: ~110 LOC.

### [CLEANUP-81] /cleanup on EisensteinFamily.lean (cadence)
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T801, T802, T803 | **Type**: cleanup
- **Progress**: 2026-06-12: degraded pass (no lean-lsp MCP): build green
  with project linter set, zero non-sorry warnings; the 2 awk-flagged
  >100-byte lines are unicode-only (char-count ≤ 100, linter quiet); all
  publics docstringed, helpers private. Note for tooled pass: the
  `((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ)`-coercion chains in
  twistedZetaHalf/coe_inv_two are golf candidates (name the scalar once);
  IsScalarTower ℤ_[p] Λ Λ instance gap noted at T803. Defer to
  CLEANUP-FINAL.

### [T804] No measure interpolates k ↦ p^k
- **Status**: done (2026-06-12) | **File**: EisensteinFamily.lean | **Depends on**: none
- **Parallel**: yes | **Type**: theorem
- **Progress**: 2026-06-12: proven (subagent, parallel with T805), statement
  verbatim, p = 2 allowed, finitary single-level route (K = 1 + φ(p²);
  replan note in the sketch). Helper `units_pow_totient_sq_sub_self_mem`
  (uniform Euler congruence via unitsToZModPow/ker_toZModPow +
  pow_card_eq_one'). Orchestrator re-verified axioms on the live module:
  standard 3 (the agent's "spurious sorryAx" note was a methodology
  artifact — the live check is clean). Cleanup: degraded mode, defer to
  CLEANUP-ALL-8.
- **Statement**: skeleton `noMeasure_interpolates_pPow` (R8 L8.4). p = 2
  allowed.
- **Proof sketch**: rintro ⟨θ, hθ⟩. Exponents k_n := 1 + φ(p^{n+1}) =
  1 + p^n(p−1) (`Nat.totient_prime_pow` for the value; k_n > 0 ✓).
  Uniform Euler congruence: ∀ u : ℤ_[p]ˣ, (u:ℤ_[p])^{φ(p^{n+1})} − 1 ∈
  span{p^{n+1}}: image in (ZMod p^{n+1})ˣ is u'^{card} = 1
  (`pow_card_eq_one'` with Nat.card = φ: `Nat.card_eq_fintype_card` +
  `ZMod.card_units_eq_totient`); pull back through
  `PadicMeasure.unitsToZModPow`/`PadicInt.toZModPow`:
  toZModPow(u^φ − 1) = 0 ⟹ mem ker = span{p^{n+1}}
  (`PadicInt.ker_toZModPow` — the §7 teichmuller_isPrimitiveRoot pattern,
  ResidueZeta.lean:141–151, COPY). Hence ‖x^{k_n} − x^1‖_sup ≤ p^{−(n+1)}:
  pointwise x^{k_n} − x = x·(x^{φ(p^{n+1})} − 1), ‖x‖ ≤ 1 +
  `ContinuousMap.norm_le` + `PadicInt.norm_le_pow_iff_mem_span_pow`.
  Then ‖θ(x^{k_n}) − θ(x¹)‖ ≤ p^{−(n+1)} (`PadicMeasure.norm_apply_le`
  Measure/Basic:109 + map_sub). Substitute hθ: θ(x^{k_n}) = p^{k_n},
  θ(x¹) = p: ‖p^{k_n} − p‖ = ‖p‖·‖p^{k_n−1} − 1‖ = p⁻¹·1 = p⁻¹ for n ≥ 1
  (k_n − 1 = φ ≥ 1 ⟹ p^{k_n−1} ∈ span p ⟹ ‖p^{φ} − 1‖ = 1 isoceles/
  `PadicInt.norm_sub`-route: ‖1‖ = 1 > ‖p^φ‖) — but the bound says
  ≤ p^{−(n+1)} → contradiction at n = 1 (p⁻¹ ≤ p⁻² false). Pick n := 1
  concretely — NO limits needed at all! Single-n contradiction: cleanest.
- **Sources**: TeX 2379–2383 (Q2 second half; our route replaces the
  sequential-limit gloss by a single explicit congruence level — same
  mathematics, finitary).
- **Sizing**: source 5 lines; ~80 LOC.

### [T805] σ^p arithmetic and the scaled upper-half-plane point
- **Status**: done (2026-06-12) | **File**: EisensteinComplex.lean | **Depends on**: none
- **Progress**: 2026-06-12: all three proven (subagent, parallel with T804),
  statements verbatim. Divisor split via `Finset.sum_nbij'` (d/p ↔ p·e) +
  `Finset.sum_filter_not_add_sum_filter`; pScale by `Complex.mul_im`.
  mathlib's `UpperHalfPlane.posRealAction` noted but the frozen raw-mul def
  kept. Verified: build green, axioms standard 3. Cleanup: degraded mode,
  defer to CLEANUP-82.
- **Parallel**: yes | **Type**: lemmas
- **Statement**: skeleton `sigmaP_eq_of_not_dvd`,
  `sigmaP_add_pow_mul_sigma_div`, `pScale`'s membership proof (R8 L8.5a).
- **Proof sketch**: pScale: (p:ℂ)·z im = p·im z > 0:
  `Complex.mul_im`-expansion (p real: ofReal-free since (p:ℂ) = ((p:ℝ):ℂ);
  `UpperHalfPlane.coe_im`, mul_pos, p > 0, z.im_pos — mathlib may have
  `UpperHalfPlane` smul by positive reals: 5-method search
  `UpperHalfPlane` `smul` first; if a `•`-structure exists, REPLACE pScale
  by it via a statement-fix-free def-tweak and note in ticket).
  sigmaP_eq_of_not_dvd: filter is everything (∀ d ∣ n, ¬p∣d when ¬p∣n:
  dvd_trans), `Finset.filter_true_of_mem` + `ArithmeticFunction.sigma_apply`.
  sigmaP_add: σ_k(n) splits over the filter and its complement
  (`Finset.sum_filter_add_sum_filter_not`); the complement
  {d ∈ divisors n : p ∣ d} biject with (n/p).divisors via d ↦ d/p
  (inverse e ↦ p·e): `Finset.sum_nbij'` with mem-side conditions from
  `Nat.mem_divisors` arithmetic (d ∣ n ∧ p ∣ d ⟹ d/p ∣ n/p:
  Nat.div_dvd_div_iff/`Nat.div_dvd_iff_dvd_mul`; n ≠ 0 carries); per-term
  (p·e)^k = p^k·e^k + `Finset.mul_sum`.
- **Sources**: TeX 2390–2393 (Q3's "easy check", expanded).
- **Sizing**: ~90 LOC.

### [T806] The q-expansion of the p-stabilisation
- **Status**: done (2026-06-12) | **File**: EisensteinComplex.lean | **Depends on**: T805
- **Pre-dispatch survey note**: bernoulli k ≠ 0 for even k via
  `riemannZeta_two_mul_nat` + `riemannZeta_ne_zero_of_one_lt_re`
  (Dirichlet.lean:326) — the route mathlib's own private
  `eisensteinSeries_coeff_identity` (QExpansion:287) uses.
- **Progress**: 2026-06-12: proven (subagent), statement verbatim. 4 private
  helpers: `bernoulli_ne_zero_of_even`, reproduced `summable_sigma_cexp`,
  `rjw_normalisation` (ζ(1−k) = −B_k/k, Odd(k−1) sign), and
  `hasSum_rjwEisenstein` (the E_qExpansion_coeff-modelled HasSum). p-reindex
  via `Function.Injective.hasSum_iff` over multiples of p; three-case
  coefficient identification against stabilisedCoeff. Verified: build
  green, axioms standard 3 (independent re-check). Cleanup: degraded mode,
  defer to CLEANUP-ALL-8.
- **Type**: theorem
- **Statement**: skeleton `hasSum_stabilisedEisenstein` (R8 L8.5b, replan
  R8.3).
- **Proof sketch**: mathlib gives, at any τ : ℍ (inside
  `EisensteinSeries.E_qExpansion_coeff`'s proof, QExpansion.lean:324–346,
  the HasSum form): HasSum (fun m => c^{ml}_m·𝕢(τ)^m) (E hk τ) with
  c^{ml}_0 = 1, c^{ml}_m = −(2k/B_k)σ_{k−1}(m). EXTRACT it as stated —
  if only the coeff-form is exported, rebuild the HasSum from
  `q_expansion_bernoulli` + `summable_sigma_mul_cexp_pow`-shape (that
  private lemma's statement is reproducible: Summable σ·q^n via
  `summable_norm_pow_mul_geometric_of_norm_lt_one` +
  `ArithmeticFunction.sigma_le_pow_succ` + `norm_exp_two_pi_I_lt_one` —
  all public mathlib ✓) exactly as QExpansion:324 does (READ AND MIMIC its
  `← hasSum_nat_add_iff' 1` dance). Scale by ζ(1−k)/2 (HasSum.mul_left):
  RJW-coefficients at τ: a_0 = ζ(1−k)/2, a_m = ζ(1−k)/2·(−2k/B_k)·σ =
  σ_{k−1}(m) [the normalisation identity ζ(1−k)·(−2k/B_k)/2 = 1 ⟸
  ζ(1−k) = −B_k/k: zetaNeg-form `zetaNeg (k−1) = −bernoulli k/k`-bridge:
  prove the ℚ-identity zetaNeg(k−1)·(2k/bernoulli k)/2 = −1 — needs
  bernoulli k ≠ 0 for even k ≥ 4: search mathlib `bernoulli_ne_zero`
  (exists? five-method; FALLBACK: from `riemannZeta_neg_nat_eq_bernoulli`
  + ζ(1−k) ≠ 0 for even k ≥ 4: `riemannZeta_ne_zero_of...`— the negative
  odd-argument nonvanishing: trivial-zeros theory… SAFER ROUTE: avoid
  division entirely: state the per-coefficient identity multiplicatively:
  a_m = ζ(1−k)/2·c^{ml}_m and prove a_m = σ_{k−1}(m) ⟺
  zetaNeg(k−1)·(−(2k/B_k)) = 2 ⟺ (−1)^{k-1}B_k/k·(−2k/B_k) = 2 ⟸
  zetaNeg (k−1) = (−1)^{k−1}·bernoulli k/k [def, (k−1)+1 = k] and B_k
  CANCELS only if B_k ≠ 0 — unavoidable for identifying the n ≥ 1
  coefficients. Get B_k ≠ 0 from ζ: riemannZeta_neg_nat_eq_bernoulli +
  the functional-equation nonvanishing of ζ(1−k) (mathlib:
  `riemannZeta_ne_zero_iff`? or via `riemannZeta_one_sub` + sin/Gamma
  factors… five-method search `bernoulli_ne_zero` FIRST — recent mathlib
  may have it for even k (von Staudt–Clausen exists in our §5 survey
  notes: BernoulliRegular reference files mention von Staudt–Clausen
  clusters in mathlib-adjacent work). If genuinely missing: Tier-A
  sub-ticket via ζ(2m) ≠ 0 (`riemannZeta_two_mul_nat`-formula +
  π^{2m}-nonvanishing) + `riemannZeta_two_mul_nat`'s B-factor.)].
  At pScale: 𝕢(pScale z) = exp(2πi·p·z) = q(z)^p (`Complex.exp_nat_mul`-
  juggling); E(pz)-series reindexes: HasSum (a_m·q^{pm}) — compose with
  the injection m ↦ p·m extended by zero:
  `Function.Injective.hasSum_iff` (mul_right_injective₀, p ≠ 0) with the
  off-range terms zero. Subtract (HasSum.sub) the p^{k−1}-scaled version:
  coefficientwise: n = 0: ζ/2 − p^{k−1}ζ/2 = stabilisedCoeff 0 ✓;
  p ∤ n: σ_{k−1}(n) − 0 = σ^p [T805]; p ∣ n, n ≠ 0: σ_{k−1}(n) −
  p^{k−1}σ_{k−1}(n/p) = σ^p [T805 ℕ-sub-free form, cast to ℂ]. Final
  function-ext: `HasSum.congr_fun`-shape (funext + the case analysis).
- **Sources**: TeX 2387–2393 (Q3) + mathlib QExpansion.lean (Birkbeck).
- **Sizing**: ~200 LOC (the section's largest; one survey risk:
  bernoulli_ne_zero).

### [CLEANUP-ALL-8] Pre-milestone /cleanup-all
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T801–T806 | **Type**: cleanup-all
- **Progress**: 2026-06-12: degraded sweep (no lean-lsp MCP): project files
  build green with zero non-sorry warnings (EisensteinFamily 459 /
  EisensteinComplex 410 lines, all publics docstringed); the only warnings
  are in the DEP checkout (2 benign change-does-nothing + 1 deprecation in
  LeanModularForms — belongs to the upstream compat branch, noted in the
  CLEANUP-82 patch task). Tooled golf deferred to CLEANUP-FINAL.

### [T807] **MILESTONE: RJW §8 Theorem** — the Λ-adic Eisenstein family
- **Status**: done (2026-06-12) | **File**: EisensteinFamily.lean
- **Depends on**: T801, T803, T806, CLEANUP-ALL-8 | **Type**: theorem
- **Progress**:
  - 2026-06-12: `eisensteinFamily_interpolation` proven (subagent), statement
    verbatim, pure assembly (constantCoeff/coeff-mk collapses +
    twistedZetaHalf_moments + divisorMeasure_moment + cast bookkeeping).
    PROJECT-WIDE ZERO SORRIES (orchestrator re-verified); axioms standard 3.
  - 2026-06-12: blueprint Chapters/Eisenstein.lean wired: eis-series ↦
    mathlib ModularForm.E + q_expansion_bernoulli + rjwEisenstein
    (mathlib-link directive); eis-dirac-interpolation ↦ unitOfNat_coe +
    divisorMeasure_moment; eis-no-measure-at-p ↦ noMeasure_interpolates_pPow
    (finitary-route note); eis-p-stabilisation ↦ sigmaP/stabilisedCoeff/
    hasSum_stabilisedEisenstein + stabilisedEisenstein(_apply) (Γ₀(p) note,
    Miyake/LeanModularForms credit); p-adic-eisenstein-family ↦
    eisensteinFamily(_interpolation) + unitsTwist/twistedZetaHalf decls with
    the erratum-#11 note. Blueprint build green (4106 jobs); site
    re-rendered, chapter page present with the wired names.
- **Statement**: skeleton `eisensteinFamily_interpolation` (R8 L8.6,
  replan R8.4).
- **Proof sketch**: constructor. Clause 1 (constant coefficient):
  intro b ν hν; `PowerSeries.constantCoeff_mk`/`coeff_mk` collapses
  coeff 0 (eisensteinFamily) = twistedZetaHalf (if_pos rfl); apply
  `twistedZetaHalf_moments p hp2 b hk ν hν`; identify
  stabilisedCoeff p k 0 = (1−p^{k−1})·zetaNeg(k−1)/2 (if_pos) and the
  ℚ→ℚ_p cast distributes (push_cast: Rat.cast of the product/div — 2 ≠ 0).
  Clause 2: intro n hn; coeff_mk + if_neg hn gives the algebraMap-form
  (left conjunct rfl-level); right: `divisorMeasure_moment` + if_neg +
  Nat-cast bookkeeping ((sigmaP : ℕ) : ℚ) : ℚ_p) = ((sigmaP : ℕ) : ℚ_p):
  push_cast. Blueprint: wire Chapters/Eisenstein.lean —
  "eis-dirac-interpolation" ↦ divisorMeasure_moment (+unitOfNat_coe),
  "eis-no-measure-at-p" ↦ noMeasure_interpolates_pPow,
  "eis-p-stabilisation" ↦ sigmaP/stabilisedCoeff/hasSum_stabilisedEisenstein
  + Γ₀(p)-deferral note, "p-adic-eisenstein-family" ↦
  eisensteinFamily/eisensteinFamily_interpolation (+ twistedZetaHalf decls)
  with the erratum-#11 prose note on (a); "eis-series" ↦
  ModularForm.E/EisensteinSeries.q_expansion_bernoulli (MATHLIB link per
  the 2026-06-10 directive) + rjwEisenstein normalisation note;
  `lake build PadicLFunctionsBlueprint` + re-render.
- **Sources**: TeX 2399–2416 (Q4 verbatim at R8).
- **Sizing**: ~60 LOC + blueprint pass.

### [T808] Γ₀(p)-modularity of the p-stabilisation (un-deferred 2026-06-12)
- **Status**: done (2026-06-12) | **File**: EisensteinComplex.lean | **Depends on**: T805
- **Progress**: 2026-06-12: all three decls proven (subagent):
  `stabilisedEisenstein : ModularForm ((Gamma0 p).map (mapGL ℝ)) k` (at the
  more general 3 ≤ k), `_apply` (pointwise E − p^{k−1}E(p·)), `_smul_apply`
  (the rjwEisenstein bridge matching hasSum_stabilisedEisenstein's RHS).
  Γ₀-invariance by hand-promotion of the Γ₁(p·1)-difference (the central
  helper `stabilisedDiff_slash_mapGL`: `slash_mapGL_levelRaiseFun` +
  `levelRaiseConjOfDvd_mem_Gamma0` + E's 𝒮ℒ-invariance); cusp-boundedness
  via `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`. DEP-COMPAT GREW: 2
  more skew fixes in the dep checkout (Gamma1Pair.lean
  `Gamma0MapUnits_surjective` simpa-reductions; LevelRaise.lean
  `levelRaiseConj_mem_Gamma1` rfl-bridges) — now 4 files total to
  upstream+repin at CLEANUP-82. Verified: build green (3809 jobs), axioms
  standard 3 on all three. Cleanup: degraded mode, defer to CLEANUP-ALL-8.
- **Parallel**: yes (after T805) | **Type**: def + theorem
- **Context**: user directive 2026-06-12: the strong-multiplicity-one
  project (CBirkbeck/LeanModularForms, branch hecke-ring) has the
  level-raising operator; this repo now REQUIRES it (lakefile.toml pin
  720d950b + two mathlib-skew compat fixes, log below). Un-defers the
  plan.md §8 deferred item "Γ₀(p)-modularity of E_k^{(p)}".
- **Statement** (add to EisensteinComplex.lean; exact Lean form fixed at
  execution against the dep's API):
  `noncomputable def stabilisedEisenstein {k : ℕ} (hk : 3 ≤ k) :
    ModularForm ((Gamma0 p).map (mapGL ℝ)) k` realising
  `E_k − p^{k−1}·ι_p E_k` (RJW TeX 2394 "Note E_k^{(p)} is a modular form
  of weight k and level Γ₀(p)"), plus
  `stabilisedEisenstein_apply : stabilisedEisenstein p hk z
    = ModularForm.E hk z − (p:ℂ)^(k−1) * ModularForm.E hk (pScale p z)`
  (ℤ/ℕ-weight cast bookkeeping at execution) and the
  rjwEisenstein-scaled corollary matching hasSum_stabilisedEisenstein.
- **Proof sketch**: from the dep
  (LeanModularForms.HeckeRIngs.GL2.LevelRaise):
  1. `modularFormLevelRaise (M := 1) (d := p) k` +
     `modularFormLevelRaise_apply` (pointwise f(α_d • τ)) +
     `coe_levelRaiseMatrix_smul` ((α_l•τ : ℂ) = l·τ — identifies
     α_p•τ = pScale p τ via UpperHalfPlane.ext).
  2. Feed mathlib's `ModularForm.E hk : ModularForm 𝒮ℒ k` restricted
     along (Gamma1 1).map ≤ 𝒮ℒ (Γ₁(1) = ⊤-side; the dep's
     restrictSubgroup at LevelRaise.lean:174; mind ℤ-weight vs ℕ).
  3. F := E|_{Γ₁(p)} − p^{k−1}·ι_p(E) lives at Γ₁(p); upgrade to Γ₀(p)
     directly (ModularForm.mk-shape): slash-invariance for
     γ ∈ Γ₀(p)-mapped from E's full 𝒮ℒ-invariance + the
     down-conjugation bridge `slash_mapGL_levelRaiseFun` with
     `levelRaiseConjOfDvd_mem_Gamma0` (LevelRaise.lean:121; at M = 1,
     Γ₀(1) = SL2 so E∣γ̃ = E ⟹ (ι_pE)∣γ = ι_pE); holomorphy/
     boundedness inherited from the Γ₁(p)-level object (subgroup-
     agnostic predicates). FIRST grep the dep for an existing
     Γ₀-bundled operator or invariance-upgrade helper.
  4. apply-lemma from modularFormLevelRaise_apply +
     coe_levelRaiseMatrix_smul + UpperHalfPlane.ext against pScale.
- **Mathlib/dep lemmas**: modularFormLevelRaise(_apply),
  coe_levelRaiseMatrix_smul, slash_mapGL_levelRaiseFun,
  levelRaiseConjOfDvd_mem_Gamma0, Gamma0_dmul_lower_left_dvd,
  restrictSubgroup (dep); ModularForm.translate, Gamma0/Gamma1
  inclusions (mathlib).
- **Sources**: TeX 2394 (the "Note" in Q3); Miyake §4.6 Lem 4.6.1 /
  DS (5.16) (the dep's own citations).
- **Sizing**: dep supplies the operator; Γ₀-upgrade + apply ~150 LOC.
- **Dep-compat log (orchestrator, 2026-06-12)**: two mathlib-skew fixes
  applied in .lake/packages/LeanModularForms (MUST be upstreamed to a
  pushed branch of CBirkbeck/LeanModularForms and repinned before this
  board closes — tracked in CLEANUP-82; remote CI cannot see
  .lake-local edits): (i) SL2Surjection.lean: add
  `import Mathlib.Data.ZMod.Units` (ZMod.coe_int_isUnit_iff_isCoprime
  no longer transitively imported); (ii) AbstractHeckeRing/Basic.lean:
  `toSet_eq_rep`'s simpa needs `HeckeCoset.rep` in the simp set
  (Quotient.out reducibility change).

### [CLEANUP-82] Final per-file cleanup (EisensteinFamily.lean +
EisensteinComplex.lean)
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T807, T808 | **Type**: cleanup
  (+ widen CLEANUP-FINAL to §8; + upstream the LeanModularForms compat
  fixes to a pushed branch and repin lakefile/manifest)
- **Progress**: 2026-06-12: (i) UPSTREAMED: compat branch
  `compat/padic-mathlib-431` pushed to CBirkbeck/LeanModularForms
  (= pin-base 720d950 + the 4 mechanical skew fixes, commit 84b03fb);
  lakefile.toml + manifest repinned to 84b03fb; dep checkout refetched
  clean (superseded local edits stashed in the checkout, patch snapshot
  removed from the repo); full build green at the new pin — remote CI can
  now fetch+build. (ii) Degraded per-file pass: both files zero non-sorry…
  zero warnings outright (project sorry-free); 3 awk >100-byte lines are
  unicode-only comments; publics docstringed. Tooled golf folded into
  CLEANUP-FINAL (§8 widening below).

## §8 dependency quick-view
```
T801 ; T802 → T803 → CL81 ; T804 ; T805 → T806
  → CLALL8 → T807*(T801,T803,T806) → CL82
T805 → T808 (dep: LeanModularForms levelRaise) → CL82
```

---

# §9–§10 board (Notation + The Coleman map; TeX 2466–2948) — created 2026-06-12

Skeleton: PadicLFunctions/Coleman/Tower.lean (11 sorried decls, build
green). STAGED SKELETON (recorded design decision): the
NormOperator/Theorem/Map layers' Lean skeletons are authored by their own
tickets (T904/T906/T911 are explicitly skeleton-authoring) because their
statement shapes consume Tower's settled API — Tower is the API-gap
developed first, per /develop's API-gap recursion. Decomposition:
decomposition.md R9–R10 (verbatim quotes Q1–Q8 + design replans
R10.1–R10.8). Statement-fix protocol applies. §10.5 (Euler
systems/Perrin-Riou) and §9's global objects: deferred (plan.md).

### [T901] The compatible ξ-system and tower membership
- **Status**: done (2026-06-12) | **File**: Coleman/Tower.lean | **Depends on**: none
- **Parallel**: yes | **Type**: lemmas
- **Progress**: 2026-06-12: all four proven (subagent), statements verbatim.
  ξ-system by Nat.rec over the subtype chain {z // IsPrimitiveRoot z (p^n)}
  with defeq choose_spec extraction (helper `primitiveRoot_pow_succ`:
  n = 0 via HasEnoughRootsOfUnity, n ≥ 1 via IsAlgClosed.exists_pow_nat_eq
  + Nat.dvd_prime_pow order pinning). Verified: build green, axioms
  standard 3. Cleanup: degraded mode, defer to CLEANUP-91.
- **Statement**: skeleton `exists_compatible_primitiveRoot`,
  `zetaSys_mem_K`, `pi_mem_K`, `K_le_succ`.
- **Proof sketch**: existence: ℕ-recursion: ξ₀ := 1 (IsPrimitiveRoot 1 1 ✓
  p^0 = 1); given ξ_n primitive p^n-th, IsAlgClosed gives a root y of
  X^p − ξ_n (`IsAlgClosed.exists_pow_nat_eq`-shape/`exists_root` of the
  polynomial — ℂ_[p] IsAlgClosed instance from §7); y is primitive
  p^{n+1}-th: orderOf-argument: y^{p^{n+1}} = ξ_n^{p^n} = 1 and y^{p^n} =
  ξ_n^{p^{n−1}}... careful n = 0: y^p = ξ₀ = 1, need y of EXACT order p:
  choose y a PRIMITIVE root via `HasEnoughRootsOfUnity`/the §7 route, then
  CORRECT it to hit ξ_n: the set of p-th roots of ξ_n is y₀·μ_p for any
  fixed root y₀; primitivity of SOME root: if all p-th roots of ξ_n had
  order < p^{n+1} then each root z satisfies z^{p^n} = 1, but
  (z^{p^n})... z^{p^n} is a p-th root... cleanest: take z with z^p = ξ_n;
  z^{p^{n+1}} = 1; order of z divides p^{n+1} and is divisible by
  order(ξ_n) = p^n (z^p = ξ_n ⟹ orderOf ξ_n ∣ orderOf z); so order ∈
  {p^n, p^{n+1}}; if p^n then z^{p^n} = 1 ⟹ ξ_n^{p^{n−1}} = z^{p^n} = 1
  contradicting primitivity (n ≥ 1); n = 0 separately: pick z primitive
  p-th (HasEnoughRootsOfUnity) — z^p = 1 = ξ₀ ✓. Package with
  `IsPrimitiveRoot` API (`IsPrimitiveRoot.orderOf`-bridges). Membership:
  `IntermediateField.mem_adjoin_simple_self`; pi: sub_mem + one_mem;
  K_le_succ: adjoin-mono via zetaSys p n = (zetaSys p (n+1))^p ∈ adjoin
  (pow_mem + zetaSys_pow_p): `IntermediateField.adjoin_le_iff` +
  singleton-subset.
- **Sources**: TeX 2507 (Q-prose); RJW §9.
- **Sizing**: ~90 LOC.

### [T902] The degree ladder and the uniformiser norms (Eisenstein)
- **Status**: done (2026-06-12) | **File**: Coleman/Tower.lean | **Depends on**: T901
- **Pre-dispatch survey (orchestrator)**: mathlib anchors verified:
  `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` (Eisenstein/
  IsIntegral.lean:77, over ℤ at span{p}) and
  `Polynomial.irreducible_of_eisenstein_criterion` (Criterion.lean:176).
  Route ℤ → ℤ_[p]-Eisenstein-transport → irreducible over ℤ_[p] →
  fraction-field transfer (Monic.irreducible_iff-family) → minpoly =
  mapped Φ → finrank = totient.
- **Progress**: 2026-06-12: all six proven (subagent). Statement fix
  applied per pre-authorization (b2-logged): finrank_K_succ += (hn : 1 ≤ n)
  (false at n = 0: degree p−1). Route refinements: degree ladder via the
  `IsCyclotomicExtension` framework (instance `isCyclotomicExtension_K`
  built from `IsPrimitiveRoot.adjoin_isCyclotomicExtension`); uniformiser
  norm WITHOUT Algebra.norm/spectral theory — Vieta on Φ_{p^n}(T+1) over
  ℂ_[p] (`Splits.coeff_zero_eq_prod_roots_of_monic` +
  `eval_one_cyclotomic_prime_pow`) + the elementary equal-conjugate-norms
  helper (`norm_root_sub_one_eq`, two-sided geometric-factor argument).
  6 private helpers (the T903 consumers). Verified: build green (3811
  jobs), Tower.lean ZERO sorries, axioms standard 3 (independent
  re-check). Cleanup: degraded mode, defer to CLEANUP-91.
- **Type**: lemmas
- **Statement**: skeleton `finrank_K`, `finrank_K_succ`,
  `norm_pi_pow_totient`, `norm_pi_lt_one`, `pi_ne_zero`, `pi_mem_O`.
- **Proof sketch**: Φ_{p^n} irreducible over ℚ_p: mathlib has the
  ℤ-statement `Polynomial.cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`
  (VERIFY exact name — survey Q2/Q3; it exists for the ℤ-coefficients
  Eisenstein at (p)); map to ℤ_[p] (Eisenstein transports along the ring
  map into the DVR with 𝔭 = (p): coefficients-in-ideal by map; or
  re-instantiate the mathlib lemma at R := ℤ_[p] if it's
  ring-generic); `Polynomial.IsEisensteinAt.irreducible` (Criterion.lean:
  needs ℤ_[p] integrally closed + IsFractionRing ℤ_[p] ℚ_[p] ✓ both
  mathlib) gives Φ_{p^n}(X+1)-irreducible hence Φ_{p^n} irreducible over
  ℚ_p (comp X+1 unit-translate: `Polynomial.irreducible_comp`-bridges);
  minpoly (zetaSys p n) = Φ_{p^n} (monic + irreducible + root:
  `IsPrimitiveRoot.isRoot_cyclotomic` + `minpoly.eq_of_irreducible_of_monic`);
  finrank_K = natDegree Φ = totient (`IntermediateField.adjoin.finrank`
  (integral element: root of monic) + `natDegree_cyclotomic`). Tower step:
  finrank mul ladder: finrank ℚ_p K_{n+1} = finrank ℚ_p K_n ·
  finrank K_n K_{n+1} (`Module.finrank_mul_finrank` through
  extendScalars/IsScalarTower — the extendScalars instances; totient
  ratio φ(p^{n+1})/φ(p^n) = p for n ≥ 1, = p−1 for n = 0:
  CAREFUL — finrank_K_succ as stated (= p) is FALSE at n = 0
  (φ(p)/φ(1) = p−1)!! STATEMENT FIX REQUIRED at execution: add (hn : 1 ≤ n)
  to finrank_K_succ — pre-authorized, b2-log + docstring note (orchestrator
  caught at board-writing; the skeleton statement lacks hn).
  Norms: N_{K_n/ℚ_p}(π_n) = ±Φ_{p^n}(1) = ±p (norm = (−1)^d·(minpoly
  constant term): `Algebra.norm_eq_neg_one_pow_natDegree_mul_coeff_zero`-
  shaped mathlib lemma — five-method search; `minpoly` of π_n =
  Φ_{p^n}(X+1) (translate); Φ_{p^n}(1) = p (`Polynomial.cyclotomic_prime_pow_eval_one`?
  — `eval_one_cyclotomic_prime_pow` exists in mathlib ✓ verify name);
  then ‖π‖^d = ‖N(π)‖ = p⁻¹: Galois-invariance of the norm on ℂ_[p]
  (the unique extension: ‖σx‖ = ‖x‖ for σ ∈ Gal — via spectralNorm
  uniqueness or: N(π) = Π σ(π), ‖N‖ = Π‖σπ‖, and ‖σπ‖ = ‖π‖ ∀σ —
  ATTACK at execution: the clean route is `spectralNorm`-invariance
  (PadicAlgCl's norm IS spectralNorm, mathlib Complex.lean:78) +
  `spectralNorm_aut_invariant`-shaped lemma (search
  Mathlib/Analysis/Normed/Unbundled/SpectralNorm — survey said spectral
  norm machinery exists); FALLBACK: ‖·‖∘σ is another ℚ_p-algebra norm
  extending and norm-unique on finite extensions
  (`spectralNorm_unique`-family)). pi_mem_O: norm ≤ 1 + mem K ✓.
- **Sources**: TeX 2475 + 2685; replan R10.2.
- **Sizing**: ~170 LOC (the Eisenstein cluster).

### [T903] Integer-ring structure, element norms, and 𝒰_∞ (authors API)
- **Status**: DONE (2026-06-12) — items 1–7 complete; item 8 (O-basis
  monogenicity) deferred to [T903b] (see below). Authored: `levelNorm`,
  `levelNorm_apply`, `levelNorm_mem`, `levelNorm_mul`, `levelNorm_one`,
  `levelNorm_zetaSys_pow_sub_one` (the TeX 2581–2585 collapse engine),
  `levelNorm_pi`, `structure NormCompatUnits` + `.one`/`.mul` (+ `One`/`Mul`
  instances). Engine route: `levelNorm` = `Algebra.norm (K p n)` on
  `IntermediateField.extendScalars (K_le_succ p n)`, junk-extended off
  `K_{n+1}`; collapse proven via (private) `minpoly_extendScalars_of_pow`
  (minpoly of `ξ^b_{n+1}` over `K_n` is `X^p − C(ξ^b_n)`, degree `p` from
  `extendScalars_adjoin_eq_top` = generation, itself from `primitiveRoot_notMem_K`
  + prime-degree divisibility), translated by `minpoly.sub_algebraMap` to
  `(X+1)^p − C(ξ^b_n)`, then `norm = (−1)^p·coeff₀` via
  `Algebra.norm_eq_norm_adjoin` + `PowerBasis.norm_gen_eq_coeff_zero_minpoly`
  (p odd ⟹ `ξ^b_n − 1`). Added `hp2 : p ≠ 2` (TeX 2470; docstringed). Norm-≤1
  lemma (item 6) omitted as unused — the `compat` equation carries `𝒪_n`-membership
  (= elems n). **Verified**: `lake build PadicLFunctions` green (3811 jobs),
  zero `sorry` in Tower.lean, `#print axioms` = {propext, Classical.choice,
  Quot.sound} on all 10 new public decls, mathlib linters green (maxHeartbeat
  comments + `change` for defeq goal shifts). Item 8's consumer T907 now
  depends on T903b.
- **(superseded planning fields below)** | **File**: Coleman/Tower.lean | **Depends on**: T902
- **Type**: def + lemmas (authors new skeleton per the staged plan)
- **Statement** (authored at execution against T902's API; shapes fixed
  here): `levelNorm (n) : ℂ_[p] → ℂ_[p]` := the K_n-norm of K_{n+1}
  (Algebra.norm through extendScalars, junk-extended off K_{n+1});
  `levelNorm_collapse {b} (hb : ¬p∣b) (n ≥ 1) :
  levelNorm p n (zetaSys p (n+1)^b − 1) = zetaSys p n^b − 1` (Q7's
  engine, TeX 2581–2585: min poly X^p − ξ_n + X^p−1 = Π(Xη−1));
  `levelNorm_mem_O`/`levelNorm_unit` (norms preserve integrality and
  units: integral closure stability — via the ball: ‖N(x)‖ = ‖x‖^p ≤ 1
  Galois-invariance again, or minpoly-coefficient integrality);
  `structure NormCompatUnits` (𝒰_∞): elems : ∀ n, ℂ_[p]ˣ with
  mem : (elems n : ℂ_[p]) ∈ O p n, inv_mem, compat :
  levelNorm p n (elems (n+1)) = elems n; O-basis monogenicity:
  `O_succ_basis (n ≥ 1)`: (ξ_{n+1}^i)_{i<p} is an O_n-basis of O_{n+1}
  (Eisenstein monogenic: mathlib Eisenstein/IsIntegral
  `IsIntegralClosure`-route — survey Q2(b); state minimally as the
  ∃!-digit-expansion form the commuting square consumes).
- **Proof sketch**: collapse: N(x) = Π_{η∈μ_p}-conjugates: over the
  degree-p step the conjugates of ξ_{n+1} are ηξ_{n+1} (roots of
  X^p − ξ_n: `minpoly`-roots + the p distinct roots ηξ; Galois ⟹ norm =
  product of conjugates `Algebra.norm_eq_prod_automorphisms` or
  norm = (−1)^p·constant-of-minpoly applied to the TRANSLATED minpoly of
  ξ^b_{n+1}−1... CLEANEST: norm multiplicative + norm(ξ^b_{n+1} − 1):
  minpoly of ξ^b_{n+1} over K_n is X^p − ξ^b_n (b coprime p: ξ^b also
  generates, same Eisenstein-shape — or reindex the system: ξ^b is
  another compatible system!); then N(ξ^b−1) = ±((X^p−ξ_n^b) at 1)·sign
  = ±(1 − ξ_n^b)... sign bookkeeping (−1)^p = −1 (p odd):
  N(ξ^b_{n+1}−1) = (−1)^p·minpolyConst(ξ^b_{n+1}−1) with minpoly
  (X+1)^p − ξ^b_n: constant = 1 − ξ^b_n ⟹ N = ξ^b_n − 1 ✓ exact (Q7's
  computation, faithfully). 𝒰_∞/basis: per sketch; basis via mathlib
  Eisenstein-IsIntegral (`IsEisensteinAt`-adjoin results) — survey-gated;
  FALLBACK: state the digit-expansion existence directly and prove via
  π-adic expansion (the single-level greedy lemma's method).
- **Sources**: TeX 2503 (𝒰_∞), 2581–2585 (Q7), 2685 (min poly).
- **Sizing**: ~200 LOC + survey risk (monogenicity).

### [T903b] O-basis monogenicity of the tower step (split from T903 item 8)
- **Status**: done (2026-06-12 — Route 2' orthogonality/value-group joint
  induction; O_succ_exists_digits + O_succ_digits_unique, hp2 dropped as
  unused; spectral-norm bridge; axioms standard 3) | **File**: Coleman/Tower.lean | **Parent**: T903
- **Depends on**: T903 (done) | **Parallel**: yes | **Type**: theorem
- **Task**: author + prove `O_succ_exists_digits {n} (hn : 1 ≤ n) (hp2 : p ≠ 2)`:
  `∀ x ∈ O p (n+1), ∃ c : Fin p → ℂ_[p], (∀ i, c i ∈ O p n) ∧
  x = ∑ i, c i * (zetaSys p (n+1))^(i:ℕ)` (i.e. `O_{n+1} = ⊕_{i<p} O_n·ξ^i`),
  plus the uniqueness companion `O_succ_digits_unique` (the `Fin p` ξ-power
  expansion with `O_n`-coefficients is unique). This is the `O_n`-module basis
  T907's commuting-square det-transport consumes.
- **Why split (2026-06-12)**: T903 item 8 carried the spawn-T903b escape hatch.
  Three distinct routes attempted at T903 execution, none lands in a single
  ticket budget under zero-sorry discipline:
  1. **Direct relative mathlib**: NO relative-monogenicity / integral-basis
     API exists in mathlib (`RingTheory/Polynomial/Eisenstein/IsIntegral.lean`
     + `IsIntegralClosure` are all *absolute*, `R = ℤ_p`-based; nothing matches
     `O_{n+1} = ⊕ O_n·ξ^i`).
  2. **MOST PROMISING — absolute monogenicity + reindex**: (a) prove
     `O_m = adjoin ℤ_p {π_m}` for all `m` via
     `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` (the minpoly
     of `π_m = ξ_m − 1` over ℚ_p IS Eisenstein at `(p)` — the file's
     `cyclotomic_irreducible_Zp` already builds that `IsEisensteinAt` witness;
     `Algebra.discr_mul_isIntegral_mem_adjoin` for the reverse ⊇ via the
     discriminant being a `p`-power-unit), giving a `ℤ_p`-power-basis
     `{π_m^j : j < φ(p^m)}` of `O_m`; (b) re-index `φ(p^{n+1}) = p·φ(p^n)` with
     `ξ_{n+1}^{i+p·j} = ξ_{n+1}^i · ξ_n^j` (since `ξ_{n+1}^p = ξ_n`,
     `zetaSys_pow_p`) to convert the absolute `ℤ_p`-basis at level `n+1` into the
     relative `O_n`-basis `{ξ_{n+1}^i : i < p}`. Each of (a),(b) is itself
     ticket-sized (≈4 sublemmas total: absolute ⊆, discriminant ⊇, basis
     packaging, reindex) — hence the split.
  3. **K-coefficient (field) version only**: `K_succ_exists_digits` — the
     `{ξ_{n+1}^i : i<p}` are a `K_n`-basis of `extendScalars` (power-basis
     independence, cheap via `adjoin.powerBasis` + `finrank_K_succ`). Feasible
     but is NOT the integral `O_n`-version T907 needs; rejected as insufficient.
- **Recommended attack**: Route 2. Budget the bulk on sub-step (a) (absolute
  `O_{n+1} = ℤ_p[π_{n+1}]`); (b) is then bookkeeping. The file already exposes
  `pi_mem_O`, `finrank_K_succ`, `zetaSys_pow_p`, the Eisenstein witness pattern.
- **Sources**: TeX 2685 (min poly / monogenicity); 2474 (`O_n` = integral
  closure). Consumer: T907 (commuting square).
- **Status update (2026-06-12)**: DONE, sorry-free, axiom-clean (the standard 3 on
  both publics; `lake env lean` + `lake build PadicLFunctions.Coleman.Tower` green,
  linter on). Landed via **Route 2'** (the orthogonality/value-group joint route from
  the brief), NOT the discriminant/monogenicity Route 2 — the value-group fact (so the
  ramification orthogonality) is cheaper than the absolute integral-closure machinery.
  - Publics: `O_succ_exists_digits {n} (hn : 1 ≤ n) {x} (hx : x ∈ O p (n+1)) :`
    `∃ c : Fin p → ℂ_[p], (∀ i, c i ∈ O p n) ∧ x = ∑ i, c i * zetaSys p (n+1)^(i:ℕ)`
    and `O_succ_digits_unique {n} (hn : 1 ≤ n) {c c'} (hc : ∀ i, c i ∈ K p n)`
    `(hc' : ∀ i, c' i ∈ K p n) (heq : … = …) : c = c'` (K_n-coeffs suffice for
    uniqueness, as the ticket allowed). NB `hp2 : p ≠ 2` turned out UNNEEDED — the
    expansion/uniqueness hold for `p = 2` too (the odd-`p` constraint was only in the
    norm-collapse sign computation, not here), so it is dropped from both signatures.
  - Key route facts: (i) spectral-norm bridge `‖x‖ = spectralNorm ℚ_[p] (K p n) x` for
    `x ∈ K_n` (`spectralNorm_unique_field_norm_ext`, ℚ_p complete) ⟹ the value-group
    fact `‖c‖^{φ(p^n)} ∈ p^ℤ` (`norm_pow_totient_mem_zpow`) via
    `spectralNorm_eq_norm_coeff_zero_rpow`; (ii) ultrametric orthogonality
    `IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne` collapses
    `‖∑ d_k π_{n+1}^k‖ ≤ 1` to all `d_k ∈ O_n`
    (`forall_norm_le_one_of_norm_sum_pi_pow_le_one`); (iii) `K_n`-coordinate expansion
    via `adjoin.powerBasis` (`extendScalars_exists_repr`) gives the π-expansion
    (`exists_pi_repr`) and the linear independence for uniqueness
    (`linearIndependent_pow`, `zetaSys_pow_sum_eq_zero_imp`); (iv) integral change of
    basis `π_{n+1}^k ∈ O_n`-span of `ξ`-powers by `add_pow` (`pi_pow_mem_span`). No new
    imports (SpectralNorm transitively via `Padics.Complex`). 8 private helpers added.
  - Consumer note for T907: the deliverable is the `ξ_{n+1}^i` basis (not the `π^i`
    basis the proof goes through internally); both existence and uniqueness are in the
    `ξ`-power form T907's det-transport wants.

### [CLEANUP-91] /cleanup on Coleman/Tower.lean (cadence)
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T901, T902, T903 | **Type**: cleanup
- **Progress**: 2026-06-12: degraded pass (no lean-lsp MCP): build green,
  zero warnings (linter set on); Tower.lean at 704 lines, publics
  docstringed, helpers private, maxHeartbeats overrides carry per-decl
  scope (the nested extendScalars instances). Tooled golf + heartbeats
  review defer to CLEANUP-FINAL.

### [T904] Evaluation at π_n (authors Coleman/Theorem.lean)
- **Status**: done (2026-06-12, items 1–6; item 7 → [T904b]) | **File**: Coleman/Theorem.lean | **Depends on**: T902
- **Parallel**: yes (after T902; independent of T903) | **Type**: def+lemmas
- **Statement** (authored): `evalPi (f : PowerSeries ℤ_[p]) (n) : ℂ_[p]`
  := seriesEval (map-to-ℂ_[p] f) (pi p n); lemmas: `evalPi_mem_O`
  (integral coeffs + ‖π‖ < 1 ⟹ value in the ball; in K_n: partial sums
  in ℤ_p[ξ_n], K_n closed (finite-dim complete subspace — mathlib
  `Submodule.complete_of_finiteDimensional`/closed); `evalPi_mul/one/add`
  (the §8 seriesEval_mul/seriesEval_one layer + summability from
  integral coeffs ‖coeff‖ ≤ 1); `evalPi_unit (f : ℤ_p⟦T⟧ˣ)`: value is a
  unit of O_n (f·f⁻¹ = 1 evaluated); `evalPi_phi (n) :
  evalPi (phiSeries p f)?? — CARE: phiSeries is over K-coefficients in
  FormalPsi; over ℤ_[p]: the §3 Toolbox `phi`-series form — use the
  measure-side `PadicMeasure.phi`-transform or restate: evalPi of
  f((1+T)^p−1): subst is formal-legal ((1+T)^p−1 has constant 0 ✓) —
  evalPi (f.subst ((1+X)^p−1)) (n+1) = evalPi f n (eq:varphi pin,
  TeX 2647–2649: (π_{n+1}+1)^p − 1 = π_n via zetaSys_pow_p) — the
  subst-eval composition: the §7 `seriesEval_subst_formalLog`-style
  bridge BUT with polynomial G = (1+X)^p−1 (FINITE subst — much easier:
  subst by a POLYNOMIAL: coeff-finite, the double sum is finite-by-rows;
  prove a small `seriesEval_subst_poly` helper or evaluate through
  `Polynomial.aeval`); single-level interpolation (TeX 2538–2547):
  ∀ u unit of O_n, ∃ f ∈ ℤ_p⟦T⟧ˣ, evalPi f n = u — the greedy π-adic
  digit construction (totally-ramified: O_n/(π_n) = 𝔽_p — from T902's
  e·f = d ramification... ATTACK: needs residue-field-trivality:
  O_n/(π_n) ≅ ℤ_p/(p)?? — totally ramified ⟸ e = d ⟸ ‖π‖^d = p⁻¹
  exactly (T902); the greedy step needs: ∀ x ∈ O_n ∃ a ∈ ℤ_p,
  x ≡ a mod π_nO_n — i.e. ℤ_p + π_nO_n = O_n — from the O-basis (T903's
  digit expansion at level... hmm the basis is for the STEP; full-level:
  O_n = ℤ_p[ξ_n] (monogenic over ℤ_p — T903-adjacent; the Eisenstein
  machinery gives O_n = ℤ_p[π_n] — survey Q2(b))); state the lemma with
  the O_n = ℤ_p[π_n]-input from T903 and recursively choose digits
  (`Nat.rec`-construction + convergence: the constructed series'
  partial sums converge to u: ‖u − S_k‖ ≤ ‖π‖^k → 0).
- **Sources**: TeX 2528–2547 (Q-prose + the single-level lemma),
  2647–2649 (eq:varphi pin); replan R10.3.
- **Sizing**: ~200 LOC.
- **Progress (2026-06-12)**: items 1–6 DONE, sorry-free + axiom-clean (standard
  3 only on all 13 publics), build green, lines ≤ 100. Authored in
  `Coleman/Theorem.lean`:
  - `toCp : ℤ_[p] →+* ℂ_[p]` := `(algebraMap ℚ_[p] ℂ_[p]).comp Coe.ringHom`
    (the §7 M-pattern); `norm_toCp` (isometry, `norm_algebraMap'`+`norm_def`);
    `norm_coeff_map_le_one`.
  - `evalPi f n := seriesEval (map toCp f) (pi p n)`; `summable_evalPi {n}
    (hn : 1 ≤ n)` (`summable_seriesEval_of_norm_coeff_le_one` + `norm_pi_lt_one`).
  - ring-hom pack `{n} (hn : 1 ≤ n)`: `evalPi_add/sub/mul` (seriesEval_add/sub/mul
    + summability), `evalPi_one` (=`C 1`, `seriesEval_C`), `evalPi_X` (= `pi`,
    seriesEval_X inlined ~3 lines), `evalPi_pow` (induction via `evalPi_mul`).
  - `evalPi_mem_O {n} (hn : 1 ≤ n)`: ‖·‖≤1 via `norm_tsum_le_of_forall_le`
    (per-term ≤1); ∈ K_n via partial sums ∈ K_n (`algebraMap_mem` + `pi_mem_K`
    pow + `sum_mem`) and K_n closed — re-derived `finiteDimensional_K` (private,
    `adjoin.finiteDimensional` + `IsPrimitiveRoot.isIntegral.tower_top`),
    `isClosed_K` (`Submodule.closed_of_finiteDimensional`), then
    `IsClosed.mem_of_tendsto` + `HasSum.tendsto_sum_nat`.
  - `evalPi_phi {n} (hn : 1 ≤ n)` (eq:varphi pin): `evalPi (phiSeries p f) (n+1) =
    evalPi p f n` — `map_phiSeries` (map ∘ φ = φ ∘ map; public in FormalPsi) +
    `seriesEval_phi_of_summable_prod` + `summable_prod_of_norm_coeff_le_one`
    (both public, NOT private — no ResidueZeta-Fubini reproduction needed since
    G = (1+X)^p−1 is already the FormalPsi φ-bridge's substituend), then the value
    identity `(1+π_{n+1})^p−1 = π_n` (private `one_add_pi_pow_sub_one`,
    `zetaSys_pow_p`) and `rfl` to fold into `evalPi p f n`.
  - **Replan note**: `phiSeries p` is R-generic (FormalPsi, over any `CommRing`),
    so `phiSeries p f` over `ℤ_[p]` is the correct φ on `ℤ_p⟦T⟧` directly — the
    ticket's "phiSeries is over K-coefficients" worry is moot.
  - Item 7 (single-level interpolation, TeX 2538–2547) MOVED to [T904b] below:
    its honest dependency is the absolute monogenicity `O_n = ℤ_p[π_n]` (T903b),
    not derivable inside T904's budget without duplicating T903b.
- **Verification**: `lake build PadicLFunctions.Coleman.Theorem` green;
  `#print axioms` on all 13 publics = `[propext, Classical.choice, Quot.sound]`;
  wired `import PadicLFunctions.Coleman.Theorem` into `PadicLFunctions.lean`.

### [T904b] Single-level interpolation (split from T904 item 7)
- **Status**: done (2026-06-12) | **File**: Coleman/Theorem.lean | **Parent**: T904
- **Progress (2026-06-12)**: DONE, sorry-free, axiom-clean (`propext`,
  `Classical.choice`, `Quot.sound`). `lake build PadicLFunctions` green.
  Final signature exactly as planned: `exists_evalPi_eq {n} (hn : 1 ≤ n) {u}
  (hu : u ∈ O p n) (hnorm : ‖u‖ = 1) : ∃ f : PowerSeries ℤ_[p], IsUnit f ∧
  evalPi p f n = u`.
  - **Replan note (residue step)**: the T903b Tower toolkit could NOT be reused —
    `exists_pi_repr`/`forall_norm_le_one_of_norm_sum_pi_pow_le_one`/
    `norm_pow_totient_mem_zpow` are `private` (file-scoped, inaccessible from
    Theorem.lean — verified) AND specialised to the `n→n+1` tower step (`K_{n+1}`),
    not the absolute level-`n` residue. `O_succ_exists_digits` is accessible but
    does not reach level 1 (degree `p−1` step), and recursing it needs the base
    case anyway. The absolute monogenicity `O_n = ℤ_p[π_n]` is unproven.
  - **Realised STEP 1 instead via the absolute orthogonal ℚ_p-power expansion**
    (self-contained, all levels `n ≥ 1` uniformly): `K_n = ℚ_p⟮π_n⟯`
    (adjoin-shift `ζ_n ↔ π_n`), power basis `{π_n^i}_{i<φ(p^n)}`
    (`IntermediateField.adjoin.powerBasis` + `finrank_K`); orthogonality from
    pairwise-distinct term norms (`‖q_i‖ ∈ p^ℤ` via `Padic.norm_eq_zpow_neg_valuation`,
    `‖π_n‖^{φ(p^n)} = p⁻¹` via the accessible `norm_pi_pow_totient`) →
    `IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne`; `‖x‖ ≤ 1` forces
    `q_0 ∈ ℤ_p` and each tail term `≤ ‖π_n‖` by elementary ℤ-arithmetic. The
    ℚ_p-coefficient route makes the value group elementary (no spectralNorm needed).
  - **Helpers added** (all private): `quot_mem_O` (remainder stays in 𝒪_n),
    `term_norm_le_pi` + `term_norm_distinct` (the value-group arithmetic),
    `exists_residue_pi` (the residue step). STEPs 2–4 (Nat.rec digit recursion +
    telescoping `u − S_m = π_n^m·r_m` + convergence via uniqueness of limits +
    unit via ultrametric isoceles `‖a_0‖ = ‖u‖ = 1`) as planned.
- **Status (historical)**: in_progress (2026-06-12) | **File**: Coleman/Theorem.lean | **Parent**: T904
- **Depends on**: T904 (done), T903b (O_n = ℤ_p[π_n] monogenicity) | **Type**: theorem
- **Statement**: `exists_evalPi_eq {n} (hn : 1 ≤ n) {u : ℂ_[p]} (hu : u ∈ O p n)
  (hnorm : ‖u‖ = 1) : ∃ f : PowerSeries ℤ_[p], IsUnit f ∧ evalPi p f n = u`
  — every norm-one element of `O_n` is the value at `π_n` of a unit power
  series (RJW TeX 2538–2547, the single-level interpolation lemma).
- **Proof sketch** (greedy π-adic digits, TeX 2542–2547 verbatim): from the
  absolute monogenicity `O_n = Σ_{i<φ(p^n)} ℤ_p·π_n^i` (T903b, route 2 sub-step
  (a): `O_m = adjoin ℤ_p {π_m}` ⟹ ℤ_p-power-basis `{π_n^i}`), the residue step
  `∀ x ∈ O_n, ∃ a : ℤ_p, x − toCp a ∈ π_n·O_n` (totally ramified ⟹ O_n/(π_n) ≅
  𝔽_p, the residue field of the absolute ℤ_p-basis), recursively build the
  digit series `f = Σ a_k T^k`: at step k, `a_k := (residue of (u − S_{k-1})/π_n^k)`,
  then `‖u − evalPi p (Σ_{j≤k} a_j T^j) n‖ ≤ ‖π_n‖^{k+1} → 0` (convergence via
  `norm_pi_lt_one` powers → 0); `evalPi p f n = u` by `HasSum`/closedness; `f` a
  unit since `evalPi p f n = u` has ‖·‖ = 1 ⟹ constantCoeff f is a unit ⟹ f ∈
  ℤ_p⟦T⟧ˣ (`PowerSeries.isUnit_iff_constantCoeff_isUnit` over local ℤ_p).
- **Sources**: TeX 2538–2547 (the single-level lemma + greedy digits). Consumer:
  T910 (existence half of the global Coleman interpolation, per-level `f_n`).
- **Sizing**: ~120 LOC (the residue step + the `Nat.rec` digit construction +
  convergence; the monogenicity input is T903b's deliverable).

### [T905] Uniqueness via Weierstrass preparation
- **Status**: DONE (2026-06-12) | **File**: Coleman/Theorem.lean | **Depends on**: T904
- **Type**: lemma
- **Statement** (authored, final): `evalPi_injective {f g : PowerSeries ℤ_[p]}
  (h : ∀ n, 1 ≤ n → evalPi p f n = evalPi p g n) : f = g`
  (lem:unique-coleman, TeX 2635–2642). [Name simplified from the sketched
  `evalPi_injective_of_forall` — it is an injectivity statement.]
- **Progress (2026-06-12)**: sorry-free, axiom-clean (standard 3 on all 5 new
  decls), `lake build PadicLFunctions` green (3818 jobs), lint-clean (≤100 cols,
  no unused-var warnings). Added `import Mathlib.RingTheory.PowerSeries.
  WeierstrassPreparation` to Theorem.lean.
  - **Weierstrass API actually used**: `PowerSeries.exists_isWeierstrassFactorization`
    (hypothesis `g.map (IsLocalRing.residue ℤ_[p]) ≠ 0`); the structure
    `PowerSeries.IsWeierstrassFactorization d' r u` with fields `.eq_mul`
    (`d' = ↑r * u`), `.isUnit`, `.isDistinguishedAt.monic`. Confirmed mathlib's
    form is `g = f·h` with NO p-power factor (f distinguished/monic, h unit),
    so the p-content extraction IS needed as a preprocessor (the sketch's
    alternative). Instances `IsLocalRing ℤ_[p]` and
    `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]` both already in mathlib
    (PadicIntegers.lean:499, :532) — no instance derivation needed.
  - **Helpers added (5 decls total)**: `evalPi_C` (@[simp], public);
    `evalPi_coe_polynomial` (private — the tsum→`Polynomial.eval` bridge,
    convergence-free finite sum, no n≥1 needed); `pi_norm_injective` (private —
    distinct norms via `norm_pi_pow_totient` + `pow_lt_pow_right_of_lt_one₀` +
    totient strict-mono); `exists_C_pow_mul` (private — the p-content extraction,
    REPLAN: no mathlib `exists_eq_pow_mul`/order-over-(p) lemma found in a
    five-method search, so hand-built ~25 lines: m := sInf of coeff valuations,
    coeff-wise division via `Classical.choice` of dvd-witnesses + `PowerSeries.mk`,
    minimality from `PadicInt.mem_span_pow_iff_le_valuation`).
  - Final assembly: `Polynomial.eq_zero_of_infinite_isRoot` +
    `Set.infinite_of_injective_forall_mem` (map `n ↦ pi p (n+1)`); residue-nonzero
    via `IsLocalRing.residue_eq_zero_iff` + `PadicInt.maximalIdeal_eq_span_p`.
- **Sources**: TeX 2635–2642 (verbatim Weierstrass argument).
- **Sizing**: ~135 LOC (incl. 4 helpers + docstrings).

### [T906] The norm operator 𝒩 via the digit basis (authors
Coleman/NormOperator.lean)
- **Status**: DONE (2026-06-12) | **File**: Coleman/NormOperator.lean
- **Depends on**: none (pure ℤ_p⟦T⟧-algebra; parallel with the tower)
- **Progress (2026-06-12)**: `Coleman/NormOperator.lean` authored, sorry-free,
  axiom-clean (standard 3 on all public decls), `lake build PadicLFunctions`
  green (3815 jobs), lint-clean. Realisation: **Algebra.norm route** landed (NOT
  the direct-det fallback). Decls (all in `PadicLFunctions.Coleman`):
  `padicIntEquivIntegerRing : ℤ_[p] ≃+* integerRing ℚ_[p]` (the bridge, via
  `RingEquiv.ofBijective` on `Coefficients.lean`'s algebraMap — both are the
  ℚ_[p] norm-ball subtype); `existsUnique_digits_padicInt` (transports
  FormalPsi's `existsUnique_digits` along `PowerSeries.map`); `phiHom`/
  `phiHom_apply` (FormalPsi's `phiSeries` as a `RingHom` via `substAlgHom`);
  `PhiAlg` type-synonym carrying LOCAL `Algebra (PowerSeries ℤ_[p]) (PhiAlg p)`
  (= `RingHom.toAlgebra phiHom`; does NOT leak onto bare `PowerSeries ℤ_[p]`)
  + `PhiAlg.toPS` (≃+* repackaging) + `toPS_algebraMap`/`smul_def`;
  `digitBasis : Module.Basis (Fin p) (PowerSeries ℤ_[p]) (PhiAlg p)` (via
  `Module.Basis.mk`: li = uniqueness half, span = existence half of the digit
  decomp) + `Module.Free`/`Module.Finite` instances; `normOp (f) := Algebra.norm`
  + `normOp_mul` (MonoidHom `map_mul`), `normOp_one`, `normOp_isUnit`
  (`IsUnit.map`); `digitMatrix`/`normOp_eq_det` (det characterisation via
  `Algebra.norm_eq_matrix_det digitBasis` — the form T907 transports through
  `RingHom.map_det`). `phi_normOp_eq_prod` NOT stated (μ_p-product not formal,
  replan R10.4 — recorded in module docstring).
- **Parallel**: yes | **Type**: def+lemmas
- **Statement** (authored): the φ-algebra `phiAlg : Algebra
  (PowerSeries ℤ_[p]) (PowerSeries ℤ_[p])` := RingHom.toAlgebra
  (the §3 φ-ring-hom (subst (1+X)^p−1) — local instance, NOT global);
  `digitBasis : Basis (Fin p) ...` from the PROVEN integral digit
  decomposition (FormalPsi T605 layer — the ∃!-decomposition F =
  Σ(1+T)^iφ(F_i) IS the free-basis statement: `Basis.mk` from
  linear-independence + span, both = the uniqueness/existence halves);
  `normOp (f) : PowerSeries ℤ_[p]` := Algebra.norm along phiAlg —
  CARE: Algebra.norm lands in the BASE = ℤ_p⟦T⟧-as-A: normOp := the
  norm VALUE (an element of the base copy) — no φ⁻¹ needed (the base IS
  ℤ_p⟦T⟧; the source's φ⁻¹ is an artifact of viewing A inside B);
  `normOp_mul` (Algebra.norm multiplicative — wait norm is
  MonoidHom-multiplicative ✓ `Algebra.norm`-MonoidHom), `normOp_one`,
  `normOp_unit` (norm of unit is unit: `Algebra.norm`-isUnit transport
  — for FREE algebras `IsUnit.map`-route via det of invertible lmul);
  `phi_normOp_eq_prod`-form NOT stated (the μ_p-product is not formal —
  replan R10.4; the evaluated form is T907's square).
- **Proof sketch**: per R10.4; the basis: FormalPsi's digit
  existence/uniqueness (grep the exact decl names of the T605 layer:
  the ∃!-statement over ℤ_[p]-coefficient series; bridge ∃!-decomposition
  ↔ Basis: `Basis.mk` with linearIndependent from uniqueness-at-0 and
  span from existence — module structure = phiAlg's restrictScalars).
- **Sources**: TeX 2654–2670 (Q3 + the B/A free-of-rank-p framing:
  "obtained by adjoining a p-th root of (1+T)^p"); replan R10.4.
- **Sizing**: ~160 LOC.

### [T907] The evaluation/norm commuting square
- **Status**: done (2026-06-12) — det route (evalPiHom + RingHom.map_det +
  Algebra.norm_eq_matrix_det on the ξ-power K_n-basis via
  basisOfLinearIndependentOfCardEqFinrank + O_succ_digits_unique); NO p ≠ 2
  needed; axioms standard 3 | **File**: Coleman/Theorem.lean
- **Depends on**: T903, T904, T906 | **Type**: theorem
- **Statement** (authored): `evalPi_normOp (f) {n} (hn : 1 ≤ n) :
  evalPi p (normOp p f) n = levelNorm p n (evalPi p f (n+1))`
  (Q4, TeX 2673–2692).
- **Proof sketch**: both sides are dets: LHS: normOp = det of
  mult-by-f in digitBasis (matrix M over A ≅ ℤ_p⟦T⟧); evalPi∘(A-copy
  embedding) = the ring hom A → O_n sending φ(g) ↦ evalPi g n... the
  A-entries map under (φ-inverse then evalPi-at-n) = evalPi-at-(n+1)∘incl
  (eq:varphi pin, T904's evalPi_phi); `RingHom.map_det`: evalPi(det M) =
  det(M mapped); RHS: levelNorm = det of mult-by-(evalPi f (n+1)) in the
  O_n-basis (ξ_{n+1}^i) (T903's O_succ_basis; Algebra.norm = det via
  `Algebra.norm_eq_matrix_det` at that basis); the mapped digit matrix
  IS the O-basis matrix: the basis correspondence (1+T)^i ↦ ξ^i_{n+1}
  under evalPi-at-(n+1) (evalPi((1+T)^i) = ξ^i: evalPi_mul/pow +
  evalPi(1+T) = 1 + π = ξ ✓) + the module-map compatibility
  (`LinearMap.toMatrix`-naturality along the ring-hom base change —
  the matrix-entry identity: f·(1+T)^i = Σ_j φ(M_{ij})(1+T)^j evaluated
  gives f(π)·ξ^i = Σ M_{ij}(π_n)·ξ^j — entrywise push of the digit
  identity through evalPi ✓ multiplicativity + additivity + a
  convergence-commutes-with-finite-sums step).
- **Sources**: TeX 2673–2692 (Q4 verbatim); replan R10.4.
- **Sizing**: ~150 LOC.

### [T908] The mod-p^k continuity of 𝒩
- **Status**: done (2026-06-12) — (i)+ModEqPow+ψ-layer (first dispatch);
  (ii) det-over-𝔽_p/Frobenius route (M̄^p = diagonal f̄ + frobenius_inj —
  replan vs the twisted-circulant), (iii) `Matrix.det_one_add_smul` + the
  trace identity tr(digitMatrix h) = p·ψ(h) (TeX 2670!), (iv) the division
  iterate. All axiom-clean.
- **Depends on**: T906 | **Type**: lemmas
- **Statement** (authored; Q5): `phi_injective_mod` ((i): φf ≡ 1 mod p^k
  → f ≡ 1 mod p^k — coefficientwise: φ's coefficient matrix is
  unitriangular-supported: coeff_{pj}(φf) = coeff_j f + (lower
  contributions p-divisible?) — honest route: φf − 1 = φ(f − 1) and
  φ-coefficient-extraction: ‖φg‖-coeff sup = ‖g‖-coeff sup mod p^k:
  the SUBSTITUTION (1+X)^p−1 has lowest term pX + … + X^p: coeff-of-φg
  at p·(top index)… prove by strong induction on the least index where
  f − 1 has a unit-mod-p^k coefficient); `normOp_congr_self` ((ii):
  𝒩f ≡ f mod p): ATTACK per R10.5 — primary route: mod p, φ̄(g) = g(T^p)
  = g^p-Frobenius-free… det route: M ≡ f·Id + N mod p?? — fallback
  (RECORDED): prove (ii) via the evaluated O₁⟦T⟧-product form using
  mathlib `PowerSeries.eval₂`/MvPowerSeries-substitution at the
  topologically-nilpotent η(1+T)−1 over the (π₁)-adic O₁⟦T⟧ (legal
  there), the congruence η(1+T)−1 ≡ T mod 𝔭₁ (TeX 2743–2751's own
  argument!), and descent by (i) + 𝔭₁ ∩ ℤ_p⟦T⟧-bookkeeping
  (TeX 2751: "this is actually an equivalence modulo 𝔭₁p^k ∩ ℤ_p =
  p^{k+1}"); `normOp_one_congr` ((iii): f ≡ 1 mod p^k, k ≥ 1 ⟹ 𝒩f ≡ 1
  mod p^{k+1}): TeX 2743–2751 verbatim route (the same O₁-congruence +
  f^p ≡ 1 mod p^{k+1} + (i)); `normOp_iterate_congr` ((iv)): from
  (ii)+(iii) by the division-and-iterate argument (TeX 2753–2755:
  𝒩^{k₂−k₁}f/f ≡ 1 mod p + iterate (iii) k₁ times — needs unit-division:
  f ∈ ℤ_p⟦T⟧ˣ here ✓ statement carries the unit hypothesis as in
  source).
- **Sources**: TeX 2726–2756 (Q5 verbatim + the source's own proofs of
  (iii)/(iv); (i)/(ii) "left as an exercise (cf. CS06 Lem 2.3.1)" —
  expanded by us per the source-gap rule, routes above).
- **Sizing**: ~220 LOC (the board's analytical heart; survey-gated on
  the O₁⟦T⟧-substitution API if the fallback route is needed).

### [T909] Compactness of ℤ_p⟦T⟧^× and sequential extraction
- **Status**: DONE (2026-06-12) | **File**: Coleman/NormOperator.lean
- **Progress (2026-06-12)**: authored in `Coleman/NormOperator.lean` (Compactness
  section, `open scoped PowerSeries.WithPiTopology`), sorry-free, axiom-clean,
  full build green. KEY: the Pi topology IS `inferInstanceAs` of the function-type
  Pi instance (`MvPowerSeries.WithPiTopology` def), so on the UNFOLDED type
  `(Unit →₀ ℕ) → ℤ_[p]` the standard Pi instances fire: `instCompactSpace`
  (`Pi.compactSpace` + `CompactSpace ℤ_[p]`) and `instSeqCompactSpace` (index
  `Unit →₀ ℕ` countable via `Data.Finsupp.Encodable` ⟹ Pi uniformity countably
  generated ⟹ metrizable ⟹ first-countable ⟹ `SeqCompactSpace` from compact),
  both via `inferInstanceAs`. NOTE: `metrizableSpace_pi` needs `[Finite ι]` (won't
  fire — index is countably infinite); the working route is the
  uniformity/`iInf.isCountablyGenerated` path, automatic here. Also:
  `exists_subseq_tendsto` (= `SeqCompactSpace.tendsto_subseq`), `tendsto_coeff`
  (projection continuity, `WithPiTopology.continuous_coeff`), `isClosed_isUnit`
  (units = preimage of `{1} ⊆ ℝ` under `‖constantCoeff ·‖`, via
  `isUnit_iff_constantCoeff` + `PadicInt.isUnit_iff` + `continuous_constantCoeff`).
  Stopped at (iii) per ticket — evalPi-continuity is T910's own (Theorem.lean).
  Imports added: `LinearAlgebra.Basis.Basic`, `RingTheory.Norm.Basic`,
  `RingTheory.PowerSeries.PiTopology`, `Topology.Metrizable.Uniformity`,
  `Data.Finsupp.Encodable`. PadicLFunctions.lean wired (after Coleman.Tower).
- **Note (orig)**: in_progress (2026-06-12, 3-way parallel) | **File**: Coleman/NormOperator.lean
- **Depends on**: none | **Parallel**: yes | **Type**: lemmas
- **Statement** (authored): with the Pi topology (open scoped
  WithPiTopology): `instance : CompactSpace (PowerSeries ℤ_[p])`
  (homeomorph to ℕ → ℤ_[p] + Tychonoff: `Pi.compactSpace` ✓ mathlib +
  the PowerSeries≃Pi homeomorphism — `PowerSeries`-toFun is literally
  ℕ →₀-free… PowerSeries R := MvPowerSeries Unit R := (Unit →₀ ℕ) → R:
  the coefficient equiv to (ℕ → R) — search FormalPsi/mathlib PiTopology
  for the established homeomorphism or build `Homeomorph.mk` from the
  linear equiv + continuity-both-ways (coordinatewise ✓));
  `seqCompact`-extraction: metrizable (countable product of metrizable:
  `TopologicalSpace.PseudoMetrizableSpace`-Pi-instance) + compact ⟹
  `IsCompact.isSeqCompact`; the unit-subset: {f | IsUnit f} =
  {f | IsUnit (constantCoeff f)} (`PowerSeries.isUnit_iff_constantCoeff` ✓
  mathlib) is CLOSED (preimage of the closed ℤ_[p]ˣ-ball-condition
  ‖constantCoeff f‖ = 1 under the continuous coeff-0 projection) ⟹
  sequences of units with convergent subsequence have unit limits;
  `evalPi`-continuity in f (coefficientwise-convergence ⟹ values
  converge: uniform bound ‖coeff‖ ≤ 1, dominated/ultrametric tail —
  needed to pass g_m(π_n) → f_u(π_n) in the diagonal argument: state as
  `evalPi_tendsto_of_tendsto`: pointwise-coefficient convergence +
  uniform integrality ⟹ evalPi converges — ultrametric 3ε: split at
  coefficient-index N with ‖π‖^N small).
- **Sources**: TeX 2784 ("such a subsequence exists, as ℤ_p⟦T⟧^× is
  compact"); replan R10.6.
- **Sizing**: ~150 LOC.

### [CLEANUP-ALL-9] Pre-milestone /cleanup-all
- **Status**: done (2026-06-12, degraded mode) — project builds green with
  ZERO warnings after the Map.lean namespace-closer fix (orchestrator);
  all four Coleman files docstringed, helpers private, axioms standard 3
  re-verified per ticket. Tooled golf defers to CLEANUP-FINAL | **Depends on**: T901–T909 | **Type**: cleanup-all

### [T910] **MILESTONE: Coleman's theorem** (RJW thm:coleman power
series + thm:coleman map 2)
- **Status**: DONE (2026-06-12) — `coleman_existsUnique` (∃!: existence via
  the TeX 2763–2791 diagonal, uniqueness via T905 `evalPi_injective`) +
  wrappers `colemanSeries` (choice), `colemanSeries_isUnit`/`normOp_colemanSeries`/
  `evalPi_colemanSeries` (the 3 choose_spec components), `colemanSeries_mul`
  (ExistsUnique.unique on the product), `colemanSeries_eq_iff` (honest
  injectivity iff — see below), `NormCompatUnits.ext` (@[ext]). All 10 new
  publics axiom-clean (propext/Classical.choice/Quot.sound); `lake build
  PadicLFunctions` green. | **File**: Coleman/Theorem.lean
- **Depends on**: T905, T907, T908, T909, CLEANUP-ALL-9 | **Type**: theorem
- **Route notes (bridges added for the (d)-step, both axiom-clean)**:
  - `norm_evalPi_sub_le_of_modEqPow {m} (hfg : ModEqPow p (m+1) f g) (hn : 1 ≤ n)
    : ‖evalPi f n − evalPi g n‖ ≤ (p⁻¹)^(m+1)`. Proof: `modEqPow_iff_exists_C_mul`
    gives `f − g = C(p^{m+1})·h`; `evalPi_sub`+`evalPi_mul`+`evalPi_C` ⟹
    `evalPi f n − evalPi g n = toCp(p^{m+1})·evalPi h n`; `norm_toCp`+`PadicInt.norm_p`
    give `‖toCp(p^{m+1})‖ = (p⁻¹)^{m+1}` and `evalPi_mem_O` gives `‖evalPi h n‖ ≤ 1`.
  - `tendsto_evalPi_of_tendsto (hg : Tendsto g atTop (nhds h)) (hn : 1 ≤ n)
    : Tendsto (fun j => evalPi (g j) n) atTop (nhds (evalPi h n))`. The honest
    ultrametric `max(head,tail)` argument (NOT a generic continuity lemma —
    evalPi is a tsum, not Pi-continuous): difference =
    `∑'_k toCp(coeff_k(g_j − h))·π_n^k`; per-term bound `≤ max(∑_{k<N} ‖coeff_k‖,
    ‖π_n‖^N)` (k<N: ‖π‖^k ≤ 1 and head-sum dominates; k≥N: ‖coeff‖ ≤ 1 and
    ‖π‖^k ≤ ‖π‖^N); `IsUltrametricDist.norm_tsum_le_of_forall_le` lifts to the
    tsum; head → 0 by `tendsto_coeff`+`tendsto_finsetSum`, tail < ε by choosing
    `‖π_n‖^N < ε`. Uses `Metric.tendsto_atTop` + `Nonempty ℕ` for the tsum bound.
  - Diagonal (d) joins TWO limits of `evalPi (g (φ j)) n` (`g_m := 𝒩^[m] F_{2m}`):
    limit A = `evalPi f_u n` (`tendsto_evalPi_of_tendsto` on `g∘φ → f_u`); limit B
    = `u_n` (squeeze: `u_n = evalPi(𝒩^[2m−n]F_{2m}) n` by the (b)-induction at
    `k=2m−n`, congruent mod `p^{m+1}` to `g_m` by `normOp_iterate_modEq` k₁=m,
    k₂=2m−n, then `norm_evalPi_sub_le_of_modEqPow`; `(p⁻¹)^{φj+1}→0` since
    `φ` StrictMono); joined by `tendsto_nhds_unique`. (b)-induction strengthened
    to `∀ n` and uses `Function.iterate_succ_apply'` + `evalPi_normOp` + `u.compat`.
  - helper `norm_elems_eq_one` (private): `‖u.elems n‖ = 1` from
    `‖u‖,‖u⁻¹‖ ≤ 1` (mem/inv_mem) + `‖u‖·‖u⁻¹‖ = 1`.
- **CLEANUP-FINAL note (level-0 vestige)**: `NormCompatUnits` carries `elems 0`
  unconstrained (its `compat` is ∀ n ≥ 1). So `colemanSeries` is NOT injective on
  the nose — stated honestly as `colemanSeries_eq_iff : colemanSeries u =
  colemanSeries v ↔ ∀ n ≥ 1, u.elems n = v.elems n` (mirrors RJW's `𝒰_∞ =
  lim_{n≥1}`, no level-0 component). Changing the structure to start at n=1 is a
  T903-statement-change — deliberately NOT done; revisit at CLEANUP-FINAL if a
  level-0 normalisation is wanted.
- **Statement** (authored; Q1+Q2): existence-uniqueness package:
  `theorem coleman (u : NormCompatUnits p) : ∃! f : PowerSeries ℤ_[p],
  IsUnit f ∧ normOp p f = f ∧ ∀ n, 1 ≤ n → evalPi p f n = u.elems n`
  + the multiplicativity/injectivity wrappers (`colemanSeries u`-def via
  choice; `colemanSeries_mul`; `colemanSeries_injective`) realising
  "unique injective homomorphism 𝒰_∞ → ℤ_p⟦T⟧^×" and the refined
  𝒩-fixed image (Q2).
- **Proof sketch**: uniqueness: T905. Existence: TeX 2763–2791 verbatim:
  per-level f_n by T904's single-level lemma; 𝒩^k f_{n+k}(π_n) = u_n by
  T907-iterate; g_m := 𝒩^m f_{2m}; u_n ≡ g_m(π_n) mod p^{m+1} by
  T908(iv) (the evalPi-side congruence: f ≡ g mod p^{m+1} ⟹ evalPi
  agree mod p^{m+1}-ball: coefficientwise + ‖π‖ ≤ 1 — small bridge);
  T909-extraction: convergent subsequence g_{m_j} → f_u (units-closed ⟹
  f_u unit); evalPi-continuity (T909) passes the limit: evalPi f_u n =
  lim g_{m_j}(π_n) = u_n; 𝒩-invariance: 𝒩(f_u) and f_u are both
  Coleman series of u (T907 + norm-compat of u) ⟹ equal by T905.
  Group-hom packaging: multiplicativity from uniqueness of the product
  series (evalPi_mul + normOp_mul); injectivity: f_u = 1-values ⟹ u = 1
  (evalPi 1 = 1). Blueprint: wire ColemanMap.lean chapter's
  thm:coleman-nodes in the same cycle (T912 does the chapter pass).
- **Sources**: TeX 2553–2560 (Q1), 2763–2807 (Q6 + thm:coleman map 2).
- **Sizing**: ~180 LOC.

### [T911] Cyclotomic units and the logarithmic-derivative bridge
(authors Coleman/Map.lean)
- **Status**: done (2026-06-12) — Map.lean authored (365 lines): cycloUnit
  (+mem/norm/ne_zero pack), cyclo : NormCompatUnits (engine + levelNorm_div),
  ∂log f_{c(a)} = (a−1) − F_a (T704 template), the residue bridge
  Res((a−1)−Fa-measure) = −Res(μ_a). All 8 publics axiom-clean. | **File**: Coleman/Map.lean | **Depends on**: T903
- **Parallel**: yes (after T903; independent of T905–T910)
- **Type**: def+lemmas
- **Statement** (authored; Q7): `cycloUnit (a) (n) : ℂ_[p]` :=
  (ξ_n^a − 1)/(ξ_n − 1); `cycloUnit_isUnit {a} (ha : ¬p∣a) {n} (hn)`:
  it's a unit of O_n (both numerator and denominator are
  same-norm: ‖ξ^a−1‖ = ‖ξ−1‖ (ξ^a = (ξ)^a with a coprime: ξ^a is also
  primitive ⟹ T902's norm formula applies to BOTH via the reindexed
  system) ⟹ ratio has norm 1 + lies in K_n ✓); `cycloUnit_normCompat`:
  levelNorm-compatibility (Q7's computation = T903's levelNorm_collapse
  at b = a and b = 1 + norm-multiplicativity/division);
  `cyclo (a) (ha) : NormCompatUnits p` (the packaged tower c(a));
  `evalPi_geomCyclo (a) (n ≥ 1) : evalPi p (geomSum-form) n = cycloUnit`:
  the explicit Coleman series f_{c(a)} = ((1+T)^a − 1)/T — REUSE
  `PadicMeasure.geomSum p a` (MuA.lean: geomSum·X = (1+X)^a − 1 — the
  SAME series!): f_{c(a)} := geomSum p a and the evaluation:
  geomSum(π_n)·π_n = ξ^a − 1 (evaluated geomSum_mul_X) ⟹ value =
  cycloUnit ✓ (division in the field); `colemanSeries_cyclo :
  colemanSeries (cyclo a) = geomSum p a` (uniqueness T905 + the
  evaluations + 𝒩-fixedness FROM T910's uniqueness package — or directly
  via the ∃!); `oneAdd_mul_derivative_log_geomSum` (Q7's prop:coleman
  zetap): ∂log f_{c(a)} := (1+T)·(geomSum)'·inverse(geomSum)-form =
  (a − 1) − Fa p a: PURE ℤ_p⟦T⟧-algebra against MuA's
  `one_add_X_pow_sub_one_mul_Fa`/geomSum-API (clear denominators by
  geomSum (unit for p∤a, isUnit_geomSum ✓): the identity
  (1+T)·D(geomSum)·1 = ((a−1) − Fa)·geomSum — derive from
  differentiating geomSum·X = (1+X)^a − 1: (the §8 T704-pattern
  VERBATIM — hQ/hDpow machinery); `restriction_bridge` (Q7's lem:relate
  cyclo to mua): (1−φψ)-applied: ∂log f_{c(a)}-measure restricted =
  −Res_{ℤ_p^×}(μ_a): at the measure level: the measure with transform
  ∂log f = (a−1)·δ₁-free… the transform-side identity
  (1−φψ)((a−1) − F_a) = −(1−φψ)F_a (constants are φψ-fixed:
  φψ(C) = C — the §3 Toolbox/ψ-of-constant: ψ(1) = 1 ✓ res-kills-
  constants: RJW's "1−φ∘ψ kills the term a−1", TeX 2620–2622).
- **Sources**: TeX 2572–2628 (Q7 verbatim); MuA.lean (geomSum, Fa).
- **Sizing**: ~190 LOC.

### [T912] **MILESTONE: the Coleman map and ζ_p = Col(c(a))/θ_a**
- **Status**: DONE (2026-06-12; degraded mode — no lean-lsp MCP, validated via
  `lake env lean` + `#print axioms` temp-file). Lean code sorry-free,
  axiom-clean (`propext, Classical.choice, Quot.sound` only on all 8 new
  publics), `lake build PadicLFunctions` green, zero linter warnings,
  zero >100-char lines. **Blueprint pass deferred to orchestrator** (per
  dispatch: do NOT wire). | **File**: Coleman/Map.lean
- **Depends on**: T910, T911 | **Type**: def+theorem
- **Progress (2026-06-12, T912 execution)**: delivered in Coleman/Map.lean
  (imports widened to `Coleman.Theorem` + `KubotaLeopoldt.ZetaP`):
  1. `evalPi_geomSum (a) {m} (hm : 1 ≤ m) : evalPi (geomSum a) m = cycloUnit a m`
     — geomSum·X = (1+X)^a−1 evaluated at π_m, ÷ π_m.
  2. `colemanSeries_cyclo {a} (ha : ¬p∣a) (hp2) : colemanSeries (cyclo a) =
     geomSum a` (RJW TeX 2589–2592) — via `coleman_existsUnique.unique`: the
     three clauses (IsUnit `isUnit_geomSum`; 𝒩-fix via `evalPi_injective` +
     `evalPi_normOp` + `levelNorm_cycloUnit`; interpolation `evalPi_geomSum`).
  3. `dlog (f) := (1+X)·f′·Ring.inverse f`; helper `iota_comp_extendByZero`
     (`ι(μ.comp extendByZero) = Res μ`, general form of `iota_muAUnits`).
  4. `Col (u : NormCompatUnits p) : PadicMeasure p ℤ_[p]ˣ` (RJW Def:coleman
     map, TeX 2826–2832) := `unitsCmul invCM ((𝒜⁻¹(dlog f_u)).comp
     extendByZero)` — the §4 zetaNum/muAUnits pattern (comp-extendByZero =
     units-section restriction, no Classical-choice section).
  5. `dlog_geomSum {a} (ha) : dlog (geomSum a) = (a−1) − Fa` (cleared
     `one_add_mul_derivative_log_geomSum` ÷ geomSum via `Ring.mul_inverse_cancel`).
  6. `Col_cyclo {a} (ha) (hp2) : Col (cyclo a) = −zetaNum a` — the
     provable core; `(𝒜⁻¹((a−1)−Fa)).comp extendByZero = −muAUnits a` pinned
     by `iota_injective` (`iota_comp_extendByZero` + `res_derivative_log_geomSum`
     + `iota_muAUnits`), then `unitsCmul_neg`.
  7. `coleman_to_kl (hp2) : algebraMap (dirac u − 1) · padicZeta =
     −algebraMap (Col (cyclo m))` (RJW thm:coleman to kl, TeX 2836–2841,
     **honest sign**) — `IsLocalization.mk'_spec'` (([u]−1)·ζ_p = zetaNum m)
     + `Col_cyclo` + `neg_neg`.
- **SIGN RESOLUTION (scenario α — ERRATUM #12 written)**: TeX 1551 θ_a =
  [a]−[1] (= our `dirac u − 1`, NO twist); TeX 1568 DefZetap ζ_p =
  (x⁻¹Res μ_a)/θ_a (= our `mk'(zetaNum, [a]−1)`). TeX 2614 lem:relate cyclo
  has the minus: Res(μ_{∂log f}) = −Res(μ_a). So Col(c(a)) = −zetaNum a. But
  TeX 2839 thm:coleman-to-kl states ζ_p = Col(c(a))/θ_a with NO sign;
  combined with 2614 + 1568 that is contradictory → the notes drop a minus
  at 2839 (errata #12). Honest theorem stated with the minus: ζ_p =
  −Col(c(a))/θ_a, i.e. ([a]−1)·ζ_p = −Col(c(a)). errata.md #12 appended.
- **Statement** (authored; Q8): `Col (u : NormCompatUnits p) :
  PadicMeasure p ℤ_[p]ˣ` := the §3/§4 composition: 𝓐⁻¹ of the
  ψ=0-series x⁻¹-divided… realised measure-side: the measure ν with
  ι(ν) = mahler-inverse of (1−φψ)(∂log f_u) restricted-divided — REUSE
  the §4 zetaNum-pattern: Col u := unitsCmul p (invCM p)
  (res-to-units of the measure of ∂log f_u) (the EXACT composite RJW
  lists, each arrow already a project construction: mahlerLinearEquiv⁻¹,
  PadicMeasure.res/iota-comp, unitsCmul invCM); `theorem coleman_to_kl
  (hp2) {a} (gen-pack for a)`: algebraMap-form: padicZeta p hp2 =
  Col(cyclo a)-image / θ_a-image in QuotientField p — stated via the
  witness equation: algebraMap (θ_a-measure) * padicZeta = algebraMap
  (Col (cyclo a))-shaped?? CARE with sign: lem:relate cyclo gives
  −Res(μ_a): ζ_p's witness is zetaNum = x⁻¹Res(μ_a); Col(c(a)) =
  x⁻¹Res(μ_{∂log f}) = −zetaNum?? — SIGN ATTACK at execution: RJW
  Q8 states ζ_p = Col(c(a))/θ_a with NO sign; our lem-bridge has the
  −: re-derive: ∂log f_{c(a)} = (a−1) − F_a; μ_{(a−1)−F_a} = (a−1)δ₀-c…
  Res kills (a−1)-part? (1−φψ)((a−1)) = 0 ✓ so Res μ_{∂log f} =
  −Res μ_a — so Col(c(a)) = −x⁻¹Res μ_a = −zetaNum(a)?! Then
  ζ_p = −Col/θ_a?? — CHECK RJW's θ_a: §4's θ_a := [a] − 1?? RJW §4
  (sec:dep on a): θ_a-measure with ∫x^k θ_a = a^{k+1}... RE-READ at
  execution; the sign discrepancy is a LIKELY ERRATUM #12 candidate
  (or θ_a's own sign absorbs it) — the ticket REQUIRES the executor to
  resolve the sign against §4's actual θ_a def and our padicZeta
  (zetaNum/(δ_a − 1)) and record (errata.md if the notes' display is
  off; replan note if our θ-realisation differs). Then the proof:
  moment-comparison of both pseudo-measures' witnesses against
  `pseudoMeasure_eq_zero_of_moments` (R10.8): the ([b]−1)-witnesses of
  both sides have equal x^k-moments for all k > 0: LHS-witness =
  zetaNum-data (padicZeta_moments-machinery); RHS: Col(cyclo a)-moments
  via the transform (∂-shifts and (1−φψ)-restriction in moments —
  the §4 moment-lemmas (`res`-moments, `unitsCmul`-moments,
  mahler-transform-of-measure moments — all §3/§4 API). Blueprint:
  Chapters/ColemanMap.lean full wiring pass (thm:coleman nodes,
  cyclo-units nodes, Col-node, coleman-to-kl node + §10.5-prose nodes
  stay unwired with a deferral note) + `lake build
  PadicLFunctionsBlueprint` + site render.
- **Sources**: TeX 2826–2841 (Q8 verbatim), 2572–2628; §4 ZetaP.
- **Sizing**: ~170 LOC + blueprint pass + the sign-resolution.

### [T-D61] Deferred-debt planning ticket: Thm 6.1(ii) at D = 1
- **Status**: done (2026-06-12 — decompose pass complete: Explore survey
  (muEtaCleared junk at D = 1 confirmed; hD1 table; Route A selected),
  decomposition.md D61 section, gated sub-board D611–D613 appended; NOT
  dispatched: awaits its own 1i review per charter) | **File**: (planning) | **Depends on**: none
- **Parallel**: yes | **Type**: develop-pass
- **Task**: run the Phase-1e decompose pass for the pure p-power-conductor
  case of RJW Thm 6.1(ii) (the notes' own gap — errata.md #6): θ = χ of
  conductor p^m, m ≥ 1, χ ≠ 1; target `LpFunction_one`-analogue at D = 1.
  Expected route (recorded 2026-06-12): pair χ directly against the
  pseudo-measure ζ_p via its ([b]−1)-witnesses (χ ≠ 1 ⟹ finite); the
  §8 twist machinery (unitsTwist generalised to χ-twists — the
  CLEANUP-FINAL-noted generalisation) + the §5 NonTame p-power Gauss-sum
  machinery + the §6 c₀-design at D = 1 (no tame clearing). Deliverable:
  decomposition.md addendum + skeleton + tickets appended to this board
  (the §6-debt sub-board). NOT dispatched to /beastmode until its own
  1i review.
- **Sources**: TeX 1987–2010 + 2040–2179 re-read; errata #6.

### [CLEANUP-92] /cleanup after T904–T906 (cadence, Theorem+NormOperator)
- **Status**: done (2026-06-12, degraded mode) — both halves swept; zero
  project warnings at every wave | **Depends on**: T904, T905, T906 | **Type**: cleanup

### [CLEANUP-93] Final per-file cleanup (Coleman/*) + close-out
- **Status**: done (2026-06-12, degraded mode) | **Depends on**: T912 | **Type**: cleanup
  (+ widen CLEANUP-FINAL to §§9–10)
- **Progress**: 2026-06-12: degraded sweep: 4 Coleman files (3773 lines
  total), build green, ZERO non-Verso warnings; >105-byte lines are
  unicode comments (linter quiet); publics docstringed, helpers private.
  Blueprint ColemanMap chapter fully wired (17 nodes; §10.5
  Kummer/Euler/Perrin-Riou nodes stay prose per the deferral) + site
  re-rendered. Tooled golf + the NormCompatUnits-elems-0 vestige + the
  Theorem.lean (1158-line) split candidate defer to CLEANUP-FINAL.

### [D611] χ-twisted moments of ζ_p (GATED: D61 1i review)
- **Status**: open (GATED — not dispatchable until the D61 sub-board passes
  its 1i review) | **File**: ValuesAtOne.lean or a new ValuesAtOneWild.lean
- **Depends on**: none | **Type**: theorem
- **Statement** (shape; skeleton at dispatch): witness-encoded
  `∫χ(x)x^k·ζ_p` moments for χ of conductor p^m (m ≥ 1), χ ≠ 1: for any b
  and witness ν of ([b]−1)ζ_p: the χ-twisted pairing of ν at x^k equals
  (χ(b)b^k − 1)-normalised (1 − χ(p)p^{k−1})·L(χ,−k)-data. Route: transport
  `padicZeta_moments` through the §5 p-power twist layer (Twist.lean) —
  the D = 1 analogue of `zetaEta_twisted_moments` (decomposition D61).
- **Sources**: TeX 1614–1768 (§5.1) + errata #6.

### [D612] The wild L_p-object at D = 1 (GATED: D61 1i review)
- **Status**: open (GATED) | **File**: as D611 | **Depends on**: D611
- **Type**: def+lemmas
- **Statement** (shape): `LpFunctionWild` — G(χ⁻¹)⁻¹-normalised χ-twisted
  ζ_p-pairing at p^m-level; Gauss-unit lemma at p-power conductor
  (mathlib gaussSum_mul_gaussSum_inv); agreement with the D > 1
  LpFunction-convention noted in docstring.
- **Sources**: TeX 1930-area (Def 5.18 at D = 1) + decomposition D61.

### [D613] L_p(χ,1) at D = 1 — the deferred Thm 6.1(ii) case (GATED)
- **Status**: open (GATED) | **File**: as D611 | **Depends on**: D611, D612
- **Type**: theorem (closes errata #6's formalisation debt)
- **Statement** (shape): `LpFunctionWild_one`: L_p(χ,1) =
  −(1−χ(p)p⁻¹)·G(χ⁻¹)⁻¹·Σ_{c mod p^m} χ⁻¹(c)·extLog(1−ε^c). Route: the §6
  c₀-design at N = p^m, no tame clearing; AT DISPATCH re-audit which §6
  helpers need 1 < D (μ_η-side: replaced by D611) vs 1 < N (fine: p^m > 1)
  — see decomposition D61's note.
- **Sources**: TeX 2040–2179 + errata #6.

## §9–10 dependency quick-view
```
T901 → T902 → T903 → CL91 ; T906 ; T909 ; T-D61(planning)
T903 → T903b (O-basis monogenicity, split 2026-06-12)
T902 → T904 → T905 ; T903b,T904,T906 → T907 ; T906 → T908
T904,T905,T906 → CL92
T905,T907,T908,T909 → CLALL9 → T910* → T912*
T903 → T911 → T912*(T910,T911) → CL93
```
Note (2026-06-12): T907's `O_n`-basis input moved from T903 to **T903b**
(T903 item 8 was split out; T903 items 1–7 are done). T911 still depends only
on T903 (`levelNorm` + `NormCompatUnits`, both delivered).

---

# §11 board — Iwasawa's theorem on the zeros: the §11 layer (TeX 2949–3112)

Decomposition: `.mathlib-quality/decomposition.md` R11 (quotes Q1–Q12, replans
R11.1–R11.8). Skeleton (canonical): `PadicLFunctions/Iwasawa/{PlusPart, ZetaGalois,
LocalUnits, CyclotomicUnits}.lean` — `lake build` green at board creation
(2026-06-13), sorries only in the four new files. Scope note (plan.md §11): the
statements of `thm:iwasawa` and the class-number index theorem are NOT on this
board (Q9 permanently-deferred prose; Q11 → §12 board). hp2-conventions: the
±-splitting and everything ζ_p carry `(hp2 : p ≠ 2)`; the bare c-invariance
criterion is p-general.

### [T1101] Generalise the convolution algebra to compact commutative monoids
- **Status**: done (2026-06-13, at skeleton construction — performed sorry-free
  during /develop to avoid a data-diamond placeholder instance for Λ(𝒢⁺); full
  `lake build` green before AND after; downstream files untouched and rebuilt
  clean; statement-preservation audited: `units_mul_apply`,
  `units_mul_apply_unitsPowCM`, `units_one_def`, `units_dirac_mul_dirac`,
  `deg`, `augmentationIdeal` all keep their exact downstream-facing statements)
  | **File**: Measure/PseudoMeasure.lean | **Depends on**: none
- **Type**: refactor (replan R11.5)
- **What changed**: `mulCM₂ G` / `conv` / `Mul`/`One`/`CommRing` instances /
  `conv_dirac_mul_dirac` / `deg` / `augmentationIdeal` now live over
  `{G} [TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]`
  (RJW Rem. 3.33's generality); `unitsMulCM₂`/`unitsConv` are abbrevs, the
  `units_*` lemmas restatements (`rfl`). This is what makes
  `CommRing (PadicMeasure p (GPlus p))` an instance, with zero new analysis
  (`innerInt`/`integral_swap` were already general).
- **Sources**: TeX 1173–1175 (eq:convolution), Rem. 3.33; R11.5 attack log.

### [T1102] The ±-decomposition: involution splitting + the c-action + the
odd-moment criterion (RJW lem:decompose plus minus + the TeX 3019 lemma)
- **Status**: done (2026-06-13; agent: all 11 decl-groups filled — general involution splitting via invOf_smul_smul disjointness + explicit ⅟2-codisjointness; SMulCommClass/IsScalarTower instances real (the §8 gap closed); cAct via mulLeft; criterion via eq_zero_of_forall_unitsPowCM + add_self_eq_zero. Helpers reordered above isCompl, no statement changes. lake build exit 0; #print axioms on ALL 11 decls = {propext, Classical.choice, Quot.sound}, no sorryAx. Degraded-mode cleanup deferred to CLEANUP-111.) | **File**: Iwasawa/PlusPart.lean | **Depends on**: T1101 (done)
- **Parallel**: yes (vs T1105, T1108 — different files) | **Type**: lemmas + instances
#### Statement (skeleton canonical)
General: `mem_invariants_iff`, `mem_antiInvariants_iff`,
`isCompl_invariants_antiInvariants [Invertible (2:R)] (σ) (hσ : σ ∘ₗ σ = id)`,
`smul_add_apply_mem_invariants`, `smul_sub_apply_mem_antiInvariants`.
Λ-side: `SMulCommClass ℤ_[p] Λ Λ` + `IsScalarTower ℤ_[p] Λ Λ` instances,
`cAct_apply`, `cAct_involutive`, `mem_plusPart_iff`, `mem_minusPart_iff`,
`mul_mem_plusPart`, `isCompl_plusPart_minusPart (hp2)`.
Criterion: `cAct_apply_unitsPowCM`, `mem_plusPart_iff_forall_odd_moment`.
#### Proof sketch
1. General splitting (Q3's idempotent proof): `e := ⅟2 • (1 + σ)`; for `x`,
   `x = ⅟2•(x + σx) + ⅟2•(x − σx)` with the parts in ker(σ∓1) by `hσ`
   (apply σ, expand); disjointness: `σx = x` ∧ `σx = −x` ⟹ `2x = 0` ⟹
   `x = ⅟2•(2x) = 0`. `IsCompl` via `disjoint + codisjoint`
   (`Submodule.isCompl_iff`-style; or `isCompl_of_proj` with the idempotent —
   mathlib has the idempotent API, LinearAlgebra/Projection).
2. Bilinearity instances: `(c•μ)*ν = c•(μ*ν)` is `rfl`-adjacent from `conv`
   (the outer μ is applied last); `μ*(c•ν) = c•(μ*ν)` via `innerInt_smul`.
   Closes the §8-noted IsScalarTower gap.
3. `cAct_involutive`: `mulLeft` composition = mulLeft of product;
   `units_dirac_mul_dirac` gives `[−1]·[−1] = [1]`; `mulLeft 1 = id`.
4. Criterion (Q5's proof): moments of `[−1]*μ` via `units_mul_apply_unitsPowCM`
   + `dirac_apply`: `((−1:ℤ_[p]ˣ):ℤ_[p])^k = (−1)^k`. (→) odd k:
   `μ(x^k) = −μ(x^k)` ⟹ `2·μ(x^k) = 0` ⟹ 0 (ℤ_[p] char-0 domain — no hp2).
   (←) δ := `[−1]*μ − μ` has ALL moments 0 (odd by hypothesis ×(−2);
   even by cancellation) ⟹ δ = 0 by `eq_zero_of_forall_unitsPowCM_eq_zero`.
- **Mathlib**: `LinearMap.mulLeft`, `IsIdempotentElem`/`LinearMap.isProj_*`
  (Projection.lean), `invOf` API; `PadicLFunctions.isUnit_two_padicInt` (§8) for
  `Invertible (2:ℤ_[p])` from hp2.
- **Sources**: Q3 (TeX 2994–3002), Q5 (TeX 3019–3029), TeX 3004.
- **Sizing**: ~150 LOC.

### [T1103] 𝒢⁺ and the projection ring hom π_*
- **Status**: done (2026-06-13; agent wave 2: projPlus RingHom fields via congr-on-curried-inner-functions (mk's hom property definitional on the quotient), projPlus_apply/dirac, deg_projPlus. Axioms standard at join. | **File**: Iwasawa/PlusPart.lean | **Depends on**: T1102 (file order)
- **Parallel**: no (same file as T1102) | **Type**: def-fields + lemmas
#### Statement
`projPlus` RingHom fields (toFun = `pushforward p (quotientMk p)` — fixed),
`projPlus_apply`, `projPlus_dirac`, `deg_projPlus`.
#### Proof sketch
1. `map_one'/map_mul'`: pushforward along the continuous MonoidHom
   `QuotientGroup.mk`. map_one: both sides are `dirac` at `mk 1 = 1`
   (`pushforward_dirac`). map_mul: for `g : C(GPlus p, ℤ_[p])`,
   `mk∘mul_𝒢 = mul_𝒢⁺∘(mk×mk)` (mk monoid hom), so
   `(g.comp quotientMk).comp (mulCM₂ 𝒢) = (g.comp (mulCM₂ 𝒢⁺)).comp (mk×mk)`;
   then `innerInt p ν` of that at `x` = `innerInt p (projPlus ν) (g∘mul⁺) (mk x)`
   (curry computation, `ContinuousMap.ext`), and the outer integral transports.
   map_zero/map_add: linearity of pushforward (`rfl`).
2. `projPlus_apply`: `rfl`. `projPlus_dirac`: `pushforward_dirac` (Basic.lean).
3. `deg_projPlus`: `1 ∘ mk = 1` (`rfl`-ext).
- **Mathlib**: `QuotientGroup.mk' `, `continuous_quotient_mk'` (already used in the
  skeleton's `quotientMk`); instance pack verified at decompose
  (Quotient.lean:36/:151).
- **Sources**: Q4's "natural surjection" (TeX 3012); R11.2 attack log item (2).
- **Sizing**: ~80 LOC.

### [T1104] The even-part section and Λ(𝒢)⁺ ≅ Λ(𝒢⁺) (RJW TeX 3006–3015)
- **Status**: done (2026-06-13; agent wave 2: all section/iso/kernel decls; 10 private helpers incl. dirac_neg_one_mul_apply (convolution-by-[−1] = argument negation), descendEven/evenPart calculus, Submodule.existsUnique_add_of_isCompl decomposition; ker_projPlus via Ideal.mem_span_singleton. Statements unchanged. Axioms standard at join: projPlus/plusEquiv/plusSection_projPlus/projPlus_surjective/ker_projPlus all clean. lake build exit 0. Cleanup deferred to CLEANUP-111 (note: one linter.style.show warning to fix). | **File**: Iwasawa/PlusPart.lean | **Depends on**: T1102, T1103
- **Parallel**: no (same file) | **Type**: defs + lemmas (replan R11.2)
#### Statement
`negTranslate` continuity field, `evenPart_even`, `descendEven` (soundness +
continuity fields), `descendEven_mk`, `plusSection` (4 linearity fields),
`plusSection_mem_plusPart`, `projPlus_plusSection`, `plusSection_projPlus`,
`projPlus_surjective`, `plusEquiv` round-trips, `projPlus_eq_zero_iff`,
`ker_projPlus`.
#### Proof sketch
1. `negTranslate`: `u ↦ -u = (-1)*u`, `continuous_const.mul continuous_id`
   (`ContinuousMul ℤ_[p]ˣ` ✓).
2. `descendEven` soundness: `Quotient.liftOn'`-coherence: `leftRel (zpowers −1)`
   relates u,v iff `v = ±u` (zpowers of an order-2 element = {1, −1}:
   `(-1:ℤ_[p]ˣ)^2 = 1`, `zpowers_eq` … enumerate via `Subgroup.mem_zpowers_iff`
   + order-2); continuity: `(QuotientGroup.isQuotientMap_mk).continuous_iff`,
   the composite with mk is `g` ✓ continuous.
3. `evenPart_even`: `−(−u) = u` + commutativity of the average; the ⅟2-smul
   is a fixed scalar.
4. `plusSection` linearity: ν linear + `descendEven`/`evenPart` additive in f
   (descendEven of a sum = sum of descends: check on `mk`-points via
   `descendEven_mk` + `Quotient.ind` — or prove `descendEven` is the unique
   continuous lift and use uniqueness).
5. Round-trips (R11.2 attack log): `projPlus (plusSection ν) = ν`: at
   `g : C(𝒢⁺)`, `evenPart (g∘mk) = g∘mk` (mk∘negTranslate = mk:
   `QuotientGroup.mk (−u) = mk u` since `(−u)⁻¹u = −1 ∈ zpowers`), and
   `descendEven (g∘mk) = g` (agree on mk-points, `Quotient.ind`).
   `plusSection (projPlus μ) = μ` for c-invariant μ:
   `μ(evenPart f) = ⅟2(μ f + μ(f∘negTranslate))`; `μ(f∘negTranslate) =
   ([−1]*μ)(f) = μ f` (mem_plusPart_iff; the convolution-by-dirac =
   argument-translation: curry computation); so `μ(evenPart f) = μ f`;
   and `(plusSection (projPlus μ))(f) = (projPlus μ)(descendEven …) =
   μ((descendEven …)∘mk) = μ(evenPart f)` ✓.
6. `projPlus_eq_zero_iff`: (←) μ ∈ minusPart: `μ(g∘mk) = μ(evenPart (g∘mk))`…
   for minus-part: `μ(f∘τ) = −μ(f)` ⟹ `μ(even fn) = 0`; g∘mk is even ⟹ 0.
   (→) `projPlus μ = 0` ⟹ plus-component of μ is `plusSection (projPlus μ⁺…)`
   — cleanest: decompose μ = μ⁺ + μ⁻ (T1102 IsCompl), projPlus μ⁻ = 0 (above),
   so projPlus μ⁺ = 0, so μ⁺ = plusSection (projPlus μ⁺) = 0.
7. `ker_projPlus`: minusPart = span{[−1]−1}: (⊇) `projPlus ([−1]−1) =
   dirac(mk −1) − dirac 1 = 0` (mk(−1) = 1). (⊆) μ ∈ minusPart ⟹
   μ = ([−1]−1)·(−⅟2•μ) (compute: ([−1]−1)·μ = [−1]μ − μ = −2μ).
- **Mathlib**: `IsQuotientMap.continuous_iff`, `Quotient.liftOn'`,
  `QuotientGroup.eq` (coset equality), `Submodule.exists_add_eq_of_isCompl`-style
  decomposition API.
- **Sources**: Q4 (TeX 3006–3017); replan R11.2 (recorded: functional route;
  the source's finite-level rank count would need the still-deferred
  Prop 3.9/3.10).
- **Sizing**: ~220 LOC. The board's largest single ticket; Tier-A split point if
  needed: descend/section machinery (4) vs round-trips (5–7).

### [CLEANUP-111] /cleanup PlusPart.lean
- **Status**: done (2026-06-13, DEGRADED MODE — no lean-lsp MCP session-wide: lake-build linter set green on PlusPart.lean, zero warnings (1 show→change fixed at join); 10 private helpers reviewed-by-name (descendEven/evenPart calculus — coherent); golf pass deferred: fold-in note added to CLEANUP-FINAL). | **Depends on**: T1102–T1104. Single-file pass after the
  PlusPart chain (degraded mode if no lean-lsp MCP — record it).

### [T1105] Odd moments of ζ_p vanish + c-invariance (erratum #13 realised)
- **Status**: done (2026-06-13; axiom check at join: all 4 decls = {propext, Classical.choice, Quot.sound}. Degraded-mode cleanup deferred to CLEANUP-112.) | **File**: Iwasawa/ZetaGalois.lean | **Depends on**: T1101 (done)
- **Progress**: 2026-06-13: agent filled all 4 sorries (odd_moment_factor_eq_zero via eq_or_lt case split + bernoulli_eq_zero_of_odd; moments via padicZeta_moments + Subtype.coe_injective descent; c-invariance via the b=−1 witness + eq_zero_of_forall_unitsPowCM; witness_neg via units_dirac_mul_dirac + mul_neg_one + IsFractionRing.injective). Statements unchanged. Degraded mode (no lean-lsp MCP). File compiles, 11 sorries remain = T1106/T1107's. AXIOM CHECK PENDING the wave-1 join (needs PlusPart olean rebuild).
- **Parallel**: yes (vs T1102-chain — different file; uses only proven §3/§4 API)
- **Type**: lemmas
#### Statement
`odd_moment_factor_eq_zero {k} (hk : Odd k) : (1 − (p:ℚ_[p])^(k−1)) ·
((zetaNeg (k−1) : ℚ) : ℚ_[p]) = 0`; `padicZeta_odd_moment_eq_zero`;
`dirac_neg_one_sub_one_mul_padicZeta : algebraMap … ([−1]−1) · ζ_p = 0`;
`padicZeta_witness_neg`.
#### Proof sketch
1. Factor lemma (the erratum-#13 case split): k = 1 ⟹ `p^(1−1) = p^0 = 1`
   ⟹ first factor 0. k odd ≥ 3 ⟹ `zetaNeg (k−1) = (−1)^{k−1}·bernoulli k/k`
   (unfold zetaNeg; `k−1+1 = k` for k ≥ 1) and `bernoulli_eq_zero_of_odd hk
   (by omega : 1 < k)` ⟹ second factor 0. Cast through ℚ → ℚ_[p].
2. Witness odd moments: `padicZeta_moments p hp2 b hk' ν hν` gives
   `(ν(x^k):ℚ_[p]) = (b^k−1)·(factor)` = 0 by (1); `ν(x^k) = 0` by
   `Subtype.coe_injective`-style (ℤ_[p] ↪ ℚ_[p], the T-pattern in
   kubotaLeopoldt's uniqueness proof — copy).
3. c-invariance: the b = −1 witness ν₀ (exists: `padicZeta_isPseudoMeasure`)
   has all moments 0: `padicZeta_moments` at b = −1: `((−1)^k − 1)·factor`;
   k even ⟹ first factor 0; k odd ⟹ second factor 0 by (1). So ν₀ = 0
   (`eq_zero_of_forall_unitsPowCM_eq_zero`), and the witness identity reads
   `([−1]−1)·ζ_p = algebraMap 0 = 0`.
4. Witness symmetry: `ν' − ν` witnesses `([−g]−[g])·ζ_p = [g]·([−1]−1)·ζ_p
   = 0` (by 3); witnesses are unique (`IsFractionRing.injective`), so ν' = ν.
- **Mathlib**: `bernoulli_eq_zero_of_odd` (Bernoulli.lean:217, verified).
- **Sources**: Q2 (TeX 2992), Q6 + erratum #13 (TeX 3033–3039; errata.md #13).
- **Sizing**: ~110 LOC.

### [T1106] ζ_p as a pseudo-measure on 𝒢⁺ (the corollary, RJW TeX 3033)
- **Status**: done (2026-06-13; agent wave 3: regularity transport via plusSection landing in plusPart ⊓ minusPart = ⊥ + mul_right_mem_nonZeroDivisors_eq_zero_iff; padicZetaPlus denominator via the packed generator; witness compat via IsFractionRing.injective + mk'_spec + IsUnit.mul_left_inj; the COROLLARY isPlusPseudoMeasure_padicZetaPlus via QuotientGroup.mk_surjective. Statements unchanged. Axioms standard at join; build green; 1 show→change lint fixed by orchestrator. Cleanup deferred to CLEANUP-112. | **File**: Iwasawa/ZetaGalois.lean
- **Depends on**: T1102, T1104, T1105 | **Parallel**: no
- **Type**: def-fields + lemmas
#### Statement
`dirac_mk_sub_one_mem_nonZeroDivisors`, the `padicZetaPlus` denominator
membership (its `by sorry` subterm), `projPlus_padicZeta_witness`,
`isPlusPseudoMeasure_padicZetaPlus`.
#### Proof sketch
1. Regularity transport (D4, R11 leaf ledger): suppose `ν·([ā]−1) = 0` in
   Λ(𝒢⁺). Lift `μ := plusSection ν ∈ plusPart` (T1104); then
   `projPlus (μ·([a]−1)) = ν·([ā]−1) = 0` (T1103 map_mul + T1104
   projPlus_plusSection + projPlus_dirac), and `μ·([a]−1) ∈ plusPart`
   (`mul_mem_plusPart`), so `μ·([a]−1) ∈ plusPart ⊓ ker = plusPart ⊓
   minusPart = ⊥` (T1104 projPlus_eq_zero_iff + T1102 IsCompl.disjoint) ⟹
   `μ([a]−1) = 0` ⟹ μ = 0 (hypothesis `ha`) ⟹ `ν = projPlus μ = 0`.
   Mirror for the left factor (CommRing — same argument).
2. Denominator membership: instantiate (1) at the packed generator
   (`topGen_pow_ne_one` + `dirac_sub_one_mem_nonZeroDivisors`, both proven §3/§4).
3. Witness compat (D5): from the 𝒢-side defining relation
   `([a]−1)·ζ_p = zetaNum m` (mk'_spec') and the witness identity at g:
   `([g]−1)·zetaNum m = ([a]−1)·ν` in Λ (pull back along the injective
   algebraMap — the padicZeta_moments-proof pattern); apply the RING HOM
   projPlus: `([ḡ]−1)·projPlus(zetaNum m) = ([ā]−1)·projPlus ν`; divide in
   Q(𝒢⁺) by the regular `([ā]−1)` (IsLocalization.mk' algebra) to get the
   claimed witness identity for ζ_p⁺ = mk'(projPlus (zetaNum m))/([ā]−1).
4. The corollary: for `ḡ : 𝒢⁺` choose a lift g (`QuotientGroup.mk_surjective`),
   take the 𝒢-side witness (padicZeta_isPseudoMeasure), push by (3).
   (Lift-independence is not even needed for the ∃-statement; it is the
   content of T1105's witness symmetry and (3) jointly.)
- **Sources**: Q6 (TeX 3033–3039), Q1's closing sentence; R11 leaf ledger D4/D5.
- **Sizing**: ~140 LOC.

### [T1107] The ideals I(𝒢)ζ_p and I(𝒢⁺)ζ_p (RJW Proposition, TeX 3052)
- **Status**: done (2026-06-13; agent wave 3: zetaIdeal/zetaIdealPlus carrier-ideals + Iff.rfl mem-iffs + eq_span antisymmetries via augmentationIdeal(Plus)_eq_span; the 𝒢⁺ principality lifted along projPlus_surjective with deg_projPlus. Axioms standard at join.) | **File**: Iwasawa/ZetaGalois.lean
- **Depends on**: T1105, T1106 | **Parallel**: no (same file)
- **Type**: def-fields + lemmas (replan R11.4)
#### Statement
`zetaIdeal` carrier-Ideal fields + `mem_zetaIdeal_iff` + `zetaIdeal_eq_span`;
`augmentationIdealPlus_eq_span`; `zetaIdealPlus` fields + `mem_zetaIdealPlus_iff`
+ `zetaIdealPlus_eq_span`.
#### Proof sketch
1. Ideal fields (no principality needed): zero: l := 0; add: l₁ + l₂
   (aug ideal add-closed); smul r x: l' := r·l (`Ideal.mul_mem_left`;
   `algebraMap (r·l) = algebraMap r·algebraMap l`, rearrange in Q). mem_iff: rfl.
2. `zetaIdeal_eq_span` (⊇): ν ∈ zetaIdeal with l := [b]−1 ∈ aug (deg of
   dirac−1 = 0). (⊆): x with `algebraMap x = algebraMap l·ζ_p`, l ∈ I(𝒢) =
   span{[b]−1} (`augmentationIdeal_eq_span p hb` — proven §3): l = ρ·([b]−1);
   then `algebraMap x = algebraMap ρ·(([b]−1)ζ_p) = algebraMap (ρ·ν)`
   (witness hν) ⟹ `x = ρ·ν` (IsFractionRing.injective) ∈ span{ν}.
3. `augmentationIdealPlus_eq_span`: `deg⁺∘π_* = deg` (T1103) + π_* surjective
   (T1104): `ker deg⁺ = π_*(ker deg)` (⊇ by composition; ⊆: lift y = π_* x,
   `deg x = deg⁺ y = 0`); then `π_*(span{[a]−1}) = span{π_*([a]−1)}`
   (`Ideal.map_span` along the surjection; `Ideal.map` vs image — use
   `Ideal.map_eq_submodule_map`-style or argue elementwise with surjectivity).
4. 𝒢⁺-ideal: same as (1)–(2) with T1106's `padicZetaPlus` witnesses and (3)
   for the principality; the span generator is `projPlus ν` by the witness
   compatibility (T1106 step 3).
- **Sources**: Q7 (TeX 3047–3057); replan R11.4 (the "topological ideal"
  line replaced by the proven principality).
- **Sizing**: ~160 LOC.

### [CLEANUP-112] /cleanup ZetaGalois.lean
- **Status**: done (2026-06-13, DEGRADED MODE: ZetaGalois.lean lint-green (1 show→change fixed at join); toQPlus-bridge idiom noted; golf deferred to CLEANUP-FINAL). | **Depends on**: T1105–T1107.

### [T1108] The local unit groups 𝒰_n, 𝒰_{n,1} and the ⁺-variants
- **Status**: done (2026-06-13; axiom check at join: localUnits/norm_eq_one/localUnitsOne/KPlus_le_K/localUnitsPlus all standard-axioms, no sorryAx. Degraded-mode cleanup deferred to CLEANUP-113.) | **File**: Iwasawa/LocalUnits.lean | **Depends on**: none new
- **Progress**: 2026-06-13: agent filled all 10 sorries / 7 decls (localUnits via Units.val_mul/mul_inv_rev/inv_inv; norm_eq_one via Subring.mem_inf + Units.mul_inv + nlinarith; localUnitsOne via norm_add_le_max + field_simp + norm_sub_rev; KPlus_le_K via adjoin_simple_le_iff; localUnitsPlus via val_inv_eq_inv_val + inv_mem). Statements unchanged, no helpers, degraded mode. 12 sorries remain = T1109/T1110's. AXIOM CHECK PENDING wave-1 join.
- **Parallel**: yes (vs T1102-chain and T1105 — different file)
- **Type**: def-fields + lemmas
#### Statement
`localUnits`/`localUnitsOne`/`localUnitsPlus` Subgroup fields, `mem_*_iff` (rfl),
`norm_eq_one_of_mem_localUnits`, `KPlus_le_K`.
#### Proof sketch
1. `localUnits` closure: mul: `O p n` is a Subring (`mul_mem`), inverses
   distribute (`mul_inv_rev`, coe lemmas `Units.val_mul`/`Units.val_inv_eq…`);
   inv: swap the two conjuncts.
2. `norm_eq_one`: `‖u‖ ≤ 1` and `‖u⁻¹‖ ≤ 1` (integerRing membership unfolds to
   the norm bound — `O = K ⊓ integerRing`, Coefficients.lean) with
   `‖u‖·‖u⁻¹‖ = 1` (`norm_mul`, NormMulClass ℂ_[p]) ⟹ both = 1.
3. `localUnitsOne` closure: mul: `uv − 1 = u(v−1) + (u−1)`, ultrametric max +
   `‖u‖ = 1`; inv: `u⁻¹ − 1 = u⁻¹(1 − u)`, norms multiply.
4. `KPlus_le_K`: `adjoin_le_iff`; `ξ + ξ⁻¹ ∈ K_n`: ξ ∈ K_n (zetaSys_mem_K),
   ξ⁻¹ ∈ K_n (IntermediateField.inv_mem), sum closed.
- **Sources**: Q12 (TeX 2474, 2494, 2473); replan R11.6.
- **Sizing**: ~120 LOC.

### [T1109] The ℤ_p-power structure on principal units (RJW TeX 2494–2496)
- **Status**: done (2026-06-13; agent wave 2: zpPow via PadicInt.addChar_of_value_at_one — the addChar route. INSTANCE-PACK DESIGN WIN: Algebra ℤ_[p] ℂ_[p] built diamond-FREE by supplying UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) and letting Completion machinery construct Module/Algebra over the pre-existing orphan SMul (a naive (toCp).toAlgebra would have hit a SMul diamond); + IsBoundedSMul via norm_toCp. New global instances flagged for promotion review at CLEANUP-113. Character laws via DenseRange.equalizer over denseRange_natCast; K_n closedness via finrank_K + Submodule.closed_of_finiteDimensional; zpPow_mem_of_closed density-transfer reused 3x. Module on Additive(localUnitsOne) complete. Axioms standard at join; build green; 2 longLine lints wrapped by orchestrator. | **File**: Iwasawa/LocalUnits.lean | **Depends on**: T1108
- **Parallel**: no (same file) | **Type**: def + lemmas + instance
#### Statement
`zpPow` (the sorried def body — to be filled with the
`PadicInt.addChar_of_value_at_one`-route or a direct `mahlerSeries` construction),
`zpPow_natCast`, `zpPow_add`, `zpPow_mul`, `norm_zpPow_sub_one_lt_one`,
`zpPow_mem_localUnitsOne`, `localUnitsOneModule` instance.
#### Proof sketch
1. Instance pack on ℂ_[p]: `Algebra ℤ_[p] ℂ_[p]` via `(toCp p).toAlgebra`
   (Coleman/Theorem.lean's `toCp`) declared as a SCOPED/local instance (do not
   leak a global instance on mathlib types) + `IsBoundedSMul` (norm of the
   algebra-map image ≤ 1 ⟹ `‖c • x‖ ≤ ‖c‖·‖x‖`… the smul is via the hom,
   bounded as `‖toCp c‖ = ‖c‖ ≤ 1`); `CompleteSpace ℂ_[p]` ✓ exists.
   FALLBACK (decision recorded at decompose): define zpPow directly as
   `mahlerSeries`-free limit `lim_k (y ^ (a_k))` over integer approximations
   a_k → a (Cauchy by `‖y^m − y^n‖ = ‖y^{n}‖·‖y^{m−n} − 1‖` + the
   1-unit-power estimate `‖y^j − 1‖ ≤ ‖y−1‖`) — no ambient instances needed.
2. `Tendsto ((y−1)^·) → 0` from `‖y−1‖ < 1` (geometric: norm_pow ≤ ‖y−1‖^k).
3. Laws: AddChar gives add; natCast: `addChar value at (k:ℤ_[p])` =
   `(1 + (y−1))^k` (the mahlerSeries-at-naturals lemma in AddChar.lean's proof
   — `mahlerSeries_apply_nat`); mul: both sides continuous characters in b
   agreeing on ℕ (density `PadicInt.denseRange_natCast`).
4. Norm estimate: each summand of `Σ_{k≥1} (a choose k)(y−1)^k` has norm
   ≤ ‖y−1‖ (binomials integral); ultrametric sum.
5. Membership: the partial sums lie in K_n (ξ-polynomials) — K_n closed
   (finite-dimensional over complete ℚ_[p] ⟹ complete ⟹ closed; instance
   `FiniteDimensional.complete` + `Submodule.closed_of_finiteDimensional`-style
   through the IntermediateField); the limit stays; norm conditions by (4);
   the unit `v`: `zpPow y a · zpPow y (−a) = 1` by the add law.
6. Module instance on `Additive`: smul a u := the (4)/(5)-packaged power;
   module axioms = the (3) laws (one/add/mul/zero).
- **Mathlib**: `PadicInt.addChar_of_value_at_one` (AddChar.lean:59, verified
  signature `(r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : AddChar ℤ_[p] R` with
  `[NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [CompleteSpace R]`).
- **Sources**: Q12 (TeX 2494–2496); replan R11.6.
- **Sizing**: ~170 LOC (instance-pack risk priced in; fallback route documented).

### [T1110] 𝒰_∞ as a group; the towers 𝒰_{∞,1} and 𝒰⁺_{∞,1}
- **Status**: done (2026-06-13; agent wave 2: NormCompatUnits.inv (levelNorm_inv' re-derived from public levelNorm_mul/levelNorm_one), CommGroup via NormCompatUnits.ext + pointwise laws, unitsTower1(Plus) + le-lemma. Axioms standard at join.) | **File**: Iwasawa/LocalUnits.lean | **Depends on**: T1108
- **Parallel**: no (same file; can start before T1109 finishes if convenient —
  no dependence on zpPow)
- **Type**: instance + def-fields
#### Statement
`NormCompatUnits.inv` fields (mem/inv_mem/compat), `CommGroup (NormCompatUnits p)`,
`unitsTower1`/`unitsTower1Plus` fields, `unitsTower1Plus_le_unitsTower1`.
#### Proof sketch
1. inv fields: mem/inv_mem are the original's swapped (coercion shuffle
   `Units.val_inv_eq_inv_val`); compat: `levelNorm (u⁻¹) = (levelNorm u)⁻¹`
   for units of K_{n+1} — from `levelNorm_mul` + `levelNorm_one`
   (Map.lean has the private `levelNorm_inv` PATTERN at :156 — re-derive
   locally or unprivate it in the cleanup).
2. CommGroup: `NormCompatUnits.ext` (Theorem.lean:1127) + pointwise group laws
   of ℂ_[p]ˣ.
3. Towers: pointwise subgroup conditions; closure under mul/inv from T1108's
   subgroups (elems of products are products).
- **Sources**: Q12 (TeX 2503–2505).
- **Sizing**: ~90 LOC.

### [CLEANUP-113] /cleanup LocalUnits.lean
- **Status**: done (2026-06-13, DEGRADED MODE: LocalUnits.lean lint-green (2 longLine wraps at join); REVIEW ITEM folded to CLEANUP-FINAL: promote the file-local instance pack (UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p), Algebra ℤ_[p] ℂ_[p], IsBoundedSMul) to a dedicated infrastructure file — genuinely global-worthy; zpPow helper-cluster golf deferred). | **Depends on**: T1108–T1110.

### [T1111] The global tower: F_n, F_n⁺, 𝒱_n and 𝒱_n ≤ 𝒰_n
- **Status**: done (2026-06-13; agent: all targets + the T1112 bonus pair. norm_le_one_of_isIntegral_int via eval₂_eq_sum_range + Finset.sum_range_succ top-term isolation + IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty + norm_intCast_le_one + pow strict-monotonicity (mirrors Coefficients.lean's IsPrimitiveRoot.norm_sub_one_lt); new helper Fglobal_le_K via adjoin_induction + eq_ratCast + SubfieldClass.ratCast_mem (the base-field crossing ℚ→ℚ_[p]). globalUnits via IsIntegral.mul/mul_inv_rev; bonus cycloUnitsPlus + cycloUnits_le_globalUnits (inf_le_right). Statements unchanged. AXIOM CHECK PENDING join. Cleanup deferred to CLEANUP-114.) | **File**: Iwasawa/CyclotomicUnits.lean | **Depends on**: T1108
- **Parallel**: yes vs T1109/T1110 (different file)
- **Type**: lemmas + def-fields
#### Statement
`FglobalPlus_le_Fglobal`, `norm_le_one_of_isIntegral_int`,
`globalUnits`/`globalUnitsPlus` fields, `globalUnits_le_localUnits`.
#### Proof sketch
1. `FglobalPlus_le_Fglobal`: adjoin_le_iff; ξ + ξ⁻¹ ∈ ℚ⟮ξ⟯ (inv_mem + add).
2. Integral norm bound (R11.7 attack log): monic `P = X^n + Σ a_i X^i ∈ ℤ[X]`,
   `P(x) = 0`. If `‖x‖ > 1`: `‖x^n‖ = ‖x‖^n > ‖x‖^i ≥ ‖a_i x^i‖` (integer
   coefficients have ‖·‖ ≤ 1 in ℂ_[p]: `norm_intCast_le_one` — ultrametric +
   `‖(1:ℂ_[p])‖ = 1`; if absent, induct), so
   `‖x^n‖ = ‖−Σ a_i x^i‖ ≤ max < ‖x‖^n` — contradiction
   (`IsUltrametricDist.norm_sum_le_max`-style, finite max over i < n).
3. `globalUnits` closure: products/inverses of integral elements are integral
   (`IsIntegral.mul`, integralClosure is a subring); field membership via
   `Fglobal` subfield ops.
4. `𝒱_n ≤ 𝒰_n`: u global ⟹ `‖u‖ ≤ 1 ∧ ‖u⁻¹‖ ≤ 1` by (2) ⟹ both in
   integerRing; `u ∈ F_n ≤ ?K_n`: F_n = ℚ⟮ξ⟯ ≤ K_n as SETS (ξ ∈ K_n,
   ℚ ⊆ ℚ_[p] ⊆ K_n; `IntermediateField.adjoin_le_iff` after transporting the
   base — argue elementwise: x ∈ ℚ⟮ξ⟯ ⟹ x ∈ K_n via `adjoin_induction`
   or `IntermediateField.restrictScalars`-monotony) ⟹ membership in O_n ✓.
- **Mathlib**: `IsIntegral.mul/inv`-API (`integralClosure`),
  `IntermediateField.adjoin_induction`, `adjoin_le_iff`.
- **Sources**: Q12 (TeX 2471–2472); R11.7.
- **Sizing**: ~140 LOC.

### [T1112] The cyclotomic units 𝒟_n and the closures 𝒞 (definitional layer)
- **Status**: done (2026-06-13; towers via the unitsTower1 template + mem_inf; cycloUnitsPlus/le-lemma by T1111's agent. Axioms standard at join.) | **File**: Iwasawa/CyclotomicUnits.lean
- **Depends on**: T1110, T1111 | **Parallel**: no (same file as T1111)
- **Type**: def-fields + lemmas
#### Statement
`cycloUnitsPlus` fields, `cycloUnits_le_globalUnits`, `cycloTower1`/
`cycloTower1Plus` fields, `cycloTower1_le_unitsTower1`.
#### Proof sketch
1. `cycloUnitsPlus` fields: intersection of a subgroup with a subfield-valued
   condition (the T1108 localUnitsPlus pattern verbatim).
2. `cycloUnits_le_globalUnits`: `inf_le_right`.
3. Towers: pointwise conditions over `cycloClosureOne` (subgroups by
   construction: closure/inf of subgroups); `le`: `cycloClosureOne ≤
   localUnitsOne` (`inf_le_right`) pointwise.
- **Sources**: Q8 (TeX 3065–3067), Q10 (TeX 3090–3094).
- **Sizing**: ~60 LOC.

### [CLEANUP-ALL-6] pre-milestone project sweep
- **Status**: done (2026-06-13, DEGRADED MODE project sweep: full lake build green, ZERO warnings project-wide, ZERO sorries project-wide, axioms standard on all §11 decls (per-ticket checks logged in T1102–T1113). Ran after T1113's join (parallel dispatch had the milestone agent in flight when the gate came due); the sweep covers the milestone output. Golf/dedupe scope folded into CLEANUP-FINAL.) | **Depends on**: T1101–T1112 + CLEANUP-111/112/113 done.
  /cleanup-all (degraded mode acceptable; record). Gate before the milestone
  ticket per the cadence rule.

### [T1113] **MILESTONE: c(a) ∈ 𝒟_n and cyclo ∈ 𝒞_{∞,1}** (RJW TeX 3084)
- **Status**: done (2026-06-13; MILESTONE. isIntegral via geomSum forms (cycloUnit_eq_geomSum / inv via the a·a' ≡ 1 mod p^n trick); D_n-membership via the closure word (ζ^{a%p^n}−1)·(ζ−1)⁻¹ + globalUnits; **STATEMENT FIX (b2-logged 2026-06-13)**: norm_cycloUnit_sub_one_lt_one + cyclo_mem_cycloTower1 + cyclo_mem_unitsTower1 gained (ha1 : a ≡ 1 [MOD p]) — c_n(a) ≡ a mod 𝔭_n so the principal-unit claims are false for a ≢ 1 (counterexample p=5, a=3); NOT an RJW erratum (TeX 3084 only claims 𝒟_n-membership, kept unconditional); §12 handoff note in b2_log + plan.md. 2 Map.lean norm-privates copied with dedupe-at-CLEANUP-FINAL markers. Project-wide ZERO sorries; axioms standard; full build green. NOTE: CLEANUP-ALL-6 ran concurrently-after due to parallel dispatch — ordering recorded.) | **File**: Iwasawa/CyclotomicUnits.lean
- **Depends on**: T1112 (+ CLEANUP-ALL-6 gate) | **Type**: lemmas
#### Statement
`isIntegral_cycloUnit`, `isIntegral_inv_cycloUnit`,
`norm_cycloUnit_sub_one_lt_one`, `cyclo_elems_mem_cycloUnits`,
`cyclo_mem_cycloTower1`, `cyclo_mem_unitsTower1`.
#### Proof sketch
1. Integrality: `c_n(a)·(ξ−1) = ξ^a−1` ⟹ for p∤a write the geometric sum:
   `c_n(a) = Σ_{i<a} ξ^i` (from `(ξ^a−1) = (ξ−1)·Σ_{i<a} ξ^i` — `geom_sum_mul`/
   `mul_geom_sum` mathlib + division by the nonzero ξ−1); ξ integral over ℤ
   (root of monic `X^{p^n} − 1`) ⟹ the sum is (subring). Inverse: pick a' with
   `a·a' ≡ 1 [MOD p^n]` (`Nat.exists_mul_emod_eq_one_of_coprime`,
   gcd(a, p^n) = 1 from p∤a): `ξ^{aa'} = ξ` (`zetaSys_primitiveRoot` order
   divides) ⟹ `(ξ−1) = (ξ^a)^{a'} − 1 = (ξ^a − 1)·Σ_{i<a'} ξ^{ai}` ⟹
   `c_n(a)⁻¹ = Σ_{i<a'} ξ^{ai}` integral.
2. Norm: `c_n(a) − 1 = Σ_{1≤i<a} ξ^i − (a−1) = Σ_{1≤i<a} (ξ^i − 1)`; each
   `‖ξ^i − 1‖ < 1` (i < a: if p ∣ i it's a lower-level root or 0 — handle
   `ξ^i = 1` term as 0; else `norm_zetaSys_pow_sub_one`-type from Map.lean's
   privates / norm_pi_pow_totient route: ANY p^n-th root of unity η has
   ‖η − 1‖ < 1: η^{p^n} = 1 ⟹ (η−1) divides… simplest: `‖η − 1‖ ≤ ‖π_m‖ < 1`
   via the primitive-root norm formulas already in Tower/Map privates —
   re-derive the single inequality `‖η−1‖ < 1` for η^{p^n} = 1, η ≠ ±…:
   from `∏_{j<p^m}(X − η^j) = X^{p^m} − 1` at X = 1 if needed, or the
   crude argument: `(η−1)^{p^n} ≡ η^{p^n} − 1 = 0 mod p`-style binomial
   estimate: `‖η−1‖^{p^n} = ‖(η−1)^{p^n}‖ = ‖Σ_{j<p^n} binom·(η−1)^j·…‖` —
   take the Tower-private route first; Tier-A sub-ticket if it resists);
   ultrametric max < 1.
3. Subgroup word: `(cyclo …).elems n` coe = `cycloUnit p a n` (dif_pos hn) =
   `(ξ^{a mod p^n} − 1)·(ξ − 1)⁻¹` (reduce: `ξ^a = ξ^{a % p^n}` by
   `pow_mod_orderOf`-style with `zetaSys_primitiveRoot`): the two factors'
   unit-versions lie in `cycloGenSet` (`a % p^n ≠ 0` since p∤a ⟹ p^n ∤ a;
   bounds `1 ≤ a % p^n ≤ p^n − 1` ✓; the (ξ−1)-generator is the a = 1 case),
   so the word ∈ `Subgroup.closure` (mul_mem + inv_mem + subset_closure);
   `Units.ext`-bridge between the mk0-units and the val-specified set members.
   Global side: (1) + `cycloUnit_mem_K`-analogue for `Fglobal` (the same
   geometric sums are ℚ⟮ξ⟯-elements) gives `∈ globalUnits` ⟹ ∈ 𝒟_n.
4. `cyclo_mem_cycloTower1`: per n ≥ 1: elems n ∈ 𝒟_n (3) ⟹
   ∈ closure(𝒟_n) (`Subgroup.le_topologicalClosure` + subset) and ∈ 𝒰_{n,1}
   ((2) + `cycloUnit_mem_O`/`inv_cycloUnit_mem_O` from Map.lean) ⟹
   ∈ 𝒞_{n,1}. `cyclo_mem_unitsTower1`: via `cycloTower1_le_unitsTower1`.
- **Mathlib**: `geom_sum_mul`, `Nat.Coprime` mod-inverse, `IsIntegral` subring
  API, `Subgroup.subset_closure`/`le_topologicalClosure`.
- **Sources**: Q10's sentence (TeX 3084) + Q8; Map.lean cycloUnit pack.
- **Sizing**: ~200 LOC. Tier-A split point: the `‖η−1‖ < 1` sub-lemma.

### [CLEANUP-114] /cleanup CyclotomicUnits.lean
- **Status**: done (2026-06-13, DEGRADED MODE: CyclotomicUnits.lean lint-green; 2 copied Map.lean norm-privates carry dedupe-at-CLEANUP-FINAL markers; geomSum-helper golf deferred). | **Depends on**: T1113.

### [T1114] Blueprint: wire the IwasawaZeros chapter
- **Status**: done (2026-06-13; 7 nodes wired (plus-minus-decomposition, lambda-plus-iso + functional-route prose note, plus-criterion, zeta-p-pseudo-measure-plus + erratum-#13 prose, ideal-of-zeta-p, cyclotomic-units-global, local-cyclotomic-units + the milestone code-refs with the a≡1-mod-p caveat prose); zeros-cyclo-units-class-number and iwasawa-zeros-theorem STAY PROSE per R11.8. lake build PadicLFunctionsBlueprint green (4130 jobs); site re-rendered via ci-pages.sh. Pre-existing emph-lint in Eisenstein.lean:168 noted for CLEANUP-FINAL.) | **Depends on**: all §11 proof tickets
- **File**: PadicLFunctionsBlueprint/Chapters/IwasawaZeros.lean
#### Work
Wire the proven §11 nodes: lem:decompose-plus-minus ↦
`isCompl_invariants_antiInvariants`/`isCompl_plusPart_minusPart`; the Λ⁺-iso
node ↦ `plusEquiv` (prose note: functional-route proof, finite-level rank count
deferred with Prop 3.9/3.10 — replan R11.2); the criterion node ↦
`mem_plusPart_iff_forall_odd_moment`; the corollary node ↦
`isPlusPseudoMeasure_padicZetaPlus` (+ erratum-#13 prose note: the k = 1
Euler-factor case); the ideal node ↦ `zetaIdeal`/`zetaIdealPlus` (+eq_span);
𝒟_n/𝒞-definition nodes ↦ `cycloUnits`/`cycloClosure`-family; the TeX-3084
node ↦ `cyclo_mem_cycloTower1`. thm:cyclo-units-class-number and thm:iwasawa
STAY PROSE (unwired; deferral notes per R11.8 — never wire partial
realisations). Prose note on the identification (Q1/R11.1) in the chapter
intro. `lake build PadicLFunctionsBlueprint` green; re-render via
`./scripts/ci-pages.sh` when convenient.

## §11 dispatch notes
- Verification bar per ticket: `lake build` green, zero sorry in the ticket's
  declarations, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound};
  record in Progress. Cleanup immediately per file-chain (degraded mode note if
  no lean-lsp MCP).
- Parallel lanes: (A) T1102→T1103→T1104→CL-111; (B) T1105 (→T1106 after A's
  T1102/T1104; →T1107)→CL-112; (C) T1108→{T1109, T1110}→CL-113;
  (D) T1111 (after T1108)→T1112 (after T1110/T1111). Then CLEANUP-ALL-6 →
  T1113 → CL-114 → T1114.
- The sorried INSTANCES (`SMulCommClass`/`IsScalarTower` in PlusPart;
  `localUnitsOneModule`, `Inv`/`CommGroup (NormCompatUnits)`) are
  load-bearing data/prop mixes: T1102/T1109/T1110 must replace them with real
  constructions FIRST in their lanes (nothing else may prove THROUGH a sorried
  instance; the axiom check catches leakage via `sorryAx`).

---

# §12 board — Proof of Iwasawa's theorem (TeX 3113–3616)

Decomposition: `.mathlib-quality/decomposition.md` R12 (quotes Q1–Q15, clusters
E12.1–E12.5). Plan: `plan.md` §12 addendum. Skeleton (canonical): six files under
`PadicLFunctions/IwasawaProof/` — `lake build PadicLFunctions` GREEN at board creation
(2026-06-14), 37 sorries confined to the new files, no lint warnings. §12 is the
LARGEST/DEEPEST section; the board stages the two critical-path sub-developments
(E12.1 Galois action, E12.2 thm:log der) FIRST. p odd (hp2) throughout. The §11
b2-logged a≡1-mod-p note is resolved NATIVELY by E12.4 (the Teichmüller correction w).

### [T1201] **E12.1 LINCHPIN: the Galois action on the tower** (GaloisAction.lean)
- **Status**: **done** (2026-06-14, beastmode §12 wave 2). GaloisAction.lean sorry-free; `lake build PadicLFunctions.IwasawaProof.GaloisAction` ✓; `#print axioms` on Col_galNCU/colemanSeries_galNCU/levelNorm_galAut/galNCU/galAut_compat = {propext, Classical.choice, Quot.sound}. Sub-ticket T1201b (Col_galNCU) closed by agent ad3ada. | **Sub-tickets**: T1201b (done) | **File**: IwasawaProof/GaloisAction.lean | **Depends on**: §10/§11 done
- **Parallel**: yes (vs T1203 — different file) | **Type**: defs + lemmas
#### Statement (skeleton canonical)
`galAut (a : ℤ_[p]ˣ) (n) : K p n ≃ₐ[ℚ_[p]] K p n`; `galAut_zetaSys` (σ_a ξ_n = ξ_n^{a_n});
`galAut_compat` (tower restriction); `levelNorm_galAut` (norm-equivariance); `galNCU`
(action on NormCompatUnits); `galSeries` (f ↦ f((1+T)^a−1)); `colemanSeries_galNCU`
(f_{σ_a u} = σ_a f_u); `Col_galNCU` (Col 𝒢-equivariant).
#### Proof sketch (decomposition E12.1, source TeX 3182–3236)
1. FIRST STEP: make Tower's `isCyclotomicExtension_K` PUBLIC (currently `private`) — or
   re-derive locally. Then `galAut p a n := (IsCyclotomicExtension.autEquivPow (K p n)
   (cyclotomic_irreducible_Qp hn)).symm (PadicMeasure.unitsToZModPow p n a)`.
2. `galAut_zetaSys`: `IsPrimitiveRoot.autToPow_spec` + `autEquivPow_symm_apply`.
3. `galAut_compat`: two autos of K_{n+1} agreeing on ξ_{n+1}↦its char-power and fixing
   K_n; uniqueness via `IsPrimitiveRoot.autToPow_injective` + the tower
   `unitsToZModPow_le` compatibility (mod-p^n reduction of a).
4. `levelNorm_galAut`: `Algebra.norm` is invariant under the Galois action of the bigger
   field that commutes — concretely, σ_a permutes the K_n-conjugates of x, and
   `Algebra.norm` is the product over conjugates (`Algebra.norm_eq_prod_embeddings` /
   conjugation-invariance); careful with the `extendScalars` framing of `levelNorm`.
5. `galNCU p a u`: elems n := the unit `galAut p a n (u.elems n)`; mem/inv_mem since
   galAut is a ring auto preserving O_n (it's an isometry of K_n — Galois autos of local
   fields are isometric); compat by (4).
6. `galSeries p a f := f.subst ((1+X)^? − 1)` — for a : ℤ_[p]ˣ the exponent is the zpPow
   binomial `(1+T)^a` (HasSubst since const term 0); for a ∈ ℕ-image, `PowerSeries.subst`.
7. `colemanSeries_galNCU`: (σ_a f_u)(π_n) = f_u((1+π_n)^a−1) = f_u(ξ_n^a−1) =
   σ_a(f_u(ξ_n−1)) = σ_a(u_n) = (galNCU a u)_n (TeX 3210–3216); then coleman_existsUnique
   uniqueness (σ_a f_u is a unit, 𝒩-fixed since 𝒩 commutes with σ_a, interpolates).
8. `Col_galNCU`: map-by-map (TeX 3217–3234) — ∂log(σ_a f)=a σ_a ∂log f, ∂⁻¹∘σ_a =
   a⁻¹σ_a∘∂⁻¹, restriction 𝒢-equivariant. FINALISE the σ_a-on-measures RHS form (the
   skeleton's `unitsCmul p 1` is a placeholder — replace with the genuine σ_a pushforward
   = `pushforward` along `u ↦ a*u` on ℤ_[p]ˣ).
- **Mathlib**: `IsCyclotomicExtension.autEquivPow` (Cyclotomic/Gal.lean:77),
  `IsPrimitiveRoot.autToPow`/`_spec`/`_injective` (RootsOfUnity/PrimitiveRoots.lean:781),
  `Algebra.norm_eq_prod_embeddings`. Project: `cyclotomic_irreducible_Qp`,
  `isCyclotomicExtension_K` (Tower, make public), `zpPow` (LocalUnits),
  `coleman_existsUnique` (Theorem).
- **Sources**: Q4, Q5 (TeX 3182–3236).
- **Sizing**: ~250 LOC. RISK: survey caveat (local-field autEquivPow) — mitigated since
  `isCyclotomicExtension_K` is already proven over ℚ_[p]; if (4) norm-equivariance
  resists, spawn a Tier-A sub-ticket for the conjugation-invariance of `levelNorm`.

### [T1202] E12.1 tail: ℤ_p-equivariance, Teichmüller split, cor:G-eq (Equivariance.lean)
- **Status**: in_progress (2026-06-14, agent a9db35 — 2/3 closed). `Col_lambdaG_equivariant` (cor:G-eq; RHS fixed to the `pushforward (unitsMulLeftCM a)` form matching T1201b's `Col_galNCU`) and `Col_eq_zero_of_torsion` (μ_{p−1} killed, via the homomorphism route `(p−1)·dlog=0` + ℤ_p⟦T⟧ torsion-free) both sorry-free + axiom-clean. The Teichmüller split `normCompat_eq_teichmuller_mul_principal` is the single remaining sorry (Equivariance.lean:122) → T1202a. | **File**: IwasawaProof/Equivariance.lean | **Sub-tickets**: T1202a | **Depends on**: T1201
- **Parallel**: no (needs T1201) | **Type**: lemmas
#### Statement
`normCompat_eq_teichmuller_mul_principal` (𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}); `Col_eq_zero_of_torsion`
(μ_{p−1} killed); `Col_lambdaG_equivariant` (cor:G-eq — already proven via Col_galNCU).
#### Proof sketch (source TeX 3137–3243)
1. Teichmüller split: the reduction `𝒰_n → μ_{p−1}` (via the residue field 𝔽_p^×-lift /
   the §5 Teichmüller `teichmullerZMod`) splits `1→𝒰_{n,1}→𝒰_n→μ_{p−1}→1`; inverse limit.
   ℤ_p-equivariance of Col on 𝒰_{∞,1}: a₀(f_u) ≡ 1 mod p (f_u(π_n) ≡ 1 mod 𝔭_n + a₀∈ℤ_p)
   ⟹ f_u−1 ∈ (p,T) ⟹ f_u^a converges = f_{u^a} (coleman_existsUnique) ⟹ ∂log equivariant.
2. μ_{p−1} killed: f_v = constant v ⟹ ∂log f_v = 0 ⟹ Col v = 0 (rem:ker Δ: 𝒩-fixed
   constant ⟹ v^p = v).
3. cor:G-eq: Col_galNCU (T1201) packages the Λ(𝒢)-equivariance.
- **Mathlib**: reduction-mod-𝔭 / Teichmüller (§5 `teichmullerZMod` port if needed).
- **Sources**: Q1, Q2, Q3, Q5 (TeX 3130–3243).
- **Sizing**: ~140 LOC.

### [T1202a] Teichmüller split `𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}` (Equivariance.lean)
- **Status**: **done** (2026-06-14, agent a02e8a — the user-authorized residue-field pass). `normCompat_eq_teichmuller_mul_principal` is now SORRY-FREE + axiom-clean (moved to new `Iwasawa/ResidueField.lean:380`; the Equivariance.lean:159 sorry is GONE). Built the residue-field-of-𝒪_n infrastructure: `residueZp` (𝒪_n→ZMod p residue, constant across levels via `norm_levelNorm_sub_one_lt_one` norm-residue compat + Fermat), `omegaNCU` (the constant Teichmüller `NormCompatUnits` ω(b)∈μ_{p−1}, torsion), using the totally-ramified ⟹ residue-field-𝔽_p insight. `exists_residue_pi` promoted public; `levelNorm_const_eq_pow` moved to Tower.lean (public). `lake build PadicLFunctions` clean (3841 jobs). HISTORY (was DEFERRED, agent a708d3): the reusable arithmetic half was CLOSED: `levelNorm_const_eq_pow` (`N_{n+1,n}(c)=c^p` for base constants `c∈K_n`, via `Algebra.norm_algebraMap` + `finrank_K_succ`; axiom-clean) — this discharges norm-compatibility of a constant `μ_{p−1}` system (`ζ^{p−1}=1 ⟹ N(ζ)=ζ`). `normCompat_eq_teichmuller_mul_principal` itself stays a single DOCUMENTED sorry (Equivariance.lean:159): the genuine blocker is an exported residue hom `O_n^× → 𝔽_p^×` + Teichmüller section `ω : O_n^× → μ_{p−1}` + norm-residue compatibility — a dedicated local-CFT pass (the project has only `private exists_residue_pi`, existence-only). Recorded as deferred to a residue-field-of-`O_n` pass (cf. rule #6's O_L dedicated-pass discipline); blueprint node stays unwired. The sorryAx is contained — nothing references this theorem, so it does NOT pollute the T1206 milestone. | **File**: IwasawaProof/Equivariance.lean | **Parent**: T1202 | **Type**: lemma + residue-field sub-development (deferred)
#### Statement (Equivariance.lean:~122, unchanged)
`normCompat_eq_teichmuller_mul_principal (u : NormCompatUnits p) : ∃ v w, w ∈ unitsTower1 p ∧ (∀ n, (v.elems n)^(p−1) = 1) ∧ u = v * w`.
#### Obstacle (agent a9db35) + plan
Needs residue-field-of-`O_n` infrastructure absent from the project: (i) a residue/Teichmüller
section `O_n^× → μ_{p−1}` (the (p−1)-th root of unity `≡ u mod 𝔭_n`); (ii) `levelNorm`-on-constants
`N(ζ)=ζ^p` — EASY via `Algebra.norm_algebraMap` (ζ ∈ ℤ_[p] constant, `[K_{n+1}:K_n]=p` from Tower);
(iii) norm-residue compatibility (so `v`,`w` are norm-compatible). (i) is the real sub-development
(residue field of the totally-ramified `K_n`; μ_{p−1} ⊂ ℤ_[p]^× so the existing `teichmullerZMod`/
`teichmullerFun` in Interpolation/Branches.lean is the ℤ_[p] analog to adapt).
- **Note (off critical path)**: T1204 (FundamentalSequence) and T1206 (Main) are stated on
  `unitsTower1` (= 𝒰_{∞,1}) directly, and `ℤ_p(1) ⊂ 𝒰_{∞,1}` (each `ξ_n ≡ 1 mod 𝔭_n`), so the
  kernel/cokernel computations and the milestone iso never invoke the 𝒰_∞-vs-𝒰_{∞,1} split.
  Recorded as deferred pending the residue-field pass; blueprint node stays unwired. Revisit only
  if a downstream proof turns out to need it.
- **Sources**: RJW §12.1 (TeX 3159–3168).
- **Sizing**: (ii) ~10 LOC; (i)+(iii) a residue-field sub-development (scope TBD — possibly the
  survey's global-number-field caveat).

### [CLEANUP-121] /cleanup GaloisAction.lean + Equivariance.lean
- **Status**: **done (degraded)** (2026-06-14, orchestrator). GaloisAction.lean + Equivariance.lean
  build green (`lake build PadicLFunctions` 3840 jobs, no lint warnings; the only sorry is the
  deferred Equivariance.lean:159 T1202a). Per-ticket cleaned at proof time (T1201/T1201b show→change,
  golf) + the a8699e Galois-fixed-field lemmas + a7678f/a820a4 galNCU infra written clean (≤100 cols,
  axiom-clean). Degraded bar met (orchestrator lacks lean-lsp MCP); deep structural golf deferred to
  CLEANUP-FINAL (the lean-lsp-MCP-tooled session). | **Depends on**: T1201, T1202.

### [T1203] **E12.2 HARD: thm:log der (Coleman–Coates–Wiles)** (LogDerivative.lean)
- **Status**: **done** (2026-06-14, beastmode §12 wave 4). LogDerivative.lean sorry-free; clean `lake build` (no errors/warnings); all of `dlog_mem_psiIdSeries`/`fp_series_eq_dlog_add_frobC`/`dlog_surjective_onto_psiId` (+ the ψ-subspaces, `del_phiHom`, `exists_normOp_fixed_lift`, `dlog_eq_zero_normOp_fixed`, lem:rest zp* halves, `dlog_*` homomorphism layer) axiom-clean. "The hardest mathematics in Part II" — DONE, and **entirely ξ-free**: the §10-deferred series-Eqphipsi was AVOIDED via (a) T1203a's Jacobi/trace route for lem:log der 1, and (b) T1203c's honest-`ψ`-over-𝔽_p projection formula for lem:B mod p. Sub-tickets T1203a/b/c all done. | **Sub-tickets**: T1203a (done), T1203b (done), T1203c (done) | **File**: IwasawaProof/LogDerivative.lean | **Depends on**: §10 done
- **Parallel**: yes (vs T1201 — different file, no Galois dep) | **Type**: lemmas (HARD)
#### Statement (skeleton canonical)
`psiIdSeries`/`psiZeroSeries` (Submodules); `del_phiHom` (Δ∘φ = p φ∘Δ);
`dlog_mem_psiIdSeries` (lem:log der 1); `exists_normOp_fixed_lift` (lem:A mod p);
`fp_series_eq_dlog_add_frobC` (lem:B mod p 2 — THE HARD ONE); `dlog_surjective_onto_psiId`
(thm:log der surjectivity); `dlog_eq_zero_normOp_fixed` (rem:ker Δ); `one_sub_phi_*`
(lem:rest zp* halves).
#### Proof sketch (source TeX 3264–3403; the hardest mathematics in Part II)
1. ψ-subspaces: Submodule fields via `psiSeries` additivity/C-linearity (NormOperator).
2. `del_phiHom`: direct coeff computation (φ = subst (1+T)^p−1; del = (1+X)·deriv).
3. `dlog_mem_psiIdSeries` (lem:log der 1): φ𝒩=∏_{η∈μ_p}f((1+T)η−1) (the §10-DEFERRED
   series Eqphipsi over ℂ_[p][μ_p] — SPAWN sub-ticket: product collapse ∏(Xη−1)=X^p−1) +
   del_phiHom + φ injective (phiHom injective — coeff-degree).
4. `exists_normOp_fixed_lift` (lem:A mod p): 𝒩^k(f̃₀) converges (normOp mod-p^k continuity
   (ii) `normOp_modEq_self` + (iv) iterate — PARTLY ABSENT, SPAWN sub-tickets for (ii)/(iv)).
5. `fp_series_eq_dlog_add_frobC` (lem:B mod p 2): the explicit 𝔽_p⟦T⟧ induction (TeX
   3366–3373) — EXPECTED TIER-A SPAWN: build h, choose α_i = −d_i/i inductively,
   h_m ∈ T^{m−1}𝔽_p⟦T⟧, g = ∏(1−α_nT^n), Δg = (T+1)/T·h; uses d_n=d_{np}, ψ-fixes (T+1)/T.
6. `dlog_surjective_onto_psiId` (thm:log der): lem:log der red mod p (A=B ⟹ onto via
   successive approx h_n = ∏ g_k^{(−1)^{k−1}p^{k−1}} + ℤ_p⟦T⟧^× compactness from §10) +
   lem:A mod p + lem:B mod p (from lem:B mod p 2 + ψ-action calc).
7. `dlog_eq_zero_normOp_fixed` (rem:ker Δ): ∂log g=0 ⟹ g constant; 𝒩-fixed ⟹ g^p=g.
8. lem:rest zp*: Σφ^n convergence + ker(1−φ)=constants + ψ(1+T)=0 + eval-at-0 onto.
- **Mathlib**: `RootsOfUnity` ∏(Xη−1)=X^p−1; `phiHom` injective. Project: `psiSeries`,
  `normOp` + `ModEqPow` + `phi_injective_mod` (NormOperator), ℤ_p⟦T⟧^× compactness (§10).
- **Sources**: Q6, Q7, Q8, Q9 (TeX 3264–3403).
- **Sizing**: ~400–500 LOC across sub-tickets; the project's hardest. Sub-ticket spawns:
  the series-Eqphipsi (step 3), normOp continuity (ii)/(iv) (step 4), lem:B mod p 2 (step 5).

### [CLEANUP-122] /cleanup LogDerivative.lean
- **Status**: **done (degraded)** (2026-06-14, orchestrator). LogDerivative.lean builds green
  (part of the 3840-job build, no lint). The entire CCW thm:log der was per-ticket cleaned at
  proof time (T1203a/b/c: show→change, ≤100 cols, the de-privatizations done). Degraded bar met
  (no lean-lsp MCP); deep golf deferred to CLEANUP-FINAL. | **Depends on**: T1203.

### [T1204] E12.3: the fundamental exact sequence (FundamentalSequence.lean)
- **Status**: **done** (2026-06-14, agents ae3306 → T1204a → T1204b → ab6d73 final closure). FundamentalSequence.lean **sorry-free** (the only build sorry is the deferred Equivariance.lean:159, a different file, which does NOT propagate here); `lake build PadicLFunctions.IwasawaProof.FundamentalSequence` clean (3711 jobs); `#print axioms mem_ker_Col_iff_mem_ZpOne range_Col_eq_ker_chiMoment` = {propext, Classical.choice, Quot.sound} (NO sorryAx — orchestrator verified independently via temp-file import, not agent self-report). FINAL CLOSURE (ab6d73): (a) added `hp2 : p ≠ 2` to `levelNorm_zpPow_zetaSys`→`normOp_binomialSeries`→`mem_ker_Col_iff_mem_ZpOne` cascade (errata #14: N(ξ_{n+1}^a)=ξ_n^a is FALSE at p=2; proved p-odd via `minpoly_extendScalars_of_pow` + `Algebra.norm_eq_norm_adjoin` + `zpPow_zetaSys'`/`PadicInt.cast_toZModPow` tower reduction); (b) re-routed the cokernel converse off the deferred `normCompat_eq_teichmuller_mul_principal` via the ℤ_[p]-Teichmüller `teichNCU (constantCoeff g)` (norm-compat by `levelNorm_const_eq_pow`+`ω^{p−1}=1`, torsion ⟹ `Col=0`, principality by `g(π_n)≡a` + `a·ω(a)⁻¹≡1 mod p`). HISTORY: in_progress (agent ae3306 — 1/3). **`ZpOne` DONE** (integral Tate twist `{(ξ_n^a)_n}` via `zpPow` character laws; sorry-free, axiom-clean). The two exact-sequence theorems `mem_ker_Col_iff_mem_ZpOne` + `range_Col_eq_ker_chiMoment` were (documented sorries, FundamentalSequence.lean:99/117) — were blocked on substrate: (1) the measure-side `PadicMeasure.mahlerTransform_psi` bridge (`𝒜(ψμ)=psiSeries(𝒜μ)`), absent — `mahlerTransform_phi`/`psi`/`psi_phi`/`phi_psi` exist but the ψ-bridge needs the PadicMeasure digit-decomposition (analogue of MeasureR `existsUnique_measure_digits`), NOT derivable purely from the φ-bridge (orchestrator verified the formal derivation is circular); (2) `normOp(binomialSeries a)=binomialSeries a` + `a↦binomialSeries a` `WithPiTopology`-continuity + de-privatizing `normOp_continuous`/`digitMatrix_continuous`/`phiSeries_continuous`/`continuous_of_coeff` (LogDerivative) + `seriesEval_map_binomialSeries` (GaloisAction). → sub-tickets T1204a (substrate bridge) + T1204b (de-privatize + binomial layer). | **File**: IwasawaProof/FundamentalSequence.lean | **Sub-tickets**: T1204a, T1204b | **Depends on**: T1202, T1203
- **Parallel**: no | **Type**: def + theorems
#### Statement
`ZpOne` (ℤ_p(1) ⊂ 𝒰_∞); `mem_ker_Col_iff_mem_ZpOne` (kernel); `range_Col_eq_ker_chiMoment`
(cokernel via the χ-moment μ ↦ μ(x)).
#### Proof sketch (source TeX 3407–3441)
1. `ZpOne`: a ↦ (ξ_n^a)_n via zpPow on ξ (the ker(1−φ)=constants pullback through Δ).
2. Kernel: compose ker's of the five maps (Col iso ∘ Δ ker μ_{p−1} ∘ (1−φ) ker ℤ_p ∘
   ∂⁻¹ iso ∘ 𝓐⁻¹ iso); the ℤ_p factor pulls back to ℤ_p(1) (TeX 3429–3431).
3. Cokernel: the (1−φ) coker is ℤ_p (lem:rest zp*); the last map ∫χμ = μ(unitsPowCM 1).
4. Λ(𝒢)-exactness: T1201/T1202 equivariance + ∫χ·σμ = χ(σ)∫χμ.
- **Sources**: Q9, Q10, Q11 (TeX 3382–3441).
- **Sizing**: ~180 LOC.

### [T1204a] PadicMeasure ψ↔series Mahler bridge `mahlerTransform_psi` (Measure substrate)
- **Status**: **done** (2026-06-14, with T1204). `mahlerTransform_psi` (the PadicMeasure ψ↔series Mahler bridge `𝒜(ψμ)=psiSeries(𝒜μ)`) ported into FundamentalSequence.lean via a project `existsUnique_measure_digits` digit decomposition; sorry-free, axiom-clean (covered by the T1204 join axiom check). | **File**: FundamentalSequence.lean (built there, not Toolbox — both psiSeries+mahlerTransform visible) | **Parent**: T1204 | **Type**: substrate lemma(s)
#### Statement
`theorem PadicMeasure.mahlerTransform_psi (μ : PadicMeasure p ℤ_[p]) : mahlerTransform p (psi p μ) = psiSeries p (mahlerTransform p μ)` (the `ψ`-analogue of `mahlerTransform_phi`, Toolbox.lean:270).
#### Proof sketch
NOT derivable from `mahlerTransform_phi` + `psi_phi` alone (circular — orchestrator verified). Needs the PadicMeasure **digit decomposition**: every `μ = Σ_{i<p} σ_i(φ μ_i)` uniquely (the measure analogue of `existsUnique_measure_digits`/`existsUnique_digits_padicInt`), with `psi μ = μ_0`. Then `𝒜` intertwines the two digit decompositions (`𝒜(σ_i ν)`, `𝒜(φν)=phiSeries(𝒜ν)` via `mahlerTransform_phi`), so `𝒜(ψμ)=𝒜(μ_0)= 0`-th series digit `= psiSeries(𝒜μ)`. Build: (1) PadicMeasure digit existence+uniqueness (port the MeasureR `existsUnique_measure_digits` substrate from FormalPsi.lean to `PadicMeasure p ℤ_[p]`; the series-side port `existsUnique_digits_padicInt` is the template), (2) `𝒜`-intertwining of the digit shift, (3) assemble `mahlerTransform_psi`.
- **Mathlib/project**: `mahlerTransform_phi`, `psi`/`phi`/`psi_phi`/`phi_psi` (Toolbox), `psiSeries`/`phiSeries`/`existsUnique_digits_padicInt`/`psiSeries_phi_padicInt` (FormalPsi/NormOperator), MeasureR `existsUnique_measure_digits`/`mahlerTransform_psi` (the template to port).
- **Sources**: RJW §3.5.5 (TeX 1147–1151) + §12.2 transport.
- **Sizing**: ~150–250 LOC (substrate port; the MeasureR template exists).

### [T1204b] expose continuity/binomial layer + `normOp(binomialSeries a)=binomialSeries a`
- **Status**: **done** (2026-06-14, with T1204). De-privatized `normOp_continuous`/`digitMatrix_continuous`/`phiSeries_continuous`/`continuous_of_coeff` (LogDerivative) + `seriesEval_map_binomialSeries` (GaloisAction); `normOp(binomialSeries a)=binomialSeries a` + the binomial-series layer proved in FundamentalSequence.lean; axiom-clean (covered by the T1204 join axiom check). | **File**: LogDerivative.lean + GaloisAction.lean (de-privatize) + FundamentalSequence.lean | **Parent**: T1204 | **Type**: visibility + lemma
#### Statement / work
(a) Make PUBLIC (remove `private`): `normOp_continuous`, `digitMatrix_continuous`, `phiSeries_continuous`, `continuous_of_coeff` (LogDerivative.lean) and `seriesEval_map_binomialSeries` (GaloisAction.lean) — visibility only, no proof change. (b) Prove `normOp (binomialSeries ℤ_[p] a) = binomialSeries ℤ_[p] a` (the binomial series is `𝒩`-fixed — it is `colemanSeries` of `ξ_n^a ∈ ℤ_p(1)`) + `a ↦ binomialSeries a` `WithPiTopology`-continuity. Used by T1204's kernel theorem (`colemanSeries u = binomialSeries a` for `u ∈ ZpOne`).
- **Sizing**: (a) trivial; (b) ~40–80 LOC.

### [T1205] E12.4: generators of the cyclotomic units (Generators.lean)
- **Status**: **done** (2026-06-14, beastmode §12 wave 4). Generators.lean sorry-free; `lake build PadicLFunctions.IwasawaProof.Generators` ✓; `cycloUnitsPlus_eq_closure_gammas` axiom-clean {propext, Classical.choice, Quot.sound}. All of `gammaUnit`, `gammaUnit_mem_cycloUnitsPlus`, `cycloUnitsPlus_eq_closure_gammas` (both directions), `closure_zspan_eq_zpspan`, `cycloTower1Plus_cyclic_generator` complete. Sub-ticket T1205a (⊆) closed. | **File**: IwasawaProof/Generators.lean | **Depends on**: T1201
- **Progress (2026-06-14)**: agent aeb98 closed `gammaUnit`, `gammaUnit_mem_cycloUnitsPlus`, `closure_zspan_eq_zpspan`, `cycloTower1Plus_cyclic_generator` (strengthened to the proven congruence `γ_{n,a} ≡ a mod 𝔭_n` = §11 b2-note), and the `⊇` direction of `cycloUnitsPlus_eq_closure_gammas`. The single remaining sorry is the `⊆` direction (Generators.lean:335) → T1205a.
- **Parallel**: yes (vs T1203/T1204 — needs only T1201's finite Galois action) | **Type**: defs + lemmas
#### Statement
`gammaUnit` (γ_{n,a}); `gammaUnit_mem_cycloUnitsPlus`; `cycloUnitsPlus_eq_closure_gammas`
(lem:cyc units gen (i)); `closure_zspan_eq_zpspan` (lem:closure);
`cycloTower1Plus_cyclic_generator` (LemmaGeneratorCinfty1).
#### Proof sketch (source TeX 3450–3578)
1. `gammaUnit a n := zetaSys^{(1−a)/2} · cycloUnit a n`, half-power via (2:ZMod p^n)⁻¹ (p
   odd); c-fixed (ξ^{a/2}−ξ^{−a/2} form) ⟹ ∈ 𝒟_n^+.
2. lem:cyc units gen: valuation argument (all v_p(ξ^a−1) equal ⟹ Σe_a=0) + the
   ξ^{bp^m}−1 = ∏(ξ^{b+jp^{n−m}}−1) reduction; cor:cyc units gen 2 finalised here via the
   finite 𝒢_n^+-action (T1201) telescoping (the skeleton states lem:cyc units gen (i)).
3. lem:closure: zpPow binomial convergence (g_i−1 ∈ 𝔭_n) + ℤ_p^r compactness.
4. lem:global generators 2: γ_{n,a} ≡ a mod 𝔭_n (from f_{c(a)}(0)=a, the §11 b2 note's w
   = Teichmüller correction making wγ ≡ 1 mod 𝔭_n); (wγ)^{p−1} generates (p−1)𝒟_n^+.
5. LemmaGeneratorCinfty1: cyclic ℤ_p[𝒢_n^+] (p−1 invertible) → Λ(𝒢^+) in the limit.
- **Mathlib**: `ZMod.inv`/`unitOfCoprime` (half-powers); `Nat.Coprime` mod-inverse.
- **Sources**: Q12, Q13, Q14 (TeX 3450–3578).
- **Sizing**: ~280 LOC.

### [T1205a] lem:cyc units gen (i) `⊆` — the valuation/reality normal-form direction
- **Status**: **done** (2026-06-14, agent a282d89 + orchestrator binder fix). The full three-piece argument: normal form (A) `mem_aug_normal_form` (closure_induction giving `u = ξ^D·δ^E·h`, `h ∈ closure(gammaGenSet)`; the `ξ^a−1` generator handled by strong induction on `v_p(a)` via the TeX 3471 `p`-fold product `zetaSys_pow_mul_sub_one_prod`); valuation (B) `valHom` kills `E` (`valHom δ ≠ 1`); reality (C) `zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus` kills `D`. ~12 private helpers. Orchestrator fixed one missing `{a : ℕ}` binder on `zetaSys_pow_sub_one_ne_zero` (the agent's reported "exits 0" predated that regression); clean build + axiom-clean confirmed after fix. | **File**: IwasawaProof/Generators.lean | **Parent**: T1205 | **Type**: theorem
- **Depends on**: T1205 (⊇ done; `gammaUnit`, `gammaUnit_mem_cycloUnitsPlus`, `neg_one_mem_cycloUnitsPlus` available)
#### Statement (the `⊆` half of `cycloUnitsPlus_eq_closure_gammas`, Generators.lean:333–335)
`cycloUnitsPlus p n ≤ Subgroup.closure ({g | ∃ b, ¬p∣b ∧ (g:ℂ_[p]) = gammaUnit p b n} ∪ {g | (g:ℂ_[p]) = -1})`.
#### Proof sketch (source TeX 3470–3482; Lean-friendly route)
The literal argument is normal-form `±ξ^d ∏(ξ^a−1)^{e_a}` ⟹ `Σe_a=0` (valuation) ⟹ rewrite via
`γ_{n,a}` ⟹ reality kills the ξ-power. Decompose into three in-file lemmas (spawn as helpers):
1. **Normal form (A)**: `cycloGenSet = {ζ, −ζ} ∪ {ξ^a−1}`; `ℂ_[p]ˣ` is a `CommGroup`, so
   `g ∈ closure(cycloGenSet)` ⟹ `g = (±1)·ζ^d·∏_{a∈s}(ξ^a−1)^{e_a}` for some `d:ℤ`,
   `e : ℕ →₀ ℤ`, sign `±`. Route: `Subgroup.closure_induction` accumulating a finsupp word,
   OR mathlib's comm-group `closure` = `zpowers`-product form. (−ζ folds into sign·ζ^d.)
2. **Valuation (B) — the shortcut**: `v_p(ξ^a−1)=v_p(ξ−1)` for `(a,p)=1` is FREE: the project
   already has `isIntegral_cycloUnit` + `isIntegral_inv_cycloUnit` (CyclotomicUnits.lean:265,306),
   i.e. `c_n(a)=(ξ^a−1)/(ξ−1)` is a global unit ⟹ `‖ξ^a−1‖=‖ξ−1‖`. Plus `‖ξ−1‖<1`
   (`norm_zetaSys_pow_sub_one_lt`, Generators) and `‖ζ‖=1` (`norm_zhp`). The additive valuation
   `V(u) = -Real.log ‖(u:ℂ_[p])‖` is a `→+` hom on `ℂ_[p]ˣ`; `V(g)=0` (global unit, integral both
   ways ⟹ `‖g‖=1`) forces `(Σ_{(a,p)=1} e_a)·V(ξ−1)=0`, and `V(ξ−1)>0` ⟹ `Σe_a=0`.
   (Reduce all `ξ^a−1` to `(a,p)=1, 1≤a<p^n/2` via `ξ^{bp^m}−1=∏_j(ξ^{b+jp^{n−m}}−1)` and
   `ξ^a−1=−ξ^a(ξ^{−a}−1)` — both pure ℂ_[p] identities.)
3. **Rewrite + reality (C)**: `Σe_a=0` ⟹ `∏(ξ^a−1)^{e_a}=∏c_n(a)^{e_a}=ζ^{−½Σe_a(a−1)}∏γ_{n,a}^{e_a}`,
   so `g=±ζ^e∏γ_{n,a}^{e_a}` with `e=d+½Σe_a(a−1)`. Each `γ_{n,a}` real (`gammaUnit_mem_FglobalPlus`).
   `g∈cycloUnitsPlus` ⟹ `g` real ⟹ `±ζ^e` real ⟹ `ζ^{2e}=1` ⟹ `2e≡0 mod p^n` ⟹ `e=0` (p odd).
   Then `g=±∏γ_{n,a}^{e_a}∈closure({γ_b}∪{−1})`.
- **Mathlib**: `Subgroup.closure_induction`, `Real.log` hom facts, comm-group closure normal form.
- **Project**: `isIntegral_cycloUnit`/`isIntegral_inv_cycloUnit`, `cycloUnit_eq_geomSum`,
  `norm_zetaSys_pow_sub_one_lt`, `norm_zhp`, `gammaUnit_mem_FglobalPlus`, `zetaSys_primitiveRoot`.
- **Sources**: Q12 (TeX 3470–3482).
- **Sizing**: ~150–250 LOC (the normal form (A) is the long pole; (B) inputs all exist).
- **Note**: currently a leaf — nothing else in IwasawaProof consumes it yet; on the eventual
  critical path to T1206 via the cyclic Λ(𝒢⁺)-module (`cor:cyc units gen 2`).

### [CLEANUP-123] /cleanup FundamentalSequence.lean + Generators.lean
- **Status**: **done (degraded)** (2026-06-14, orchestrator). FundamentalSequence.lean +
  Generators.lean build green (part of the 3840-job build, no lint). Per-ticket cleaned at proof
  time (T1204, T1205) + the a7678f/a820a4 infra (galNCU_mul/_one/_elems_val/_mem_unitsTower1,
  Col_galNCU_eq_dirac_mul, dirac_mul_eq_pushforward, zpPow_zetaSys_mem_cycloClosureOne) written
  clean (≤100 cols, axiom-clean). Degraded bar met (no lean-lsp MCP); deep golf deferred to
  CLEANUP-FINAL. | **Depends on**: T1204, T1205.

### [CLEANUP-ALL-7] pre-milestone project sweep
- **Status**: **done (degraded)** (2026-06-14, orchestrator). Degraded /cleanup-all
  per the standing allowance (orchestrator context lacks lean-lsp MCP). The §12 files
  were each per-ticket cleaned at proof time (show→change conversions, golfing — see
  T1201b/T1203a-c/T1204/T1205 progress notes). Pre-milestone sweep: full
  `lake build PadicLFunctions.IwasawaProof.FundamentalSequence` (3711 jobs) surfaced
  exactly ONE lint issue across the §12 dependency tree — the
  `AddSubmonoidClass.coe_finset_sum` deprecation (GaloisAction.lean:757) — now fixed to
  `coe_finsetSum` (build re-verified clean, 3708 jobs). Linter is green; the only build
  `sorry` is the deferred Equivariance.lean:159 (T1202a, gated). Deeper structural golf
  deferred to CLEANUP-FINAL (a lean-lsp-MCP-tooled session). | **Depends on**:
  T1201–T1205 + CLEANUP-121/122/123.

### [T1206] **MILESTONE: thm:iwasawa 2** (Main.lean)
- **★ MAJOR ADVANCE — ⊇ DENSITY-CROSSING CLOSED, residual sharpened to ⊆ cyclic-module density
  (2026-06-14, agent a7cc206 + orchestrator on-disk verify)**: the continuity route succeeded for the
  `⊇` half. NEW file **`PadicLFunctions/Coleman/ColContinuity.lean` (536L, 29 decls, ALL axiom-clean
  {propext,Classical.choice,Quot.sound})**: weak-* topology on `PadicMeasure` (`instTopologicalSpace`,
  `continuous_iff_eval`, `instT2Space`, `continuous_mul_right` — the convolution Λ-action continuity),
  closed-subgroup⟹ℤ_p-submodule (`smul_mem_of_isClosed_subgroup`), Dirac-span weak-* density
  (`approxDirac`/`tendsto_approxDirac`/`mul_mem_of_dirac_mul_mem`), `continuous_evalPi`, the
  inverse-AVOIDING paired pipeline `colemanPipe2`+`continuous_colemanPipe2`+`colemanPipe2_eq_Col`, and
  the compactness chain ⇒ **`isCompact_col_image`/`isClosed_col_image`** (`Col '' 𝒞_{∞,1}` is weak-*
  closed). In Main.lean: **`zetaIdeal_le_col_image` (the ⊇ density-crossing) PROVED + axiom-clean**
  (via `isClosed_col_image` + `mul_mem_of_dirac_mul_mem` + `zetaIdeal_eq_span`), and the injectivity
  half **`mem_cycloTower1_of_col_mem_zetaIdeal` axiom-clean**. ON-DISK VERIFIED: `lake build
  PadicLFunctions` green (3842 jobs, exit 0); `#print axioms` → `zetaIdeal_le_col_image`,
  `mem_cycloTower1_of_col_mem_zetaIdeal`, `isClosed_col_image` = {propext,Classical.choice,Quot.sound};
  `col_image_cycloTower1_eq_zetaIdeal`/`iwasawa_theorem`/`iwasawa_exact_sequence` = +sorryAx.
  **REMAINING (the SOLE sorry, Main:295): only the `⊆` half** `Col '' 𝒞_{∞,1} ⊆ I(𝒢)ζ_p`
  (descent well-definedness) = the cyclic-module density `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))` (RJW
  LemmaGeneratorCinfty1, TeX 3573–3578). Agent PROVED (not just asserted) this is a **tower-level
  ALGEBRAIC density, NOT a continuity gap**: the continuity layer makes `Col '' 𝒞_{∞,1}` closed but
  the `⊆` provably requires either this cyclic-module density or `IsClosed zetaIdeal` (≡ the full
  equality, so can't precede it). → **SPAWN T1206c** (algebraic route; continuity is exhausted for ⊆).
  Committed+pushed (axiom-clean progress). NOT a milestone DONE (sorryAx remains).
- **Status (prior)**: **STRUCTURE COMPLETE — 2 documented deferred sorrys** (2026-06-14, agent a8d7585 +
  orchestrator verify). Both milestone theorems are GENUINELY proved (the real RJW Coleman-map
  descents, NOT vacuous maps): `iwasawa_exact_sequence (i)` = `⟨colDescent⟩` ([u]↦[Col u] via
  `QuotientGroup.lift` of the real `ColMul` hom); `iwasawa_theorem (ii)` = the genuine `≃+` via the
  plus-descent `colDescentPlusMul` + `MulEquiv.ofBijective`. ~12 helper lemmas all clean
  ({propext,Classical.choice,Quot.sound}): `Col_one`, `ColMul`, `Col_cyclo_mem_zetaIdeal`,
  `colDescentMul`/`colDescent`, `cycloTower1Plus_le_cycloTower1`, `zetaIdealPlus_eq_map_projPlus`
  (the bridge `I(𝒢⁺)ζ=π_*(I(𝒢)ζ)`), `ColPlusMul`, `colDescentPlusMul`. `lake build ...Main` clean
  (3717 jobs). `#print axioms iwasawa_theorem/iwasawa_exact_sequence` = [propext,sorryAx,Classical.
  choice,Quot.sound] — sorryAx confined to the 2 deferred lemmas below.
  **The milestone is NOT a clean DONE** (sorryAx present); the 2 remaining inputs:
  - **T1206b (Main.lean) `col_mem_zetaIdeal_iff_mem_cycloTower1`** — REDUCED + body sorry-free
    (2026-06-14, agent a7678f). Agent built AXIOM-CLEAN reusable infrastructure: `galNCU_mul`/
    `galNCU_one` (Generators.lean — the σ_a-action is a group hom of 𝒰_∞, the backbone of the
    Λ(𝒢)-module structure), `zpPow_zetaSys_mem_cycloClosureOne` (CyclotomicUnits.lean — ξ_n^a ∈
    𝒞_{n,1}), `ZpOne_le_cycloTower1` (Main.lean — ℤ_p(1) ⊆ 𝒞_{∞,1}, the injectivity sub-lemma).
    Both directions of the iff (well-definedness + injectivity via `mem_ker_Col_iff_mem_ZpOne` +
    `ZpOne_le_cycloTower1`) are now COMPLETE, reducing everything to the single set-identity:
    **`col_image_cycloTower1_eq_zetaIdeal (hp2) : Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`** (Main.lean:127, the
    lone new sorry). This is RJW §12.4 `LemmaGeneratorCinfty1` content (TeX 3553–3578, the cyclic-
    Λ(𝒢)-module generation of 𝒞_{∞,1} by the Teichmüller-corrected `wγ(a₀)`) — IN-SCOPE §12.4 (the
    `cycloTower1Plus_cyclic_generator` stub, deferred to "E12.4"), NOT §13. Attacking via E12.4.
    NOTE the canonical generator a₀ is not ≡1 mod p, so the principal generator is `wγ(a₀)` (Teich
    correction), and NormCompatUnits has no topology yet (so route via the cyclic-module generation,
    not Col-continuity).
  - **CONVERGED BOUNDARY (2026-06-14, THREE agents ~600k tokens: a8d7585 → a7678f → a820a4)**: the
    milestone is now reduced to the SINGLE identity `col_image_cycloTower1_eq_zetaIdeal (hp2) :
    Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (Main.lean:151). All three agents independently converged on the SAME
    precise blocker, needing TWO genuinely PROJECT-DEFERRED inputs:
    (I) the principal generator `wγ(a₀) ∈ 𝒞_{∞,1}` with `Col(wγ a₀) = ±zetaNum a₀` — needs the
        **𝒪_n-residue Teichmüller** lift `w` = exactly the **deferred T1202a**
        `normCompat_eq_teichmuller_mul_principal` (Equivariance.lean:159; residue hom 𝒪_n^×→𝔽_p^× +
        section + norm-residue compat = a dedicated residue-field-of-𝒪_n / local-CFT pass);
    (II) the closure-crossing: `Continuous (Col p)` (unavailable; Col is a limit construction) OR
        `IsClosed (↑zetaIdeal)` + the inverse-limit cyclic-Λ(𝒢)-module description
        (`cycloTower1Plus_cyclic_generator` full form, TeX 3573–3578) = **deferred §13/IMC**.
    Reusable AXIOM-CLEAN infra banked en route (a7678f + a820a4, 8 lemmas): `galNCU_mul`/`_one`/
    `_elems_val`/`_mem_unitsTower1`, `Col_galNCU_eq_dirac_mul`, `dirac_mul_eq_pushforward`,
    `zpPow_zetaSys_mem_cycloClosureOne`, `ZpOne_le_cycloTower1`. The milestone's full closure genuinely
    requires the T1202a residue-field pass + §13 — both dedicated passes the project's plan defers
    (rule #6 "don't widen ad hoc"; D611–D613 gating; MainConjecture is blueprint-only).
  - **T1206a DONE — Galois fixed-field + (ii) injectivity (2026-06-14, agent a8699e, axiom-clean)**:
    `KPlus_eq_fixedField : K_n⁺ = (K_n)^{⟨σ_{-1}⟩}` (via cyclotomic Galois theory — `isGalois_K`,
    `orderOf_galAut_neg_one`=2, `finrank`-counting, `IntermediateField.eq_of_le_of_finrank_le'`),
    `mem_localUnitsOnePlus_iff_galAut_fixed`, plus-equivariance `Col_mem_plusPart_of_mem_unitsTower1Plus`,
    and **`colDescentPlusMul_injective` proven** (≈15 helpers in GaloisAction.lean + Main.lean, all
    axiom-clean `{propext,Classical.choice,Quot.sound}` modulo the shared col_image). `colDescentPlusMul_
    bijective`'s ONLY remaining sorry (surjectivity, Main:492) now reduces to col_image too.
  - **MAXIMAL REDUCTION REACHED (2026-06-14)**: the ENTIRE §12.5 milestone (both `iwasawa_theorem` and
    `iwasawa_exact_sequence`) now bottlenecks on the SINGLE identity `col_image_cycloTower1_eq_zetaIdeal`
    (Main:151). Everything else — genuine Coleman descents, kernel (`mem_ker_Col_iff_mem_ZpOne`), cokernel
    (`range_Col_eq_ker_chiMoment`), plus-descent (`plusEquiv`/`isCompl`), Galois fixed-field, (ii)
    injectivity, ℤ_p(1)⊆𝒞₁ — is sorry-free + axiom-clean. ~23 reusable axiom-clean infra lemmas banked
    across 4 agents (~900k tokens). col_image is the genuine §13/IMC + T1202a-residue-field boundary
    (4-agent converged). `lake build PadicLFunctions` 3840 jobs ✓.
  - **T1206a (Main.lean:263 / LocalUnits.lean, §12-bounded)** the Galois fixed-field characterisation
    `𝒰⁺_{n,1} = (𝒰_{n,1})^{⟨c⟩}` (`K_n⁺ = (K_n)^{σ_{-1}}`) needed for `colDescentPlusMul_bijective`'s
    injectivity (plus-equivariance of `Col`). KPlus is defined concretely (ξ+ξ⁻¹) with the Galois
    characterisation flagged "§12 material" in LocalUnits.lean. This is BOUNDED, in-scope — being
    attacked via Tier-A. (Note: `colDescentPlusMul_bijective`'s *surjectivity* also needs T1206b.)
- **File**: IwasawaProof/Main.lean | **Depends on**: T1204✓, T1205✓, CLEANUP-ALL-7✓ | **Sub**: T1206a, T1206b
- **Type**: theorems (MILESTONE)
#### Statement
`iwasawa_theorem` (ii): 𝒰_{∞,1}^+/𝒞_{∞,1}^+ ≅ Λ(𝒢^+)/I(𝒢^+)ζ_p (= §11's unwired
thm:iwasawa); `iwasawa_exact_sequence` (i): the Λ(𝒢) SES with cokernel ℤ_p(1).
#### Proof sketch (source TeX 3597–3608)
1. (i): thm:fund exact seq (T1204) mod 𝒞_{∞,1}; image of 𝒞_{∞,1} under Col = I(𝒢)ζ_p by
   `coleman_to_kl`/`Col_cyclo` (§10) at the generators (wγ_{n,a}, T1205 LemmaGenerator-
   Cinfty1: Col((ξ^b γ_{n,a})_n) = Col(c(a)) = ([σ_a]−1)ζ_p, TeX 3602–3606).
2. (ii): take ⟨c⟩-invariants (p odd ⟹ exact, the §11 isCompl_plusPart_minusPart); ℤ_p(1)
   has c acting by −1 so ℤ_p(1)^{⟨c⟩}=0 ⟹ the SES (i)+ collapses to the iso.
3. FINALISE the module-iso encoding (the skeleton's bare AddEquiv → the Λ(𝒢^+)-linear
   form once the quotient module structures are wired).
- **Mathlib**: `MonoidHom`/`QuotientGroup` iso API; `Additive`/module-quotient plumbing.
- **Sources**: Q15 (TeX 3587–3608) + §10 `coleman_to_kl`, §11 `zetaIdeal(Plus)`.
- **Sizing**: ~200 LOC.
- **Progress (2026-06-14, orchestrator dispatch-ready prep — Explore map + substrate verify)**:
  T1206 blocked ONLY on T1204 landing (ab6d73 in flight); all other substrate verified present.
  DISPATCH PLAN (assemble both theorems faithfully — no vacuous 0-map/triv-iso):
  - **(i) `iwasawa_exact_sequence`**: build the genuine descent hom `[u] ↦ [Col u]`,
    `Additive(𝒰₁/𝒞₁) →+ (Λ(𝒢) ⧸ zetaIdeal)`.
    · Well-definedness `Col(𝒞₁) ⊆ zetaIdeal`: `Col_cyclo` (Map.lean:509,
      `Col p (cyclo a) = -zetaNum p a`) + `zetaNum ∈ zetaIdeal` (it IS `([σ_a]−1)·ζ_p`;
      cf. `coleman_to_kl` Map.lean:535) + `Col` is a hom (`Col_add`, FundSeq) + `cycloTower1`
      is generated by the `cyclo a` systems (CyclotomicUnits.lean `cycloTower1`/closure) →
      Col continuous/density to push the inclusion to the closure. The map descends since
      `Col(𝒞₁) ⊆ zetaIdeal`. (Injectivity is NOT required by the `Nonempty (→+)` shape, but
      the SES content — `ker = 𝒞₁`, `coker = ℤ_p(1)` — uses T1204 `mem_ker_Col_iff_mem_ZpOne`
      + `range_Col_eq_ker_chiMoment`; record the SES structure in the proof even though the
      statement only asks for the hom.)
  - **(ii) `iwasawa_theorem`**: plus-descent of (i), as AddEquiv `𝒰₁⁺/𝒞₁⁺ ≃+ Λ(𝒢⁺)⧸zetaIdealPlus`.
    · plus-functor exact for p odd: `isCompl_plusPart_minusPart` (PlusPart.lean:169).
    · `(Λ(𝒢)⧸zetaIdeal)⁺ ≅ Λ(𝒢⁺)⧸zetaIdealPlus`: `plusEquiv` (PlusPart.lean:449),
      `projPlus_surjective` (442), `ker_projPlus` (505), `augmentationIdealPlus_eq_span`
      (ZetaGalois:306), `zetaIdealPlus_eq_span` (ZetaGalois:351).
    · `ℤ_p(1)⁺ = 0` (c acts by −1, p odd): `ZpOne` (FundSeq:376) is c-anti-invariant →
      its plus-part vanishes; mirror `mem_plusPart_iff_forall_odd_moment` (PlusPart:190) /
      `cAct_apply_unitsPowCM` (178). NOTE `ZpOne` lives in the in-flight file — confirm its
      final form after T1204 lands.
    · Confirmed NOT needed (ticket line ~5774): the full `Λ(𝒢⁺)`-cyclic-module structure /
      `cycloTower1Plus_cyclic_generator` full content (that's §13/IMC; the Generators stub's
      vacuous `∃_μ,True` second conjunct is fine to leave — (ii) routes through plus-exactness,
      not cyclicity).
  - SUBSTRATE ALL PRESENT & VERIFIED: `Col_cyclo`/`coleman_to_kl`/`colemanSeries_cyclo`/`zetaNum`
    (Map.lean), `plusEquiv`/`projPlus`(+surjective/ker/section)/`isCompl_plusPart_minusPart`/
    `mem_plusPart_iff_forall_odd_moment` (PlusPart.lean), `zetaIdeal(Plus)`(+`_eq_span`)/
    `augmentationIdeal(Plus)_eq_span`/`padicZeta_odd_moment_eq_zero` (ZetaGalois.lean). The ONLY
    missing pieces are the two assembly theorems themselves + the `Col(𝒞₁)⊆zetaIdeal`
    well-definedness sub-lemma (a T1206-internal step, possibly its own private lemma in Main.lean).
  - NO safe parallel pre-build exists: every remaining piece touches `Col`/`ZpOne` (in-flight
    FundamentalSequence/Map). Wait for ab6d73 → join T1204 → dispatch T1206 sorry-filler-deep on Main.lean.
  - **EXACT signatures verified (2026-06-14, second prep pass)** — the (i) crux is the explicit-
    reciprocity identity `Col(𝒞₁) = Iζ`, assembled from:
    · `Col_cyclo` (Map.lean:509): `Col p (cyclo p ha hp2) = -zetaNum p a` (ha : ¬p∣a).
    · `cyclo_mem_cycloTower1` (CyclotomicUnits.lean:477): `cyclo p ha hp2 ∈ cycloTower1 p`
      (the generator system lives in the tower) + `cyclo_mem_unitsTower1` (500).
    · `coleman_to_kl` (Map.lean:535) + the localisation relation (Map.lean:532-3, `IsLocalization.
      mk'_spec'`): `([a]−1)·ζ_p = zetaNum a` in QuotientField, `[a]−1 ∈ augmentationIdeal` ⟹
      `zetaNum a ∈ zetaIdeal` by `mem_zetaIdeal_iff` (ZetaGalois:270, Iff.rfl). Hence
      `Col(cyclo a) = −zetaNum a ∈ zetaIdeal`.
    · `zetaIdeal_eq_span` (ZetaGalois:279): `Iζ = span{ν}` for any witness ν of `([b]−1)ζ_p` at
      a topological generator b ⟹ `zetaNum a₀` generates Iζ at the canonical generator a₀.
    · `Col_add` (FundSeq:994, stable): `Col(u·v)=Col u+Col v` (the hom property for the descent).
    · `Col_apply_unitsPowCM_one_eq_zero` (FundSeq:900): every `Col u` has χ¹-moment 0 (the easy
      `range ⊆ ker χ-moment` half; the hard ⊇ is T1204 `range_Col_eq_ker_chiMoment`).
    OPEN SUB-STEP for (i) ⊇ (`Iζ ⊆ Col(𝒞₁)`, the cokernel side): needs `cycloTower1` generated
    (topologically) by the `cyclo a` systems — likely a T1206-internal Tier-A sub-lemma
    (`cycloTower1 ≤ Subgroup.closure {cyclo a}` or the image equality `Col '' cycloTower1 = Iζ`).
    For (ii): `plusEquiv` (PlusPart:449) `plusPart p ≃ₗ[ℤ_[p]] PadicMeasure p (GPlus p)`;
    `projPlus_eq_zero_iff` (482) = minusPart; `ker_projPlus` (505) = `span{dirac(−1)−1}`.

### [T1206c] col_image ⊆: the cyclic-module density `𝒞_{∞,1} = closure(Λ(𝒢)·wγ(a₀))`
- **Status**: **DECOMPOSED 2026-06-15 → Route-P board T1220–T1229 (user authorized §12.4 finish +
  chose the faithful plus-part route).** The /develop pass (2026-06-15) REFRAMED this: the residual is
  NOT the deferred §13 `Module(Λ(𝒢))(NormCompatUnits)` structure — it is provable **topologically**
  (banked ST1 induced topology + ST3a levelNorm continuity, NO module instance) by reducing the tower
  density to a per-level density `𝒞_{n,1} ⊆ closure(D_n)`. User chose **Route P** (faithful to RJW
  §12.4–12.5): prove the PLUS density via LemmaGeneratorCinfty1(i) (clean plus cyclicity, banked
  level-n), split `𝒞_{∞,1} = 𝒞⁺_{∞,1}·ℤ_p(1)`, and handle the ξ/minus direction via `Col(ZpOne)=0`
  (banked) + `ℤ_p(1)^⟨c⟩=0` — NOT a novel ξ-component argument. This REPLANS the non-plus reduction
  `col_image_cycloTower1_le_zetaIdeal_of_density` (Main:380). Board: T1220–T1229 below. The pieces
  banked this session (ST1/ST2/ST3a/(A)/(B)/outer-reduction) are the foundations.
  --- (the prior "irreducible §13" surface, now superseded by the /develop reframing) ---
- **Status**: **ENTIRE attackable layer BANKED + axiom-clean — residual is now genuinely irreducible
  by sorry-filling: the deferred §13 inverse-limit `Module (Λ(𝒢)) (NormCompatUnits)` structure.
  B3 surfaced to user 2026-06-15 (SEVENTH converged agent; this time after every sub-layer is closed,
  NOT premature).** Since the user re-fired (below), the full ⊆ chain was driven to its irreducible
  core across 7 background agents (3d6455a→425b957). BANKED axiom-clean ({propext,Classical.choice,
  Quot.sound}), build green (3857 jobs):
  • **ST1** — inverse-limit `TopologicalSpace (NormCompatUnits p)` (SOURCE side, the missing piece all 3
    prior agents flagged): `elemsCoe`/`instTopologicalSpace`/`continuous_elems`/`continuous_iff_elems`/
    `instT2Space`/`continuous_elemsUnits`/`isClosed_cycloTower1` (ColContinuity.lean).
  • **ST2** — `continuous_Col` w.r.t. ST1, via the colemanSeries-continuity core 4+ agents had circled:
    colemanSeries is the UNIQUE solution of `coleman_existsUnique` (NOT an opaque `Classical.choose`),
    so the diagonal collapses to a homeomorphism — `normFixedUnits` compact → `colEval`/`colSec` closed
    embedding → `continuous_colemanSeries`/`continuous_inv_NCU`/`continuous_Col` (ColContinuity.lean).
  • **ST3a** — `continuous_levelNorm` gateway (ColContinuity.lean:375).
  • **Outer reduction** — `col_image_cycloTower1_le_zetaIdeal_of_density` + `cycloGenSubgroup` (M=⟨σ_a·wγ⟩),
    `colPreimageZeta`/`isClosed_colPreimageZeta`/`galNCU_wGamma_mem_colPreimageZeta`/
    `cycloGenSubgroup_le_colPreimageZeta` (Col''M⊆ζ-ideal)/`closure_cycloGenSubgroup_le_cycloTower1` (Main).
  • **(A)** `wGamma_elems_pow_eq_cycloUnit_pow` — (wγ(a₀).elems n)^(p−1)=c_n(a₀)^(p−1), Teichmüller factor
    cancels (Generators.lean:1764, 425b957).
  • **(B)** `cycloUnitU_a0_generates` — every c_n(b') (p∤b') ∈ 𝒢_n-translate subgroup of c_n(a₀) via a₀
    generating (ℤ/p^nℤ)^× + explicit telescoping (Generators.lean:1798, 425b957).
  **SOLE RESIDUAL** (the 2 documented sorries: Main:419 density hypothesis fed to
  `col_image_cycloTower1_le_zetaIdeal_of_density`, + the dependent Main:774 `colDescentPlusMul`
  surjectivity): the **inverse-limit `Module (Λ(𝒢)) (NormCompatUnits)` structure** — a coherent
  `Λ(𝒢)`-module action on the unit tower reconciling (B)'s level-n cyclicity (whose telescoping
  exponent is level-dependent) into the tower-level density `𝒞_{∞,1}=closure(Λ(𝒢)·wγ(a₀))` over the
  ST1 limit topology. This is a major architectural addition (a `Module (Λ(𝒢)) (NormCompatUnits)`
  instance + the level-compatibility of the telescoping), **outside the deep sorry-filler's mandate**
  and **explicitly deferred by plan.md** ("deferred Λ-module structure theorem (that is §13/IMC)") and
  **CLAUDE.md rule #6** ("don't widen ad hoc"). → **B3**: needs explicit user authorization for a
  dedicated `/develop`-planned §13 inverse-limit module-theory pass (with ST1/ST2/ST3a/(A)/(B) as the
  banked foundations) OR acceptance of the maximally-reduced milestone. `iwasawa_theorem`/
  `iwasawa_exact_sequence` carry sorryAx ONLY from this one residual.
  --- (RE-OPEN that drove the above; superseded — all 4 sub-steps now closed) ---
- **Status**: **RE-OPENED 2026-06-14 (user re-fired beastmode = keep attacking) — NEW ANGLE: the
  inverse-limit `TopologicalSpace` on `NormCompatUnits`, never attempted.** The 3 prior agents all
  hit the same wall: ⊆ needs to push `𝒞_{∞,1}=closure(Λ·wγ)` through `Col` into the closed `zetaIdeal`,
  which needs a TOPOLOGY ON `NormCompatUnits` (the SOURCE side) + `Continuous Col` w.r.t. it — they
  flagged it ABSENT but a7cc206 only built topology on `PadicMeasure`/`PowerSeries` (the TARGET side).
  THE CHAIN (4 sub-steps, all now feasible given the banked pieces): (ST1) inverse-limit
  `TopologicalSpace (NormCompatUnits p)` from the levelwise `ℂ_pˣ` topologies (the `elems n` coords);
  (ST2) `Continuous (Col p)` w.r.t. it (Col factors levelwise via the Coleman series → `colemanPipe2`,
  banked continuous); (ST3) `𝒞_{∞,1} = closure(ℤ_p[𝒢]-span{σ_a•wγ(a₀)})` in that topology — the
  inverse-limit assembly of the BANKED `cycloUnit_mem_cycloTranslateSubgroup` (cor:cyc units gen 2) +
  `galNCU` σ_a-action + `closure_zspan_eq_zpspan` + (p−1)-descent; (ST4) ⊆: `Col(closure(span)) ⊆
  closure(Col span) = closure(ℤ_p[𝒢]·ζ_num) ⊆ zetaIdeal` via ST2 continuity + banked `isClosed_zetaIdeal`
  + `dirac_mul_zetaNum_mem_col_image`. This is in-scope §12/§13 (RJW's own LemmaGeneratorCinfty1 route);
  "multi-file" = beastmode target, not exit. Dispatching a fresh agent on the full chain (new angle).
  --- (prior B3 surface, now superseded by the re-fire) ---
- **Status**: **BLOCKED on the plan-DEFERRED §13/IMC Λ(𝒢)-module layer — B3 boundary, surfaced to user
  2026-06-14 (THREE deep agents converged: a7cc206, a4573cd, a276ef)**. Maximal reduction reached:
  every closeable piece of the milestone is now axiom-clean + pushed — (i) ⊇ density-crossing
  `zetaIdeal_le_col_image` (3d6455a, via the 536L ColContinuity.lean weak-* topology layer); (ii)
  closedness `isClosed_zetaIdeal` (386020a, p-adic Banach–Alaoglu); (iii) **level-n cyclicity
  `cor:cyc units gen 2` = `cycloUnit_mem_cycloTranslateSubgroup` (7167ea6, σ_a-action `galAutVal_cycloUnit`
  + telescoping `prod_galAutValU_cycloUnit_telescope`, replacing the vacuous stub)**; (iv) injectivity
  `mem_cycloTower1_of_col_mem_zetaIdeal`. The SOLE residual (Main:308 ⊆ sorry + the dependent Main:663
  surjectivity) is the **inverse-limit `Λ(𝒢)`-module structure on `NormCompatUnits`**: a
  `Module (Λ(𝒢)) (NormCompatUnits)` instance + the intertwining `Col(λ•u)=λ·Col u` for arbitrary
  `λ∈Λ(𝒢)` — proven EQUIVALENT to the absent `Continuous Col` (circular), so it genuinely needs the
  multi-file tower-lift `𝒞_{∞,1}=closure(Λ(𝒢)·wγ(a₀))` (RJW LemmaGeneratorCinfty1, TeX 3573–3578).
  This is the **deferred §13/IMC module layer** (CLAUDE.md rule #6 "don't widen ad hoc"; plan "deferred
  Λ-module structure theorem (that is §13/IMC)"; "MainConjecture is blueprint-only"; D611–D613 gating).
  → **B3**: needs explicit user authorization for a dedicated multi-file §13 module-theory development
  (a NEW scope decision beyond the user's earlier "§13-continuity + T1202a" authorization, which is now
  fully discharged). `iwasawa_theorem`/`iwasawa_exact_sequence` carry sorryAx ONLY from this one residual.
  --- (prior) ---
- **Status**: **OPEN — closedness half BANKED, residual = level-n cyclic generation (2026-06-14, agent
  a4573cd + on-disk verify)**. NEW axiom-clean in ColContinuity.lean: `isClosed_zetaIdeal` (proved
  INDEPENDENTLY of the image identity via p-adic Banach–Alaoglu: `instCompactSpace (PadicMeasure ℤ_p^×)`
  = weak-* coercion induces onto the compact Tychonoff product `∏_f ℤ_[p]` with closed range
  `isClosed_range_coe`; then `isClosed_span_singleton` ⇒ `zetaIdeal=span{zetaNum a₀}` closed). This
  REMOVES the closedness half of the ⊆ obstruction (the file comment's `IsClosed ↑zetaIdeal` requirement).
  On-disk verified: build green (3842 jobs); these 4 = {propext,Classical.choice,Quot.sound}; iwasawa_theorem
  still +sorryAx. **The ⊆ now reduces to EXACTLY ONE thing**: the algebraic level-n single-generator
  cyclicity **`cor:cyc units gen 2`** (TeX 3484–3486) — `𝒟_{n,1}^+` is generated over `ℤ[𝒢_n^+]` by one
  `γ_{a₀}` (a₀ generating `(ℤ/p^nℤ)^×`), needing a CLOSED FORM for the σ_a-action on `c_n(b)` (`σ_{a₀}(c_n(b))
  = (ξ^{a₀b}−1)/(ξ^{a₀}−1)`) + the telescoping `γ_{n,b}=∏(γ_{n,a₀})^{σ_{a₀}^i}` + (p−1)-invertibility
  descent + Λ(𝒢^+) inverse-limit assembly. SECOND deep agent converged here (a7cc206 continuity + a4573cd
  algebraic). a4573cd was a SHORT run (133k tok) that IDENTIFIED but did not deeply attack `cor:cyc units
  gen 2` in isolation → spawn a focused narrow agent on JUST that level-n generation. Committed+pushed.
- **(prior status)**: **OPEN — spawned 2026-06-14** (Tier-A from T1206; the §13 *continuity* route is
  EXHAUSTED for this half — agent a7cc206 proved continuity gives only ⊇ + `isClosed_col_image`, and
  ⊆ provably needs this algebraic density or `IsClosed zetaIdeal`≡full-equality). Attack via the
  ALGEBRAIC inverse-limit cyclic-module description, NOT continuity.
- **File**: PadicLFunctions/IwasawaProof/Main.lean:295 (the lone `sorry`); likely new lemmas in
  Generators.lean / CyclotomicUnits.lean. | **Depends on**: T1206 (⊇ + injectivity, DONE/clean).
- **Type**: theorem (closes the milestone's sorryAx).
#### Statement
The `⊆` half of `col_image_cycloTower1_eq_zetaIdeal`: `Col '' 𝒞_{∞,1} ⊆ I(𝒢)ζ_p`. Equivalently
(and the intended route) the RJW LemmaGeneratorCinfty1 inverse-limit module density: `𝒞_{∞,1}` is the
topological closure of the `Λ(𝒢)`-span (= `ℤ_p[[𝒢]]`-span) of the single Teichmüller-corrected
generator `wγ(a₀)` (`a₀` = the canonical topological generator of `ℤ_p^×`, NOT ≡1 mod p). Then for
`u ∈ 𝒞_{∞,1}`, `Col u ∈ closure(ℤ_p·{[σ_a]·ζ_num a₀}) = I(𝒢)ζ_p` since `Col(σ_a·wγ a₀) = [σ_a]·Col(wγ a₀)
= ±[σ_a]·ζ_num a₀` (`Col_wGamma` + `Col_lambdaG_equivariant`, both axiom-clean) and `Col` is weak-*
continuous into the closed `I(𝒢)ζ_p` (now available: `continuous`-pairing + `isClosed`; `zetaIdeal` is
the closed `colImageSubgroup`-style span — reuse `isClosed`/`approxDirac` machinery from ColContinuity).
#### Proof sketch (source TeX 3553–3578, RJW §12.4 LemmaGeneratorCinfty1)
1. Level-n: `𝒞_{n,1}^+` is cyclic over `ℤ_p[𝒢_n^+]` generated by `wγ_{n,a₀}` — partially banked:
   `cycloUnitsPlus_eq_closure_gammas` (𝒟ₙ⁺ = closure{γ_b}∪{−1}, Generators:803), `closure_zspan_eq_zpspan`
   (r=1 closure=ℤ_p-pow, Generators:897), `gammaUnit_congr_natCast`/`cycloTower1Plus_cyclic_generator`
   (γ≡a₀ mod πₙ congruence, Generators:971/1000). MISSING: the (p−1)-divisibility cyclic generation
   (`(wγ)^{p−1}` gen `(p−1)𝒟ₙ⁺`, p−1 invertible in ℤ_p) assembling these into "`𝒞_{n,1}^+` cyclic
   ℤ_p[𝒢ₙ⁺]-mod gen by `wγ_{n,a₀}`" — this is the genuine content of the `cycloTower1Plus_cyclic_generator`
   stub (currently has a vacuous `∃ _μ, True` tail; replace with the real statement).
2. Inverse limit: `𝒞_{∞,1}^+ = ⟦lim⟧ 𝒞_{n,1}^+ = Λ(𝒢⁺)·(wγ_{n,a₀})ₙ` (the Λ-module limit of cyclic
   ℤ_p[𝒢ₙ⁺]-modules). Then drop the `+` via the established split. The σ_a-stability is banked
   (`galNCU_*`, `galNCU_wGamma_mem_cycloTower1`).
3. Apply `Col`: equivariance (`Col_lambdaG_equivariant`) + `Col_wGamma` send the Λ(𝒢)-span of `wγ(a₀)`
   onto the ℤ_p[𝒢]-span of `ζ_num a₀`, whose closure is `I(𝒢)ζ_p` (`zetaIdeal_eq_span`,
   `augmentationIdeal`-span). Continuity (now available) crosses the closure.
- **Banked axiom-clean infra to reuse**: `wGamma`/`Col_wGamma`/`wGamma_mem_cycloTower1`,
  `Col_lambdaG_equivariant`, `cycloUnitsPlus_eq_closure_gammas`, `closure_zspan_eq_zpspan`,
  `cycloUnitsPlus`/`cycloTower1`/`cycloTower1Plus` defs, the entire ColContinuity.lean topology layer.
- **RISK**: this is the repeatedly-deferred tower-level Iwasawa-module density. If a focused agent
  cannot close it after a genuine algebraic attack, it is a real B3-adjacent boundary → surface to user
  with the precise residual (do NOT fake).

## Route-P board — EXECUTION LOG (2026-06-15 /beastmode)
- **TOP cluster DONE + axiom-clean** (commit 41fd35d): `mem_closure_iff_elemsCoe` (closure_induced
  bridge), `Col_eq_of_elems_eq` (Col level-0-insensitivity, the KEY lever — level-0 coord is free,
  Col ignores it), `exists_delta_descent` + `mem_closure_of_levelwise` (inverse-limit descent).
- **Col-density layer DONE** (commit 27b9481): `glueLevel0` + `Col_mem_closure_image_of_levelwise`
  (level-0-SATURATED density — the correct workhorse, since cycloGenSubgroup's level-0 image is
  ⟨wγ.elems 0⟩, p−1-torsion, NOT {1}, making the h0-form unusable). **T1223 PROVED**:
  `col_mem_zetaIdeal_of_mem_cycloTower1Plus` (u∈𝒞⁺ ⟹ Col u∈ζ-ideal) via the saturated density +
  T1222(stmt) + `elemsMonoidHom`/`map_elemsMonoidHom_cycloGenSubgroup` + Units.val bridge.
- **DISPATCHED (background agents, 2026-06-15)**: T1222 (`cycloClosureOnePlus_le_closure_wGammaTranslate`,
  level-n plus density = LemmaGeneratorCinfty1(i)) → Generators worktree agent; the Main completion
  (T1224' minus-structural `mem_ZpOne_of_mem_cycloTower1_cAnti` = lem:cyc units gen (ii), col_mem
  rewrite via plus+minus+2-inv, col_image ⊆, surjectivity via ℤ_p(1)^⟨c⟩=0) → Main-tree agent.
- Reframing CONFIRMED: NO Module(Λ(𝒢))(NormCompatUnits) needed; level-0 handled by Col-insensitivity.
- Un-privated: `cycloTranslateSubgroup`, `galAutValU`, `galNCU_elems_eq_galAutValU` (Generators).
- RE-DISPATCHED 2026-06-15 (after a premature kill — the agents were progressing, not stuck):
  T1222 → worktree agent ac377453 (Generators, level-n plus density, with explicit (p−1)-descent +
  lem:closure structure); T1224' → worktree agent acd539bc (Main, minus→ℤ_p(1) via lem:cyc units
  gen(ii), with the ξ×𝒟⁺ decomposition + galAut(-1) building blocks). Both NARROW single-lemma
  targets + plumbing tips (conv-targeted rw, Units.ext). PATIENT this time: let them run to
  auto-completion. On both landing: apply proofs → main tree, then col_mem assembly (plus+minus+
  2-inv via T1223+T1224') + col_image ⊆ + surjectivity (ℤ_p(1)^⟨c⟩=0) + blueprint wiring (T1228).
- IN-FLIGHT (prior, superseded by re-dispatch): the two dispatched agents are on the deepest proofs (T1222
  LemmaGeneratorCinfty1(i) level-n plus density; T1224' lem:cyc units gen(ii) minus→ℤ_p(1) +
  col_mem assembly + surjectivity), both ACTIVE (Main agent transcript ~442KB = extensive
  search/build cycles, expected for these PhD-grade formalisations; no successful Lean emitted
  yet). Watches armed (bguivy9ah on Main sorry-drop); agents auto-notify on completion. On
  completion: apply T1222 worktree proof → main Generators, verify Main agent's
  col_mem/col_image/surjectivity, `#print axioms` milestone, then T1228 blueprint wiring.

- **MILESTONE STATUS 2026-06-15 (late) — 3/4 cores DONE+pushed**:
  • T1222 + H1 (`galNCU_neg_one_mem_cycloTower1`) → Generators sorry-free @ad5a631. Ported from
    worktree agents, then degraded-mode build-fixed (no lean-lsp this session): `⟨c,rfl⟩`
    elaboration order (`refine pow_mem (subset_closure ?_)`), cycloUnit rw-count, the
    `zetaSys_eq_cycloUnit_two_ratio` field identity (`pow_mul` direction, `eq_div_iff`+`mul_inv_cancel₀`
    instead of group-only `mul_inv_eq_iff_eq_mul`), inline K-closedness (`isClosed_KCp` is in
    ColContinuity which imports Generators ⟹ unavailable; used `Submodule.closed_of_finiteDimensional`),
    `MulOpposite.continuous_op` + field-inverse `hcoeinv`.
  • surj `colDescentPlusMul_bijective` sorry-free @a16c95c — right-exactness route, col_image OFF path.
  • LAST: T1224' `mem_ZpOne_of_mem_cycloTower1_cAnti` — agent a3402eb9 (3rd dispatch).
  ROOT OBSTACLE: `cycloUnits_normalForm`/`galAutVal_cycloUnit`/`cycloUnit`/`cycloGenSet` are PRIVATE in
  Generators ⟹ T1224' can't be done in Main alone; need a PUBLIC bridge lemma in Generators.
  CORRECTED PLAN (target is ⟨−ξ⟩ NOT ⟨ξ⟩): cycloGenSet gens are RAW values ξ, −ξ, ξ^a−1; the
  antisymmetrisation A(w)=w·σ(w)⁻¹ gives A(ξ^a−1)=−ξ^a, A(ξ)=ξ², A(−ξ)=ξ² — all in ⟨−ξ⟩ (order 2pⁿ,
  finite⟹closed). Public `cycloUnits_anti_mem_zpowers_negZeta : ∃m, A(w).val=(−ξ)^m`; then Main:
  z_n²=(−ξ)^m, principal⟹m even⟹ξ-power, sqrt(2⁻¹), level-assemble via `levelNorm_zpPow_zetaSysM`+compat.
  LESSON: do NOT kill agents on file-idle/small-transcript — they work in `lean_run_code` (no file
  writes) for long stretches; a8b5e038 was killed wrongly while productively deriving this plan.

## Route-P board (§12.4–12.5 finish, faithful plus-part) — created 2026-06-15 (/develop)

**Goal**: close the milestone's two sorries — `col_image_cycloTower1_eq_zetaIdeal` ⊆ (Main:433) and
`colDescentPlusMul_bijective` surjectivity (Main:786) — via RJW's faithful plus-part route. **Endgame
identity**: `Col '' cycloTower1 = zetaIdeal` (⊇ banked `zetaIdeal_le_col_image`; ⊆ = the Route-P work).

**Prose proof (Step 1, RJW §12.4–12.5, TeX 3495–3608)**: `𝒰_{n,1} = 𝒰⁺_{n,1} × 𝒰⁻_{n,1}` (p odd, c =
complex conj). The cyclotomic units `𝒟_n = ⟨ξ, 𝒟_n^+⟩` (lem:cyc units gen), so the closure
`𝒞_{n,1} = 𝒞⁺_{n,1} × ℤ_p(1)_n`, minus part `= ⟨ξ⟩`-closure `= ℤ_p(1)` at level n. (i) [LemmaGenerator-
Cinfty1(i)] `𝒞⁺_{n,1}` is cyclic `ℤ_p[𝒢_n^+]` gen by `wγ_{n,a₀}` (via `(p−1)𝒟_n^+ = ℤ[𝒢_n^+]·(wγ)^{p−1}`,
lem:closure, `(p−1)` invertible). (ii) inverse limit: `𝒞⁺_{∞,1} = closure(Λ(𝒢⁺)·(wγ)_n)`. Then
`Col '' cycloTower1 = Col '' (cycloTower1Plus·ℤ_p(1)) = Col '' cycloTower1Plus` (Col kills ℤ_p(1)) `=
I(𝒢)ζ_p` (each `Col(σ_a wγ)=[a](−ζ_num a₀)`, RJW thm:coleman to kl). The plus iso (ii) follows from the
SES (i) by ⟨c⟩-invariants: `ℤ_p(1)^⟨c⟩=0` (c acts by −1, p odd).

**Source quotes** (from `.mathlib-quality/references/2309.15692-padic-L-functions.tex`, agent-verified):
- LemmaGeneratorCinfty1 (3553–3578): "(i) The module 𝒞_{n,1}^+ is a cyclic ℤ_p[𝒢⁺_n]-module generated
  by wγ_{n,a}. (ii) The module 𝒞⁺_{∞,1} is a cyclic Λ(𝒢⁺)-module generated by (wγ_{n,a})_{n≥1}." Proof
  (ii): "𝒞⁺_{∞,1} ≅ lim 𝒞⁺_{n,1} = lim(ℤ_p[Γ⁺_n]·wγ_{n,a}) ≅ Λ(Γ⁺)·(wγ_{n,a})_n, with all maps as
  Λ(Γ⁺)-modules and where the middle equality is (i)."
- lem:closure (3503–3519): "the p-adic closure X̄ of X = ⟨g_1,…,g_r⟩ in 𝒰_{n,1} is the ℤ_p-submodule
  generated by g_1,…,g_r" (proof: binomial convergence g_i^{a_j}→g_i^a + compactness of ℤ_p^r).
- lem:global generators 2 (3526–3550): "(ii) (wγ_{n,a})^{p−1}=γ_{n,a}^{p−1} ∈ 𝒰⁺_{n,1}, and generates
  ℤ[Γ⁺_n]·(wγ_{n,a})^{p−1} = (p−1)𝒟_n^+."
- thm:iwasawa 2 (3587–3608): SES (i) `0→𝒰_{∞,1}/𝒞_{∞,1}→Λ(𝒢)/I(𝒢)ζ_p→ℤ_p(1)→0`; iso (ii)
  `𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`. "Since p is odd … c acts on ℤ_p(1) by −1, ℤ_p(1)^⟨c⟩=0."

**Banked foundations (sorry-free, reuse)**: ST1 `instTopologicalSpace`/`continuous_elems`/
`isClosed_cycloTower1` (ColContinuity), ST2 `continuous_Col`, ST3a `continuous_levelNorm`; level-n
`cycloUnit_mem_cycloTranslateSubgroup`/`closure_zspan_eq_zpspan`/`cycloUnitsPlus_eq_closure_gammas`;
(A) `wGamma_elems_pow_eq_cycloUnit_pow`, (B) `cycloUnitU_a0_generates`; `ZpOne`/
`mem_ker_Col_iff_mem_ZpOne`/`range_Col_eq_ker_chiMoment` (FundamentalSequence); `Col_wGamma`/
`galNCU_elems_eq_galAutValU`/`galNCU_wGamma_mem_cycloTower1`/`closure_cycloGenSubgroup_le_cycloTower1`/
`cycloGenSubgroup_le_colPreimageZeta`/`isClosed_colPreimageZeta`. mathlib: `closure_induced`,
`IsInducing.closure_eq_preimage_closure_image`, `Subgroup.map_closure`, `EMetric.mem_closure_iff`,
`Subgroup.topologicalClosure_coe`.

### [T1220] Inverse-limit closure characterization (TOP)
- **Status**: open | **File**: Coleman/ColContinuity.lean (or IwasawaProof/TowerDensity.lean new) |
  **Depends on**: ST1, ST3a (banked) | **Type**: theorem
#### Statement
```lean
theorem mem_closure_normCompat_iff {S : Subgroup (NormCompatUnits p)} {u : NormCompatUnits p} :
    u ∈ closure (S : Set (NormCompatUnits p)) ↔
      ∀ n, 1 ≤ n → (u.elems n : ℂ_[p]) ∈
        closure ((fun s : NormCompatUnits p => (s.elems n : ℂ_[p])) '' S) := by sorry
```
#### Proof sketch
ST1: `instTopologicalSpace` is `induced (elemsCoe p)`, so `closure_induced` gives `u ∈ closure S ↔
elemsCoe u ∈ closure (elemsCoe '' S)` in `∏_n ℂ_p`. (⟹) project: `continuous_elems n` ⟹ coordinate-n
in `closure(elems_n '' S)`. (⟸) the content: a basic nhd of `u` constrains finitely many levels
`{n_1<…<n_k}`; pick top `N=n_k`, get `s∈S` with `s.elems N ≈ u.elems N` within `δ`; iterated
`continuous_levelNorm` (ST3a) + norm-compat (`s.compat`, `u.compat`, levels ≥1) propagate to
`s.elems n_i ≈ u.elems n_i` ∀i. Bridge via `Units.continuous_val` (ℂ_pˣ→ℂ_p). Use `mem_closure_iff_nhds`
+ `EMetric.mem_closure_iff`.
- **Mathlib**: `closure_induced` (Topology/Order.lean:940), `IsInducing.closure_eq_preimage_closure_image`
  (Maps/Basic.lean:136), `continuous_levelNorm` (ST3a), `Units.continuous_val`, `EMetric.mem_closure_iff`.
- **Generality**: arbitrary subgroup `S` (the char is structural, not wγ-specific). Levels ≥ 1 (norm-compat
  domain). RISK: level-0 coordinate — exclude it (the topology/towers only constrain n≥1; verify the
  induced topology's basic opens reduce to n≥1, else add an `n=0` triviality leaf).

### [T1221] Level-n image of the Galois-orbit subgroup (TOP)
- **Status**: open | **File**: IwasawaProof/TowerDensity.lean | **Depends on**: T1220 | **Type**: theorem
#### Statement
```lean
-- elems_n is a MonoidHom NormCompatUnits →* ℂ_[p]ˣ; the level-n image of the wγ-orbit subgroup
-- is the level-n Galois-translate subgroup of (wGamma).elems n.
theorem elems_image_cycloGenSubgroupPlus (hp2 : p ≠ 2) (n : ℕ) :
    (fun s : NormCompatUnits p => (s.elems n : ℂ_[p]ˣ)) '' (cycloGenSubgroupPlus p hp2) =
      (cycloTranslateSubgroup p n ((wGamma p hp2).elems n) : Set ℂ_[p]ˣ) := by sorry
```
#### Proof sketch
`elems_n : NormCompatUnits →* ℂ_[p]ˣ` (levelwise mul/inv: `(u*v).elems n = u.elems n * v.elems n`,
`u⁻¹.elems n = (u.elems n)⁻¹`). `cycloGenSubgroupPlus = Subgroup.closure {galNCU a wGamma}` (plus variant).
`Subgroup.map_closure`: image `= closure {elems_n(galNCU a wGamma)} = closure {galAutValU a n (wGamma.elems n)}`
(`galNCU_elems_eq_galAutValU`, banked) `= cycloTranslateSubgroup n (wGamma.elems n)`.
- **Mathlib**: `Subgroup.map_closure` (Map.lean:573), `Subgroup.coe_map`.
- **Banked**: `galNCU_elems_eq_galAutValU` (Generators:1582).
- **Note**: define `elemsHom n : NormCompatUnits p →* ℂ_[p]ˣ` (small bundling leaf).

### [CLEANUP-130] /cleanup the TOP cluster (T1220–T1221)
- **Status**: open | **Depends on**: T1221 | **Type**: cleanup

### [T1222] Level-n PLUS density 𝒞⁺_{n,1} ⊆ closure(Dⁿ⁺) (LemmaGeneratorCinfty1(i))
- **Status**: DONE (@ad5a631, 2026-06-15) — `cycloClosureOnePlus_le_closure_wGammaTranslate`
  sorry-free (+18 private helpers: (p−1)-power descent over c_n/ξ/γ/𝒟ₙ normal form +
  zpPow-closure of the unique (p−1)-root). Verified via degraded-mode build (lean-lsp absent
  this session). | **File**: IwasawaProof/Generators.lean | **Depends on**: (A),(B) banked |
  **Type**: theorem (the hard plus cyclicity — most banked)
#### Statement
```lean
-- The level-n plus cyclotomic closure lies in the topological closure of the ℤ[𝒢_n]-translate
-- subgroup of wγ_{n,a₀}.  D_n := cycloTranslateSubgroup n ((wGamma).elems n).
theorem cycloClosureOnePlus_le_closure_translate (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    (cycloClosureOnePlus p n : Set ℂ_[p]ˣ) ⊆
      closure (cycloTranslateSubgroup p n ((wGamma p hp2).elems n) : Set ℂ_[p]ˣ) := by sorry
```
#### Proof sketch (RJW LemmaGeneratorCinfty1(i) + lem:global generators 2(ii) + lem:closure)
1. `cycloUnitsPlus_eq_closure_gammas` (banked): `𝒟⁺_n = closure({γ_{n,b}:p∤b}∪{−1})`.
2. Level-n cyclicity (`cycloUnit_mem_cycloTranslateSubgroup`, banked): each `c_n(b') ∈ ⟨σ_a c_n(a₀)⟩`
   (a₀ generates `(ℤ/pⁿ)^×`). The γ_{n,b} relate to c_n(b) by the ξ^{(1−b)/2} twist (plus-correction);
   `(wγ)^{p−1}=c_n(a₀)^{p−1}` (A, banked) ties wγ to c_n(a₀).
3. `(p−1)𝒟⁺_n = ℤ[𝒢_n^+]·(wγ)^{p−1}` (lem:global generators 2(ii)); `(p−1)` invertible in ℤ_p ⟹
   the ℤ_p[𝒢_n^+]-closure is gen by `wγ` itself (unique (p−1)-th root ≡1 mod 𝔭_n).
4. `closure_zspan_eq_zpspan` (banked, lem:closure, r=1): p-adic closure of ℤ-span = ℤ_p-span (`zpPow`).
   Assemble: `𝒞⁺_{n,1} = closure(𝒟⁺_n) ⊓ 𝒰_{n,1} ⊆ closure(⟨σ_a wγ_n⟩)`.
- **Banked**: `cycloUnitsPlus_eq_closure_gammas` (Gen:803), `cycloUnit_mem_cycloTranslateSubgroup`
  (Gen:1569), `wGamma_elems_pow_eq_cycloUnit_pow` (Gen:1776), `cycloUnitU_a0_generates` (Gen:1798),
  `closure_zspan_eq_zpspan` (Gen:897), `gammaUnit_*`.
- **RISK (highest in board)**: connecting the γ-based `𝒟⁺_n`-generators to the c_n-based wγ-orbit (the
  ξ^{(1−b)/2} twist bookkeeping + the (p−1)-descent) may need 1–3 sub-leaves — Tier-A spawn point. The
  source does this in lem:global generators 2; mirror it.

### [T1223] Tower PLUS density cycloTower1Plus ⊆ closure(M⁺) (LemmaGeneratorCinfty1(ii))
- **Status**: open | **File**: IwasawaProof/TowerDensity.lean | **Depends on**: T1220,T1221,T1222 |
  **Type**: theorem
#### Statement
```lean
theorem cycloTower1Plus_le_closure_cycloGenSubgroupPlus (hp2 : p ≠ 2) :
    (cycloTower1Plus p : Set (NormCompatUnits p)) ⊆
      closure (cycloGenSubgroupPlus p hp2 : Set (NormCompatUnits p)) := by sorry
```
#### Proof sketch
`u ∈ cycloTower1Plus` ⟹ ∀n≥1, `u.elems n ∈ cycloClosureOnePlus p n`. By T1220 (char), suffices ∀n≥1,
`u.elems n ∈ closure(elems_n '' M⁺)` = `closure(cycloTranslateSubgroup n (wGamma.elems n))` (T1221).
That is T1222. Done.
- **Depends**: T1220 (char), T1221 (image), T1222 (level density).

### [T1224] The plus/minus split cycloTower1 ⊆ cycloTower1Plus · ZpOne (structural)
- **Status**: open | **File**: IwasawaProof/TowerDensity.lean (or Iwasawa/PlusMinusTower.lean) |
  **Depends on**: ZpOne (banked), the c-action galNCU(−1) | **Type**: theorem
#### Statement
```lean
-- Every non-plus cyclotomic tower unit factors as (plus tower unit) · (ξ-power tower in ℤ_p(1)).
theorem cycloTower1_le_mul_ZpOne (hp2 : p ≠ 2) (u : NormCompatUnits p) (hu : u ∈ cycloTower1 p) :
    ∃ u₊ ∈ cycloTower1Plus p, ∃ z ∈ ZpOne p, u = u₊ * z := by sorry
```
#### Proof sketch (RJW lem:cyc units gen `𝒟_n = ⟨ξ, 𝒟_n^+⟩`, p odd c-split)
Level-n: `𝒰_{n,1} = 𝒰⁺_{n,1} × 𝒰⁻_{n,1}` (c = `galAut(−1)`, p odd; `localUnitsPlus` = c-fixed field
`KPlus`). `𝒞_{n,1}` minus part `= ⟨ξ_{pⁿ}⟩`-closure `= ℤ_p(1)_n` (`𝒟_n=⟨ξ,𝒟_n^+⟩`). Decompose
`u.elems n = (u.elems n)₊ · ξ_{pⁿ}^{a_n}`; the `(·)₊` parts assemble (norm-compat) to `u₊∈cycloTower1Plus`,
the `ξ^{a_n}` to `z∈ZpOne` (single `a∈ℤ_p` by norm-compat of the minus, `zetaSys_pow_p`).
- **Banked**: `ZpOne` (FundSeq:382), `localUnitsPlus`/`KPlus`, `galAut(−1)` ξ↦ξ⁻¹ (Gen:362),
  `mem_localUnitsOnePlus_iff_galAut_fixed` (GaloisAction).
- **RISK (2nd highest)**: the level-n plus/minus SPLIT of `𝒰_{n,1}` and the norm-compat assembly of the
  minus into a single `ZpOne` element are partly ABSENT — needs a level-n `c`-eigen-decomposition leaf
  (idempotents `(1±c)/2` need 2 invertible — p odd ✓, but on a multiplicative group use `x = x₊·x₋` with
  `x₊ = (x·c(x))^{1/2}`-style, or the `KPlus` projection). Tier-A spawn: `localUnitsOne_eq_plus_mul_minus`
  + `cycloClosureOne_minus_eq_ZpOne_level`. Mirror RJW lem:decompose plus minus (§11, p odd).

### [CLEANUP-131] /cleanup the density clusters (T1222–T1224)
- **Status**: open | **Depends on**: T1224 | **Type**: cleanup

### [T1225] col_image ⊆ : Col '' cycloTower1 ⊆ zetaIdeal (closes Main:433)
- **Status**: open | **File**: IwasawaProof/Main.lean | **Depends on**: T1223,T1224 | **Type**: theorem
  (REPLANS `col_image_cycloTower1_le_zetaIdeal_of_density` → split-based, no non-plus density needed)
#### Statement
```lean
-- replaces the sorry at Main:433 inside col_image_cycloTower1_eq_zetaIdeal (the ⊆ branch)
theorem col_image_cycloTower1_le_zetaIdeal (hp2 : p ≠ 2) :
    Col p '' (cycloTower1 p : Set (NormCompatUnits p)) ⊆
      (PadicMeasure.zetaIdeal p hp2 : Set (PadicMeasure p ℤ_[p]ˣ)) := by sorry
```
#### Proof sketch
`u ∈ cycloTower1` → (T1224) `u = u₊·z`, `u₊∈cycloTower1Plus`, `z∈ZpOne`. `Col u = Col u₊ + Col z`
(`Col_add`). `Col z = 0` (`mem_ker_Col_iff_mem_ZpOne`, banked; `z∈ZpOne⊓unitsTower1`). `u₊∈cycloTower1Plus
⊆ closure(M⁺)` (T1223) `⊆ colPreimageZeta` (plus version of `cycloGenSubgroup_le_colPreimageZeta` +
`isClosed_colPreimageZeta`), so `Col u₊ ∈ zetaIdeal`. Hence `Col u = Col u₊ ∈ zetaIdeal`. Then wire into
`col_image_cycloTower1_eq_zetaIdeal` ⊆ branch (replacing the `_of_density` call + sorry).
- **Banked**: `mem_ker_Col_iff_mem_ZpOne` (FundSeq:810), `Col_add`/`Col_one`, `isClosed_colPreimageZeta`
  (Main:325), `cycloGenSubgroup_le_colPreimageZeta` (Main:357 — adapt to plus M⁺).

### [T1226] ℤ_p(1)^⟨c⟩ = 0 (the c acts by −1, p odd)
- **Status**: open | **File**: IwasawaProof/FundamentalSequence.lean | **Depends on**: ZpOne, galNCU(−1)
  | **Type**: theorem
#### Statement
```lean
-- complex conjugation acts by inversion on ℤ_p(1); its ⟨c⟩-invariants are trivial (p odd).
theorem ZpOne_galNCU_neg_one (z : NormCompatUnits p) (hz : z ∈ ZpOne p) :
    galNCU p (-1) z = z⁻¹ := by sorry
-- and: an element of ZpOne fixed by c (p odd) is trivial — used for the (ii) collapse.
theorem ZpOne_cInvariant_eq_one (hp2 : p ≠ 2) {z : NormCompatUnits p}
    (hz : z ∈ ZpOne p) (hc : galNCU p (-1) z = z) : z = 1 := by sorry
```
#### Proof sketch
`σ_{-1}(ξ_{pⁿ}) = ξ_{pⁿ}⁻¹` (`galAut(−1)`, Gen:362) ⟹ `σ_{-1}(ξ^a)=ξ^{-a}`, i.e. `galNCU(−1) z = z⁻¹`
on ZpOne. If also `=z` then `z²=1`; `z=ξ^a`-type with `2a≡0`, p odd ⟹ `a` torsion in ℤ_p ⟹ `a=0` ⟹ `z=1`.
- **Banked**: `galAut p (-1) … = (zetaSys)⁻¹` (Gen:362), `ZpOne` group laws (`zpPow` character).

### [T1227] colDescentPlusMul surjectivity (closes Main:786) + milestone
- **Status**: DONE (@a16c95c, 2026-06-15) — `colDescentPlusMul_bijective` sorry-free. REPLAN:
  surjectivity proved DIRECTLY via right-exactness `range_Col_eq_ker_chiMoment` + odd-moment
  vanishing on the plus part (the `ℤ_p(1)^⟨c⟩=0` step internalised), NOT via the deferred
  `col_image_cycloTower1_eq_zetaIdeal` (T1225) — that identity is OFF this path. | **File**:
  IwasawaProof/Main.lean | **Depends on**: T1225,T1226,
  range_Col_eq_ker_chiMoment (banked) | **Type**: theorem (MILESTONE-closing)
#### Statement
```lean
-- the sorry at Main:786 inside colDescentPlusMul_bijective
theorem colDescentPlusMul_surjective (hp2 : p ≠ 2) :
    Function.Surjective (colDescentPlusMul p hp2) := by sorry
```
#### Proof sketch (RJW thm:iwasawa 2: SES (i) ⟹ iso (ii) by ⟨c⟩-invariants)
With `col_image_cycloTower1_eq_zetaIdeal` (T1225 closes it), the SES (i)
`0→𝒰_{∞,1}/𝒞_{∞,1}→Λ(𝒢)/I(𝒢)ζ_p→ℤ_p(1)→0` holds (`range_Col_eq_ker_chiMoment` for the cokernel
ℤ_p(1)-image). Take ⟨c⟩-invariants: p odd ⟹ exact; `ℤ_p(1)^⟨c⟩=0` (T1226) kills the cokernel ⟹
`𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p` ⟹ `colDescentPlusMul` onto. Then `colDescentPlusMul_bijective`
is sorry-free ⟹ `iwasawa_theorem` + `iwasawa_exact_sequence` close.
- **Banked**: `range_Col_eq_ker_chiMoment` (FundSeq:1162), `mem_ker_Col_iff_mem_ZpOne`, the plus
  infrastructure (`projPlus`/`plusSection`/`zetaIdealPlus`/`Col_mem_plusPart_of_mem_unitsTower1Plus`).

### [CLEANUP-132] /cleanup the assembly (T1225–T1227) + Main.lean
- **Status**: open | **Depends on**: T1227 | **Type**: cleanup

### [CLEANUP-ALL-6] /cleanup-all before the milestone confirm
- **Status**: open | **Depends on**: T1227 | **Type**: cleanup-all

### [T1228] MILESTONE confirm + blueprint wiring (folds T1207)
- **Status**: open | **Depends on**: T1227, CLEANUP-ALL-6 | **Type**: milestone
#### Work
`#print axioms iwasawa_theorem iwasawa_exact_sequence` = {propext,Classical.choice,Quot.sound} (NO
sorryAx); `lake build PadicLFunctions` green. Then T1207 wiring: `iwproof-iwasawa-final` →
`.iwasawa_theorem, .iwasawa_exact_sequence`; `iwasawa-zeros-theorem` (IwasawaZeros:224) →
`.iwasawa_theorem`; re-assess the generator nodes (`iwproof-cyc-gen`/`-local-gen`/`-global-gen-2`) now
realisable (T1222/T1223/T1224). `lake build PadicLFunctionsBlueprint` + `./scripts/ci-pages.sh`. Mark
T1206/T1206c/T1207 DONE.

### [CLEANUP-124] /cleanup Main.lean
- **Status**: open | **Depends on**: T1206.

### [T1207] Blueprint: wire IwasawaProof + the §11 thm:iwasawa node
- **Status**: **PARTIAL** (2026-06-14, orchestrator). 11 §12 nodes wired+VERIFIED (`lake build
  PadicLFunctionsBlueprint` green, 4137 jobs): `iwproof-mu-killed`→`Col_eq_zero_of_torsion`,
  `iwproof-ker-dlog`→`dlog_eq_zero_normOp_fixed`, `iwproof-galois-equiv`→`Col_galNCU`,
  `coleman-equivariance`→`Col_lambdaG_equivariant`, `iwproof-log-der`→`dlog`, `iwproof-log-der-seq`
  →`dlog_surjective_onto_psiId`+`dlog_mem_psiIdSeries`+`dlog_eq_zero_normOp_fixed`,
  `iwproof-log-der-image`→`dlog_mem_psiIdSeries`, `iwproof-W-modp`→`exists_normOp_fixed_lift`,
  `iwproof-B-modp-decomp`→`fp_series_eq_dlog_add_frobC`, `iwproof-zp-one`→`ZpOne`,
  `fundamental-exact-sequence`→`mem_ker_Col_iff_mem_ZpOne`+`range_Col_eq_ker_chiMoment`.
  REMAINING (blocked on T1206 full closure, rule-2 "no partial-realisation wiring"):
  `iwproof-iwasawa-final`→`iwasawa_theorem`+`iwasawa_exact_sequence` (IwasawaProof.lean:432) +
  IwasawaZeros.lean:224 `iwasawa-zeros-theorem`→`iwasawa_theorem` — wire once the milestone's 2
  deferred sorrys (T1206a/T1206b) close. Generator nodes (`iwproof-cyc-gen`/`-cyclic`/`global-gen-2`/
  `-closure`/`-local-gen`) skipped: partial/stub matches. ci-pages.sh re-render pending final wiring.
  PER-NODE FAITHFULNESS AUDIT (orchestrator 2026-06-14, while a7cc206 closes col_image — confirms
  rule-2 "no partial-realisation wiring" for each, so all stay UNWIRED until milestone lands):
  • `iwproof-cyc-gen` (two-part: (i) 𝒟ₙ⁺ gen by −1+{γₙₐ}, (ii) 𝒟ₙ=⟨ξ,𝒟ₙ⁺⟩) — `cycloUnitsPlus_eq_closure_gammas`
    (Generators.lean:803) realises ONLY part (i) (𝒟ₙ⁺=closure({γ_b:¬p∣b}∪{−1})); part (ii) absent. PARTIAL.
  • `iwproof-closure` (r-generator: closure⟨g₁..g_r⟩ = ℤ_p-span) — `closure_zspan_eq_zpspan` (897) realises ONLY
    the r=1 cyclic case (closure⟨g⟩=zpPow g '' ℤ_p). PARTIAL (r=1 is all the local cyclic route needs, node states general r).
  • `iwproof-local-gen` (𝒞ₙ,₁⁺ cyclic ℤ_p[𝒢ₙ⁺], 𝒞_∞,₁⁺ cyclic Λ(𝒢⁺)) — `cycloTower1Plus_cyclic_generator` (1000)
    has a vacuous `∃ _μ, True` tail; genuine content = γ≡a congruence only. NOT the cyclic-module claim. STUB.
  • `iwproof-global-gen-2` (wγₙₐ≡a mod πₙ; (wγ)^{p−1}=γ^{p−1} gen (p−1)𝒟ₙ⁺) — the γ≡a congruence is
    `gammaUnit_congr_natCast`(971)/`cycloTower1Plus_cyclic_generator`(1000); the (p−1)𝒟ₙ⁺-generation half absent. PARTIAL.
  • `iwproof-cyc-gen-cyclic` (γₙₐ gen 𝒟ₙ⁺ as ℤ[𝒢ₙ⁺]-mod for a cyclic) — no single faithful decl; the
    σ_a-translate telescoping lives inside the col_image route, not a standalone lemma. UNREALISED standalone.
  `gammaUnit_mem_cycloUnitsPlus`(219) is a membership fact (γₙₐ∈𝒟ₙ⁺), matches the node PREAMBLE def not a node.
  POST-MILESTONE: per node, either wire to a then-existing full realisation OR adjust node prose to the Lean's
  actual (e.g. r=1 closure) while staying source-faithful — decide per node; do NOT batch-wire.
  JOIN WIRING REFS (verified on-disk 2026-06-14, namespace `PadicLFunctions.Coleman`, Main.lean:571/583):
  `iwproof-iwasawa-final` (IwasawaProof.lean:432; part (i) SES→`iwasawa_exact_sequence`, part (ii) iso→`iwasawa_theorem`)
    ⇒ `(lean := "PadicLFunctions.Coleman.iwasawa_theorem, PadicLFunctions.Coleman.iwasawa_exact_sequence")`;
  `iwasawa-zeros-theorem` (IwasawaZeros.lean:224) ⇒ `(lean := "PadicLFunctions.Coleman.iwasawa_theorem")`.
  Milestone proof-body sorries to confirm closed before wiring: `col_image_cycloTower1_eq_zetaIdeal` (Main:228),
  surjectivity inside `colDescentPlusMul_bijective` (Main:564, used by `iwasawa_theorem` at Main:571).
  EXACT EDITS (both nodes are four-colon `::::theorem`, no lean ref yet — verified on-disk 2026-06-14):
   • IwasawaProof.lean:432  `::::theorem "iwproof-iwasawa-final"`  →
     `::::theorem "iwproof-iwasawa-final" (lean := "PadicLFunctions.Coleman.iwasawa_theorem, PadicLFunctions.Coleman.iwasawa_exact_sequence")`
   • IwasawaZeros.lean:224  `::::theorem "iwasawa-zeros-theorem"`  →
     `::::theorem "iwasawa-zeros-theorem" (lean := "PadicLFunctions.Coleman.iwasawa_theorem")`
  Then `lake build PadicLFunctionsBlueprint` (verifies refs resolve) → ci-pages.sh.
  | **Depends on**: all §12 proof tickets
- **File**: PadicLFunctionsBlueprint/Chapters/IwasawaProof.lean (+ IwasawaZeros.lean's
  `iwasawa-zeros-theorem` node, currently prose)
#### Work
Wire the §12 nodes (equivariance, thm:log der, fund exact seq, generators) to the
IwasawaProof decls; **wire IwasawaZeros.lean's `iwasawa-zeros-theorem` node** (the
§11 prose placeholder) to `iwasawa_theorem` now that it's proven. `lake build
PadicLFunctionsBlueprint` green; re-render via ci-pages.sh.

## §12 dispatch notes
- Verification bar per ticket: `lake build` green, zero sorry in the ticket's decls,
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}; record in Progress.
- Parallel lanes at start: (A) T1201→T1202→CL-121 ; (B) T1203 (independent of Galois)
  →CL-122 ; (C, after T1201) T1205. Then T1204 (needs T1202+T1203) ; CL-123 ;
  CLEANUP-ALL-7 ; T1206 (needs T1204+T1205) ; CL-124 ; T1207.
- Two RISK FLAGS carried from /develop: (1) E12.1's `isCyclotomicExtension_K`-public +
  tower-compat + levelNorm-conjugation-invariance — if (4) resists, Tier-A spawn; (2)
  E12.2's lem:B mod p 2 is the EXPECTED Tier-A spawn (the 𝔽_p⟦T⟧ induction) + the
  §10-deferred series-Eqphipsi (step 3) + normOp continuity (ii)/(iv) (step 4) come due.
- The §11 b2-logged a≡1-mod-p note resolves in T1205 (the Teichmüller w); thm:iwasawa 2
  (T1206) uses `coleman_to_kl` at the generator a — no a≡1 restriction needed there
  (the ([σ_a]−1)ζ_p image is over ALL a ∈ ℤ_p^×).
- NO leaf needs the deferred Λ-module structure theorem (that is §13/IMC).

### [T1203a] lem:log der 1 — Δ(𝒲) ⊆ ℤ_p⟦T⟧^{ψ=id} via the Jacobi det-formula
- **Status**: **done** (2026-06-14, agent a808a4). `dlog_mem_psiIdSeries` sorry-free; `#print axioms` = {propext, Classical.choice, Quot.sound}. Closed via the ξ-free Jacobi/trace route (sidesteps the deferred series-Eqphipsi μ_p-product that the plan flagged for this leaf): identity K `digitMatrix_del` `(digitMatrix Δf)_{ij}=(i−j)M_{ij}+pΔ(M_{ij})` + `trace_digitMatrix h = pψ(h)` + Jacobi `del_det_eq_smul_trace` + `adjugate M = f•M⁻¹`, giving `pψ(dlog f)=p·dlog f`, cancel p. Reusable helpers banked: `derivation_det` (Jacobi's formula, absent from mathlib), full Δ-Leibniz API, and the `dlog_mul`/`dlog_one`/`dlog_inverse`/`dlog_pow` homomorphism layer. | **File**: IwasawaProof/LogDerivative.lean | **Parent**: T1203
- **Depends on**: T1203 (the 12 filled leaves + 16 helpers) | **Type**: lemma
#### Statement
`dlog_mem_psiIdSeries {f : PowerSeries ℤ_[p]} (hf : IsUnit f) (hN : normOp f = f) :
dlog p f ∈ psiIdSeries p` (LogDerivative.lean:102).
#### Proof sketch
RJW's μ_p-product route `φ(f) = ∏_{η∈μ_p} f((1+T)η−1)` is NOT a formal power-series
identity (substrate replan R10.4 — the substitution has non-nilpotent constant term).
The FORMAL substitute (the T1203 agent's characterisation): `normOp f = det (digitMatrix f)`
(`normOp_eq_det`, NormOperator.lean), so `Δ(normOp f) = Δ(det M) = tr(adjugate(M)·ΔM)/det`
— Jacobi's log-derivative-of-determinant formula. Steps:
1. Jacobi: for `M : Matrix (Fin p) (Fin p) (PowerSeries ℤ_[p])` with `IsUnit (det M)`,
   `Δ(det M) = det M · tr(M⁻¹ · M.map Δ)` (= `tr(adjugate M · M.map Δ)` since
   `M⁻¹ = (det M)⁻¹ • adjugate M`). Build from `Matrix.det` Leibniz expansion +
   `derivativeFun` product rule, OR find `Matrix.derivative_det`-style in mathlib
   (search `Matrix.det` derivative; likely ABSENT → this is the ~100-line sub-development).
2. `dlog f = Δ f / f`; with `f = normOp f = det M`, `dlog f = Δ(det M)/det M =
   tr(M⁻¹ · ΔM)`.
3. Link `tr = p·ψ`: `trace_digitMatrix : tr (digitMatrix h) = p · ψ(h)` (NormOperator,
   RJW TeX 2670) — generalise to `tr(M⁻¹·ΔM)` form to show `ψ(dlog f) = dlog f`.
   Concretely `(φ∘Δ)(f) = (φ∘ψ)(Δf)` ⟹ `ψ(Δf) = Δf` by `phiHom` injectivity (the
   T1203 agent has `del_phiHom`).
- **Mathlib lemmas**: `Matrix.det`, `Matrix.trace`, `Matrix.adjugate`,
  `Matrix.mul_adjugate`, `Ring.inverse`; `PowerSeries.derivativeFun` product rule.
  Project: `normOp_eq_det`, `digitMatrix`, `trace_digitMatrix`, `del_phiHom`,
  `phiHom` injective.
- **Sources**: RJW lem:log der 1 (TeX 3292–3306), the Jacobi-formula realisation.
- **Sizing**: ~120–150 LOC (the Jacobi det-derivative is the bulk; may spawn a
  `Matrix.derivative_det` sub-lemma).

### [T1203b] lem:B mod p 2 — the 𝔽_p⟦T⟧ construction ("most delicate and technical part")
- **Status**: **done** (2026-06-14, agent a8234d). `fp_series_eq_dlog_add_frobC` sorry-free; clean build (`lake build PadicLFunctions.IwasawaProof.LogDerivative` ✓, only line-834 T1203c sorry remains); `#print axioms` = {propext, Classical.choice, Quot.sound}. Closed via a NOVEL topology-free route (avoided the planned infinite-product/multipliability): a direct coefficient recursion `AWfp` with `n·aₙ = wₙ + Σ_{j<n} a_{n−j}wⱼ` (the `T·a′ = a·w` identity), `c := H − w` supported on `pℕ` ⟹ ∈ range φ (`phiSeries = expand` over 𝔽_p). 13 private helpers banked. | **File**: IwasawaProof/LogDerivative.lean | **Parent**: T1203
- **Depends on**: T1203 | **Type**: lemma (the section's hardest leaf)
#### Statement (RESTATE to the faithful source form — statement-fix authorised, docstring note)
Faithful: `𝔽_p⟦T⟧ = Δ(𝔽_p⟦T⟧^×) + (T+1)/T · C` where `C = {Σ_{n≥1} a_n T^{pn}}`. The
skeleton's `fp_series_eq_dlog_add_frobC` (LogDerivative.lean:238) is a vacuous
placeholder — replace with: `∀ g : PowerSeries (ZMod p), ∃ (u : PowerSeries (ZMod p))
(c ∈ ((T+1)/T)·C-submodule), IsUnit u ∧ g = dlogFp u + c` (define the `Δ` over `ZMod p`
and the `C`-submodule explicitly).
#### Proof sketch (RJW TeX 3366–3373)
1. Define `Δ_{𝔽_p}` (= `(1+T)·D·inverse`) over `ZMod p` and the submodule `(T+1)/T·C`.
2. Write `(T/(T+1))·g = Σ a_n T^n`; set `h = Σ_{(m,p)=1} a_m Σ_{k≥0} T^{m p^k}`.
3. Inductively choose `α_i ∈ 𝔽_p` so `h_m := (T+1)/T·h − Σ_{i<m} Δ(1−α_iT^i) ∈ T^{m−1}𝔽_p⟦T⟧`,
   using `Δ(1−α_iT^i) = −(T+1)/T Σ_k i α_i^k T^{ik}`, the invariant `d_n = d_{np}`, and
   `α_m = −d_m/m` (m prime to p ⟹ invertible in 𝔽_p).
4. `g_∞ = ∏_{n≥1}(1−α_nT^n)` converges in `𝔽_p⟦T⟧` (the `(1−α_nT^n)` factors → 1 in the
   T-adic topology); `Δ(g_∞) = (T+1)/T·h`; `(T/(T+1))·g − h ∈ C` closes it.
- **Mathlib lemmas**: `PowerSeries` T-adic completeness over `ZMod p`; `Finset.prod`
  convergence; `ZMod p` field inverse. Likely several `coeff`-level sub-lemmas
  (the `d_n=d_{np}` invariant, the `∏` convergence) → spawn as needed.
- **Sources**: RJW lem:B mod p 2 (TeX 3359–3373), the delicate induction.
- **Sizing**: ~200–250 LOC; the deepest leaf. Spawn sub-lemmas freely (the α-induction,
  the d_n=d_{np} invariant, the ∏-convergence).

### [T1203c] thm:log der — surjectivity of Δ onto ℤ_p⟦T⟧^{ψ=id}
- **Status**: **done** (2026-06-14, agent abd388). `dlog_surjective_onto_psiId` (the Coleman–Coates–Wiles theorem) sorry-free; clean `lake build` (no errors/warnings); `#print axioms` = {propext, Classical.choice, Quot.sound}. Closed ξ-free as planned: built honest `ψ` over `𝔽_p⟦T⟧` (digit-uniqueness via the `θ=(1+T)∂` eigenvalue + Lagrange argument — new substrate), the projection formula `ψ(φd·F)=d·ψF` over 𝔽_p replacing RJW's Eqphipsi-based "ψ fixes (T+1)/T" (the `b̄=0` step `psiId_one_add_X_div_X_phi_eq_zero` via a `PowerSeries.order` kill), then successive approximation `hₙ=∏gₖ^{(−1)^{k−1}pᵏ⁻¹}` + compact limit using `𝒩`-continuity (`= det∘digitMatrix`, homeomorphic digit-assembly) and the cleared form `(1+T)∂h=F·h` to pass `Δ` through the limit (avoiding inverse-continuity). ~40 private helpers. | **File**: IwasawaProof/LogDerivative.lean | **Parent**: T1203
- **Depends on**: T1203a (done), T1203b (done) | **Type**: theorem
- **ξ-free route note (2026-06-14, orchestrator)**: the T1203 agent flagged the `B ⊆ A`
  step's "ψ fixes `(T+1)/T`" as the deferred Eqphipsi. NOT a wall: RJW's `LemmaPsiInvariant`
  (ψμ_a=μ_a, the measure analog) is ALREADY proven ξ-free in the project (`psi_muA`,
  MuA.lean:460) via the ξ-free projection formula `psi_phi_mul` (Toolbox.lean:312 /
  MuA.lean:366). The missing ξ-free ingredient is the SERIES analog
  `psiSeries (phiSeries d * G) = d * psiSeries G` (the digit-shift projection formula —
  provable from the unique digit decomposition like its measure cousin; FormalPsi.lean has
  `psiSeries_phi`/`_C`/`_add`/`_C_mul`, NormOperator has `psiSeries_phi_padicInt`). Build that
  helper, then "ψ fixes `(T+1)/T`" / "ψ b = b" follows ξ-free, mirroring the T1203a Jacobi win.
  COMPILE-VERIFIED helper (orchestrator ran `lake env lean`, exit 0, 0 errors — paste verbatim
  into LogDerivative.lean, which already imports the NormOperator API; names resolve under
  `open PadicLFunctions PadicLFunctions.Coleman PowerSeries`):
  ```
  theorem psiSeries_phiSeries_mul (d F : PowerSeries ℤ_[p]) :
      psiSeries p (phiSeries p d * F) = d * psiSeries p F := by
    obtain ⟨GF, hGF, -⟩ := existsUnique_digits_padicInt p F
    rw [psiSeries_eq_of_isDigitDecomp_padicInt hGF]
    refine psiSeries_eq_of_isDigitDecomp_padicInt (G := fun i => d * GF i) ?_
    change phiSeries p d * F = ∑ i : Fin p, (1 + PowerSeries.X) ^ (i : ℕ)
        * phiSeries p (d * GF i)
    rw [hGF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phiSeries, phiSeries, phiSeries,
      PowerSeries.subst_mul (hasSubst_one_add_X_pow_sub_one p)]
    ring
  ```
  This `ψ(φd·F) = d·ψF` (digit-shift projection formula) is the ξ-free substitute for RJW's
  Eqphipsi-based "ψ fixes `(T+1)/T`"; "ψ b = b" for the `(T+1)/T·C` part follows from it.
  Second buildable input (passing Δ through the compactness limit): you likely do NOT need full
  Pi-topology continuity of `dlog`. The cleaner route mirrors the file's existing limit arguments:
  prove `dlog_modEq_of_modEq` (for units `f ≡ g mod p^{k+1} ⟹ dlog f ≡ dlog g mod p^{k+1}` —
  elementary, since `derivativeFun` and `Ring.inverse` on units both preserve mod-`p^{k}`
  congruence; parallels the existing `normOp_modEq_of_modEq`), then pass `Δ` through the
  convergent subsequence with the already-present `modEqPow_of_tendsto` + `eq_of_forall_modEqPow`
  Hausdorff helpers. This avoids a WithPiTopology rabbit hole. So T1206 stays reachable.
#### Statement
`dlog_surjective_onto_psiId {F : PowerSeries ℤ_[p]} (hF : F ∈ psiIdSeries p) :
∃ g, IsUnit g ∧ normOp g = g ∧ dlog p g = F` (LogDerivative.lean:244).
#### Proof sketch (RJW TeX 3308–3333 + 3375–3379)
1. lem:log der red mod p: A = B (reductions mod p) ⟹ surjective, via successive
   approximation: build `g_i ∈ 𝒲`, `f_i ∈ ℤ_p⟦T⟧^{ψ=id}` with `Δ(g_i) − f_{i−1} = p f_i`;
   `h_n = ∏_{k=1}^n g_k^{(−1)^{k−1} p^{k−1}} ∈ 𝒲`, `Δ(h_n) = f_0 + (−1)^{n−1} p^n f_n`;
   compactness limit `h ∈ 𝒲` with `Δ h = f_0` (the §10 ℤ_p⟦T⟧^× compactness + the
   T1203-agent's `modEqPow_of_tendsto`/`eq_of_forall_modEqPow` Hausdorff helpers).
2. A = B: `A = Δ(𝒲) mod p = Δ(𝔽_p⟦T⟧^×)` (lem:A mod p `exists_normOp_fixed_lift` +
   lem:log der 1 T1203a) and `B = ℤ_p⟦T⟧^{ψ=id} mod p = Δ(𝔽_p⟦T⟧^×)` (lem:B mod p,
   from T1203b + the ψ-action calc TeX 3352–3356). So A = B.
- **Mathlib/project**: §10 compactness (CompactSpace/SeqCompactSpace ℤ_p⟦T⟧^×),
  T1203a, T1203b, the T1203-agent helpers (`normOp_modEq_of_modEq`, `solCoeff`,
  `modEqPow_of_tendsto`, `eq_of_forall_modEqPow`).
- **Sources**: RJW lem:log der red mod p + lem:B mod p + thm:log der proof.
- **Sizing**: ~150 LOC (the successive-approximation + the A=B assembly).

### [T1201b] Col_galNCU — measure-side σ_a-equivariance of the Coleman map
- **Status**: **done** (2026-06-14, agent ad3ada). 6 in-file private helpers (succ_mul_ringChoose, coeff_binomialSeries', one_add_X_mul_derivative_binomialSeries, subst_inverse_of_isUnit, dlog_galSeries, mahlerSymm_galSeries) + unitsMulLeftCM-pushforward assembly; axiom-clean; statement unchanged. GaloisAction.lean sorry-free. | **File**: IwasawaProof/GaloisAction.lean | **Parent**: T1201
- **Depends on**: T1201 (8/9 done — galAut/galNCU/galSeries/colemanSeries_galNCU + ~25 helpers) | **Type**: theorem
#### Statement (finalized by T1201, authorised statement-fix)
`Col_galNCU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : Col p (galNCU p a u)
= PadicMeasure.pushforward p (unitsMulLeftCM p a) (Col p u)` where
`unitsMulLeftCM a = ⟨fun v => a * v, _⟩ : C(ℤ_[p]ˣ, ℤ_[p]ˣ)` (define it). The last
remaining sorry in GaloisAction.lean (line ~842).
#### Proof sketch (T1201 agent's hand-off; source TeX 3217–3234)
Unfold `Col u = unitsCmul (invCM) ((𝒜⁻¹(dlog (colemanSeries u))).comp extendByZero)`.
1. `colemanSeries_galNCU` (DONE) gives `colemanSeries (galNCU a u) = galSeries a (colemanSeries u)`.
2. dlog chain rule: `∂log(σ_a f) = a · galSeries a (∂log f)` — via `PowerSeries.derivative_subst`
   + `(1+T)·(binomialSeries a)' = a · binomialSeries a` (the `del`-of-binomial identity).
3. `𝒜⁻¹ ∘ galSeries a = PadicMeasure.sigma a ∘ 𝒜⁻¹` — this IS the existing
   `PadicMeasure.mahlerTransform_sigma` (Measure/Toolbox.lean:262), since
   `galSeries = subst (binomialSeries a − 1)`.
4. The units-side `x⁻¹` (`invCM`) absorbs the `a` factor: `∂⁻¹∘σ_a = a⁻¹ σ_a∘∂⁻¹`
   (TeX 3223) — the §4 zetaNum `x⁻¹`-renormalisation; restriction-to-ℤ_[p]ˣ is
   equivariant under the pushforward `unitsMulLeftCM a`.
- **Mathlib/project**: `PadicMeasure.mahlerTransform_sigma` (Toolbox.lean:262 — the key
  bridge, already present), `PadicMeasure.sigma`, `PadicMeasure.pushforward`,
  `PowerSeries.derivative_subst`, `colemanSeries_galNCU` + the §4 `invCM`/`unitsCmul` API.
- **Sources**: RJW §12.1 Prop (TeX 3217–3234).
- **Sizing**: ~80–120 LOC (~4–5 measure-side lemmas; the key bridge exists).

- **MILESTONE COMPLETE 2026-06-16 — §12.4–12.5 (RJW thm:iwasawa 2) sorry-free + axiom-clean**:
  all 4 cores done & pushed — T1222 `cycloClosureOnePlus_le_closure_wGammaTranslate` + H1
  `galNCU_neg_one_mem_cycloTower1` (@ad5a631), surjectivity `colDescentPlusMul_bijective`
  (@a16c95c, right-exactness route), T1224' `mem_ZpOne_of_mem_cycloTower1_cAnti` (@579bb00,
  antisymmetrisation A(w)=w·σ(w)⁻¹ into ⟨−ξ⟩ + zpPow sqrt + levelNorm assembly). `#print axioms`
  on `iwasawa_theorem`, `iwasawa_exact_sequence` (+ all 4 cores) = {propext, Classical.choice,
  Quot.sound}. `lake build PadicLFunctions.IwasawaProof.Main` green (3734 jobs), zero sorry.
  DEFERRED (paused at user request 2026-06-16 to change approach — NOT yet done): T1228 blueprint
  wiring (iwproof-iwasawa-final, iwasawa-zeros-theorem → the 2 milestone decls; build
  PadicLFunctionsBlueprint + ci-pages), full ticket done-markings (T1206/T1206c/T1207/T1220-T1228),
  CLEANUP-124/131. NOTE: T1224' was proved by a worktree agent in degraded (no-lean-lsp) main
  session; a tooled /cleanup pass on the new Generators bridge + Main assembly is advisable.

- **WRAP-UP 2026-06-16 (resumed)**: T1228 blueprint wiring DONE — `iwproof-iwasawa-final` →
  (iwasawa_theorem, iwasawa_exact_sequence), `iwasawa-zeros-theorem` → iwasawa_theorem;
  `lake build PadicLFunctionsBlueprint` green (4154 jobs), refs resolve, milestone nodes render
  green. T1206/T1206c/T1207/T1220-T1228 are all effectively DONE (covered by the MILESTONE COMPLETE
  record above). Remaining §12 follow-ups: ci-pages re-render (when convenient) + a tooled /cleanup
  of the T1224' Generators bridge + Main assembly (written degraded). Next: /develop §13 (IMC).

## §13 board — Iwasawa Main Conjecture (full, unconditional) — created 2026-06-16 (/develop, AINTLIB monorepo)

**AINTLIB note**: this is the dev/padic PRODUCER board. NO CLEANUP/CLEANUP-ALL tickets here — golf/
dedup/style/sorry-discharge is the central fleet's job on `main` (handed off via a dev→main PR when a
cluster lands). `sorry`-as-WIP is allowed. Reuse-don't-duplicate: each ticket names the monorepo/mathlib
decls to import. **Staging**: S → G → E → M; Thm IMC is STATED after S+G (S13-STMT), proof filled across
E+M. G/E/M are cluster milestones — decompose-when-reached via a follow-on /develop pass.

### New files (projects/PadicLFunctions/PadicLFunctions/)
- `Iwasawa/StructureTheory/{IwasawaAlgebra,PseudoIso,StructureTheorem,CharIdeal,Isotypic}.lean` (Stage S;
  candidate to lift into AINTLIB `Common/` later — flag at dev→main PR)
- `IwasawaProof/GaloisModules.lean` (Stage G), `IwasawaProof/MainConjecture.lean` (statement + Stage M)

### Stage S — Λ-module structure theory + characteristic ideals (§13.1, Washington Ch.13)

#### [S13-S1] Iwasawa algebra Λ = 𝒪_L⟦T⟧ + distinguished-polynomial API
- **Status**: open | **File**: Iwasawa/StructureTheory/IwasawaAlgebra.lean | **Depends on**: — | **Type**: def+API
- **Reuse**: mathlib `RingTheory/PowerSeries/*`, `Polynomial/Eisenstein/Distinguished`, `PowerSeries/WeierstrassPreparation`.
- Define `Λ := 𝒪_L⟦T⟧` (PowerSeries over 𝒪_L); distinguished-polynomial predicate (RJW 3644: monic, lower
  coeffs in 𝔭) + Weierstrass-preparation wrapper (`f = unit · distinguished`). **Source**: Washington §13.1; RJW 3631–3644.

#### [S13-S2] pseudo-isomorphism `M ~ M'`
- **Status**: open | **File**: Iwasawa/StructureTheory/PseudoIso.lean | **Depends on**: S13-S1 | **Type**: def+API
- `M ~ M' := ∃ (0→A→M→M'→B→0) with A,B finite`; show it's an equivalence relation on f.g. torsion Λ-modules
  (Washington §13.2 Warning — NOT general). **Source**: RJW 3631–3635.

#### [S13-S3] STRUCTURE THEOREM (Washington Thm 13.12) — CLUSTER, decompose at execution
- **Status**: open | **File**: Iwasawa/StructureTheory/StructureTheorem.lean | **Depends on**: S13-S1,S2 | **Type**: theorem (HARD core)
- f.g. Λ-module `M ~ Λ^r ⊕ ⊕ᵢ Λ/(pⁿⁱ) ⊕ ⊕ⱼ Λ/(fⱼ^{mⱼ})`, fⱼ distinguished irreducible. Build on mathlib
  `Algebra/Module/PID` (template) + Weierstrass (S1): Λ is a 2-dim regular local UFD; sub-leaves at execution
  (prime factorisation in Λ, the finite-kernel/cokernel reduction, the elementary-divisor analogue). **Source**: Washington Thm 13.12.

#### [S13-S4] characteristic ideal + multiplicativity
- **Status**: open | **File**: Iwasawa/StructureTheory/CharIdeal.lean | **Depends on**: S13-S3 | **Type**: def+theorem
- `Ch_Λ(M) := (pⁿ)∏ⱼ(fⱼ^{mⱼ})` for f.g. torsion M (n=Σnᵢ); MULTIPLICATIVITY in exact sequences (CS06 A.1 Prop 1).
  **Source**: RJW 3652–3657, 3679–3681.

#### [S13-S5] equivariant isotypic decomposition + `Ch_{Λ(𝒢)}`
- **Status**: open | **File**: Iwasawa/StructureTheory/Isotypic.lean | **Depends on**: S13-S4 | **Type**: def+theorem
- `Λ(𝒢) ≅ 𝒪_L[H]⊗Λ` (H=μ_{p-1} prime-to-p); projectors `e_ω=|H|⁻¹Σω⁻¹(a)[a]`; `M=⊕_ω M^(ω)` each f.g. torsion Λ;
  `Ch_{Λ(𝒢)}(M):=⊕_ω Ch_Λ(M^(ω))`. **Reuse**: mathlib `RepresentationTheory` group-algebra idempotents. **Source**: RJW 3659–3676 (CS06 A.1).

### Statement
#### [S13-STMT] state Thm IMC + define `𝒳⁺_∞` (after S + G)
- **Status**: blocked (needs S13-S5 + S13-G) | **File**: IwasawaProof/MainConjecture.lean | **Type**: theorem statement (sorry proof)
- `theorem iwasawa_main_conjecture : (𝒳⁺_∞ f.g. torsion Λ(𝒢⁺)) ∧ Ch_{Λ(𝒢⁺)}(𝒳⁺_∞) = I(𝒢⁺)ζ_p := by sorry`.
  Wire blueprint node in `MainConjecture.lean` chapter once sorry-free-on-the-statement. **Source**: RJW Thm IMC 3740.

### Cluster milestones (decompose-when-reached — own /develop sub-pass each)
#### [S13-G] Stage G — Galois Λ-modules + class field theory (§13.2) | Depends on: S13-S5
- Define 𝓜⁺/𝓛⁺, 𝒳⁺_∞/𝒴⁺_∞ + Λ(𝒢)-action; G1 `𝒴⁺_n≅Cl(F⁺_n)_p` (REUSE FltRegular Unramified/Hilbert94, mathlib ClassGroup);
  G2 CFT seq (Washington Cor 13.6 — ramified CFT, hardest; via Chebotarev infra or axiomatise); G3 coinvariants
  (Washington 13.22, mathlib Coinvariants); G4 Cor CFTunits2.

#### [S13-E] Stage E — Euler system / Thaine (Washington Ch.15 / Rubin) | Depends on: S13-G
- E1 Thaine annihilation (REUSE FRB Thaine/{AnnihilatorDescent,SingleCharacter}); E2 Euler-system→char-ideal
  divisibility `Ch(𝒳⁺_∞) | I(𝒢⁺)ζ_p` (deepest new build); E3 pin to 𝒳⁺_∞.

#### [S13-M] Stage M — assembly | Depends on: S13-E, §12 (done)
- M1 analytic class-number-formula / cyclotomic-unit index = class number (reverse divisibility; REUSE FRB + our §11);
  M2 combine E+M1+S4-multiplicativity → `Ch(𝒳⁺_∞)=I(𝒢⁺)ζ_p`, wire §12; M3 f.g.-torsion-ness. Closes S13-STMT + the milestone.
