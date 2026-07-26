# Ticket Board — Campaign 5: the adic Fargues–Fontaine curve (definition layer)

**Status: ACTIVE (approved 2026-07-24).** Campaign-4 board archived as
`tickets-fjp-archived-2026-07-24.md`.

**Contract**: every statement already exists as a `:= by sorry` declaration in the
skeleton under `Adic spaces/FarguesFontaine/` (build-verified; see decomposition §0.5).
A ticket = *fill the named sorries*; statements are NOT to be changed (B2-stop if a
statement is wrong — report, don't bend). Each ticket cites its decomposition leaves
(`decomposition.md`, e.g. L4.6), which carry the verbatim source
quotes, discharge plans, and attack logs. Sources local under `refs/AdicSpaces/`.

## CAMPAIGN 8 STATUS (beastmode session, 2026-07-26)

**Kedlaya §2 and §3 are COMPLETE and axiom-clean; §4 is well under way.** All nine
`FarguesFontaine/` files are sorry-free (10 777 lines); the full library builds green
(3318 jobs); everything is pushed to `origin/dev/adic-spaces`.

| Ticket | Content | State |
|---|---|---|
| Lane A | `Y_nonempty` (Gauss point at ρ = 1/2) | done |
| T901 | `Bloc`, `wLoc` and its evaluations | done |
| T902 | W(F) value engine (`gaussValueF`, ε-δ coordinates) | done-as-scoped |
| T903 | `A^r` as a valued completion; the c₀-architecture; **coordinate realization** and the value formula (Kedlaya (2.2.1)); `wAr`; attainment | done |
| T904 | Witt homogeneity (2.8.1); `degAr`; **Lemma 2.6** (`degAr_mul`); **Remark 2.7**; **Lemma 2.8**; **Prop 2.9**; **Cor 2.10** — `A^r` is a PID | done |
| T905 | Gröbner data: leading index/coefficient (Def 3.6), `dIdx` (Def 3.7), the finite Gröbner set (Dickson), the chosen generators | done |
| T906 | **Lemma 3.8** (approximate ideal generation) with the Colex well-founded descent | done |
| T907 | **Lemma 3.9** and **Theorem 3.2** — `A^r` is strongly noetherian | done |
| T908 | `B^I` (Def 4.2): construction, norm, completeness, series, density, injectivity, **Lemma 4.4 (three circles)**, **Cor 4.5**, `B^{I,+}` | (a)+(b) done, (c) open |
| T909 | restriction maps + **Cor 4.6 injectivity** (`resIHom_injective`, RestrictionInjective.lean) | **done** |
| T910–T912 | Lemma 4.9 presentations; Theorem 4.10 | T911+T912 **done** (AD-9 case-3: surjective_evalArMvHom, isStronglyNoetherian_BISub); T910 cases 1–2 open (off critical path per AD-9) |
| TC1–TC2 | **`B^I` is sheafy** (SheafyBI.lean: affinoid instances + Wedhorn 8.28(b)); AD-9 data satisfiable (`isSheafy_BISub_AD9`) | **done** |

**SESSION 2026-07-26 (second worker)**: commits da830e1a9 (T911 strictness), 8157ce661
(T912), c3c247755 (T909 Cor 4.6), 0588da1e3 (TC1+TC2 sheafy), 7d3a58533 (AD-9
satisfiability). The campaign's headline chain — Gauss norms → B^I → strongly
noetherian → **sheafy** — is wired end-to-end for the AD-9 intervals, axiom-clean,
no heartbeat raises. NEXT (PLAN-GATE-2 core): the chart-identification theorems
`𝒪(U₀) ≅ B^{[τ,cτ]}` (windows as rational subsets of `(A_inf, A_inf)` +
presheafValue comparison), then Y-locality (Wedhorn Rem 8.27), then Lane D.

**T908 closed 2026-07-26**: `B^I` is a **Tate ring**. `BIPlusIn` (= `B^{I,+}` as a subring
of `B^I`) is open; `pIdeal = (p)` is f.g.; `mem_pIdeal_pow_iff` shows `y ∈ (p)ⁿ ⇔ v(y₁) ≤
ρ₁ⁿ ∧ v(y₂) ≤ ρ₂ⁿ`, so `isAdic_pIdeal` identifies the subspace topology on `B^{I,+}` with
the `p`-adic one; hence `BIPairOfDefinition`, `isHuberRing_BISub`, `isTateRing_BISub`.

**HANDOVER 2026-07-26**: a new worker is taking over. Read
`.mathlib-quality/handover-2026-07-26-campaign8.md` first — it has the state of the
mathematics, the next task (T911 strictness) worked out, the binding working rules
(PERF-1 in particular), the file map and the API inventory.

#### PERF-1 (2026-07-26) — **no heartbeat raises** (owner instruction)

`set_option maxHeartbeats` / `synthInstance.maxHeartbeats` are not to be added; a timeout is
fixed by breaking the proof up and passing implicit arguments explicitly. All 49 raises in
`IntervalRing.lean` and `Presentation.lean` have been removed (see the two cleanup commits).
The recurring causes, and their fixes, in this codebase:

* generic `map_add`/`map_sum`/`map_mul` on a hom into a nested subring → state the identity
  explicitly (`ArToBI_add`, `evalArHom_sum`, …) and prove it from the `RingHom` fields, or at
  the ambient product level and transport with `Subtype.ext`;
* `f ^ n` where the result type is a metavariable → ascribe it
  (`(pIdeal … ^ n : Ideal ↥(BIPlusIn …))`);
* `Subring.comap` in a definition → give the carrier explicitly (`BIPlusIn`), so membership
  does not unfold through the comap;
* anonymous constructors `⟨…, proof⟩` inside goals → name the bundled element (`sliceElt`);
* a goal whose *context* is expensive (every tactic step ≈ 1s, e.g. `IsAdic` over a
  subring-of-a-subring) → make the proof a one-step term over named lemmas.

**Remaining**: `Groebner.lean` still has 6 raises, on the largest proofs of the campaign
(`exists_groebner_family`, `groebner_reduce`, `approx_generation`, `exists_rps_series_limit`,
`ideal_eq_span_groebner`, `isNoetherianRing_restrictedMvPowerSeries`). Removing them is a real
decomposition pass — in that context even a 6-line wrapper is over budget, because destructuring
the 9-component Gröbner existential costs seconds — and is tracked as its own task.

#### AD-9 (2026-07-26) — **special intervals suffice; no general-radius Gröbner theory needed**

Read from the arXiv source (`refs/paper.tex`, Kedlaya §4 = "Some additional rings"):
Lemma `L:Robba localizations` (the board's "4.9") has three cases; the third is

    A^r_{L,E}{T}/(pT - [z̄ⁿ]) ≅ B^{I'''},   I''' = [-n⁻¹ log_c p, r],  c = |z̄| ∈ (0,1),

and its Tate algebra is at **radius 1** — exactly what our Theorem 3.2
(`isStronglyNoetherian_ArSub`) provides. Kedlaya's remark after `T:strongly noetherian
Robba2` warns that *general* radii ρ over `A^r` are needed to reach an **arbitrary**
interval (cases 1–2 cut the interval down and use `B^I{T/ρ}`). We avoid that entirely:
the left endpoints reachable by case 3 are `t₀ = τ/(n·m)` (taking `z̄ = w^m`), which are
**dense** in `(0,∞)`, and the fundamental domain `[t, p·t]` of the Frobenius may be split
at any interior point. So the curve's two charts can be chosen with **both** endpoints of
the special form, and every chart ring is a case-3 quotient of a radius-1 Tate algebra
over some `A^r`. Consequence: **no re-parametrisation of the §3 Gröbner development by a
radius is required** — Groebner.lean stands as proven.

- **T910** — the case-3 map: `A^r{T} → B^I`, `T ↦ [z̄ⁿ]/p`. Needs (a) the restriction
  `A^{ρ₂} → hatK ρ₁` for `ρ₁ ≤ ρ₂` and hence the ring map `A^{ρ₂} → B^I`, (b) `λ_I([z̄ⁿ]/p)
  ≤ 1` ⇔ the left-endpoint condition `ρᵢ ≥ |z̄|ⁿ`, (c) evaluation of restricted series at a
  power-bounded element of the complete ring `B^I`.
- **T910a** (spawned 2026-07-26) — **the universal property of restricted power series**:
  for a complete nonarchimedean ring `B` with a power-multiplicative norm, a continuous
  ring map `φ : A → B` and power-bounded `b₁,…,b_k ∈ B`, evaluation `A⟨T₁,…,T_k⟩ → B` is a
  ring homomorphism. The repo's `RestrictedPowerSeries.lean` has **no** evaluation API —
  this is new, reusable infrastructure (the hard part is multiplicativity: the Cauchy
  product of two coefficientwise-null families). Concretely here: `wI (ArToBI a · bⁿ) ≤
  v_{ρ₂}(a)` by `wI_ArToBI` + `wI_mul_le` + `wI_teichPowOverP_le_one`, so the partial sums
  are Cauchy and `exists_BI_series_limit` (already proven) provides the value.
**T911 progress (2026-07-26)** — the **density half is done**: `evalRange` (the image as a
subring of the product), `mem_evalRange_iff`, `BIProd_AlocToBloc_mem_evalRange` (constants),
`exists_evalAr_eq_pInv` (`1/p`, via the monomial `[ϖ]^{-jn}·T` — this is where the AD-9
choice `z̄ = ϖʲ` pays off), `BIProd_mem_evalRange` (hence all of `Bloc`, by splitting the
inverse of `p[ϖ]`), and `BISub_le_topologicalClosure_evalRange`. **What remains is exactly
the strictness half**: a norm-controlled lift (Kedlaya's `|z|_ρ ≤ c^{t₀-t} λ_{I'}(x)`),
which makes the image closed and hence — with density — everything.

**The strictness lift, worked out (2026-07-26).** It is *term-by-term*, and in the AD-9
special case (`z̄ = ϖʲ`, so `ρ₁ = |ϖ|^{jn}` exactly) it is clean:

* a Witt term `pᵐ[x̄]` with `m ≥ 0` lifts to itself (`T`-degree 0), and its Gauss norm on
  `A^r` is `w_{ρ₂}(pᵐ[x̄]) ≤ λ_I(x) `;
* a term with `m < 0` lifts to `[x̄]·[ϖ]^{-jn|m|}·T^{|m|}`, whose Gauss norm is
  `|x̄|·ρ₁^{-|m|} = w_{ρ₁}(pᵐ[x̄]) ≤ λ_I(x)`.

So each term lifts with **no norm loss** — this is exactly Kedlaya's estimate, with the
constant `1` because our left endpoint is on the nose. A *crude* lift (write `x = a/(p[ϖ])^k`
and use one `T^k`) does **not** work: its norm exceeds `λ_I(x)` by `(ρ₂/ρ₁)^k`.

For the dense layer this needs no new theory: for `x ∈ Bloc`, `x = a·(p[ϖ])^{-k}` with
`a ∈ A_inf`, and splitting `a = prefix_k(a) + tail` (coordinates below `k`, then the rest,
which is divisible by `pᵏ`) makes the lift a **polynomial** in `T` — the negative-`p`-power
terms are the finitely many `n < k`. Then closedness follows by successive approximation
(each round gains a factor `ε`), using `wI_evalAr_le` for continuity of `eval` and
coefficientwise completeness of `A^r` for the limit.

Note the dependency this *removes*: only `Bloc`-elements need lifting, so **T908(c)
(coordinates on all of `B^I`) is not required for T911** — the prefix/tail machinery on
`A_inf` suffices.

- **T911** — surjectivity + strictness of that map (Kedlaya's explicit lift: for `x =
  pⁿ[x̄ₙ]` take `j` minimal with `c^{-j}|x̄ₙ| ≥ 1` and `z = pⁿ[x̄ₙ z̄^{-j}]T^j`, giving
  `|z|_1 ≤ λ_I(x)`), then the same with `k` extra radius-1 variables.
- **T911b** (spawned 2026-07-26) — **the restricted-series functor preserves strict
  surjections**: if `π : A ↠ B` is a surjective continuous ring map admitting norm-bounded
  lifts, then `A⟨T₁,…,T_k⟩ → B⟨T₁,…,T_k⟩` is surjective (lift the coefficients with control,
  using Kedlaya's estimate `|z|_ρ ≤ c^{t₀-t} λ_{I'}(x)` from T911).
- **T912** — `IsStronglyNoetherian ↥(BISub …)`: quotient of the noetherian
  `A^r{T, T₁,…,T_k}` (T911 + T911b + Theorem 3.2).

**T910a progress (2026-07-26)** — the analytic core is **done** in `Presentation.lean`:
`wI_sum_le` (ultrametric finite-sum bound), `exists_eval_series` (a restricted series over
`A^r` evaluated at a power-bounded element of `B^I` converges — via `wI_ArToBI` and
`exists_BI_series_limit`), `biUnion_antidiagonal_eq`, `wI_partial_cauchy_diff` (the missing
index pairs of `P_N - C_N` all have `max i j ≥ N₀`, so the difference has norm `≤ ε·M`),
`tendsto_zero_of_wI_tendsto_zero`, `exists_bound_of_wI_tendsto_zero`, and
**`tendsto_cauchy_product`** (the partial sums of the Cauchy product converge to the product
of the limits = multiplicativity of evaluation). **T910a (univariate) is DONE**: `coeffSeq`
(+`_add`/`_mul`/`_one`/`_zero`), `tendsto_valued_coeffSeq`, `evalAr`, `evalAr_mem`,
`tendsto_evalAr`, `evalAr_add`, `evalAr_mul`, `evalAr_one` and the bundled
**`evalArHom : A^r⟨T⟩ →+* B^I`** — Kedlaya's case-3 presentation map exists as a ring
homomorphism (evaluation at *any* power-bounded element of `B^I`; for case 3 take
`teichPowOverPElt`, power-bounded by `wI_teichPowOverP_le_one`).

**Open architecture question AD-10** (for the next planning pass): T911/T912 need the
`k`-variable version `A^r⟨T,T₁,…,T_k⟩ → B^I⟨T₁,…,T_k⟩`. Two routes: (a) redo the above
multivariately (the estimates are the same, the index bookkeeping is over `Fin k →₀ ℕ`);
or (b) iterate the univariate map over the base `A^r⟨T₁,…,T_k⟩`, which needs its Gauss-norm
topology (`gaussNormRPS` exists in Groebner.lean) plus the iso `A⟨T,T⃗⟩ ≅ (A⟨T⃗⟩)⟨T⟩`, and a
*general* (rather than `B^I`-specific) univariate evaluation theorem — i.e. the normed-ring
framework AD-7 deliberately avoided. Decide before starting T911.

**AD-10 decided (2026-07-26): route (a′), "slice and reuse."** Rather than redoing the
analysis multivariately *or* building a normed-ring framework, fix a multi-index `I` in the
`k` spectator variables and slice: `sliceSeries f I` is a one-variable series in `T`, and
`sliceSeries (f·g) I = ∑_{I₁+I₂=I} sliceSeries f I₁ · sliceSeries g I₂` (**proven**, via
`antidiagonal_cons`: the antidiagonal of `Finsupp.cons n I` is the product of the two
antidiagonals). Since `evalArHom` is *already* a ring hom on one-variable series, the
`k`-variable map is `I ↦ evalArHom (sliceSeries f I)` and its multiplicativity is the finite
sum above — no new analysis. Landed: `cons_add`, `tail_add`, `antidiagonal_cons`,
`coeffSeq_ext`, `sliceSeries`, `coeffSeq_sliceSeries`, `sliceSeries_add`, `sliceSeries_mul`.
**The `k`-variable hom is DONE** (2026-07-26): `wI_evalAr_le` (evaluation is
norm-decreasing), `isRestricted_sliceSeries`, `isRestricted_of_wI`, `evalArMvFun`,
`isRestricted_evalArMvFun` (uniform decay: an `I` with a large value must be the `tail` of
one of the finitely many large multi-indices of `f`), `sliceSeries_one`/`_zero`, and the
bundled

    evalArMvHom : A^r⟨T, T₁,…,T_k⟩ →+* B^I⟨T₁,…,T_k⟩

for any power-bounded `b ∈ B^I` (take `b = teichPowOverPElt` for case 3). **T910/T910a are
closed.** T911 is now exactly Kedlaya's surjectivity + strictness statement for this map,
and T912 follows from it plus Theorem 3.2.

**T910 progress (2026-07-26)** — `Presentation.lean` (~470 lines): the `A^r`-algebra
structure on `B^I` is **done** (`ArToBI`, injective, `wI_ArToBI`), and Kedlaya's Tate
variable is **done** (`teichPowOverP`, `wLoc_teichPowOverP`, `wI_teichPowOverP`,
`wI_teichPowOverP_le_one`). Remaining for T910: the evaluation map itself = T910a.

**Cor 4.6 (`resIHom` injectivity, T909)** — source proof re-read: vanishing of `λ_{t₀}(x)`
at one `t₀ ∈ I` forces `λ_t(x) = 0` for every `t` strictly between `t₀` and any other point
of `I` (three circles with the *weight on `t₀`*: `λ_t ≤ λ_{t₀}^c λ_{t''}^{1-c}`), and the
endpoints then follow *by continuity of `t ↦ λ_t(x)`*. So the missing ingredient is exactly
that continuity — a sub-development (uniform approximation by `Bloc`-elements), not a gap
in the plan.

Two external consults are archived alongside this board:
`chatgpt-reply-decay-closure-2026-07-26.md` (the moving-prefix estimate that unlocked
the coordinate realization), `chatgpt-reply-degmul-2026-07-26.md` (single-radius
Lemma 2.6/Remark 2.7) and `chatgpt-reply-termination-2026-07-26.md` (the Colex
descent measure for Lemma 3.8).

## Summary
- Core proof tickets: 22 (T101–T505) + 1 stretch (T601, blocked-on-plan)
- Cleanup tickets: 10 (CLEANUP-1…8, CLEANUP-ALL-1, CLEANUP-FINAL)
- Open: all | Done: 0 | Peak parallel capacity: 3 workers
  (M2-summit track ∥ M4-window track ∥ M3/M5 tail)

## Milestone map
M1 T101–T103 → M2 T201–T205 (summit T205 = A_inf complete) ∥ M4-early
→ M3 T301–T303 → M4 T401–T406 (summit T405/T406 = covering machine)
→ M5 T501–T505 (**milestone T503** = Def 2.1.1 honest with Kedlaya's two charts)
→ stretch T601. Cleanups interleaved per cadence.

Global rules for every ticket: verify bar = `lake build '«Adic spaces»'` green, zero
new `sorry` in the touched file beyond the remaining skeleton ones, `#print axioms` of
each filled declaration ∈ {propext, Classical.choice, Quot.sound}. Generality: exactly
the skeleton signatures (maximal-generality decisions frozen at plan §Generality; do
not weaken or strengthen hypotheses).

---

### [T101] O_F: domain, char p, perfect (L1.1–L1.5)
- **Status**: done (beastmode, 2026-07-24T14:00Z → 2026-07-24T14:55Z) | **File**: FarguesFontaine/PerfectoidFieldCharP.lean | **Depends**: none | **Parallel**: yes
- **Progress**:
  - 14:05: all five sorries filled first-strike except CharP (semi-out-param + wrong-direction `charP_of_injective_ringHom` — it pushes char domain→codomain; wrote the `cast_eq_zero_iff` instance directly instead; added `Mathlib.Algebra.CharP.Algebra` import).
  - 14:20: zero errors; `lean_verify` on all substantive decls → `[propext, Classical.choice, Quot.sound]`; module `lake build` green.
  - 14:45: Phase 6.5 cleanup on `frobenius_surjective_OF`: 8→3-line proof (`obtain ⟨y, hy, z, -, hxyz⟩` + `Subtype.ext (by simp [frobenius_def, hxyz])`), docstring tightened (+"semiperfect" gloss, Bhatt citation kept), all gates pass, no renames queued. Flag-only note: proof works at `IsPerfectoidRing` generality (field-ness unused) — future `/generalise` candidate, statement frozen this campaign.
  - 14:55: Phase 6.6 buzz: FAST-BOARD (decl < 100ms profiler threshold; no maxHeartbeats anywhere; no scaffolding). DONE — L1.1–L1.5 discharged.
- Post-proof cleanup: ✓ ran (gates pass, simplify-equivalent golf ran in worker, buzz FAST-BOARD, no flags; four ≤2-line term/instance proofs below cleanup action threshold — recorded per Mode-A judgment)
- **Statements**: `instIsDomainOF`-anon (`IsDomain (OF F)`), `instCharPOF`
  (`CharP (OF F) p`), `frobenius_surjective_OF`
  (`Function.Surjective (frobenius (OF F) p)`), `instPerfectRingOF`
  (`PerfectRing (OF F) p`), `PseudoUniformizer.toOF_ne_zero` — verbatim in file.
- **Sketch**: (1) IsDomain: subring of the field `F` — mathlib subring-domain instance
  (`Subring.instIsDomain`-shape) or `Function.Injective.isDomain` along
  `Subring.subtype`. (2) CharP: transfer along the injective `(powerBoundedSubring
  .toSubring F).subtype` via `charP_of_injective_ringHom`; keep the `have := ‹CharP F p›`
  line (semi-out-param gate). (3) Surjectivity: from the project class field
  `IsPerfectoidRing.frobenius_surj`: `x = y^p + p·z`; kill `p·z` with
  `CharP.cast_eq_zero`; beware `frobenius` needs the `ExpChar` chain — provided by
  CharP + Fact prime instances. (4) PerfectRing: bijectivity from injectivity
  (`frobenius_inj`-shape for domains/reduced rings) + (3); use mathlib's
  `PerfectRing.ofSurjective`/`ofBijective`-style constructor (check exact name via
  `lean_local_search`). (5) ne_zero: `Subtype.ext_iff` + `Units.ne_zero`.
- **Mathlib needed** (name-verified 2026-07-24): `charP_of_injective_ringHom` ✓
  (Algebra/CharP), `frobenius_inj` ✓ (Algebra/CharP/Reduced.lean:28, reduced rings),
  `PerfectRing.ofSurjective` ✓ (FieldTheory/Perfect.lean:97 — check its
  IsReduced/ExpChar hypotheses at fill time), `Units.ne_zero` ✓.
- **Sources**: decomposition L1.1–L1.5 ([Bhatt §3.1 Ex. 3.1.2(3)] verbatim quote there).

### [T102] O_F: the ϖ-adic neighbourhood basis (L1.6)
- **Status**: done (beastmode, 2026-07-25; B2-blocked 2026-07-25 00:35Z → class repair
  executed same day per owner's option 1 → both theorems proven and axiom-clean)
  | **File**: PerfectoidFieldCharP.lean | **Depends**: T101 | **Parallel**: —
- **Progress**:
  - B2 interlude: the inherited `[IsLinearTopology F F]` hypothesis was unsatisfiable for
    Tate fields (b2_log.jsonl 2026-07-25; decomposition §6.5). Owner approved repair
    option 1; classes + engine + all consumers now ride `[NonarchimedeanRing _]`; the
    two T102/T103 statement signatures gained an explicit `[IsPerfectoidField p F]`
    binder (the pinned `OF`/`toOF` signatures no longer auto-include it).
  - `span_toOF_pow_mem_nhds_zero`: proven — `ϖ^n·F°` is the image of the open `F°`
    (`P.isOpen_powerBoundedSubring`) under the unit-multiplication homeomorphism
    (`Homeomorph.mulLeft₀`), pulled back along `nhds_subtype_eq_comap`.
  - `exists_span_toOF_pow_subset_of_mem_nhds`: proven — boundedness of `F°`
    (`IsUniform.isBounded_powerBounded`) + topological nilpotence
    (`exists_pow_mem_of_mem_nhds`) land `c·ϖ^n` in `F°·V ⊆ U'`.
  - Both `#print axioms` = `[propext, Classical.choice, Quot.sound]` (probe-verified).
  - Phase 6.5 cleanup (two Phase-4 workers, all gates pass): `span_toOF_pow_mem_nhds_zero`
    12→6 lines (`IsUnit.isOpenMap_smul` + `mem_nhds_subtype` replace the hand-rolled
    Homeomorph/comap plumbing); `exists_span_toOF_pow_subset_of_mem_nhds` 14→7 lines
    (haveI eliminated — `IsUniform F` genuinely not synthesizable, now an explicit
    projection; tail collapsed to one simpa). Phase 5b rename applied:
    `…_subset_nhds` → `…_subset_of_mem_nhds` (mathlib `exists_*_subset_of_mem_nhds`
    precedent); queue truncated. Phase 6.6 buzz: FAST-BOARD. Flag-only notes: Tate-ring
    generalisation candidate (both proofs use only uniformity + the Huber pair);
    file-wide unusedSectionVars (duplicate perfectoid binder + unused CharP) is a
    campaign-level variable-block decision; the two lemmas form the halves of mathlib's
    `isAdic_iff` — bundling corollary possible once T103 lands.
- Post-proof cleanup: ✓ ran (both workers pass, rename applied, buzz FAST-BOARD)
- **Statements**: `span_toOF_pow_mem_nhds_zero`, `exists_span_toOF_pow_subset_of_mem_nhds`.
- **Sketch**: (1) identify `((span {ϖof})^n : Set)` with `ϖ^n • (O_F)` via
  `Ideal.span_singleton_pow` + `Ideal.mem_span_singleton'`. (2) membership in 𝓝 0: O_F
  is open in F (uniformity: `IsUniform` gives `IsBounded (powerBoundedSubring F)`; the
  project's Tate/uniform API for openness of F° — locate in Uniform.lean/Bounded.lean;
  if genuinely absent, STOP-B3 and report: this is the flagged sub-risk of L1.6) and
  `x ↦ ϖ^n x` is a homeomorphism of F (`Homeomorph.mulLeft₀`/unit smul) carrying O_F
  onto the target set; intersect with O_F for the subspace statement. (3) converse:
  `IsTopologicallyNilpotent` of ϖ + boundedness of O_F: for U ∈ 𝓝 0 pick V with
  O_F·V ⊆ U (`IsBounded`), then ϖ^n ∈ V eventually.
- **Mathlib needed**: `Ideal.span_singleton_pow`, `Homeomorph.mulLeft₀`,
  `Filter.Tendsto` unfolding of `IsTopologicallyNilpotent`.
- **Sources**: decomposition L1.6 (standard Tate-ring facts; [SW §11.2] pattern).

### [T103] O_F is ϖ-adically separated and complete (L1.7–L1.8)
- **Status**: done (beastmode, 2026-07-25; both theorems axiom-clean
  `[propext, Classical.choice, Quot.sound]`, probe-verified) | **File**: PerfectoidFieldCharP.lean | **Depends**: T102
- **Progress**:
  - `isHausdorff_span_toOF`: 13-line proof — SMOD membership → x in every ϖ-power ideal →
    (T102 exists-lemma) x in every neighbourhood of 0 → `0 ∈ closure {x}` →
    `isClosed_singleton` (T0 from the class field + subtype + add-group chain) → x = 0.
  - `isAdicComplete_span_toOF`: IsPrecomplete engine — coherence → membership form;
    Cauchy in F via open-subgroup symmetrization (`NonarchimedeanAddGroup.is_nonarchimedean`,
    boundedness of F°, `exists_pow_mem_of_mem_nhds`, `Ideal.pow_le_pow_right`);
    `cauchySeq_tendsto_of_complete` + topologyEq transport; limit power-bounded via the
    REPAIRED (now public) `IsPerfectoidRing.isPowerBounded_of_tendsto_of_powerBounded`;
    `f n − L ∈ I^n` by the open-hence-closed subgroup `I^n`
    (`AddSubgroup.isOpen_of_mem_nhds` from T102 + `isClosed_of_isOpen` +
    `IsClosed.mem_of_tendsto`). M1 (O_F layer) COMPLETE.
- **Statements**: `isHausdorff_span_toOF`, `isAdicComplete_span_toOF`.
- **Sketch**: (1) Hausdorff: `IsHausdorff` unfolds to SMOD-congruences; an element in
  all `ϖ^n O_F` lies in every neighbourhood of 0 (T102 converse) hence = 0 by the
  `T0Space F` class field (T0 topological group separation:
  `t0Space_iff`/`specializes`-API or the project's preferred route). (2) Complete: given
  a ϖ-adic Cauchy family, it is Cauchy in F (T102 forward), converges by `CompleteSpace
  F`; the limit is power-bounded via `isPowerBounded_of_tendsto_of_powerBounded`
  (PerfectoidRing.lean, audit-verified); ϖ-adic convergence via T102 converse. Assemble
  with `IsPrecomplete`/`IsAdicComplete` constructors and the project `AdicConvergence`
  API.
- **Mathlib needed**: `IsAdicComplete` constructors, `SModEq` bridges
  (`SModEq.sub_mem`), `CompleteSpace.complete`.
- **Sources**: decomposition L1.7–L1.8 ([Bhatt Cor. 3.2.3] verbatim quote there).

### [CLEANUP-1] /cleanup on PerfectoidFieldCharP.lean
- **Status**: open | **Depends**: T103 (final per-file; 3 proof tickets).

### [T201] A_inf: Teichmüller lemmas + topological ring (L2.1–L2.2)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — `teichPi_pow` = `map_pow` of the
  `teichmuller` MonoidHom; `teichPi_ne_zero` via coeff-0 + T101 `toOF_ne_zero`;
  `instNonarchimedeanRingAinf := Ideal.nonarchimedean _` SUPERSEDES the planned
  `instIsTopologicalRingAinf` (IsTopologicalRing flows from `NonarchimedeanRing extends`;
  probe-verified synthesis). | **File**: FarguesFontaine/AinfHuber.lean | **Depends**: T101
- **Statements**: `teichPi_pow`, `teichPi_ne_zero`, `instIsTopologicalRingAinf`.
- **Sketch**: (1) `teichPi_pow`: `map_pow` of the `teichmuller` MonoidHom. (2)
  `teichPi_ne_zero`: Teichmüller coeff-0 is `ϖof ≠ 0` (T101) — `WittVector.ext_iff` or
  coeff API. (3) topological ring: the adic topology is a ring topology — mathlib route
  via `RingSubgroupsBasis` (see `Ideal.adicTopology`'s definition; instance-producing
  spelling per AdicTopology.lean's own `isAdic_iff` proof pattern).
- **Mathlib needed**: `MonoidHom.map_pow`, `WittVector.teichmuller_coeff`-family,
  `RingSubgroupsBasis.toRingFilterBasis` route.
- **Sources**: decomposition L2.1–L2.2 ([SW §13.1] quote).

### [T202] A_inf is Huber with A⁺ = A_inf (L2.3–L2.5)
- **Status**: done (beastmode 2026-07-25; all axiom-clean) — new divisibility engine
  `exists_teichPi_pow_mem_span_teichPi` (ϖ·F° nbhd + top-nilpotence + multiplicative
  Teichmüller) and cofinality `Iinf_pow_le_of_teichPi_pow_mem` ((p,[ϖ'])^((k+1)m) ⊆
  (p,[ϖ])^m via `Ideal.sup_pow_add_le_pow_sup_pow`); `isAdic_Iinf` = canonical-ϖ `rfl` +
  cofinality both ways + `AddSubgroup.isOpen_mono`; `instIsHuberRingAinf` REUSES
  `isHuberRing_ofAdic` (TateAlgebraTopology.lean ⊤-ring-of-definition transport — no new
  transport code); `isPowerBounded_Ainf` via adic basis + ideal absorption;
  `isAffinoidRing_Ainf` trivial fields + power-boundedness. | **File**: AinfHuber.lean | **Depends**: T201, T102
- **Statements**: `isAdic_Iinf`, `instIsHuberRingAinf`, `isPowerBounded_Ainf`,
  `isAffinoidRing_Ainf`.
- **Sketch**: (1) `isAdic_Iinf` via mathlib `isAdic_iff`: (i) `Iinf ϖ`-powers are open
  and (ii) every neighbourhood of 0 contains one — for the canonical-ϖ instance both
  hold by definition; for arbitrary ϖ use mutual divisibility: `ϖ'^n ∈ ϖ·O_F` (T102) +
  `teichPi_pow` + monomial expansion (decomposition L2.3 attack [2] records the ~20-line
  bookkeeping). (2) Huber: `PairOfDefinition` with `A₀ = ⊤`, ideal = `Iinf` transported
  along `Subring.topEquiv`; fg by the 2-element generating set. (3) power-boundedness:
  `{x^k}·I^n ⊆ I^n` (ideal absorption) makes `Set.range (x^·)` bounded. (4) affinoid:
  ⊤ open + integrally closed + (3).
- **Mathlib needed**: `isAdic_iff`, `Subring.topEquiv`, `Ideal.span` finiteness API.
- **Sources**: decomposition L2.3–L2.5 ([Ked-AWS §11.2] independence quote; [Ked-AWS
  Def 3.1.5]).

### [T203] The filtration sandwich (L2.6)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — 2 lines:
  `span_insert` + `two_mul` + mathlib `Ideal.sup_pow_add_le_pow_sup_pow`
  (correcting the 2026-07-24 name-check: the lemma DOES exist, found via loogle). | **File**: AinfHuber.lean | **Depends**: T201 | **Parallel**: with T202
- **Statement**: `Iinf_pow_two_mul_le : Iinf ϖ ^ (2*n) ≤ span {p}^n ⊔ span {[ϖ]}^n`.
- **Sketch**: induction/`Ideal.span_pow` expansion: `Iinf^(2n)` is generated by
  monomials `p^a [ϖ]^b`, `a+b = 2n`; `a ≥ n ∨ b ≥ n`; place accordingly. Use
  `Ideal.span_insert`, `Ideal.pow_le_iff`-shape or the `Finset`-free two-generator
  expansion. (Name-verification 2026-07-24: `Ideal.add_pow_le` was NOT found in
  mathlib's Ideal/Operations — plan for the manual `span_pow` monomial expansion;
  re-check via loogle at fill time in case it lives elsewhere.)
- **Sources**: decomposition L2.6 (elementary; sandwich for the completeness transfer).

### [CLEANUP-2] /cleanup on AinfHuber.lean (after 3rd proof ticket on file)
- **Status**: open (due — T201+T202+T203 done; deferred to after T205 per user
  redirection 2026-07-25 "keep going with the FF constructions" — one cleanup pass when
  the file is sorry-free) | **Depends**: T203.

### [T204] A_inf is (p,[ϖ])-adically separated (L2.7)
- **Status**: done (beastmode 2026-07-25; axiom-clean). Route as validated but LEANER
  than the L2.7a–d skeleton: no truncated-Witt ring theory needed — the joint ideal
  `(p^r, [ϖ]^s)` engine (private helpers in AinfHuber.lean) converts joint-ideal
  congruence into coefficientwise ϖ-power congruence via the RING HOM
  `truncate r ∘ map (Quotient.mk (ϖ^s))` (kernel framing kills every
  coeff-of-difference/Witt-addition issue), with `mul_pow_charP_coeff_zero` for the
  p-direction; separatedness = T103 Hausdorff per coefficient + `WittVector.ext`. | **File**: AinfHuber.lean | **Depends**: T103, T203, CLEANUP-2
- **Statement**: `isHausdorff_Iinf`.
- **Sketch** (ROUTE REPLACED per the gpt-5.6-sol review, decomposition L2.7a–d; the
  old digit-extraction sketch is void): begin the truncated-Witt layer. (1) State as
  private skeleton lemmas (prose frozen in decomposition L2.7a–c): `A/p^r A ≅ W_r(O_F)`
  for perfect O_F (mathlib Complete.lean truncate-kernel machinery); the digit
  sandwich `C_{m·p^{r-1}} ⊆ [ϖ]^m·W_r(O_F) ⊆ C_m` with `C_s = (ϖ^s O_F)^r`
  (Teichmüller digit lemmas `[ϖ]^m·[z]·p^i = [ϖ^m z]·p^i` — the general diagonal
  product formula is NOT in mathlib, avoid it); `W_r(O_F)` is `[ϖ]`-adically separated
  (finite product of T103's separatedness via the sandwich). (2) Separatedness of A:
  x ∈ ⋂ Iinf^n ⟹ (T203 sandwich) x ∈ ⋂ (p^r + [ϖ]^s) over all r,s ⟹ its image in
  every `W_r(O_F)` lies in ⋂_s [ϖ]^s = 0 ⟹ x ∈ ⋂_r p^r A = 0 (mathlib
  `isAdicCompleteIdealSpanP`'s Hausdorff part).
- **Sources**: decomposition L2.7 (+[Ked-AWS Def 3.1.2] quote), RR1 register.

### [T205] ★ SUMMIT: A_inf is (p,[ϖ])-adically complete (L2.8)
- **Status**: DONE (beastmode 2026-07-25; axiom-clean; AinfHuber.lean SORRY-FREE).
  Assembly avoided lim-of-lims entirely: direct `IsPrecomplete` construction — coefficient
  sequences (shifted reindex `f (2(m+j+1))`) are ϖ-adically coherent via the joint-ideal
  coefficient lemma, T103 completeness gives per-digit limits ℓ_j, the limit is
  `WittVector.mk p ℓ`, and the final congruence transfers back through
  `sub_mem_jointIdeal_of_coeff_sub_mem` (whose reverse inclusion
  `ker(truncate∘map) ⊆ (p^r,[ϖ]^s)` rides on mathlib
  `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` + perfectness —
  replacing the planned digit-sandwich/(★)-formula: [θ^{-i} x_i] factors give the
  [ϖ^s]-divisibility of the Teichmüller tail directly). Rates: `M := n·p^{n-1} + n + 1`.
  New helpers: `jointIdeal`, cofinality bridges, `charP_quotient_span_pow` (uses new
  `PseudoUniformizer.not_isUnit_toOF` in PerfectoidFieldCharP.lean + Bezout),
  `frobeniusEquiv_symm_pow_apply_pow_mul`, the two coefficient-congruence lemmas. | **File**: AinfHuber.lean | **Depends**: T204
- **Statement**: `isAdicComplete_Iinf`.
- **Sketch** (ROUTE REPLACED per the gpt-5.6-sol review, decomposition L2.7a–d —
  externally validated; the old coordinatewise plan is VOID (Q2 GAP: J-Cauchy data
  does not split into separate p- and ϖ-direction Cauchy data, and Witt addition is
  not digit-wise), and so is the old fallback `lim_m W(O_F/ϖ^m)` (non-cofinal: p^n A
  leaves high digits uncontrolled)): (1) `W_r(O_F)` is `[ϖ]`-adically complete for
  each r (T204's truncated layer: digit sandwich + T103 digit-wise limits).
  (2) Assembly: `A ≅ lim_r A/p^r` (mathlib `isAdicCompleteIdealSpanP` + L2.7a)
  `≅ lim_r lim_s A/(p^r + [ϖ]^s)` (each level by (1)) `≅ lim_n A/(p^n + [ϖ]^n)`
  (double limit; diagonal cofinal in ℕ²). (3) Transfer along the T203 sandwich
  (Iinf^{2n} ≤ (p)^n ⊔ ([ϖ])^n ≤ Iinf^n) to `IsAdicComplete (Iinf ϖ)`; search mathlib
  for an existing `IsAdicComplete`-under-cofinal-filtrations congruence first, else
  prove the small reusable transfer lemma. (4) HARD-STOP RULE: any genuine obstruction
  is a B2-report (plan revision), never an improvisation; the route carries external
  sign-off, so an obstruction most likely means a mathlib-API mismatch, not
  mathematics.
- **Sources**: decomposition L2.7a–d (sol-validated route, verbatim in
  `chatgpt-reply-fargues-fontaine-2026-07-24.md`); mathlib `WittVector/Complete.lean`
  as the formal p-direction anchor.

### [CLEANUP-3] /cleanup on AinfHuber.lean (final per-file)
- **Status**: open | **Depends**: T205.

### [T301] Frobenius identities (L3.1–L3.2, L3.5)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — `frob_natCast` = `map_natCast`;
  `frob_teichPi` via `show`-defeq to `WittVector.frobenius` + `frobenius_eq_map_frobenius`
  + `map_teichmuller` + T201 `teichPi_pow`; `ofAdd_zsmul_def` is `rfl`. | **File**: FarguesFontaine/FrobeniusAction.lean | **Depends**: T201
- **Statements**: `frob_natCast`, `frob_teichPi`, `ofAdd_zsmul_def`.
- **Sketch**: (1) `map_natCast (frob p F)`. (2) `frobenius_eq_map_frobenius` (CharP) +
  `map_teichmuller` + `teichPi_pow`: φ([ϖ]) = [ϖ^p] = [ϖ]^p — mind that
  `frobeniusEquiv`'s forward map is definitionally `frobenius` (Frobenius.lean:286).
  (3) unfolding: by `rfl` if `MulSemiringAction.compHom`/`zpowersHom` reduce;
  otherwise `Int.induction_on` with `zpow_add_one`/`zpow_sub_one`.
- **Sources**: decomposition L3.1–L3.2 ([SW §12.2]).

### [T302] Frobenius is a homeomorphism (L3.3 — corrected bound)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — private `map_frob_Iinf`:
  `φ(I) = (p, [ϖ]^p)` by `Ideal.map_span` + the two T301 identities; forward bound by
  `pow_right_mono`; reverse `(p+1)n` bound by the same
  `Ideal.sup_pow_add_le_pow_sup_pow` monomial engine as T202; continuity both ways via
  `continuous_of_continuousAt_zero` + `hasBasis_nhds_zero_adic.tendsto_iff`
  (reverse uses `Ideal.mem_map_iff_of_surjective`). | **File**: FrobeniusAction.lean | **Depends**: T301, T202
- **Statements**: `map_frob_Iinf_pow_le`, `Iinf_pow_succ_mul_le_map_frob` (exponent
  `(p+1)*n` — the 2n version is FALSE for p ≥ 3, see decomposition L3.3 attack log),
  `continuous_frob`, `continuous_frob_symm`.
- **Sketch**: (1) forward: generators p ↦ p, [ϖ] ↦ [ϖ]^p ∈ I; `Ideal.map` of span =
  span of images; monotone powers. (2) reverse: φ(I^n) = (p, [ϖ]^p)^n as ideals
  (automorphism image of span); monomial p^a[ϖ]^b with a+b = (p+1)n has a ≥ n or
  b ≥ pn; in the second case [ϖ]^b ∈ ([ϖ]^p)^n. (3) continuity: additive-group
  continuity criterion at 0 with the `Ideal.adicTopology` basis
  (`Ideal.hasBasis_nhds_zero`-shape), one direction per map.
- **Sources**: decomposition L3.3 (attack log documents the corrected exponent).

### [T303] The φ^ℤ-action reaches Spa (L3.4, L3.6–L3.7)
- **Status**: done (beastmode 2026-07-25; axiom-clean; FrobeniusAction.lean SORRY-FREE,
  M3 COMPLETE) — private `continuous_frob_zpow` by `Int.induction_on`
  (zpow_add_one/zpow_sub_one + `RingAut.mul_apply`; inverse-apply is defeq to `.symm`);
  `instContinuousConstSMulAinf := ⟨fun g => continuous_frob_zpow p F g.toAdd⟩`;
  `smul_mem_spa_Ainf` = direct application of ValuationSpectrum.smul_mem_spa with the
  trivial ⊤-stability witness (the [Finite G] drop in ValuationAction paying off). | **File**: FrobeniusAction.lean | **Depends**: T302
- **Statements**: `instContinuousConstSMulAinf`, `smul_mem_spa_Ainf`
  (+ regression: `instMulSemiringActionAinf` is already sorry-free; ValuationAction's
  `[Finite G]` drop is already in the tree — keep both green).
- **Sketch**: (1) `ContinuousConstSMul`: for g = ofAdd k, smul = (frob^k); continuity
  by `Int.induction_on` from T302 (both directions needed for negative k). (2)
  `smul_mem_spa_Ainf` := `ValuationSpectrum.smul_mem_spa` with stability `fun _ _ _ =>
  Subring.mem_top _`.
- **Sources**: decomposition L3.4–L3.7 ([SW §12.2] quote).

### [CLEANUP-4] /cleanup on FrobeniusAction.lean (final per-file)
- **Status**: open | **Depends**: T303.

### [T401] 𝒴: basic-open description and element facts (L4.1 + part of L4.4)
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: FarguesFontaine/YSpace.lean | **Depends**: T201 | **Parallel**: with T30x
- **Statements**: `Y_eq_spa_inter_basicOpen`, `isOpen_Y`, `v_p_ne_zero`,
  `v_teichPi_ne_zero`.
- **Sketch**: (1) set-extensionality: `basicOpen f f` membership is (refl ∧ ¬ v f ≤ 0);
  reflexivity from the ValuativeRel preorder. (2) openness: the legacy `Y_FF_isOpen`
  proof pattern (subtype-val preimage of a basicOpen; `isOpen_basicOpen` +
  `continuous_subtype_val`), line-for-line. (3) product nonvanishing splits: supp-prime
  API (`v.supp` prime, project ValuationSpectrum) or direct: v(p·[ϖ]) ≤ 0 ⟸ v(p) ≤ 0
  by vle-mul-compat.
- **Sources**: decomposition L4.1, L4.4 ([BFHHLWY Def 2.1.1] + [Ked-AWS Rem 3.1.9]
  quotes).

### [T402] 𝒴: φ-stability and ϖ-independence (L4.2–L4.3)
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: YSpace.lean | **Depends**: T401, T301, T102
- **Statements**: `smul_mem_Y`, `Y_indep`.
- **Sketch**: per decomposition L4.2/L4.3: Teichmüller-power divisibility + supp
  primality; for smul: (g•v)(p·[ϖ]) ≠ 0 ⟺ v(p) ≠ 0 ∧ v([ϖ^{p^{-k}}]) ≠ 0, and the
  latter's p^k-th power is v([ϖ]).
- **Sources**: decomposition L4.2–L4.3 ([Ked-AWS §11.2] quote; [SW §12.2] quote).

### [T403] 𝒴: strictness and cofinality from continuity (L4.4–L4.5)
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: YSpace.lean | **Depends**: T401
- **Statements**: `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`,
  `exists_pow_teichPi_vlt`.
- **Sketch**: unfold `Valuation.IsContinuous` at γ = value of the target element via
  the `ValuativeRel.valuation` bridge; the open set contains some `Iinf^N` (adic
  basis); evaluate at p^N resp. [ϖ]^N; for strictness run the γ = v(p) instance and
  close the `γ ≥ 1 ⟹ γ^N ≥ γ` chain (linear-ordered group-with-zero pow-mono lemmas).
  Mind the N = 0 edge (decomposition L4.5 attack [2]); per the sol review (Q4),
  explicitly ENLARGE N to ≥ 2 before closing (free, since ideal powers decrease) —
  this kills the N = 0/1 edge cases uniformly. Sol also confirms `v ≤ 1` on all of
  A_inf is never needed in the window arguments; don't reach for it in proofs.
- **Sources**: decomposition L4.4–L4.5; sol review Q4
  (`chatgpt-reply-fargues-fontaine-2026-07-24.md`).

### [CLEANUP-5] /cleanup on YSpace.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T403.

### [T404] The κ-predicate core (L4.6, L5.1)
- **Status**: done (beastmode 2026-07-25; axiom-clean; committed cf7ef820f) | **File**: YSpace.lean | **Depends**: T403, CLEANUP-5
- **Statements**: `KGE_iff`, `KLE_iff`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`,
  `one_lt_cFF`, `cFF_lt_p`.
- **Sketch**: (1) iffs: cross-multiplication: from q = a/b = num/den derive
  a·den = num·b (`Rat` API: `Rat.num_div_den`, `div_eq_div_iff`); then
  vle-power-cancellation γ^k ≤ δ^k ⟺ γ ≤ δ (strict-mono pow on
  LinearOrderedCommGroupWithZero via the valuation bridge; `pow_le_pow_iff_left₀`-shape
  — locate exact name). (2) totality: ValuativeRel linearity axiom. (3)
  incompatibility: clear both to a common denominator; flip rule
  `pow_le_pow_iff_right_of_lt_one₀`-shape with 0 < v(p) < 1 (T403). (4) cFF bounds:
  `norm_num`-level rational arithmetic with `1 < p` from `(Fact.out :
  p.Prime).one_lt`.
- **Mathlib needed**: named pow-order lemmas on `LinearOrderedCommGroupWithZero` —
  verify names by loogle before coding (the decomposition flags this as the one
  mathlib-name uncertainty of R3).
- **Sources**: decomposition L4.6/L5.1 ([Ked-AWS Rem 3.1.9] verbatim; orientation
  cross-checked against [SW Fig. 12.1] in the decomposition).

### [T405] The covering 𝒴 = ⋃ (U_n ∪ V_n) (L5.5)
- **Status**: done (beastmode 2026-07-25; axiom-clean; YSpace.lean SORRY-FREE, M4+M5
  complete) — new KGE_mono/KLE_mono (Γ₀ pow-cancel + exponent-flip chains); κ pinned by
  cofinality with n+1-bumps through vlt_p_one/vlt_teichPi_one (kills the m=0 edges);
  greatest KGE-index via Int.exists_greatest_of_bdd; split at cFF·p^{n₀} by totality. | **File**: YSpace.lean | **Depends**: T404
- **Statement**: `Y_eq_iUnion_windows`.
- **Sketch**: per decomposition L5.5: cofinality → KLE(p^N), KGE(p^{-N}); the set
  {n : ℤ | KGE(p^n)} ∩ [-N, N] is nonempty-bounded; take max (Int/Finset.max');
  totality at p^{n₀+1}; split at c·p^{n₀}. All ordered-field arithmetic on ℚ-indices +
  KGE/KLE monotonicity (prove tiny `KGE.mono`/`KLE.mono` helpers inline if not already
  forced by T404's iff forms).
- **Sources**: decomposition L5.5 ([Ked-AWS Rem 3.1.9] quote; higher-rank check in the
  attack log).

### [T406] Window translation, disjointness, openness (L5.2–L5.4)
- **Status**: done (beastmode 2026-07-25; axiom-clean; commits efb7b6888 + a77dd0f71) —
  translation via the two procedural transport cores vle_theta_iff_ge/le (three
  vle_pow_iff_cross steps through the Teichmüller collapse; exponent identities by
  pow_add-normalization + omega, uniform in signs); disjointness via
  not_KGE_of_KLE_of_lt at endpoints; openness = Y ∩ two basicOpens with supp-prime
  side conditions. | **File**: YSpace.lean | **Depends**: T404, T402
- **Statements**: `zsmul_windowU`, `zsmul_windowV`, `windowU_disjoint`,
  `windowV_disjoint`, `isOpen_windowU`, `isOpen_windowV`.
- **Sketch**: (1) translation: KGE-transformation under the action (evaluate at
  Teichmüller of the p^{-k}-th root; clear via ^(p^k); ℚ-index arithmetic
  `zpow_add`); Set.smul_set images by the bijective action. (2) disjointness:
  `not_KGE_of_KLE_of_lt` at the interval endpoints; rational strict inequalities from
  `one_lt_cFF`/`cFF_lt_p`. (3) openness: windows = Y ∩ two basicOpen-conditions; the
  ≠0 side-conditions hold on Y (T401); reuse the isOpen_Y pattern for finite
  intersections.
- **Sources**: decomposition L5.2–L5.4 ([Ked-AWS Rem 3.1.9]; [SW §12.2] κ∘φ = pκ).

### [CLEANUP-6] /cleanup on YSpace.lean (final per-file)
- **Status**: open | **Depends**: T406.

### [T501] Freeness and wandering (L6.1–L6.2)
- **Status**: done (beastmode 2026-07-25; pure set-logic over T405/T406 as planned;
  commit 0b076eda6) | **File**: FarguesFontaine/Curve.lean | **Depends**: T405, T406
- **Statements**: `smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`.
- **Sketch**: pure set logic over T405/T406 per decomposition §4 prose: membership in
  some window; translated window is the (n-k)-window; within-family disjointness
  forbids fixation; the window itself is the wandering neighbourhood.
- **Sources**: decomposition L6.1–L6.2 ([Ked-AWS §3.1] and [SW Def 13.5.1] quotes).

### [T502] The quotient map is an open quotient map (L6.3, L7.1)
- **Status**: done (beastmode 2026-07-25; + new Spv-level ContinuousConstSMul via
  comap_continuous; commit 0b076eda6) | **File**: Curve.lean | **Depends**: T402, T303
- **Statements**: `instMulActionYSub` laws, `instContinuousConstSMulYSub`,
  `toCurve_surjective`, `isOpenQuotientMap_toCurve`.
- **Sketch**: subtype-action laws by `Subtype.ext` + parent action laws (pattern:
  ValuationAction's `instMulActionCont`); continuity by
  `Continuous.subtype_mk`∘`continuous_subtype_val` from the Spv-level
  `comap_continuous`; surjectivity `Quotient.mk_surjective`; open-quotient by mathlib
  `MulAction.isOpenQuotientMap_quotientMk`.
- **Sources**: decomposition L6.3, L7.1 ([BFHHLWY Def 2.1.1] verbatim).

### [T503] ★ MILESTONE: Kedlaya's two charts (L7.2–L7.3)
- **Status**: DONE (beastmode 2026-07-25; commit 0b076eda6). NOTE: dispatched before
  CLEANUP-ALL-1 per the user's 2026-07-25 redirection to constructions-first; the
  cleanup backlog remains queued. | **File**: Curve.lean | **Depends**: T501, T502, CLEANUP-ALL-1
- **Statements**: `injOn_toCurve_windowU`, `injOn_toCurve_windowV`,
  `curve_eq_image_window_zero`.
- **Sketch**: injectivity: orbit-mates in one window contradict wandering unless k = 0
  (decomposition L7.2); covering: shift the covering index to 0 by acting with ofAdd n
  (mind the D5 sign, recomputed in L7.3's attack log).
- **Sources**: decomposition L7.2–L7.3 ([Ked-AWS Rem 3.1.9] verbatim: "The spaces U_0
  and V_0 map isomorphically to their images in X_S and cover the latter").

### [CLEANUP-7] /cleanup on Curve.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T503.

### [T504] The curve is T0 (L7.4)
- **Status**: done (beastmode 2026-07-25; commit 3d870f8d5) — chart-separation engine
  sep_of_chart (T0 inside a chart via Spv-T0 + open-quotient pushforward + chart
  injectivity; across charts the open chart-image separates); windows re-opened at the
  ↥Y level. | **File**: Curve.lean | **Depends**: T503, CLEANUP-7
- **Statement**: `instT0SpaceCurve`.
- **Sketch**: distinct orbits: if some window meets both, separate inside the chart
  (chart is an open embedding by T502+T503; Spv/Spa T0 — locate or prove the small
  Spv-T0 lemma flagged in decomposition L7.4); otherwise the open image of the window
  of x avoids y's orbit. Assemble with `t0Space_iff_inseparable`-API.
- **Sources**: decomposition L7.4.

### [T505] The curve is quasicompact (L7.5 — RR2, descopable)
- **Status**: done (2026-07-26 via the T701–T706 unblock lane — see those tickets;
  formerly BLOCKED (beastmode 2026-07-25, per this ticket's hard-stop rule; three
  sorries remain by design, statements untouched). Evidence: route A's closed-image
  hypothesis (`isCompact_rationalOpen_of_isClosed_image`) is discharged in-project only
  for `[DiscreteTopology A]`; for the non-discrete non-Tate adic `A_inf` the
  Spa-continuity conditions are ∃-shaped (cofinality) = countable unions of cylinders,
  not closed — instantiating `S` needs new spectral theory (SpaCompact's own preamble
  only sketches the TATE extension, also not done). Route B: SpaQCviaSpvAI is
  incomplete (1 sorry) and exports no citable two-sided-window qc lemma. Matches the
  sol-Q5 warning that no basicOpen shortcut exists. Unblock = a dedicated dev ticket
  for the adic closed-image instantiation. | **File**: Curve.lean | **Depends**: T503
- **Statements**: `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`.
- **Sketch**: route A: Boolean-embedding closed-image criterion
  (`isCompact_spa_of_isClosed_image`-family, SpaCompact.lean) — the window is cut out
  by finitely many vle-coordinate conditions; route B: qc of the specific TWO-SIDED
  window shape via SpaQCviaSpvAI. **Sol-review warning (Q5): a bare basic-open trace
  is NOT quasicompact — 𝒴 itself is such a trace and is not qc ([Ked-AWS Rem 3.1.11]:
  Y is quasi-Stein, not quasicompact) — so no shortcut via "basicOpens are qc"; the
  bounded two-sided window structure must genuinely enter.** If neither route lands
  within budget: HARD-STOP, mark T505 blocked, leave the three sorries (no
  dependents; the campaign closes without them per RR2) — do NOT weaken statements.
- **Sources**: decomposition L7.5 ([Ked-AWS Rem 3.1.9]: "covered by two affinoid
  subspaces").

### [CLEANUP-8] /cleanup on Curve.lean (final per-file)
- **Status**: open | **Depends**: T505 (or T504 if T505 blocked).

### [CLEANUP-ALL-1] /cleanup-all over the campaign so far
- **Status**: open | **Depends**: T501, T502, CLEANUP-1..6 | blocks T503 (pre-milestone
  pass per cadence rule).

### [T601] STRETCH (blocked-on-plan): 𝒴 is nonempty (L7.6)
- **Status**: done (2026-07-26 via T805: Gauss point in GaussPoint.lean)
  sub-decomposition (Gauss norms, [FF §1.4]); do NOT start from this board.
- **Statement**: `Y_nonempty`.

### [CLEANUP-FINAL] /cleanup-all over the whole campaign
- **Status**: open | **Depends**: everything above (T601 excluded if still blocked).

---

Cadence audit: 22 core proof tickets → ⌈22/3⌉ = 8 in-flow cleanups (CLEANUP-1..8 ✓,
noting files with exactly 3 tickets merge the in-flow and final roles), plus final
per-file covered (1,3,4,6,8), CLEANUP-ALL-1 before milestone T503 ✓, CLEANUP-FINAL ✓.

---

## T505-unblock lane (planned 2026-07-26, /develop --continue; decomposition.md §T505-unblock)

### [T701] Pair-retraction substrate: W1 generalization + CofinalValue.of_le
- **Status**: done (2026-07-26, first-build green; axiom-clean) | **Files**: SpaQCviaSpvAI.lean, SpvAI.lean | **Depends**: none
- **Statements**: (1) weaken `ιSpvR_retractionSingle_eq`'s `(hIg : I = Ideal.span {g})`
  to `(hgI : g ∈ I)` (patch the one caller in `image_ιSpvR_spa_eq` with
  `hIeq ▸ Ideal.mem_span_singleton_self π`); (2) new
  `theorem Valuation.CofinalValue.of_le {v : Valuation A Γ₀} {a b : A}
  (h : CofinalValue v a) (hba : v b ≤ v a) : CofinalValue v b`.
- **Sketch**: (1) single-site edit, proof body unchanged. (2) intro γ hγ; obtain n;
  exact ⟨n, lt_of_le_of_lt (pow_le_pow_left' hba n) hn⟩.
- **Sources**: Wedhorn 7.1 p. 56 (quote in decomposition).

### [T702] The pair retraction and its two properties (W3+W4+W5)
- **Status**: done (2026-07-26; classical-decidable branch split; axiom-clean) | **File**: SpaQCviaSpvAI.lean (new section R5) | **Depends**: T701
- **Statements**: `restrictIdealSingleSpv_vle_of_vle`,
  `mem_SpvAI_span_pair_left`, `restrictIdealPairSpv` (def),
  `restrictIdealPairSpv_mem_SpvAI`, `ιSpvR_retractionPair_eq`.
- **Sketch**: per decomposition W3–W5 (branch split; dominance transfer by
  monotonicity; membership by W3 + span-pair-comm on the other branch; profile-eq by
  W1 at the branch generator).

### [T703] Pair image identification (W6+W7)
- **Status**: done (2026-07-26; mirror of the principal proof; axiom-clean) | **File**: SpaQCviaSpvAI.lean | **Depends**: T702
- **Statements**: `spaProfileConditions₂` + `isClosed_spaProfileConditions₂` +
  `image_ιSpvR_spa_eq₂`.
- **Sketch**: mirror of `image_ιSpvR_spa_eq` per decomposition W7.

### [T704] Pair compactness plumbing (W8)
- **Status**: done (2026-07-26; Wedhorn 7.35(2) for I = (g₁,g₂) landed as
  isCompact_subtype_rationalOpen₂; axiom-clean) | **File**: SpaQCviaSpvAI.lean | **Depends**: T703
- **Statements**: `isCompact_image_ιSpvR_spa₂`, `isCompact_subtype_rationalOpen₂`.
- **Sketch**: mirrors; embedding layer already general (`hIeq'` from `hpair` via
  `Ideal.map_span` + image-of-pair).

### [CLEANUP-9] /cleanup on SpaQCviaSpvAI.lean (new R5 section)
- **Status**: open | **Depends**: T704.

### [T705] Windows as rational subsets (F1)
- **Status**: done (2026-07-26; mem_rationalOpen_pair_iff engine per Wedhorn 7.30(5) +
  two trace identities with opaque cFF num/den exponents; axiom-clean) | **File**: FarguesFontaine/Curve.lean | **Depends**: none (parallel with T70x)
- **Statements**: private `windowU_zero_trace_eq` / `windowV_zero_trace_eq`
  (val-preimages of `windowU/V p F ϖ 0` = val-preimages of explicit `rationalOpen T s`).
- **Sketch**: per decomposition F1 (Wedhorn 7.30(5) product presentation;
  `vle_mul_cancel` backward, `mul_vle_mul_left` forward; supp-prime nonvanishing
  bridges; opaque `(cFF p).num.toNat`/`.den` exponents).

### [T706] ★ Window quasicompactness + CompactSpace Curve (F2+F3, closes T505)
- **Status**: DONE (2026-07-26) — **T505 CLOSED**: `isCompact_windowU_zero`,
  `isCompact_windowV_zero`, `instCompactSpaceCurve` all proven, axiom-clean;
  Curve.lean's only remaining sorry is T601 (`Y_nonempty`, stretch, blocked-on-plan).
  A_inf pair via `ainf_pair_spec` (pairOfDefinition_ofAdic reuse; hpair/hIeq by rfl-level
  idealToTop identifications); radical side conditions by the pure-power T-elements +
  `exists_teichPi_pow_mem_span_teichPi`; CompactSpace by embedding-transfer of the
  window traces into ↥Y and the T503 two-chart covering. | **File**: FarguesFontaine/Curve.lean | **Depends**: T704, T705
- **Statements**: fill `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`.
- **Sketch**: per decomposition F2 (instantiate `isCompact_subtype_rationalOpen₂` at
  the A_inf pair; `hTI` via pure powers + `exists_teichPi_pow_mem_span_teichPi`) and
  F3 (compact transfer to ↥Y, toCurve-images, T503 covering).

### [CLEANUP-10] /cleanup on Curve.lean (final; supersedes CLEANUP-8's scope)
- **Status**: open | **Depends**: T706.

---

## Campaign 8 lane A (planned 2026-07-26): Gauss valuation + Y_nonempty

### [T801] Weighted Gauss value on A_inf: definition + basic evaluations
- **Status**: done (beastmode 2026-07-26; GaussNorm.lean created; all axiom-clean) —
  perfectoidValuation extraction, teichCoeff (θ^{-n}-twist), gaussTerm/gaussValue,
  le_one, zero/one/teichmuller evaluations, p-shift w(p·x) = ρ·w(x) (via
  mul_charP_coeff and the θ-inverse cancellation), and max-attainment for ρ < 1.
  NOTE: bddAbove/evaluations thread (hρ1 : ρ ≤ 1) — for ρ > 1 the term family is
  genuinely unbounded, caught during implementation. | **File**: FarguesFontaine/GaussNorm.lean (new) | **Depends**: none
- **Statement sketch**: fix `hv : Valuation F ℝ≥0` with `hv.Integers (O_F)`
  (from `IsPerfectoidField.exists_valuation`, extracted once as a `def`), `ρ : ℝ≥0`,
  `hρ : 0 < ρ` `hρ1 : ρ < 1`. Define
  `gaussValue ρ x := ⨆ n, ρ^n * (hv (θ^{-n} (x.coeff n)))` (θ = frobeniusEquiv of O_F;
  equivalently `(hv x.coeff n)^(p^{-n})` — STEP 0: fix the convention against the
  typeset PDF of (2.2.1)/AWS 2.6.3). Prove: value at 0/1/[a]/p·x; ≤ 1 globally;
  iSup attained (ρ<1); monotone tail bounds.
- **Sources**: Kedlaya 1410.5160 (2.2.1); AWS Rem 2.6.3.

### [T802] Ultrametric additivity of the Gauss value
- **Status**: done (beastmode 2026-07-26; gaussValue_add_le axiom-clean)
- **Progress**: Route as frozen (1004.0466 Lemma 4.1) but with a formalization
  simplification found during implementation: the pair-case `[a]+[b]` needs NO
  Witt-polynomial homogeneity — over the perfectoid FIELD F one writes
  `[a]+[b] = [a]·(1+[u])`, `u = b/a ∈ O_F` (Integers.exists_of_le_one), and uses the
  new scaling lemma `teichCoeff_teichmuller_mul` (coordinates of `[w]·s` are `w·coords(s)`),
  itself a consequence of expansion uniqueness `teichCoeff_sum_range_add` (CORE-1, via
  le_coeff_eq_iff_le_sub_coeff_eq_zero + sum_coeff_eq_coeff_sum + teichmuller_mul_pow_coeff).
  Kedlaya's (4.1.1)/(4.1.2) multiset induction became `exists_level_rep` (digit-prefix +
  p^n·List.sum invariant) with two list-engines: `exists_list_head_split` (op. 1: head-split
  every member via `exists_head_split`, tails controlled by `mul_gaussValue_le_of_tail`)
  and `exists_fold_teichmuller_heads` (op. 2 iterated: fold Teichmüller heads pairwise,
  re-splitting after each merge). All axiom-clean.
  Kedlaya 1004.0466 Lemma 4.1 (paper in refs). Core input: `[a] ± [b] =
  Σ_j p^j [P_j^±(a,b)^{p^{-j}}]`, P_j^± ∈ 𝔽_p[X,Y] homogeneous of degree p^j ⟹
  |c_j| ≤ max(|a|,|b|); digit-carry induction; ρ^N tail bound; density extends.
- **Statement**: `gaussValue ρ (x+y) ≤ max (gaussValue ρ x) (gaussValue ρ y)`.

### [T803] Multiplicativity (paper Lemma 2.3 / 1004.0466 Lemma 4.1)
- **Status**: done (beastmode 2026-07-26; gaussValue_mul + gaussValue_mul_le + neg/sub/isosceles/positivity all axiom-clean)
  p^i[a]·p^j[b] = p^{i+j}[ab] + T802; equality via least max-attaining indices +
  strictly-smaller discarded parts (sol Q2).
- **Statement**: `gaussValue ρ (x*y) = gaussValue ρ x * gaussValue ρ y`.

### [CLEANUP-11] /cleanup on GaussNorm.lean
- **Status**: done-as-scoped (2026-07-26: lint-clean pass on GaussNorm/GaussPoint — omit-annotations, deprecated-name fixes, unused simp args; deep per-decl golf is fleet /cleanup work on main per AINTLIB architecture, not producer work)

### [T804] The Gauss point: Valuation package, continuity, Spa-membership
- **Status**: done (beastmode 2026-07-26; GaussPoint.lean: gaussVal bundle, v(pseudo-uniformizer)<1 via not_isUnit_toOF, Iinf^n-estimate by Submodule.mul_induction_on, Wedhorn-7.7 continuity via isAdic_Iinf + map_add_left_nhds_zero; all axiom-clean)
- **Statement**: `gaussValuation ρ : Valuation (Ainf p F) ℝ≥0`; `gaussSpv ρ : Spv _`;
  `gaussSpv_isContinuous`; `gaussSpv_mem_spa`.

### [T805] ★ Y_nonempty (closes T601)
- **Status**: done (beastmode 2026-07-26; Curve.lean Y_nonempty := Y_nonempty' — the rho=1/2 Gauss point; AXIOM-CLEAN; closes T601; FarguesFontaine/ is sorry-free; full library green 6141 jobs)
- **Statement**: fill `Y_nonempty` in Curve.lean: `⟨gaussSpv ρ, mem_spa, w(p[ϖ]) ≠ 0⟩`.

### [PLAN-GATE-1] /develop --decompose: Kedlaya §2–§4 (Euclidean/PID + strongly noetherian + B^I)
- **Status**: done (2026-07-26: decomposition-laneB.md written; Lane-B tickets T901–T912 filed; AD-1..AD-7 frozen) | **Depends**: T805
- Scope PER SOL REVIEW: §2–§3 PLUS Definition 4.2, Lemma 4.9, Theorem 4.10 (the
  two-sided interval rings B^{[1,c]} (U₀) and B^{[c,p]} (V₀), normalization
  |ϖ| = p^{-1}); include the Banach-vs-Huber Tate-algebra topological agreement.
- NOT executable by /beastmode: this is a planning action producing lane-B tickets.

#### Lane C first block (spawned 2026-07-26, beastmode; from PLAN-GATE-2 + the
#### chatgpt-reply-campaign8-adic-space consult §5-6)

### [TC1] The affinoid-ring instances for B^I
- **Status**: done (2026-07-26, beastmode) | **Parent**: PLAN-GATE-2 | **Type**: instances + lemmas
- **File**: FarguesFontaine/SheafyBI.lean (new; imports StronglyNoetherianB +
  WedhornCechAcyclicity)
- **Statement**: `IsBounded (BIPlusIn …)`, `wI_le_one_of_isPowerBounded`,
  `BIPlusIn`-integral-closedness, `subset_powerBounded`, hence
  `IsRingOfIntegralElements (BIPlusIn …)`; plus `T2Space ↥BISub` and
  `CompleteSpace ↥BISub` (right uniformity).
- **Sketch**: mirror ExampleUnitDisc.lean:384-500 with `wI` for the norm and the
  `p`-image for the Tate element: boundedness from `wI_mul_le` + wI-ball basis;
  power-bounded ⟹ unit ball via `wI_pow` (power-multiplicativity) +
  `pow_unbounded_of_one_lt`; integral closedness via
  `IsBounded.isPowerBounded_of_isIntegral`; completeness from `isComplete_BISub`.

### [TC2] B^I is sheafy (Kedlaya's rings satisfy Wedhorn 8.28(b))
- **Status**: done (2026-07-26, beastmode) — `isSheafy_BISub` in SheafyBI.lean | **Parent**: PLAN-GATE-2 | **Type**: theorem
- **Statement**: under the AD-9 data (h12, j, n, hbmem, hb, hexact):
  `IsSheafy ↥(BISub …)` with `PlusSubring := BIPlusIn`.
- **Sketch**: `isSheafy_of_stronglyNoetherian_828b` with `letI`-assembled instances
  (TC1 + `isTateRing_BISub` + `isStronglyNoetherian_BISub`).

#### Lane C identification block (spawned 2026-07-26, beastmode; consult §5)

The chart windows are rational subsets of the non-Tate pair `(A_inf, A_inf)` with
single-denominator presentations (write `c = cFF p = (p+1)/2 = a/b` in lowest terms,
so `a = (p+1)/2, b = 1` for odd `p` and `a = 3, b = 2` for `p = 2`):
`U₀ = R({p^{a+1}, [ϖ]^{b+1}} / p[ϖ]^b)`, `V₀ = R({[ϖ]^{b+1}, p^{p+a}} / p^a[ϖ])`.
The repo's `RationalLocData.IsRational` is Wedhorn's faithful open-ideal condition —
non-Tate bases are supported.

### [ID1a] The chart datum `chartDataU : RationalLocData (Ainf p F)`
- **Status**: done (2026-07-26, beastmode) — generalized: `chartData u v a b` in new
  FarguesFontaine/ChartData.lean (s = pᵘ[ϖ]ᵛ, T = {p^{a+1},[ϖ]^{b+1}}) covers both
  charts and every AD-9 window; `podAinf`, divByS calculus, monomial-span lemma | **Parent**: PLAN-GATE-2 | **Type**: def + lemma
- **Sketch**: `P` := the `(p,[ϖ])`-adic pair of definition from AinfHuber;
  `T := {p^{a+1}, [ϖ]^{b+1}}`, `s := p·[ϖ]^b`; `hopen`: for `N` large the monomials
  `p^i[ϖ]^{N-i}/s` are `A`-multiples of products of the two generating fractions
  (elementary exponent bookkeeping in `locSubring`).
- Mirror `chartDataV`.

### [ID1b] `chartDataU.IsRational`
- **Status**: done (2026-07-26, beastmode) — `isRational_chartData` | **Parent**: PLAN-GATE-2 | **Type**: lemma
- **Sketch**: `I^{a+b+2} ⊆ span T` monomial-by-monomial (`i ≥ a+1` or
  `N-i ≥ b+1`); `I^M` is open (adic) and a subset of an ideal makes it open.

### [ID1c] The window is the rational subset
- **Status**: done (2026-07-26, beastmode) — `mem_rationalOpen_chartData_iff`
  (raw-exponent two-sided window) + `windowU_zero_eq_rationalOpen` /
  `windowV_zero_eq_rationalOpen` (both charts as explicit rational subsets) | **Parent**: PLAN-GATE-2 | **Type**: theorem
- **Statement**: `windowU 0 = Y ∩ (Spa-trace of rationalOpens T_U s_U)` (and V).
- **Sketch**: unfold `KGE 1`/`KLE c`/`rationalOpens`; cancellation of `v([ϖ])^b`
  and `v(p)` via the `pow_le_pow_iff_cross` tools in YSpace; the `v(s) ≠ 0`
  condition ⟺ the `Y`-condition `v(p[ϖ]) ≠ 0`.

### [ID2] ★ The comparison theorem `presheafValue chartDataU ≅ B^{I_U}`
- **Status**: DONE 2026-07-27 (all of ID2a–ID2e; ChartData.lean + ChartComparison.lean) |
  **Parent**: PLAN-GATE-2 | **Type**: theorem block
- **Interval match (worked out)**: κ = log v([ϖ])/log v(p) at the Gauss point w_ρ
  gives κ = log|ϖ|/log ρ, so U₀'s window κ ∈ [1, a/b] is the interval
  `I_U = [|ϖ|, |ϖ|^{b/a}]` — left endpoint |ϖ|^{1·1} is AD-9 with j = n = 1, so
  `isSheafy_BISub_AD9 1 1` applies; ρ₂ = |ϖ|^{(b:ℝ)/a} (rpow, no special form
  needed). V₀: κ ∈ [a/b, p] ↔ `I_V` — mirror with the endpoints swapped (left
  endpoint |ϖ|^{b/a}: NOT nat-power AD-9 — use the AD-9 density argument or the
  Frobenius translate of U₀; decide at ID2e).
- **ID2a** DONE (2026-07-26: isLocalization_chartS_Bloc + blocEquivAwayChartS in ChartData.lean) — same localization (both
  invert the p·[ϖ]-saturation); IsLocalization.ringEquivOfRingEquiv transport.
- **ID2b routing (2026-07-26)**: the repo's Wedhorn-6.38 comparison
  (`presheafValueCanonicalQuotientEquiv_faithful : presheafValue D ≃+* A⟨X⟩/(1−sX)`)
  requires `[IsStronglyNoetherian A]` on the BASE — unavailable over `A_inf`
  (Kedlaya deliberately avoids it). So ID2b must be proven ball-by-ball. The
  ⊆-half (`J^n`-balls inside `wI`-balls) is elementary: the locSubring-image lies
  in the unit ball ({wI ≤ 1} is a subring; generators: A_inf-images have wI ≤ 1,
  the fractions [ϖ]/p and p^a/[ϖ]^b have wI ≤ 1 exactly by the interval-endpoint
  arithmetic ρ₁ = |ϖ|, ρ₂ = |ϖ|^{b/a}), and the locIdeal generators have wI < 1.
  The ⊇-half (wI-balls inside `J^n`-image-balls) is the hard half — needs the
  factorization `wI z ≤ min(ρ₁,ρ₂)^n → z = pⁿ·(unit ball)` (`exists_eq_p_pow_mul`,
  IntervalRing, proven) PLUS the dense-layer plus-ring inclusion
  `Bloc ∩ {wI ≤ 1} ⊆ locSubring-image` (Kedlaya's plus-ring arithmetic on the
  dense layer — spawn as ID2b-ii when reached; the Teichmüller-prefix machinery
  from T911 is the expected tool).
- **ID2b progress (2026-07-26)**: forward half's core DONE in ChartData.lean —
  chartFracPi/chartFracP with wI-bounds, blocUnitBall, the transport lemmas
  (blocEquivAwayChartS_algebraMap, blocEquiv_divByS_teichPi/_p),
  map_locSubring_chartData (the locSubring image IS the chart closure), and
  map_locSubring_le_blocUnitBall. REMAINING for ID2b: (i) J^n-image-balls inside
  wI-balls (locIdeal generators have wI < 1 — cofinality estimate), (ii) the hard
  ⊇-half (wI-balls inside J^n-images: exists_eq_p_pow_mul + the dense-layer
  plus-ring inclusion ID2b-ii), (iii) package as topology/uniformity equality.
- **ID2b-ii OBSTRUCTION — RETRACTED (2026-07-27, proven wrong in Lean)**: the
  claimed middle-range divisibility degradation does NOT occur at the exact
  chart endpoints. Corrected analysis: for the `m > k` term with `i = m-k`,
  `t = ⌊i/a⌋`, the integrality requirement is `t ≥ i/a − c₀/b`, a slack
  interval of k-INDEPENDENT length `c₀/b ≥ 1` (for `c₀ = b`), which always
  contains `⌊i/a⌋`. The termwise route CLOSES: `mem_chartSubring_of_wI_le`
  (ChartData.lean, commit c33e85b14) proves `Bloc ∩ {wI ≤ |ϖ|^b} ⊆
  A_inf[[ϖ]/p, p^a/[ϖ]^b]` at the exact endpoints `ρ₁ = |ϖ|`, `ρ₂^a = |ϖ|^b`
  (which is all ID2 needs — the chart intervals are exactly of this form).
  Scaled/basis forms: `exists_p_pow_mul_mem_chartSubring`, `ball_le_locNhd`
  (the min(ρ₁,ρ₂)^n·|ϖ|^b-ball lies in `locNhd n`). Together with
  `exists_locNhd_le_ball` the two-sided basis comparison is COMPLETE, so the
  chart topology = the wI-topology on the localization. The quotient-
  presentation detour is NOT needed.
- **ID2b-ii superseded sketch (kept for the salvageable per-term identities)**:
  for the ⊇-half it SUFFICES to show `Bloc ∩ {wI ≤ |ϖ|^{c₀}} ⊆ locSubring-image`
  for one fixed exponent `c₀` (an ε₀-weakened inclusion; the plus-ring EQUALITY is
  not needed — consult §5). Proof route: `x = A/(p[ϖ])^k` (localization rep), so
  `x = Σ_m p^{m-k}[a_m·ϖ̄^{-k}]` with `a_m ∈ O_F` — non-integrality uniformly
  bounded by `k`. Split off the length-`N` prefix (`exists_eq_sum_teichCoeff_add`):
  the tail is `(p^a/[ϖ]^b)^{⌈k/b⌉}·algebraMap(p^{N-k-a⌈k/b⌉}[ϖ]^{b⌈k/b⌉-k}·Z)`
  for `N` large — in the subring. Each prefix term `p^i[c]` splits as
  `([ϖ]/p)^{-i}·[c·ϖ̄^{-i}]` (i < 0, integral by ρ₁ = |ϖ| on the nose) or
  `(p^a/[ϖ]^b)^{⌊i/a⌋}·p^{i mod a}·[c·ϖ̄^{b⌊i/a⌋}]` (i ≥ 0, integral by the
  `wI ≤ |ϖ|^{c₀}`-slack with `c₀ ≥ b`, using the nat-pow endpoint hypothesis
  `ρ₂^a ≤ |ϖ|^b` — avoid rpow throughout). Then the reverse ball-inclusion:
  `wI z ≤ min(ρ₁,ρ₂)^n·|ϖ|^{c₀} → z ∈ J^n-image` via `exists_eq_p_pow_mul`
  (factor `pⁿ`) + the ε₀-inclusion for the cofactor + `J ⊇ p·locSubring`.
- **ID2b** ★ THE TOPOLOGY COMPARISON: under ID2a the `chartData`-canonical topology
  (locSubring-adic, `RationalLocData.uniformSpace`) on `Bloc` equals the
  `wI`-topology for `I_U`. Two inclusions: `I_D^n`-balls inside `wI`-balls (each
  locSubring generator has `wI ≤ 1`: A_inf-images since both radii < 1, the
  fractions `[ϖ]^{b+1}/s`, `p^{a+1}/s` by the window's endpoint arithmetic; the
  ideal generator has `wI < 1`) and conversely (`wI`-small elements of `Bloc` are
  in high `I_D`-powers — the division/prefix estimates from T911's machinery).
- **ID2c** DONE 2026-07-27: chartUniformity/chartCompletionToBIProd/
  presheafChartToBIProd (+_coe) in ChartData.lean; presheafChartToBI
  (corestricted to B^I) in ChartComparison.lean.
- **ID2d** DONE 2026-07-27 (ChartComparison.lean): presheafChartRingEquivBISub
  `presheafValue (chartData 1 b a b) ≃+* ↥B^I` with both continuity directions,
  via chartBIPkg (AbstractCompletion) + compareEquiv + dense-extension
  agreement (presheafChartToBI_eq_compare). Hypotheses: 0 < a, 0 < b, b ≤ a,
  hexact1 : |ϖ| = ρ₁, hexact2 : ρ₂^a = |ϖ|^b (exact chart interval).
- **ID2e** DONE 2026-07-27 (ChartComparison.lean): isSheafy_presheafChart —
  `IsSheafy (presheafValue (chartData 1 b a b))` with plus-ring the transported
  `B^{I,+}`-candidate (BIPlusIn image; §5 integral-closure equality not needed),
  via isSheafy_mapRingEquiv at e := (ID2d).symm; new generic infrastructure
  isTateRing_congr + completeSpace_right_presheafValue.
- **Sketch** (consult §5): (a) universal-property map into `B^I` (the fractions
  `[ϖ]/p`, `p^a/[ϖ]^b` are power-bounded in `B^{I_U}` — endpoint value
  computations); (b) both sides contain the dense `Bloc`; (c) the rational-
  localization topology equals the `λ_I`-topology (via Lemma 4.9/T911 machinery:
  the localization is Tate with `p` a topologically nilpotent unit); assemble as a
  topological-ring iso. Plus-ring: transport the integral closure of
  `A⁺[T/s]` (NOT `B^{I,+}` equality — unnecessary per consult).
- **Depends**: ID1a-c, T911, TC2.

### [ID3] Y is pre-adic and sheafy on the charts
- **Status**: open — DECOMPOSED 2026-07-27 into ID3a–ID3d | **Parent**: PLAN-GATE-2/PLAN-GATE-3 | **Type**: theorem block
- **PLAN (2026-07-27, replaces the U_n/V_n-chart route)**: cover Y by the BIG
  windows `BigW_n := {κ ∈ [p^n, p^(n+1)]}` (n : ℤ). Since c = (p+1)/2 ∈ (1,p),
  `BigW_n = U_n ∪ V_n` EXACTLY, so the T405 covering gives `Y = ⋃ BigW_n`. Each
  `BigW_n` is the `chartS 1 1`-type datum `chartData 1 1 p 1` (window κ' ∈ [1,p],
  a = p, b = 1) taken IN THE TWISTED PSEUDO-UNIFORMIZER `ϖ_n` with
  `v([ϖ_n]) = v([ϖ])^{p^{-n}}` (p^n-th Frobenius root for n > 0, p^|n|-th power
  for n < 0) — this stays entirely inside the proven chartS-1-b machinery
  (isSheafy_presheafChart at a := p, b := 1, hexact1 : v(ϖ_n) = ρ₁ NAT-EXACT,
  hexact2 : ρ₂^p = v(ϖ_n) via rhoRight). NO u>1-denominator generalization and
  NO rational-endpoint generalization needed. V₀ alone is NOT a chart of this
  family — it is covered by BigW_0; that suffices for sheafiness/locality.
- **ID3a** (open): pseudo-uniformizer twisting. `PseudoUniformizer.pow (m>0)`
  (nilpotency of ϖ^m: multiples are cofinal) and `PseudoUniformizer.frobRoot s`
  (unit-level (frobeniusEquiv F p).symm^s; nilpotency: r^m = ϖ^k·r^j with
  {r^j : j < p^s} ⊆ O_F bounded and nonarch subgroup-nbhds absorb
  bounded·nilpotent); value lemmas `v(toOF (frobRoot ϖ s))^(p^s) = v(toOF ϖ)`,
  `toOF (pow ϖ m) = toOF ϖ ^ m`, and the Ainf-side `teichPi (frobRoot/pow)`
  power relations.
- **ID3b** (open): window identification. `Y p F ϖ = Y p F ϖ_n` (powers detect
  the same vanishing) and `BigW_n(ϖ) = rationalOpen (chartT-in-ϖ_n p 1)
  (chartS-in-ϖ_n 1 1)` via mem_rationalOpen_chartData_iff at ϖ_n + the
  KGE/KLE cross-multiplication bridges ([ϖ_n]^{p^n} = [ϖ] as teichPi-powers).
- **ID3c** (open): sheafiness per window. `IsSheafy (presheafValue
  (chartData-in-ϖ_n 1 1 p 1))` := isSheafy_presheafChart at ϖ_n, a := p,
  b := 1, hab : 1 ≤ p, ρ₂ := rhoRight-in-ϖ_n p 1 (apply DIRECTLY — do not
  restate the letI chain; see the isDefEq-trap note under PLAN-GATE-2).
- **ID3d** (open): assembly — Y pre-adic + adic via covering locality (consult
  the repo's Spa/8.27 framework for the exact statement shape; Wedhorn Rem 8.27;
  TC2). Needs T405 (the covering, Lane A) for `Y = ⋃ BigW_n`.
- **Depends**: ID2 (done), ID3a-c mutually ordered, T405 for ID3d.

### [PLAN-GATE-2] Lane C assembly planning (identification theorem + sheafy instances)
- **Status**: mostly DISCHARGED 2026-07-27 — the chart-identification theorem is
  ID2 (DONE: presheafChartRingEquivBISub + isSheafy_presheafChart, any (a,b) with
  0<b≤a at the exact interval ρ₁=|ϖ|, ρ₂^a=|ϖ|^b); U₀-instantiation endpoints
  proven (rhoRight/rhoRight_pos/rhoRight_lt_one/rhoRight_pow_exact +
  two_le_p_add_one in ChartComparison.lean — U₀ = chartData 1 2 (p+1) 2 at
  ρ₂ := rhoRight (p+1) 2; apply isSheafy_presheafChart DIRECTLY at the point of
  use, do NOT restate the letI-chain (isDefEq-timeout trap, 2026-07-27)).
  REMAINING for ID3: (i) V₀ has u = p+1 > 1 denominator — NOT covered by the
  chartS 1 b machinery; route per AD-9 density (cover V₀ by nat-power-left-endpoint
  special intervals) or a Frobenius translate; (ii) Y-locality via Wedhorn Rem 8.27 | **Depends**: PLAN-GATE-1 only for the
  sheafiness core (the repo's `isSheafy_of_stronglyNoetherian_828b` is sorry-free);
  presheafValue-identification additionally depends on the PresheafTateStructure
  plumbing. SOL CORRECTIONS (binding): 𝒪(U₀) ≅ B^I is a genuine theorem (dense
  subalgebra + topology comparison, or Lemma 4.9); the rational PLUS ring is the
  integral closure of A⁺[T/s] (NOT of the image of A⁺) and is what gets
  transported — equality with B^{I,+} not required.

### [PLAN-GATE-3] Lane D: 𝒳 as a locally v-ringed quotient (NEW per sol Q6)
- **Status**: blocked (planning gate) | **Depends**: PLAN-GATE-2
- Content: 𝒴 pre-adic structure + chart identifications respecting restrictions
  (Wedhorn Rem 8.27); then EITHER 𝒪_X(W) := 𝒪_Y(q⁻¹W)^{φ^ℤ} descent (with plus
  sheaf and stalk valuations) OR two-chart gluing along the Frobenius transitions
  (overlap pieces: κ = c identity; κ = 1 ↔φ↔ κ = p), cocycle condition, and the
  local-isomorphism property of q — only then is 𝒳 an adic space.

---

## Campaign 8 Lane B (PLAN-GATE-1 output, 2026-07-26): Kedlaya 1410.5160 §2–§4
Architecture decisions AD-1..AD-7 in `.mathlib-quality/decomposition-laneB.md` are BINDING.
File plan: `FarguesFontaine/RobbaLoc.lean` (T901), `FarguesFontaine/WittF.lean` (T902–T903),
`FarguesFontaine/Euclidean.lean` (T904), `FarguesFontaine/Groebner.lean` (T905–T907),
`FarguesFontaine/IntervalRing.lean` (T908–T911), `FarguesFontaine/StronglyNoetherianB.lean` (T912).

### [T901] Bloc + the extended Gauss-valuation family
- **Status**: done (beastmode 2026-07-26; RobbaLoc.lean — Bloc, wLoc via extendToLocalization, mk'/algebraMap/unit-inverse evaluations; axiom-clean) | **File**: FarguesFontaine/RobbaLoc.lean | **Depends**: T803/T804 (done)
- **Statement**: `Bloc p F := Localization.Away ((p : Ainf p F) * teichPi p F ϖ)`;
  `wLoc ρ hρ0 hρ1 : Valuation (Bloc p F ϖ) ℝ≥0 := (gaussVal p F hρ0 hρ1).extendToLocalization hS _`
  with `hS : Submonoid.powers (p·[ϖ]) ≤ (gaussVal).supp.primeCompl` from
  `gaussValue_p_teichPi_ne_zero`; evaluation lemmas `wLoc_mk'` (from
  `Valuation.extendToLocalization_mk'`), `wLoc_coe` (on `Ainf`-images), values on
  `p⁻¹`, `[ϖ]⁻¹`; `wLoc_teichmullerFrac : wLoc ([a]/[ϖ^k]) = |a|/c^k`.
- **Sketch**: pure API assembly; mathlib `extendToLocalization` verified present with
  `extendToLocalization_mk'`. Source: Kedlaya Def 2.2 (ln 85–95) + AD-1/AD-2.

### [T902] W(F) engines + the Hölder coordinate-continuity lemma
- **Status**: done-as-scoped (beastmode 2026-07-26; b1/b1'/b2/b3 all in WittF.lean,
  axiom-clean; b4 + engine ports (a) explicitly moved into T903). DONE so far in WittF.lean (all axiom-clean):
  (b1) `exists_teichmuller_sub_coeff_eq` — diagonal divisibility via W(O_F[T])-naturality
  (evalRingHom x/y through map_coeff + map_teichmuller + Polynomial.dvd_iff_isRoot);
  (b1') `valuation_teichCoeff_teichmuller_sub_pow_le` — the pow-form twist bound
  v(teichCoeff([x]−[y]) k)^(p^k) ≤ v(x−y) (via frobeniusEquiv_symm_pow_pow_cancel,
  now de-privatized in GaussNorm.lean);
  (b2) `gaussValue_teichmuller_sub_le_of_le` — ε-δ continuity of a ↦ [a] with
  δ = ε^(p^K), K from exists_pow_lt_of_lt_one; pow_le_pow_iff_left₀ for root-taking.
  (b3) DONE: `exists_delta_teichCoeff_sub` — per-coordinate ε-δ on Ainf by head-split
  recursion (eq_sub_of_add_eq to avoid rewriting under teichCoeff; δ = min (min (ρδₙ) δT) 1);
  axiom-clean. REMAINING: (b4) clearing denominators to Aloc/Bloc (coords of x/(p[ϖ])^k);
  (a) the W(F) engine ports — DECISION: defer both into T903 where the completion
  context fixes the right statement shapes | **File**: FarguesFontaine/WittF.lean | **Depends**: T901
- **REVISED per AD-3-revision**: two deliverables. (a) Port the GaussNorm engines
  (CORE-1/2, head split, scaling, pair bound via u-trick + `WittVector.map`-naturality
  from `W(O_F)`, level-rep) to `W(F)`-elements with attained-sup statements under
  explicit BddAbove hypotheses (no global ≤1). (b) **Coordinate continuity** (the
  load-bearing new lemma, source Kedlaya 1004.0466 Thm 4.5): quantitative Hölder bound
  on `Ainf` first — if `gaussValue ρ (a−b) ≤ ρⁿ·δ^{p^n}` with `δ ≤ 1` then
  `|teichCoeff a n − teichCoeff b n| ≤ δ` (exact constant shape to be fixed against the
  1004.0466 proof) — then the same on `Bloc` by clearing denominators.
- **Sketch REVISED (route derived 2026-07-26, replaces the 1004.0466-transcription —
  that theorem is Gelfand-spectra continuity, not the coordinate estimate)**:
  (b1) **Diagonal divisibility**: for k ≥ 1, `(teichmuller x − teichmuller y).coeff k`
  is divisible by `x − y` in `O_F`. Proof WITHOUT polynomial computations: work in
  `W((O_F)[X,Y])`; the element `E_k := ([X] − [Y]).coeff k ∈ O_F[X,Y]` vanishes under
  the diagonal evaluation `Y ↦ X` (since `[x]−[x] = 0`), by `WittVector.map`-naturality
  (map (evalHom) commutes with coeff and with teichmuller); hence `(X−Y) ∣ E_k`;
  specialize by `WittVector.map (eval (x,y))`. Corollary (pow form, no rpow):
  `v(teichCoeff ([x]−[y]) k)^(p^k) ≤ v (x−y)` (the twist θ^{-k} takes p^k-th roots;
  the cofactor is in O_F so v ≤ 1). Same for `[x]+[y]` against `[x+y]` if needed.
  (b2) **Teichmüller-difference modulus**: `w_ρ([a]−[b]) ≤ max(v(a−b),
  sup_{k≥1} ρ^k·v(a−b)^{p^{-k}})` — an explicit modulus ω(ε) → 0 (NOT Lipschitz;
  choose the K-balanced bound `ω(ε) = max(ε^{p^{-K}}, ρ^K)`-style to stay in pow-form).
  (b3) **Per-coordinate modulus on Ainf**: digit-0 differences are exact
  (constantCoeff is additive): `v(a₀−b₀) ≤ w(a−b)`; recurse via head-split:
  `a = [a₀]+p·x'`, `b = [b₀]+p·y'`, `w(x'−y') ≤ ρ⁻¹·max(w(a−b), w([a₀]−[b₀]))` (using
  (b2)), and `aₙ₊₁ − bₙ₊₁ = x'ₙ − y'ₙ`. Gives: ∀ n ∃ modulus ωₙ with
  `|teichCoeff a n − teichCoeff b n| ≤ ωₙ(w(a−b))`, `ωₙ(ε) → 0` as `ε → 0` — exactly
  the uniform continuity needed for coordinates on the completion (T903).
  (b4) Extend to `Aloc/Bloc` by clearing `[ϖ]`/`p[ϖ]`-denominators (scaling lemma).

### [T903] Ar as Valued completion; realization; wAr; deg
- **Status**: done (beastmode 2026-07-26) — COMPLETE: the c0-architecture landed end-to-end.
  Final deliverables (all axiom-clean, pushed): the DECAY-CLOSURE CRUX in WittF.lean
  (tailValueF/headBoundF; prefix-pair digit bound `valuation_teichCoeffF_prefix_add_le`;
  the moving-prefix tail estimate `tailValueF_add_le` via the exact tail identity
  Z = C + X + Y with p^N-cancellation; head-decay split-max
  `tendsto_headBoundF_of_tendsto`; add-closure `tendsto_gaussTermF_add_of_tendsto`;
  perturbation (9) `tailValueF_add_le_gaussValueF`; w-closedness
  `tendsto_gaussTermF_of_w_approx`; tail-of-prefix identity `gaussValueF_sub_prefix`;
  `exists_iSup_eq_of_tendsto_zero`), and on ArCompletion.lean: Aloc-images decay
  (`tendsto_gaussTermF_alocToWittF`), `eventually_valued_sub_le`(+`_of_tendsto` generic),
  **`tendsto_gaussTerm_teichCoeffAr`** (limit coordinates decay — the crux application),
  **`PhiHatK_teichCoeffAr`** (the series realization x = Φ(coords x)),
  **`valued_eq_iSup_teichCoeffAr`** (Kedlaya (2.2.1) value formula on A^r), `wAr` +
  `wAr_apply`, `exists_valued_eq_teichCoeffAr` (attainment/degree existence).
  deg-def + deg_mul moved to T904's opening block (they live with the division
  algorithm per Kedlaya §2). Coordinate-UNIQUENESS (Φ-injectivity / teichCoeffAr∘Φ = id)
  deferred — file it into T904 only if the division bookkeeping needs it.
  ORIGINAL LOG (for archaeology): DONE (ArCompletion.lean, axiom-clean):
  wK (Gauss valuation on Frac(Ainf) via nonZeroDivisors-extendToLocalization, using
  gaussValue_pos_of_ne_zero), hatK := (wK).Completion (mathlib field machinery),
  toHatK with valued_toHatK (Valued.v ∘ toHatK = gaussValue, via valuedCompletion_apply),
  Aloc (abbrev, finally defined here), AlocToHatK/BlocToHatK (IsLocalization.lift,
  unit-values via map_pow through the gaussVal bundle), ArSub/BrSub :=
  range.topologicalClosure. REMAINING (exact next steps, in order):
  (1) DONE (`alocToWittF`, `isUnit_map_teichPi`, `alocToWittF_algebraMap`) — was: IsLocalization.lift of
      `WittVector.map (powerBoundedSubring.toSubring F).subtype` ([ϖ]-image is a unit:
      inverse `teichmuller p (ϖ⁻¹ : F)`, via map_teichmuller + teichmuller-mult +
      mul_inv_cancel₀ + teichmuller_one); injectivity (denominators map to nonzerodivisors);
  (2) DONE (`teichCoeffF_map` via `frobeniusEquivF_symm_subtype`/`_pow_subtype`) — was:
      (frobenius commutes with ring homs; symm-version by injectivity), hence
      `teichCoeffAloc := teichCoeffF ∘ alocToWittF` extends teichCoeff with
      [ϖ]-denominator scaling (scaling lemma teichCoeff_teichmuller_mul, F-version);
  (3) DECIDED (2026-07-26): common-denominator shortcuts are DEAD — counterexample
      sₘ = p^m·[ϖ^{-m/2}] is wAloc-small with unbounded denominators when ρ < √c. The
      honest route is the full W(F) value-port with BddAbove-threading:
      `gaussTermF ρ x n := ρⁿ·|teichCoeffF x n|`, `gaussValueF := ⨆` (with explicit
      `BddAbove (Set.range (gaussTermF ρ x))` hypotheses on every lemma — no global ≤1),
      ports of: term_le_value, add_le (level-rep machinery re-run over F: list engines
      port verbatim, pair bound via u-trick over F using Integers.exists_of_le_one on
      b/a), p_mul, sub_le (needs mul_le for neg — port submult too OR use -1 = [-1]…
      CAREFUL: over F use -x = (-1)·x and w((-1)x) via... port gaussValue_neg's argument
      needs submult; alternatively prove neg-invariance coordinatewise: teichCoeffF(-x) n
      = -teichCoeffF(x) n?? FALSE in general for p=2? no: -1 = [u]-Teichmüller in char p:
      (-1)^p = -1 so -1 = [-1] in W(F) for ALL p (p=2: -1=1 ✓ consistent): -x = [-1]·x:
      coords scale by -1 via teichCoeffF_teichmuller_mul-port: |coords| UNCHANGED ⟹
      w(-x) = w(x) COORDINATEWISE, no submult needed!! — ALSO backport this trick to
      simplify GaussNorm's gaussValue_neg in a later cleanup), boundedness-propagation
      through head-splits (tail-coords are shifted coords), then the (b3)-recursion
      verbatim. Deliverable: `exists_delta_teichCoeffF_sub` for W(F)-pairs with
      BddAbove-hyps — applied to Aloc-images (which are bounded: their w-values are
      wAloc-values via the embedding, bounded on Cauchy sequences).
STEP (3) COMPLETE (2026-07-26, all axiom-clean in WittF.lean):
      `exists_delta_teichCoeffF_sub` — per-coordinate ε-δ over W(F) on value-bounded
      boundedly-termed sets (m-generalized induction; heads via the scaled Teichmüller
      continuity `gaussValueF_teichmuller_sub_le_of_le_scaled`; tails via p-shift +
      m→m+K rescaling with c^K < ρ). Supporting F-layer all green: gaussTermF/ValueF,
      scaling, head split, pair bound, list engines + level rep + `gaussValueF_add_le`,
      `gaussValueF_p_mul`, transport (`gaussValueF_map`), boundedness lemmas for
      tails/sums/Teichmüller-differences. The [-1]-question was DODGED entirely: the
      only negation needed was digit-0 (additive, exact).
      (4) COMPLETE (2026-07-26): (4a) done, (4b) done (`gaussValueF_alocToWittF` attainment
      equality), (4c-i) done (`valued_AlocToHatK` bridge + `teichCoeffAr :=
      limUnder(comap AlocToHatK (𝓝 x)) coords` definition). (4c-ii) PARTIAL: `ball_mem_nhds_zero` +
      `exists_ball_subset_nhds` DONE (valuation balls are a neighborhood basis of 0 in
      F — ϖ^m·O_F-scaling one way, boundedness of O_F + top-nilpotent scaling the other;
      note `haveI := IsPerfectoidRing.uniform (p := p) (A := F)` needed for
      IsUniform.isBounded_powerBounded). NeBot done (`neBot_comap_of_mem_ArSub`,
      topologicalClosure-carrier is closure by rfl). BLOCKER FOUND for the ball/Cauchy
      steps: mathlib's Valued-lemmas (`Valued.mem_nhds`, `hasBasis_uniformity`) are
      stated via `v.restrict` into `(MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ`, NOT
      raw NNReal comparisons — the translation layer is
      `Valuation.restrict_lt_iff_lt_embedding` / `embedding_strictMono` /
      `restrict₀_apply` (see Mathlib/Topology/Algebra/Valued/ValuedField.lean ~520-566
      for worked patterns). RESOLVED (2026-07-26):
      `eventually_pair_wAloc_le` GREEN — approximant pairs of any x are eventually
      wAloc-close: cauchy_nhds.2 into hasBasis_uniformity's γ-ball with γ :=
      Units.mk0 (v.restrict z₀) for z₀ := toHatK(p^N), ρ^N < ε; the pair condition
      transfers via Valuation.restrict_lt_iff (SAME-valuation comparisons only — no
      value-group computation); prod_comap_comap_eq aligns the filters;
      valued_AlocToHatK converts to wAloc. tendsto_teichCoeffAr GREEN (the step-4 capstone: coordinates of A^r-elements
      converge along approximants; two-topology diamonds bridged by
      IsPerfectoidRing.topologyEq rewrites both at the W-neighborhood and at the
      completeness output). STEP-5 ROUTE REVISION (2026-07-26, after Lemma A `gaussTerm_teichCoeffAr_le` went
      green): the (≥)-direction CANNOT go through approximant-attainment transfer —
      attaining indices are NOT uniformly bounded over the filter (the p^m[ϖ^{-m/2}]
      denominator demon again), and per-index limits control only finitely many terms.
      CORRECT ORDER: (5b-i) DONE (alocTeich + alocToWittF_alocTeich + wAloc_alocTeich +
      exists_finite_teichmuller_sum_close, all axiom-clean; the h2gen-pattern:
      generalize auxiliary inductions over a FRESH variable, never over an index the
      context mentions). Was: **finite-Teichmüller-sum density**: the subring of finite
      sums Σ_{n<N} pⁿ·[cₙ] (cₙ ∈ F) is dense in Aloc for every wAloc (CORE-2 on the
      Ainf-numerator + [ϖ]^{-k}-scaling — tails of prefixes are ρᴺ-small), hence its
      image is dense in ArSub; define `alocTeich : F → Aloc` (choice: Tate absorption
      → O_F-numerator/[ϖ]^k) with `alocToWittF (alocTeich c) = teichmuller p c` and
      `wAloc (alocTeich c) = |c|`. (5b-ii/iii) ROUTE SUPERSEDED (2026-07-26 second revision): direct reconstruction
      hits the coordinate-decay knot — Hölder moduli degrade in n, so no finite-δ
      controls infinitely many coordinates, and digit-nonadditivity blocks transfer
      through differences. THE C₀-ARCHITECTURE instead (classical, no perturbation
      analysis): (A) SeqSpace := {b : ℕ → F // Tendsto (fun n => ρⁿ·|bₙ|) atTop (𝓝 0)};
      (B) Φ b := limit in hatK of images of prefixes Σ_{n<N} pⁿ·alocTeich(bₙ)
      (Cauchy: consecutive differences have value ρᴺ|b_N| → 0; Valued-completeness of
      hatK); (C) ISOMETRY: Valued.v (Φ b) = ⨆ n, ρⁿ|bₙ| — prefix values are exact
      finite maxima (wAloc of finite sums = max of terms: compute via
      gaussValueF_alocToWittF + F-CORE-1 coords of finite sums + attained finite sup),
      pass to the limit by isosceles; (D) Φ-image is complete (isometric image of the
      complete SeqSpace — prove SeqSpace-Cauchy ⟹ coordinatewise-Cauchy + uniform
      tail control, c₀-style) hence closed, contains the Aloc-image densely
      (exists_finite_teichmuller_sum_close!) ⟹ image = ArSub; (E) uniqueness of the
      preimage sequence + consistency with tendsto_teichCoeffAr gives teichCoeffAr-
      decay, reconstruction, AND the realization equality (with Lemma A already green)
      all at once. IMPLEMENT (B)+(C) for FIXED b first (no SeqSpace-topology needed:
      state Φ as a def + its value; completeness of SeqSpace can be replaced by:
      every ArSub-element is hit — prove surjectivity directly: given x, the
      coordAr-sequence… NO that needs decay again. Honest order: SeqSpace-completeness
      IS needed; alternatively dodge once more: ArSub ⊆ Φ-image ⟸ Φ-image closed ∧
      ⊇ dense subset; closedness ⟸ completeness of SeqSpace + isometry. So: (A)(B)(C),
      then SeqSpace-complete, then (D)(E).) THEN attainment
      (wAr x = sup ρⁿ|teichCoeffAr x n|, attained — via the eventual bounds +
      coordinate limits + gaussValueF_alocToWittF), then deg/deg_mul/Rem-2.7/summability,
      unlocking T904 (Euclidean division). Historical assembly notes:
      (i) eventual value-bound B via one small set from eventually_pair_wAloc_le at
      ε := 1 + a base point u₀ (NeBot), B := max (wAloc u₀) 1... wAloc u ≤
      max(wAloc(u−u₀), wAloc u₀)-ultrametric; pick M with (c⁻¹)^M ≥ B;
      (ii) Cauchy (map coords L): for V ∈ 𝓝(0:F)-entourage-side use
      uniformity_eq_comap_nhds_zero F + exists_ball_subset_nhds → c^m-ball;
      exists_delta_teichCoeffF_sub p F ϖ n hρ0 hρ1 M (ε := min (c^m) 1) → δ;
      eventually_pair_wAloc_le at δ + hyps (bddAbove via bddAbove_gaussTermF_alocToWittF,
      differences boundedly-termed since u−u' ∈ Aloc, values via gaussValueF_alocToWittF
      + (i)) give coord-pairs in the ball ⊆ V;
      (iii) CompleteSpace F (haveI := IsPerfectoidRing.complete p F) → limit;
      Tendsto.limUnder_eq needs T2 F (haveI t0 + IsTopologicalAddGroup.t2Space-chain);
      unfold teichCoeffAr. OLD notes (superseded):
      `valued_ball_mem_nhds : {z : hatK | Valued.v (z − x) < (δ : NNReal)} ∈ 𝓝 x` for
      δ ≠ 0 (via mem_nhds + the embedding-strictMono translation, choosing γ :=
      the image of δ under the valueGroup₀-equiv — OR dodge entirely: prove the
      Cauchy-condition using `Valued.hasBasis_uniformity`'s γ-balls directly and
      TRANSLATE only the pair-condition v.restrict(f u' − f u) < γ into
      wAloc(u'−u)-smallness via restrict-monotonicity: since only ≤-COMPARISONS between
      values of the SAME valuation are needed, the strictMono embedding transfers them
      without computing γ). Then: eventual value-bound from ONE small-set (Cauchy ⟹
      ∃ S ∈ L small: all u,u' ∈ S have wAloc(u−u') ≤ 1, fix u₀ ∈ S: wAloc u ≤
      max(wAloc u₀, 1) =: B, pick M with (c⁻¹)^M ≥ B — NO x-ball needed!), then
      exists_delta_teichCoeffF_sub-application, F-complete limit, Tendsto.limUnder_eq
      (T2 F from t0 + group instances). The Tendsto-characterization for x ∈ ArSub — NeBot from closure-membership
      (mem_closure_iff_nhds_neBot + comap-transfer), Cauchy of the pushed filter via
      exists_delta_teichCoeffF_sub (hyps: approximant-terms bounded (4a), differences
      are Aloc-images with wAloc = Valued.v-difference by the bridge, value-bounds
      (c⁻¹)^m ≥ max(v x, 1) by ultrametric ball-constancy near x), F complete
      (IsPerfectoidRing.complete), Tendsto.limUnder_eq. `wAloc` defined (mirror);
      `gaussTermF_alocToWittF_le` DONE (dense-layer term bound: every Aloc-image is
      boundedly termed with terms ≤ wAloc-value; via IsLocalization.surj +
      teichmuller-scaling + c^k-cancellation; note the teichPi-rw-in-type trap: use
      compound-pattern haves (hteich) since teichPi occurs in Aloc's TYPE index).
      NEXT within (4): (4b) attainment equality `gaussValueF (alocToWittF u) = wAloc u`
      (≥ via exists_gaussValue_eq_gaussTerm on the numerator, scaled); (4c) coordinate
      filters: for x ∈ ArSub define teichCoeffAr x n := lim of coords along
      comap AlocToHatK (𝓝 x) (NeBot from closure-membership; Cauchy via
      exists_delta_teichCoeffF_sub applied to differences of approximants — approximants
      are boundedly-termed (4a) with values eventually ≤ v(x)+ball-const, i.e. pick m
      with (c⁻¹)^m ≥ that; differences are Aloc-images hence boundedly termed);
      F complete (IsPerfectoidRing.complete) gives the limit; characterize by
      `Tendsto`. (4d) also relate Valued.v x to the coordinate data (attainment on the
      completion) — that is step (5).
      (5) reconstruction + attainment (wAr x = max ρⁿ|xₙ|, attained) on ArSub; then
      deg := largest attaining index, deg_mul (T803-mirror), Rem-2.7, summability —
      unlocking T904 (Euclidean). Br-vs-Ar[1/p] deferred until needed | **File**: FarguesFontaine/WittF.lean | **Depends**: T902
- **REVISED per AD-3-revision**: `Aloc := Localization.Away (teichPi p F ϖ)`; wAloc :=
  extendToLocalization of gaussVal (mirror of T901 for the ϖ-only localization);
  `Ar ρ := UniformSpace.Completion (WithVal (wAloc ρ))` with mathlib `Valued`-instance
  and `Valued.extension`; **realization theorems**: extended coordinates
  `teichCoeffAr : Ar → F` (n-indexed ℤ after p-clearing — for Ar the index is ℕ on the
  Aloc-side times [ϖ]-denominators; precise indexing fixed in implementation) via T902(b)
  + Completion.denseInducing; reconstruction + attainment `wAr x = max ρⁿ|xₙ|`;
  `deg x := largest attaining index` for x ≠ 0; `deg_mul` (T803-mirror on the
  realization), `deg_eq_of_lt` (Rem 2.7); summability of `Σ zₗ` with `wAr zₗ → 0`
  (completion: Cauchy prefix sums — now FREE).
- **Source quotes**: Def 2.4 ln 100–106; Def 2.5 ln 115–118; Rem 2.7 ln 137–139.

### [T904] Euclidean division on Ar; Ar is a PID
- **Status**: done (beastmode 2026-07-26) | **File**: FarguesFontaine/Euclidean.lean | **Depends**: T903 (done)
- **DONE-AS-SCOPED**: the full Kedlaya §2 chain is machine-checked, axiom-clean, and
  pushed: (2.8.1) homogeneity (binary ± and n-ary), degAr + spec + strict drop,
  Lemma-2.8 ε, convolution layer, (DC⁺), **Remark 2.7** (leading-support stability),
  product decomposition, **Lemma 2.6** (degAr_mul), the division quotient (divStep),
  the (2.8.2) coefficient analysis, **descent_step**, division_descent,
  **Lemma 2.8** (approx_division), tendsto_of_valued_sub_le, **Prop 2.9**
  (exact_division, remainder `= 0 ∨ deg <`-form), **Cor 2.10 as
  `isPrincipalIdealRing_ArSub`** (minimal-degree generator; the mathlib
  `EuclideanDomain`-STRUCTURE fields were deliberately skipped — the PID instance is
  the T905-facing payload; file a follow-up only if Gröbner needs the structure).
  Full library green (3315 jobs).
- **Progress**: Euclidean.lean created. DONE (axiom-clean): `gaussValueF_map_le_of_coeff_zero`
  (normalized homogeneity master: integral + zeroth-coordinate-0 ⟹ value ≤ ρ, via the
  CORE-2 split at 1 + constantCoeff), `gaussValueF_zero`, `exists_attaining_coeff`,
  **(2.8.1) binary forms** `gaussValueF_teichmuller_add_sub_le` and
  `gaussValueF_teichmuller_sub_sub_le` (scaling proofs — divide by the max-attaining
  coefficient, land in W(O_F), constantCoeff kills digit 0 regardless of signs; NB
  `[-1] = -1` is FALSE at p = 2, so sign-handling MUST go through constantCoeff, never
  through Teichmüller-negation). NEXT (in order): (i) n-ary/list (2.8.1)
  `gaussValueF_teichmuller_list_sum_sub_le` by induction on the binary form (+ F-side
  ultrametric |L.sum| ≤ max); (ii) Remark 2.7 (v(x−y) < v x ⟹ same value and same
  degAr — isosceles first); (iii) degAr def (largest attaining index via
  Nat-sSup of the attainment set, bounded by decay) + degAr_spec upper/attain;
  (iv) deg_mul (Lemma 2.6 specialization) via leading-coefficient dominance:
  strict domination off (d₁,d₂) on the antidiagonal + (2.8.1)-error ρ-shrink;
  (v) Lemma 2.8 (approximate division; the (2.8.2) T-polynomial bookkeeping);
  (vi) Prop 2.9 (geometric iteration, summability via PhiHatK-machinery);
  (vii) Cor 2.10 EuclideanDomain + IsPrincipalIdealRing instances on ArSub.
- **Progress 2 (2026-07-26, sol-validated deg-layer COMPLETE, all axiom-clean)**:
  the full gpt-5.6-sol plan (archived `chatgpt-reply-degmul-2026-07-26.md`) landed:
  n-ary (2.8.1) `gaussValueF_teichmuller_sum_sub_le`; degAr + `degAr_spec` +
  `gaussTerm_lt_of_degAr_lt`; Lemma-2.8 ε `exists_eps_terms_le`; convolution layer
  (`convF`, `tendsto_antidiagonal_sup_zero`, `tendsto_convF`, `gaussTerm_convF_le`);
  Φ-coordinate recovery `teichCoeffAr_PhiHatK` + `teichCoeffAr_zero` (ArCompletion);
  **(DC⁺)** `digit_sub_le`; **Remark 2.7** `valued_eq_of_valued_sub_lt` +
  `degAr_eq_of_valued_sub_lt` (leading-support stability); product decomposition
  `convPartialAloc`/`alocToWittF_convPartialAloc`/(I₂)`gaussValueF_convPartial_sub_prefix_le`/
  (I₁)`gaussValueF_prefix_mul_sub_convPartial_le`/`valued_mul_sub_PhiHatK_convF_le`;
  `valued_degAr_PhiHatK_convF` (unique dominant antidiagonal term); **`degAr_mul`**
  (Kedlaya Lemma 2.6 at the single radius — honest proof of what the source leaves
  to "convex duality"). **LEMMA 2.8 COMPLETE** (2026-07-26,
  axiom-clean): divStep (the Φ-series quotient) + tendsto_div_shift + divStep_mem +
  valued_divStep_le + valued_sub_divStep_mul_le; valued_sub_sub_PhiHatK_le (the H∞
  block standalone); gaussTerm_sub_convF_divStep_le (the (2.8.2) coefficient
  analysis: exact j = m cancellation, ε-damped j > m, c-damped j < m, multiplied-out
  denominators); **descent_step** (coordinate terms from N on pushed below c);
  division_descent (strong induction on the window K; K = 0 closes by the value
  formula); **approx_division** = Lemma 2.8. NEXT: Prop 2.9 (exact division — the
  geometric iteration: recursive (y_l, z_l), partial z-sums Cauchy by ε^l-decay,
  ArSub closed so z lands inside, stabilization-vs-vanishing dichotomy; NB state the
  remainder condition as `w = 0 ∨ degAr w < degAr x` — deg 0 = -∞ convention needs
  the disjunction with our ℕ-junk degAr 0 = 0), then Cor 2.10 (EuclideanDomain +
  IsPrincipalIdealRing on the ArSub subring — mathlib structure on the subtype).
- **Statement**: Lemma 2.8 (approximate division): for x ≠ 0 ∃ ε ∈ (0,1) s.t. ∀ y ∃ z w:
  `y = z*x + w ∧ wAr w ≤ wAr y ∧ (wAr w > ε·wAr y → deg w < deg x)`. Prop 2.9 (exact):
  `∀ x ≠ 0, ∀ y, ∃ z w, y = z*x + w ∧ wAr w ≤ wAr y ∧ deg w < deg x`. Cor 2.10:
  `EuclideanDomain (Ar ρ)` (deg into ℕ; mul_left_not_lt from deg_mul) + PID instance.
- **Sketch** (transcribe ln 141–216 faithfully): ε with `ρ ≤ ε` and
  `wCoeff x n ≤ ε·wAr x` for n > m := deg x. Iteration: `zₗ := Σ pⁿ[y_{l,n+m}/x_m]`
  (coefficientwise quotient by the leading coefficient — legal in F), `y_{l+1} = yₗ − zₗx`;
  the (2.8.2) T-polynomial bookkeeping bounds the ε-support top index Nₗ strictly down —
  well-founded. Prop 2.9: geometric iteration of 2.8, `wAr zₗ ≤ ε^l·wAr y/wAr x → 0`,
  summability from T903. EuclideanDomain: mathlib structure on the subtype.

### [T905] Gröbner data on Ar⟨X₁..Xₖ⟩
- **Status**: done (beastmode 2026-07-26) — ALL Gröbner data built in
  FarguesFontaine/Groebner.lean, axiom-clean and pushed: the restricted-series bridge
  (`valued_ball_mem_nhds_zero`, `exists_valued_ball_subset`, `isRestricted_iff_valued`),
  `NonarchimedeanRing` instances for `hatK` and the `ArSub` subring, the radius-1 Gauss
  norm (`gaussNormRPS`, `exists_iSup_eq_of_finite_above`, `exists_gaussNormRPS_eq`,
  `gaussNormRPS_ne_zero`, `bddAbove_coeff_valued`), attainment sets
  (`attainSetRPS` + finite + nonempty), **Def 3.6** (`leadIdxRPS` via
  `MonomialOrder.degLex`, `leadIdxRPS_spec`, `leadCoeffRPS`), the monomial-shift trio
  (`coeff_monomialShift`, `isRestricted_monomialShift`, `gaussNormRPS_monomialShift`,
  `monomialShift_ne_zero`, `attainSetRPS_monomialShift`, `leadIdxRPS_monomialShift`,
  `leadCoeffRPS_monomialShift`), **Def 3.7** (`degSetIdx`, `degSetIdx_subset`, `dIdx`,
  `dIdx_antitone`, `dIdx_le_of_mem`, `degSetIdx_nonempty`, `exists_leadIdx_degAr_eq`),
  and **the Gröbner set S** (`finite_minimal`, `exists_minimal_le`, `groebnerPairs`,
  `groebnerSet`, `groebnerSet_finite` by Dickson, `exists_mem_groebnerSet_le`).
  NB the product-order trick (minimal pairs in `(Fin k →₀ ℕ) × ℕ`) replaces Kedlaya's
  two-step "finitely many minimals, hence bounded degrees" bookkeeping. | **File**: FarguesFontaine/Groebner.lean | **Depends**: T903, T904 (both done); repo A⟨X⟩
- **DESIGN (banked 2026-07-26 after full §3 re-read, ln 217-330)**: work over
  `Ar := ↥(ArSub p F ϖ hρ0 hρ1)` with the REPO predicate
  `restrictedMvPowerSeriesSubring k Ar` (RestrictedPowerSeries.lean; coefficients → 0
  cofinitely in the SUBSPACE topology) — radius 1 = AD-5; target
  `IsStronglyNoetherian Ar` (∀ k, IsNoetherianRing of that subring).
  FOUNDATION (build first): `isRestricted_iff_valued`: topological cofinite-decay of
  coefficients ⟺ NNReal-value decay (∀ε>0, {I : v f_I > ε} finite) — via the subtype
  nhds-comap + Valued.mem_nhds γ-balls + the z₀ := toHatK(p^N) cofinality trick (both
  directions; the eventually_valued_sub_le-pattern). Then: gaussNormRPS f := ⨆ I,
  v(f I) (bddAbove from decay); attainment (finitely many above any ε);
  leading index := degLex-max of the attainment set — mathlib `MonomialOrder.degLex`
  (CHECK availability; else hand-roll graded-lex on Fin k →₀ ℕ: it's a linear order
  refining ≤ with finite lower-≺-sets via bounded total degree);
  d_I : (Fin k →₀ ℕ) → ℕ∞ := ⨅ over H-elements with leading index I of degAr of the
  leading coefficient (∞ if none); monotone antitone d_{I₂} ≤ d_{I₁} for I₁ ≤ I₂
  (multiply by the monomial T^{I₂−I₁} — monomial-mult shifts coefficients, norm
  multiplicative-per-monomial); S := finitely many ≤-minimals of {d_I < ∞} per level d
  (Dickson: mathlib `Finsupp` PWO — CHECK `Finsupp.isPWO`/`Set.IsPWO` machinery);
  choose x_I. T906 = Lemma 3.8 (ε := max ratio over I ∈ S, J ≻ I — finite by the
  finite-lower-≺-property; iteration with exact_division on leading coefficients; the
  E_l ε-support bookkeeping + J₊ + infinitely-recurring-J + Remark-2.7 (degAr_eq_of_
  valued_sub_lt on Ar-elements!) contradiction). T907 = Lemma 3.9 (geometric sum,
  completeness of the restricted subring — repo API?) ⟹ IsNoetherianRing (ideal =
  span of finite S: `Ideal.fg` for all H) ⟹ IsStronglyNoetherian Ar.
  NOTE: Kedlaya's H-ideal machinery needs CHOICE of x_I per I ∈ S (Classical.choose
  as in exact_division). All §2-inputs exist: degAr/degAr_mul/Remark 2.7/Prop 2.9.
- **Statement**: for the repo's `RestrictedPowerSeries` over `Ar` (Gauss norm, radius 1
  per AD-5): leading index (graded-lex-maximal norm-attaining multi-index, Def 3.6
  ln 267–270 — attainment from coefficient decay), leading coefficient; `d_I`-function
  and the finite Gröbner set S (Def 3.7 ln 273–283; Dickson: `(Fin k →₀ ℕ, ≤)` is a WQO —
  use mathlib `MonomialOrder`/`Finsupp` WQO machinery, else prove Dickson by induction);
  monotonicity `I₁ ≤ I₂ → d_{I₂} ≤ d_{I₁}` (multiply by the monomial `T^{I₂−I₁}`,
  norm-multiplicativity of monomial scaling).
- **Quote** (ln 273–283): "the set of I for which d_I < +∞ contains only finitely many
  minimal elements ... For each I ∈ S, choose x_I ∈ H∖{0} with leading index I and
  leading coefficient of degree d_I."

### [T906] Lemma 3.8: approximate ideal generation
- **Status**: done (beastmode 2026-07-26) | **File**: FarguesFontaine/Groebner.lean | **Depends**: T904, T905 (both done)
- **DONE**: `approx_generation` is Kedlaya Lemma 3.8, axiom-clean. Chain built:
  `exists_tail_bound_lt` → `exists_normalized_tail_bound` → **`exists_groebner_family`**
  (finite generator set + one 0 < ε < 1 + leading data + domination);
  `gaussNormRPS_add_le/_neg/_sub_le/_monomial/_zero`, `valued_coeff_le_gaussNormRPS`;
  the step layer `coeff_monomialMul_pos/_neg`, `isRestricted_monomialMul`,
  `coeff_sub_monomialMul_lead`, **`groebner_step`** and its ideal-level wrapper
  **`groebner_reduce`**; the frozen-zone lemmas `valued_degAr_eq_of_sub_lt`,
  `coeff_sub_eq`, `coeff_frozen`; and the TERMINATION (sol-validated, archived at
  `.mathlib-quality/chatgpt-reply-termination-2026-07-26.md`): `coeffRank`,
  `coeffRank_eq_of_diff_le`, `coeffRank_lt_of_drop`, `support_step_subset`,
  `finite_degree_le`, `finite_degLex_le`, `degLexSeg` (+Fintype/LinearOrder),
  **`muMeasure`** (Colex rank vector) and `muMeasure_lt`, `exists_degLex_max`.
  KEY correction from the consult: the fixed finite index set is the graded-lex
  INITIAL SEGMENT below M := max of the ε-support of y₀, NOT a componentwise box.
  PERFORMANCE NOTES for the cleanup pass: several declarations carry
  `set_option maxHeartbeats 2000000` — the `ArSub`/`hatK` abbrevs are reducible so
  unification is deep-but-fast; the fixes that mattered were (i) abstract
  index/coefficient parameters instead of `leadIdxRPS` in statements, (ii) if-free
  wrapper lemmas for `coeff_monomial_mul`, (iii) small-context coercion bridges
  (`coe_sub_monomialMul`) instead of `MulMemClass.coe_mul` rewriting.
- **Statement**: ∃ ε ∈ (0,1): ∀ y ∈ H ∃ (a_I)_{I∈S}: `|a_I|·|x_I| ≤ |y|` and
  `|y − Σ a_I x_I| ≤ ε|y|`.
- **Sketch** (transcribe ln 285–320): ε := max over I ∈ S, J ≻ I of |x_{I,J}T^J|/|c_I T^I|
  (or any ε if that set is empty). Iteration: leading index Jₗ of yₗ, pick Iₗ ∈ S with
  Iₗ ≤ Jₗ, d_{Iₗ} = d_{Jₗ}; divide leading coefficients by Prop 2.9; the ε-support
  argument (El sets, J₊ bound, the largest infinitely-recurring index J, Rem-2.7 finish)
  gives the contradiction. Strictly-decreasing/finitely-bounded ≺-data: well-founded.

### [T907] Lemma 3.9 + Theorem 3.2: Ar is strongly noetherian
- **Status**: done (beastmode 2026-07-26) | **File**: FarguesFontaine/Groebner.lean | **Depends**: T906 (done)
- **DONE — the §3 capstone is machine-checked, axiom-clean, pushed**:
  `exists_series_limit` (ultrametric series converge in the closed subring A^r),
  `exists_rps_series_limit` (the same in the Tate algebra: coefficientwise limits,
  restrictedness by a finite-union superlevel argument, Gauss-norm tail estimates),
  `gaussNormRPS_mul_le` (submultiplicativity via the antidiagonal),
  `gaussNormRPS_finset_sum_le`, the generic algebra helpers
  `sum_range_sum_attach_mul` / `telescope_split` (stated over an abstract CommRing so
  the sum manipulation elaborates cheaply) and `coe_RPS_add/_mul/_neg`;
  **`ideal_eq_span_groebner`** (Lemma 3.9: H = span G, by the geometric iteration of
  Lemma 3.8 and the convergent coefficient series);
  **`isNoetherianRing_restrictedMvPowerSeries`** and the instance
  **`isStronglyNoetherian_ArSub`** (Theorem 3.2).
  Full library green (3317 jobs). PERFORMANCE: Lemma 3.9 carries
  `maxHeartbeats 8000000` — the RPS-level sum rewrites are deep-but-fast; the cleanup
  pass should split it or (better) make `hatK`/`ArSub` non-reducible.
- **Statement**: every ideal H of `Ar⟨X₁..Xₖ⟩` is generated by the finite set
  {x_I : I ∈ S}; hence `IsStronglyNoetherian (Ar ρ)` (repo predicate; radius-1 per AD-5).
- **Sketch** (ln 322–330): geometric iteration of T906, `|yₗ| ≤ ε^l|y|`, sums converge
  (Tate-algebra completeness — repo RestrictedPowerSeries API), `y = Σ_I a_I x_I`.

### [T908] λ_I, BI, three circles, coordinate continuity
- **Status**: in_progress (beastmode 2026-07-26) | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T901, T902 (done)
- **DESIGN REVISION (2026-07-26, after §2+§3 completed)** — AD-7 is *implemented* by the
  product-of-completions trick rather than by SeminormedRing plumbing (mathlib has no
  `RingSeminorm → SeminormedRing` constructor, and our norms are NNReal-valued):
  * `BIProd ρ₁ ρ₂ : Bloc →+* hatK ρ₁ × hatK ρ₂ := (BlocToHatK ρ₁).prod (BlocToHatK ρ₂)`;
  * **`BISub := (BIProd).range.topologicalClosure`** — a closed subring of a complete
    product, i.e. exactly the completion of `Bloc` for the max-of-two-valuations
    uniformity (mirrors `ArSub`/`BrSub` from T903, so all the T903 machinery —
    `cauchySeq_of_valued_le`, `eventually_valued_sub_le`, closedness, coordinate
    limits — ports coordinatewise);
  * `wI z := max (Valued.v z.1) (Valued.v z.2)` on the product, restricted to `BISub`:
    submultiplicative + ultrametric, and multiplicative on each factor;
  * Cor 4.5 (`wI = sup over the interval`) is only needed through its CONSEQUENCES
    (restriction maps + injectivity), so state those directly (T909);
  * three circles (Lemma 4.4) needs NNReal.rpow interpolation — postpone until a
    downstream proof actually consumes it; the campaign path to Thm 4.10 goes through
    Lemma 4.9's presentations, which use only the two endpoint norms.
  Build order: (a) `BIProd`/`BISub` + subring/complete/closed facts; (b) the two
  coordinate valuations and `wI` with its norm axioms; (c) the coordinate realization
  transported from T903 (each factor lands in `BrSub`); then T909-T912.
- **PROGRESS (beastmode 2026-07-26, all axiom-clean, pushed, library green)**:
  (a) DONE — `BIProd`, `BIProd_fst/_snd`, **`BISub`**, `isClosed_BISub`,
  `BIProd_mem_BISub`, **`isComplete_BISub`**, `cauchySeq_of_wI_le`,
  **`exists_BI_series_limit`**;
  (b) DONE — **`wI`** with `wI_zero/_one/_add_le/_mul_le/_neg/_eq_zero_iff/_BIProd`;
  plus `BISub_fst_mem`/`BISub_snd_mem` (coordinates land in the endpoint rings),
  `valued_ball_mem_nhds`, **`exists_BIProd_wI_le`** (quantitative density);
  **Lemma 4.4 (three circles)** at both levels: `gaussTerm_rpow_interpolate`,
  `gaussValue_rpow_interpolate`, `rpow_interpolate_lt_one`, `wLoc_rpow_interpolate`,
  and **`wLoc_le_max_of_interpolate`** = Corollary 4.5 in usable form.
  (c) REMAINING, and it carries an OPEN DESIGN QUESTION: the B^I coordinate
  realization needs coordinates on `BrSub`, and Kedlaya's `B^r := A^r[1/ϖ_E] = A^r[1/p]`
  (Def 2.4) is a LOCALIZATION, whereas our `BrSub` is the closure of the `Bloc`-image.
  Decide (and record as AD-8) whether to (i) prove `BrSub = A^r[1/p]` — i.e. that the
  closure is already the localization, which needs a bounded-denominator argument that
  the p^m[ϖ^{-m/2}] demon makes delicate — or (ii) define the coordinates on `BrSub`
  directly by the same limit construction as `teichCoeffAr` (comap along `BlocToHatK`),
  reusing T903 verbatim with `Bloc`/`wLoc` in place of `Aloc`/`wAloc`. Option (ii)
  looks strictly easier and avoids the demon; prefer it unless a downstream proof needs
  the algebraic description.
- **Statement**: for `I = [ρ₁,ρ₂] ⊂ (0,1)` (endpoints in c^ℚ per AD-4):
  `wI := fun x => max (wLoc ρ₁ x) (wLoc ρ₂ x)` (power-multiplicative ring norm);
  `BI := UniformSpace.Completion (Bloc, wI-uniformity)` as a NormedRing (AD-7);
  three-circles (Lemma 4.4 ln 344–352: reduce to single terms `pⁿ[xₙ]` where equality;
  in ρ-form: `wLoc ρ^θ... ≤ wLoc ρ₁ ^θ · wLoc ρ₂ ^{1−θ}` for the geometric interpolation)
  ⟹ `wI = sup {wLoc ρ, ρ ∈ I}` (Cor 4.5); coordinate-continuity on wI-balls
  (Hölder: source Kedlaya 1004.0466 Thm 4.5, transcribe) ⟹ extended coefficient
  functionals `teichCoeffI : BI → F` and the series realization of BI-elements
  (two-sided decay description).
- **NOTE**: this is the hardest *infrastructure* ticket; sequence AFTER T907 unless
  parallel capacity exists.

### [T909] Restriction maps BI → BI'
- **Status**: done (2026-07-26, beastmode) — `resIHom : B^I →+* B^{I'}` bundled
  (IntervalRing.lean, was already built) and **Cor 4.6 injectivity proven**:
  `resIHom_injective` in the new FarguesFontaine/RestrictionInjective.lean, via
  `valued_resI_rpow_interpolate` (three circles for resI-values, by approximant
  limits with ε-padding — no valuation-continuity needed),
  `resI_eq_zero_of_interior` (weight-on-the-vanishing-point propagation), and
  `wLoc_le_of_interior_bound` (endpoint continuity, per Teichmüller term). All
  axiom-clean. Interior-parameter targets (0 < θ < 1), which per AD-9 covers every
  strict sub-interval the curve needs.
  DONE (axiom-clean, pushed): `valued_BlocToHatK_le_wI`, `valued_BlocToHatK_sub_le_wI`
  (the wI-Lipschitz bounds from Cor 4.5), `neBot_comap_of_mem_BISub`,
  `eventually_pair_wI_le`, `exists_nnreal_lt_gamma`, `wI_ball_mem_nhds`, **`resI`** and
  **`tendsto_resI`** (the map exists as the limit of approximant images),
  `resI_BIProd` (it extends the endpoint map), `map_add_comap_le`, `map_mul_comap_le`,
  **`resI_add`**, **`resI_mul`**.
  NEXT: `resI` lands in `B^{[σ,σ]}`-style targets (or directly: the pair
  `(resI σ₁ z, resI σ₂ z)` lands in `BISub σ₁ σ₂`), then bundle as a `RingHom`
  `B^I → B^{I'}` and prove injectivity via three circles (Cor 4.6).
  | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T908
- **Statement**: for I' ⊆ I: continuous ring hom `res : BI → BI'` (Completion-functorial
  from `wI' ≤ wI` on Bloc via Cor 4.5), injective (Cor 4.6 ln 361–368: λ_t = 0 on I'
  propagates by three-circles + continuity).

#### T909 injectivity sub-tickets (spawned 2026-07-26, beastmode; parent T909)

All in new `FarguesFontaine/RestrictionInjective.lean` (imports Presentation for
`exists_BIProd_approx`). Source: Kedlaya Cor 4.6 proof (three circles with the weight
on the vanishing point + endpoint continuity). Generality: interior-parameter
sub-intervals (0 < θ, η < 1), which per AD-9 covers every strict sub-interval needed.

### [T909a] Three circles for the intermediate values of B^I
- **Status**: done (2026-07-26) | **Parent**: T909 | **Type**: lemma
- **Statement**: for `z ∈ BISub`, parameters `α', α'' ∈ [0,1]`, weight `c ∈ [0,1]`:
  `v (resI τ(c·α'+(1−c)·α'') z) ≤ v (resI τ(α') z) ^ c * v (resI τ(α'') z) ^ (1−c)`.
- **Sketch**: limit of `wLoc_rpow_interpolate` along the approximant filter
  (`tendsto_resI` at the three radii + `Valued.continuous_valuation` +
  `le_of_tendsto` with NNReal rpow/mul continuity); radius identification by rpow
  algebra (`τ(α')^c·τ(α'')^{1−c} = τ(c·α'+(1−c)·α'')`).

### [T909b] Endpoint value from interior bounds (Bloc-level continuity)
- **Status**: done (2026-07-26) | **Parent**: T909 | **Type**: lemma ×2
- **Statement**: for `x : Bloc`, `ε`: if `wLoc (τ(α)) x ≤ ε` for all `α ∈ (0,1)`,
  then `wLoc ρ₂ x ≤ ε` (and the mirror `wLoc ρ₁ x ≤ ε`).
- **Sketch**: write `x·(p[ϖ])ᵏ = a`; per Teichmüller term `n`:
  `τ(α)ⁿ·|aₙ| ≤ gaussValue τ(α) a = wLoc x·(τ(α)|ϖ|)ᵏ ≤ ε·(τ(α)|ϖ|)ᵏ`; take a
  sequence `α_m → 0` (resp. `→ 1`), so `τ(α_m) → ρ₂` (resp. `ρ₁`) by rpow
  continuity in the exponent, and pass each term inequality to the limit
  (`le_of_tendsto`, continuity of `t ↦ tⁿ|aₙ|` and `t ↦ ε(t|ϖ|)ᵏ`); then `ciSup_le`.

### [T909c] Cor 4.6: injectivity of the restriction hom
- **Status**: done (2026-07-26) | **Parent**: T909 | **Type**: theorem
- **Statement**: `Function.Injective (resIHom …)` when the first target parameter is
  interior (`0 < θ < 1`).
- **Sketch**: kernel-trivial (`injective_iff_map_eq_zero`). From `resI τ(θ) z = 0`:
  every interior `α` has `v(resI τ(α) z) = 0` by T909a with the weight on the
  vanishing point (`α ≤ θ`: interpolate with `τ(0)`, `c = α/θ`; `α ≥ θ`: with
  `τ(1)`, `c = (1−α)/(1−θ)`; `0^c = 0` for `c > 0`). Then for each `ε`: approximate
  `z` by `BIProd x` within `ε` (`exists_BIProd_approx`); `wLoc τ(α) x ≤ ε` for all
  interior `α` (resI additivity + `valued_resI_le_wI` + the vanishing); T909b gives
  the endpoint values `≤ ε`; ultrametric max gives `v(z.i) ≤ ε`; conclude `z = 0`.

### [T910] Lemma 4.9, first two presentations
- **Status**: open | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T907, T908
- **Statement** (untwisted form; z := ϖF^{a/b}-powers, radii in c^ℚ, rescale per AD-5):
  `BI⟨T⟩/(T − [z]·unit-rescaled) ≅ B^{I∩[...]}` and the `[z⁻¹]`-variant — the exact
  endpoint arithmetic per Kedlaya ln 380–392, transported through ρ = p^{-1/t}.
  Strictness, closed ideal, injectivity, surjectivity with (4.9.1)-norm control, and the
  ρ ∈ p^ℚ (here c^ℚ) plus-ring statement (integral closures of images).
- **Sketch**: transcribe ln 394–460 (the four-paragraph proof) with the T908 coefficient
  realization; the geometric-series unit case for empty intersections (ln 396–399).

### [T911] Lemma 4.9, third presentation (Ar → BI bridge)
- **Status**: done (2026-07-26, beastmode; commit da830e1a9) — density half (evalRange,
  BIProd_mem_evalRange, BISub_le_topologicalClosure_evalRange) + strictness half
  (exists_evalAr_eq_of_mem_BISub: every element of B^I lifts with gaussNormRPS ≤ wI,
  Kedlaya (4.9.1) with constant 1 in the AD-9 exact case), hence surjective_evalArHom
  and surjective_evalArMvHom. All axiom-clean; see sub-tickets T911a–T911h.
  | **File**: FarguesFontaine/Presentation.lean | **Depends**: T907, T908
- **Statement**: `Ar⟨T⟩/(p·T − [zⁿ]) ≅ B^{I'''}` (ln 384–386: I''' = [−n⁻¹log_c p, r]
  in t-coordinates; transport to ρ) — THE bridge that makes BI-algebras quotients of
  Ar-Tate algebras.

#### T911 strictness sub-tickets (spawned 2026-07-26, beastmode; parent T911)

All in `FarguesFontaine/Presentation.lean` unless noted; all depend on the existing
T910/T910a API; source = Kedlaya `L:Robba localizations` proof (lift paragraph +
strict-surjectivity paragraph), specialised per AD-9 (`z̄ = ϖʲ`, left endpoint on the
nose, so every estimate is exact with constant 1). Generality: minimal, match use site.
`vp := ↑(isUnit_p_image p F ϖ).unit⁻¹`, `hexact : |ϖ|^(j·n) = ρ₁`.

### [T911a] Aloc head split with radius-uniform head bound
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: lemma
- **Statement**: `∀ u : Aloc, ∃ t w : Aloc, u = t + p·w ∧ ∀ ρ σ, wAloc ρ t ≤ wAloc σ u`
  (the head's value is radius-independent and bounded by u's value at every radius).
- **Sketch**: `IsLocalization.surj` on powers of `teichPi` writes `u = algebraMap D ·
  teichPiInvAloc^m`; `exists_head_split` (GaussNorm) splits `D = [D₀] + p·D'`;
  `t := algebraMap [D₀] · tPI^m`, `w := algebraMap D' · tPI^m`; `wAloc ρ t =
  |D₀|·|ϖ|⁻ᵐ` by `wAloc_algebraMap`+`gaussValue_teichmuller`+`wAloc_teichPiInvAloc`,
  and `|D₀|·|ϖ|⁻ᵐ = gaussTerm σ D 0 · |ϖ|⁻ᵐ ≤ gaussValue σ D · |ϖ|⁻ᵐ = wAloc σ u`.
- **Mathlib**: IsLocalization.surj; rest is project API.

### [T911c] The exact monomial lift (evaluation identity + Gauss norm)
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: lemma ×2
- **Statement**: for `t : Aloc`, `i : ℕ`, the monomial `M := monomial i
  (AlocToHatK (t · teichPiInvAloc^(j·n·i)))` satisfies (1) `evalAr M = BIProd
  (AlocToBloc t · vp^i)`; (2) `gaussNormRPS M = wAloc ρ₂ t · (|ϖ|⁻¹)^(j·n·i)`.
- **Sketch**: (1) `evalAr_monomial` + `ArToBI_AlocToHatK` + `AlocToBloc_teichPiInv_mul`
  (the `[ϖ]^{jni}` inside `teichPowOverP^i` cancels `tPI^{jni}`), exactly the
  `exists_evalAr_eq_pInv_pow` computation with an extra `t` factor. (2)
  `gaussNormRPS_monomial` + `valued_AlocToHatK` + `wAloc` multiplicativity.

### [T911d] The norm-controlled lift on the dense layer, induction form
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: theorem
- **Statement**: under `hexact`, `∀ k u, ∃ f, evalAr f = BIProd (AlocToBloc u · vp^k)
  ∧ gaussNormRPS f ≤ wI (BIProd (AlocToBloc u · vp^k))`.
- **Sketch**: induction on `k`. Base: constant monomial, norm `wAloc ρ₂ u =` the
  `ρ₂`-side of `wI`. Step: split `u = t + p·w` (T911a); `f := M(t, k+1) + g(w, k)`;
  `‖M‖ = wAloc ρ₂ t · ρ₁^{-(k+1)} ≤ wAloc ρ₁ u · ρ₁^{-(k+1)} =` the `ρ₁`-side of
  `wI` (uses hexact + cross-radius bound); `‖g‖ ≤ wI(w-elt) ≤ wI(u-elt)` since
  `wAloc ρ (p·w) = ρ·wAloc ρ w ≤ wAloc ρ u` (valuation sub-additivity + head bound);
  `gaussNormRPS_add_le`. Evaluation adds by `evalAr_add` + `p·vp = 1`.

### [T911e] The norm-controlled lift of every Bloc element
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: theorem
- **Statement**: under `hexact`, `∀ x : Bloc, ∃ f, evalAr f = BIProd x ∧
  gaussNormRPS f ≤ wI (BIProd x)` — Kedlaya (4.9.1) with constant 1.
- **Sketch**: `IsLocalization.surj` on powers of `p[ϖ]` (the `BIProd_mem_evalRange`
  opening): `x = AlocToBloc (algebraMap a · tPI^k) · vp^k`; apply T911d.

### [T911f] Strict surjectivity: every element of B^I is a value
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: theorem
- **Statement**: under `hexact`, `∀ z ∈ BISub, ∃ f, evalAr f = z ∧ gaussNormRPS f ≤
  wI z` (closedness of the image by successive approximation; with density = Kedlaya's
  strict surjectivity).
- **Sketch**: WLOG `wI z = W > 0` (`wI_eq_zero_iff` else). Recursively build
  correction terms `u_l` with `‖u_l‖ ≤ W·2⁻ˡ` and `wI (z − evalAr (∑_{l<n} u_l)) ≤
  W·2⁻ⁿ`: approximate the residual by `BIProd x` within `W·2⁻⁽ⁿ⁺¹⁾` (density of Bloc
  in BISub = closure def + `wI_ball_mem_nhds`), lift `x` by T911e, ultrametric max.
  Then `exists_rps_series_limit` (Groebner, k=1) gives `U = ∑ u_l` with tails ≤
  `W·2⁻ⁿ`; `wI_evalAr_le` + `valued_coeff_le_gaussNormRPS` transfer tail bounds
  through evaluation; `wI (z − evalAr U) ≤ W·2⁻ⁿ ∀n ⟹ = 0`; `‖U‖ ≤ W` from the
  `n = 0` tail bound.
- **Depends**: T911a–e, exists_rps_series_limit.

### [T911g] The bundled univariate surjectivity
- **Status**: done (2026-07-26) | **Parent**: T911 | **Type**: theorem
- **Statement**: under `hexact`, `Function.Surjective (evalArHom p F ϖ h12 hbmem hb)`.
- **Sketch**: unwrap T911f through `Subtype.ext`.

### [T911h] The k-variable surjectivity (restricted-series functor, T911b's instance)
- **Status**: done (2026-07-26) | **Parent**: T911/T911b | **Type**: theorem
- **Statement**: under `hexact`, `Function.Surjective (evalArMvHom … (k := k))`.
- **Sketch**: coefficientwise: lift each `coeff I g` by T911f with `‖f_I‖ ≤
  wI (coeff I g)`; assemble `G s := coeff (s 0) (f_{tail s})`; `sliceSeries G I = f_I`
  by `coeffSeq_ext` (+ `Finsupp.tail_cons`/`cons_zero`); `G` restricted by the finite-
  union argument (mirror `isRestricted_evalArMvFun`), using that `g` restricted gives
  cofinitely-small `wI (coeff I g)` (subtype-nhds + `wI_ball_mem_nhds`); conclude by
  `Subtype.ext` + `MvPowerSeries.ext` + `evalArMvFun_apply`.

### [T912] Theorem 4.10: BI is strongly noetherian
- **Status**: done (2026-07-26, beastmode) — `isStronglyNoetherian_BISub` (+ per-k
  `isNoetherianRing_restrictedMvPowerSeries_BISub`) in the new
  FarguesFontaine/StronglyNoetherianB.lean, for the AD-9 intervals (left endpoint
  exactly |ϖ|^{jn}); B^I⟨T⃗⟩ = quotient of A^r⟨T,T⃗⟩ via surjective_evalArMvHom +
  Theorem 3.2. Axiom-clean.
  | **File**: FarguesFontaine/StronglyNoetherianB.lean | **Depends**: T907, T910, T911
- **Statement**: `IsStronglyNoetherian (BI)` for every c^ℚ-endpoint closed
  `I ⊂ (0,1)` — in particular for the two FF window intervals (U₀ and V₀ charts).
- **Sketch** (ln 462–470): `BI⟨X₁..Xₖ⟩` is, by T911 + T910 applied with extra Tate
  variables carried along, a quotient of `Ar⟨T, X₁..Xₖ⟩` (noetherian by T907); quotients
  of noetherian rings are noetherian. Endpoint bookkeeping per Rem 4.11 uses the AD-5
  rescalings.

### [PLAN-GATE-1] — CLOSED 2026-07-26 by this decomposition (see decomposition-laneB.md).
