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
| T908 | `B^I` (Def 4.2): construction, norm, completeness, series, density, injectivity, **Lemma 4.4 (three circles)**, **Cor 4.5**, `B^{I,+}` | **done** ((a)+(b); (c) closed-as-scoped 2026-07-30: Bloc-layer ℤ-coordinates landed (IntervalCoordinates.lean), completion-level functionals struck per AD-8 resolution — obstructed + not source-backed) |
| T909 | restriction maps + **Cor 4.6 injectivity** (`resIHom_injective`, RestrictionInjective.lean) | **done** |
| T910–T912 | Lemma 4.9 presentations; Theorem 4.10 | **ALL DONE 2026-07-27**: T911+T912 (AD-9 case-3: surjective_evalArMvHom, isStronglyNoetherian_BISub); T910 cases 1–2 (robba_case1_presentation, robba_case2_presentation — both axiom-clean; plus-ring 'Moreover' clause + A^r third iso deferred as non-critical follow-ups) |
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

#### PROCESS-INCIDENT 2 (2026-07-27, beastmode, self-logged): commit ca132f97c
pushed RED (8 errors — the ported block used Opens/leOfHom under the
scratch's extra `open TopologicalSpace CategoryTheory` absent in the
target file; the `build | grep -c ; commit`-chain used `;` so the
nonzero gate did not stop the commit). Fixed forward next commit
(fully-qualified names). LESSONS RE-BOUND: (1) the gate must be a
SEPARATE step and the commit must be manually issued only after
reading the gate output — never `;`-chained; (2) when porting, diff
the scratch's `open`-header against the target's — scratch-only opens
are a red flag; prefer fully-qualified names in ported blocks.

#### PROCESS-INCIDENT 2026-07-27 (beastmode, self-logged): commit 6d6958bb1
pushed a BROKEN build (evalBI_finset_sum ported outside its variable
section — 20 errors); fixed forward within minutes by the next commit
(section-wrap). LESSON (binding): when porting a scratch block that
depends on section variables (φ/hφ/σ-radii), port the WHOLE section
including `variable`-lines, and ALWAYS run the `lake build` gate BEFORE
`git commit`, not concurrently with it — the `build | grep -c` + `&&
commit` one-liner commits even when the grep count is nonzero.

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
- **ID3a** DONE (2026-07-27, FarguesFontaine/UniformizerTwist.lean:
  isTopologicallyNilpotent_of_pow, PseudoUniformizer.pPow/frobRoot with
  toOF_pPow/toOF_frobRoot + perfectoidValuation_pPow/frobRoot_pow; the
  teichPi-power relations deferred to ID3b where the statements live): `PseudoUniformizer.pow (m>0)`
  (nilpotency of ϖ^m: multiples are cofinal) and `PseudoUniformizer.frobRoot s`
  (unit-level (frobeniusEquiv F p).symm^s; nilpotency: r^m = ϖ^k·r^j with
  {r^j : j < p^s} ⊆ O_F bounded and nonarch subgroup-nbhds absorb
  bounded·nilpotent); value lemmas `v(toOF (frobRoot ϖ s))^(p^s) = v(toOF ϖ)`,
  `toOF (pow ϖ m) = toOF ϖ ^ m`, and the Ainf-side `teichPi (frobRoot/pow)`
  power relations.
- **ID3b** DONE (2026-07-27, FarguesFontaine/BigWindows.lean: teichPi_frobRoot_pow/
  teichPi_pPow, Y_eq_of_teichPi_pow, vle_pow_iff, bigWindow (def) +
  bigWindow_eq_union (split at c·p^n; KGE/KLE_mono de-privatized in YSpace) +
  Y_eq_iUnion_bigWindow + bigWindow_eq_rationalOpen_ofNat/_neg): `Y p F ϖ = Y p F ϖ_n` (powers detect
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
- **Status**: OPEN — interface survey done 2026-07-27 (beastmode); execution
  decision recorded below | **Depends**: PLAN-GATE-2 (now discharged)
- **INTERFACE SURVEY (2026-07-27)**: the repo's object layer is
  `VPreObj`/`VObj` (StructureSheaf.lean — valued presheafed spaces; VObj adds
  `IsSheafOfTopologicalRings`); the pair-level presheaf is
  `structurePresheaf : TopCat.Presheaf CompleteTopCommRingCat (SpaTop A)`
  (StructurePresheafBundled.lean) with sheaf-condition `IsLimitSheaf`
  (SheafyPair.lean) ⇔ `IsSheafy` (isSheafy_iff_isLimitSheaf, needs
  HasLocLiftPowerBounded); the chart point-set identification is
  `Spa (presheafValue D) (presheafValue D)⁺ ≃ₜ R(T/s) ∩ Spa(A,A⁺)`
  (SpaRationalOpenHomeomorph.lean).
- **OBSTRUCTION**: `structurePresheaf` at the AMBIENT pair (A_inf, ringPlus)
  needs `[HasLocLiftPowerBounded (Ainf p F)]`, whose only sorry-free supplier
  `hasLocLiftPowerBounded_faithful` requires `[IsTateRing]` — FALSE for A_inf.
  So the ambient-restriction route (𝒪_Y := 𝒪_{Spa A_inf}|_Y) is blocked unless
  HasLocLiftPowerBounded (Ainf) is proven directly (content: every VALID
  rational datum of A_inf has s-unit + power-bounded fractions in its completed
  localization — true for the bigWindow charts by ID2, open in general).
- **DECISION (PLAN-GATE-3 route, 2026-07-27)**: build Y (and then X) by GLUING
  the sheafy chart spaces `Spa(B_n, B_n⁺)` (B_n := presheafValue of the n-th
  Big-window datum, sheafy by isSheafy_presheafChart at the twisted
  uniformizer) along the overlap circles `bigWindow n ∩ bigWindow (n+1) =
  {κ = p^{n+1}}` (a rational subset of BOTH neighbouring charts), rather than
  restricting a global A_inf-presheaf. Sub-plan:
  (D-i) overlap data: PARTIAL DONE 2026-07-27 (BigWindows.lean:
    bigWindow_inter_succ — the κ = p^{n+1} circle in KGE/KLE form — and its
    A_inf-level rational identifications bigWindow_inter_succ_eq_rationalOpen_
    ofNat (at frobRoot n, right-edge datum (p,1,p,1)) / _neg (at pPow p^m)).
    CIRCLE-IN-CHART DONE 2026-07-27 (ChartSpa.lean:
    bigWindow_inter_succ_eq_rationalOpen_left — the same circle as the κ' = 1
    left edge of chart n+1 — and the two preimage characterizations
    spaChartHomeoBigWindow_preimage_circle (right edge, in chart n, params
    image of (chartT (2p-1) 1, chartS p 1)) / _left (left edge, in chart n+1,
    params image of (chartT 1 1, chartS 1 1)) via
    comap_canonicalMap_mem_rationalOpen_iff; the homeo's forward coe is
    definitionally comap — rfl). REMAINING for D-i — TRANSITION ISO ROUTE
    (settled 2026-07-27 after the keystone audit): RelativeDescent.keystone
    (the 8.5-transitivity iso presheafValue E ≃+* presheafValue (imgDatum D₀ E))
    needs [HasLocLiftPowerBounded A] — over A_inf that class includes NON-Tate
    completions (the trivial datum gives presheafValue = A_inf itself), so
    the faithful supplier cannot work; a general proof = Wedhorn 7.51/7.52
    in Huber generality (a real deferred work-package, NOT taken). INSTEAD:
    apply keystone OVER the chart rings B_n (Tate ✓ IsRingOfIntegralElements
    via canonical plus ✓ HasLocLiftPowerBounded via faithful ✓) — the circle
    ring over chart n is presheafValue of a B_n-datum; compare the two
    neighbouring circle rings through their B^I-identifications and the
    DEGENERATE interval ring B^{[τ,τ]} at the circle radius. New ingredient
    (easy): B^I is UNIFORMIZER-EQUIVARIANT — Bloc-in-ϖ' = Bloc-in-ϖ
    canonically ([ϖ] = [ϖ']^{p^s} makes the localizations agree:
    1/[ϖ'] = [ϖ']^{p^s-1}/[ϖ]), and wLoc/gaussValue are ϖ-independent, so
    BISub-in-ϖ' [ρ₁,ρ₂] = BISub-in-ϖ [ρ₁,ρ₂] under the canonical iso.
    Sub-tickets: (D-i-t1) DONE 2026-07-27
    (FarguesFontaine/UniformizerEquivariance.lean: isLocalization_twist_Bloc,
    blocTwistEquiv + _algebraMap, gaussValue_p_teichPi_pow,
    wLoc_blocTwistEquiv); (D-i-t2) DONE 2026-07-27 — STRONGER than planned:
    hatK is uniformizer-FREE by construction (wK lives on FractionRing A_inf),
    so BlocToHatK_twist (the change iso intertwines, by localization-lift
    uniqueness) gives BISub_twist: BISub-in-ϖ' = BISub-in-ϖ as SUBRING
    EQUALITY (not just iso) — the neighbouring charts' interval rings at a
    common interval literally coincide; (D-i-t3) REVISED 2026-07-27 after the
    signature audit: imgDatum/keystone need span(E.T) = ⊤ OVER THE BASE —
    false for the circle datum over A_inf (chartT ⊆ Iinf); the circle datum
    over B_n would need its own ID2-scale comparison. INSTEAD, exploit t2's
    subring-EQUALITY: build the Y-structure directly on the κ-interval basis
    with 𝒪(interval) := B^I (uniformizer-free by t2), i.e. the (D-ii)
    'alternatively'-route. NEW t3 DONE 2026-07-27 (UniformizerEquivariance.lean:
    blocWIUniformSpace + blocToBI + isUniformInducing/denseRange/
    isUniformAddGroup_blocWI + uniformContinuous_blocToBI_interpolate
    (1-Lipschitz via wLoc_le_max_of_interpolate) + biRes (the restriction
    hom via IsDenseInducing.extendRingHom) + biRes_blocToBI (dense-layer
    identity)). Original plan: the interval-RESTRICTION maps
    `BISub-[ρ₁,ρ₂] →+* BISub-[σ₁,σ₂]` for [σ₁,σ₂] ⊆ [ρ₁,ρ₂] — the identity
    on the dense Bloc is wI-to-wJ continuous (interior interpolation, the
    three-circles machinery of RestrictionInjective/wLoc_rpow_interpolate)
    and extends by the ID2d AbstractCompletion pattern; functoriality
    (comp/id) from dense-extension uniqueness. t4 (revised; DESIGN 2026-07-27): the biRes-composition laws
    hit dependent-radius casts (the composite interpolated radii are only
    propositionally equal). SUBSTRATE BUILT 2026-07-27 (UniformizerEquivariance.lean: vpiQ + pos/lt_one
    + vpiQ_interpolate (affine-θ rpow identity), biCongr (subst-transport,
    proof-irrelevant), BIQ (q₁ q₂ : ℚ), theta_mem_unit, biResQ + its
    dense-layer identity biResQ_blocToBI). t4 FUNCTORIALITY DONE 2026-07-27
    (biRes_continuous, biCongr_continuous, biResQ_continuous, biResQ_id,
    biResQ_comp — all via the dense equalizer on blocToBI). The BIQ-substrate
    is COMPLETE: a contravariant functor from the poset of rational-exponent
    intervals to topological rings. REMAINING: the presheaf assembly on the
    κ-interval basis and the Y-object gluing (next planning step: the
    presheaf-of-BIQ over the basis, its sheaf condition from
    isSheafy_presheafChart + the chart homeos, the VPreObj packaging).
    ORIENTATION NOTE (2026-07-27, read before assembling): vpiQ is ANTITONE,
    so the radius-ordered interval [ρ₁ ≤ ρ₂] corresponds to a DECREASING
    exponent pair q₁ > q₂ (κ-window [p^n, p^{n+1}] ↔ radii
    [vπ^{1/p^n}, vπ^{1/p^{n+1}}] ↔ q-pair (1/p^n, 1/p^{n+1})). biResQ's
    `hlt : q₁ < q₂` is only used for hlt.ne (interpolation) and the
    theta_mem_unit sign-bookkeeping; MIRROR DONE 2026-07-27: theta_mem_unit' + the
    decreasing-orientation family biResQ' with dense-layer identity,
    continuity, and the id/comp laws (UniformizerEquivariance.lean) — the
    radius-ordered (q₁ > q₂) orientation used by the chart-side BIQ-pairs
    is now first-class. Also vpiQ_natCast /
    vpiQ_one bridge to the chart layer's nat-power radii; the bigWindow-n
    chart ring is BIQ at the (1/p^{n+1}, 1/p^n)-pair up to the ID2d equiv at
    ϖ_n (rhoRight-in-ϖ_n p 1 = vpiQ-in-ϖ (1/p^{n+1}) via
    perfectoidValuation_frobRoot_pow — the rpow-arith bridge lemma to prove
    when connecting). STATUS 2026-07-27: chartRingEquivBIQ DONE
    (FarguesFontaine/ChartBIQ.lean — presheafValue(chart-ϖ_n) ≃+*
    ↥(BIQ (1/p^n) (1/p^{n+1})) as three named steps: ID2d at ϖ_n, radius
    rewriting via rhoRight_eq_vpiQ + twist bridges, biSubringCongr of
    BISub_twist; step-1/2 continuities landed, biCongr/biSubringCongr symm-
    continuity generic lemmas landed). OPEN SUB-PROBLEM (PERF): transporting
    IsSheafy from the ϖ_n-side BISub to BIQ — three attempts hit heartbeat
    walls: (i) composite continuity of chartRingEquivBIQ (whnf through the
    trans-chain; step2-symm/step3 instances kernel-ground); (ii) ▸-transport
    of the letI-package (dependent instP/instI mismatch); (iii) elementwise
    BIPlusIn_map_twist via biSubringCongr (whnf through the closed
    BIPlusIn/BISub instances). ATTEMPT (a) RESULT (2026-07-27): mem_BIPlusIn_iff
    already existed in IntervalRing; with MINIMAL imports (ChartBIQ only, no
    transport files) biSubringCongr_coe_val compiles clean — the t10 grind
    was partly instance-pollution from the transport imports — but the
    map-membership ext still whnf-grinds (Subring.map unfolds to .carrier
    under the anonymous constructor). DECISION: route (c) — the presheaf
    VALUES stay at the twisted-side BISub's (IsSheafy free from TC2 at ϖ_n;
    isSheafy_presheafChart already gives the chart-presheafValue side), the
    BIQ layer serves as the INDEXING/bookkeeping normalization
    (chartRingEquivBIQ/Neg identify values where needed), and the twists
    live in the restriction maps (biResQ pre/post-composed with
    biSubringCongr of BISub_twist — RingHom-level composition, no
    elementwise membership juggling). The plus-map correspondence
    (BIPlusIn_map_twist) is NOT needed on this route; keep the (b)-profiler
    idea only if a future consumer genuinely needs IsSheafy ↥BIQ verbatim.
    ROUTE-(c) PROGRESS 2026-07-27: windowResBIQ (ChartBIQ.lean) — the
    restriction hom from the n-th window chart's presheaf value to any
    rational sub-interval BIQ r₁ r₂ of [1/p^{n+1}, 1/p^n], as
    biResQ' ∘ chartRingEquivBIQ (+ invPow_succ_lt). CONTINUITY DEFERRED:
    needs the composite chartRingEquivBIQ-continuity whose step-3 instance
    kernel-ground — profiler task; alternatively restate windowResBIQ as the
    unfolded four-step RingHom-comp so each factor's continuity applies
    foldedly. windowResBIQNeg DONE 2026-07-27. SUBSTRATE
    ASSESSMENT (2026-07-27): NO pairwise-compatibility lemma is needed at
    the value level — the presheaf-on-basis is manifestly well-defined:
    values 𝒪(I) := BIQ-I, restrictions biResQ' (functorial: id/comp laws
    proven), window-independent by construction; the windows enter only in
    the SHEAF-condition proof (transporting sections through
    windowResBIQ/Neg and the chart sheafiness). THE INTERVAL-PRESHEAF
    SUBSTRATE IS COMPLETE. NEXT PHASE (spawn as D-ii-1..3, D-iii):
    (D-ii-1) the Y-presheaf on all opens: STARTED 2026-07-27
    (FarguesFontaine/YPresheaf.lean — intervalTrace (the κ ∈ [1/q₁,1/q₂]
    loci in KGE/KLE form, matching the BIQ q₁ q₂-indexing),
    bigWindow_eq_intervalTrace, intervalTrace_mono). DYADIC OPENNESS DONE 2026-07-27
    (intervalTrace_dyadic_eq_rationalOpen — the (j₁/p^s, j₂/p^s)-trace is the
    κ' ∈ [1/j₁, 1/j₂] chart of the p^s-th root uniformizer, via the
    (1,j₁,1,j₂)-datum and typed collapse-haves — and
    isOpen_intervalTrace_dyadic). The dyadic traces form an OPEN BASIS
    substrate. THE PRESHEAF CONSTRUCTION DONE 2026-07-27
    (YPresheaf.lean): DyadicIdx (the index structure with q₁/q₂-exponents,
    positivity, ordering, and the Nested relation with mem-lemmas),
    dyadicVal/dyadicRes (values BIQ, restrictions biResQ'), dyadicTrace, the
    limit subring **limitSectionsY W** (compatible families over dyadic
    traces inside W), and **limitRestrictY** with id/comp laws BY RFL. The
    Y-structure presheaf exists as a functor on the poset of subsets of Y.
    NEXT (D-ii-2, the sheaf condition): (a) the values-on-basis comparison
    𝒪(dyadic-trace) ≅ BIQ: limitEvalTop + limitEvalTop_spec DONE 2026-07-27
    (evaluation at the top index; the family is pinned on NESTED indices).
    (a) COMPLETE 2026-07-27 (commit 31b48a9a2): the GEOMETRIC BRIDGE
    dyadicTrace_subset_nested (trace-inclusion ⇒ interval-nesting) via the
    two ENDPOINT Gauss points — gaussPoint_mem_intervalTrace_iff (the Gauss
    point at radius vpiQ q is in the (q₁,q₂)-trace iff q₂ ≤ q ≤ q₁; proven
    through KGE_iff/KLE_iff at the (den, num.toNat)-representation with
    gaussVal_p_pow/gaussVal_teichPi_pow + vpiQ_pow/vpiQ_natCast/
    vpiQ_le_vpiQ_iff); Nested.trans + dyadicRes_id/_comp (direct from the
    biResQ' laws — the Prop-args make dyadicRes proof-irrelevant, so the
    biResQ' statements apply verbatim); **limitEvalTop_bijective** — the
    values-on-basis comparison 𝒪(dyadic-trace) ≅ BIQ: injectivity =
    limitEvalTop_spec through the bridge, surjectivity = the
    dyadicRes-family of a top value (compatibility = dyadicRes_comp,
    top-evaluation = dyadicRes_id). All 10 new decls axiom-clean.; (b) REPLANNED 2026-07-27 (beastmode): prove the
    sheaf condition DIRECTLY on the interval rings as the SPLIT FIBER-PRODUCT
    THEOREM — for q₂ ≤ r ≤ q₁, restriction is a bijection
    BIQ[q₁,q₂] ≅ BIQ[q₁,r] ×_{hatK (vpiQ r)} BIQ[r,q₂] — with NO Spa
    transport (the isSheafy-transport route stays available but costs
    equalizer-shape alignment through the chart homeos). Sub-steps:
    (b1) DONE 2026-07-27 + (b2) DONE 2026-07-27 (commit: IntervalSplitting.lean
    — biFstQ/biSndQ explicit-toFun projections, the three dense-equalizer
    laws, biResQ'_split_injective; teichCoeff_init/tail,
    pow_mul_gaussValue_init/tail_le in multiplied no-division form,
    exists_wLoc_split; all axiom-clean). (b3) DONE 2026-07-27: THE SPLIT
    FIBER-PRODUCT THEOREM COMPLETE (IntervalSplitting.lean) —
    exists_blocApprox_pair (joint ε-approximation via closure approximants
    + splitting the discrepancy at the split radius), tendsto-from-bounds
    helpers, biResQ'_eq_left/right_of_tendsto (abstract-f restriction
    recognition), glueSeq/biGlue (the glued element = the pair of outer
    endpoint components, in BIQ by mem_closure_of_tendsto),
    biResQ'_biGlue_left/right, **biResQ'_split_surjective** — with
    biResQ'_split_injective: B^{[q₁,q₂]} ≅ B^{[q₁,r]} ×_{hatK r} B^{[r,q₂]},
    the sheaf axiom of the interval presheaf on a two-piece cover. All 14
    new decls axiom-clean. NEW PERF LESSON (binding): the KERNEL ignores
    @[irreducible] and head-compares ring homs at DIFFERENT radii before
    projecting — cross-radius component equations must be routed through
    the val-projection (biGlue_coe-style) and kept out of rfl-args, else
    (kernel) deterministic timeout; also per-declaration kernel budgets ⇒
    hoist branch proofs into abstract-parameter lemmas (the aux-lemma +
    named-def restructure pattern). DYADIC LIFT DONE 2026-07-27
    (YPresheaf.lean, now importing IntervalSplitting):
    DyadicIdx.splitL/splitR (+_nested), biResQ'_split_existsUnique,
    **exists_unique_dyadicRes_glue** — the two-piece sheaf axiom in
    dyadicRes form (the splitL/splitR-radii are iota-defeq to the
    Q-instantiation, so the Q-theorem applies verbatim; matching stated via
    biSndQ/biFstQ at the split radius). Axiom-clean.
    Original sub-step text: (b1) endpoint projections biFst/biSnd : BISub → hatK ρᵢ
    (= RingHom.fst/snd ∘ subtype; continuous; dense-layer = BlocToHatK) and
    the three dense-equalizer laws: biFst∘biResQ'(left-shared) = biFst,
    biSnd∘biResQ'(right-shared) = biSnd, biSnd∘resL = biFst∘resR (middle
    match) ⇒ SEPARATION (the pair (resL, resR) is injective since an
    element of BISub IS its endpoint pair). (b2) the SPLITTING LEMMA on
    Bloc (the analytic core, Mittag-Leffler-style): every z = x/(p[ϖ])^k
    splits z = zM + zP via mathlib's WittVector.init/tail (init_add_tail)
    at threshold k: zM = init k x/(p[ϖ])^k (Laurent part, m−k < 0) has
    wLoc_σ(zM) ≤ wLoc_τ(z) for all σ ≥ τ, zP = tail k x/(p[ϖ])^k (m−k ≥ 0)
    has wLoc_σ(zP) ≤ wLoc_τ(z) for σ ≤ τ (per-term σ^{m−k} vs τ^{m−k}
    monotonicity through the gaussValue sup-formula). (b3) assembly: the
    matching subring M := {(g₁,g₂) | biSnd g₁ = biFst g₂} is closed in the
    complete product ⇒ complete; Φ := (resL, resR) is uniform-inducing
    (outer components recover the identity embedding by the b1-laws) with
    complete source ⇒ closed range; the diagonal D = Φ(blocToBI z) is dense
    in M by the b2-splitting (given (g₁,g₂) ∈ M ε-approximated by z₁, z₂:
    d := z₁ − z₂ has w_τ(d) ≤ ε by the middle match; d = dM + dP; then
    h := z₁ − dP = z₂ + dM is ε-close to BOTH) ⇒ M = range Φ ⇒ ∃!.
    (c) the topology on limitSectionsY (product-induced) and the embedding
    condition. The ID2-sheafiness note stands: dyadic data are
    chartS-1-b-shaped. ARCHITECTURE NOTE (2026-07-27, binding for D-ii-3):
    the dyadic STRIPS are NOT a neighbourhood basis of Y (a small rational
    open around v — e.g. cut by p−[a]-type functions — contains no full
    κ-annulus), so the strips-limit presheaf limitSectionsY computes 𝒪 only
    on strip-generated opens and its naive stalks are TRIVIAL; D-ii-3 must
    therefore package stalks/valuations FROM THE CHART SIDES (per the
    original plan line 'stalks/valuations from the chart sides'), either by
    (i) enlarging the limit basis to ALL chart rational opens (cross-chart
    transition on sub-circle rationals = keystone OVER the Tate B_n — valid)
    or (ii) VPreObj-gluing machinery for the ℤ-chain (cocycle-free since
    only adjacent windows meet). Decide when (b) lands. (D-ii-2) the sheaf condition: per-window via
    isSheafy_presheafChart + spaChartHomeoBigWindow + windowResBIQ,
    refinement via the rational basis; (D-ii-3) VPreObj packaging — RECONNAISSANCE 2026-07-27 (beastmode,
    load-bearing): the pair-level ALL-OPENS presheaf ALREADY EXISTS
    generically (StructurePresheafLimit.lean: limitSections V = compatible
    families over RationalIndex V, complete+T2, limitRestrict with rfl-laws,
    **limitEval : 𝒪(spaOpens D₀) ≃+* presheafValue D₀** the top-element
    argument, bundled structurePresheaf; StructurePresheafBundled.lean:
    **structurePresheaf_isSheafOfTopologicalRings (h : IsLimitSheaf A)**) —
    all gated on [HasLocLiftPowerBounded A] which holds for the TATE charts
    B_n via the faithful supplier + isSheafy_presheafChart ⟹ IsLimitSheaf.
    So per-chart 𝒪_{Spa(B_n)} as a sheaf of topological rings is DONE
    modulo instantiation, and the Y-assembly must REUSE this generic
    machinery per chart (do NOT rebuild dyadic-style limits per chart —
    only the CROSS-chart layer is new). Ambient route stays closed (the
    class over A_inf needs Wedhorn 7.51/7.52 in general-Huber form —
    deferred work-package, decision stands). WHAT IS GENUINELY MISSING
    (checked: no Spa-as-VObj constructor, no stalk-locality anywhere):
    **the Wedhorn 8.14 stalk package**, generic over a pair with
    [HasLocLiftPowerBounded] (+Tate where needed) — spawn as:
    (S1)+(S2) DONE 2026-07-27 (StructureSheafStalks.lean, generic Huber
    pair): pointValue + mem_spa/isContinuous/comap_pointValue/
    eq_pointValue_of_comap_eq + comap_restrictionMapHom_pointValue (germ
    coherence). Axiom-clean.;
    (S3) the stalk valuation on (structurePresheaf A).ringStalk v via the
    mathlib germ API (exists_germ_eq + germ_eq CONVERSE both exist in
    mathlib Stalks.lean; well-defined by S2); (S3a) DONE 2026-07-27
    (StructureSheafStalks.lean §OpenValue): openValue (the point valuation
    on limitSections V for ANY open V ∋ v, via choice of a rational index
    from exists_isRational_spaOpen_subset) + choice-independence (common
    rational refinement + S2 + the one-line eval-restriction law
    restrictionMapHom_comp_limitEvalHom = the compatible-family identity) +
    restriction coherence comap_limitRestrict_openValue +
    openValue_vle_restrict. (S3b) DONE 2026-07-27 (§StalkValue):
    spaRingPresheaf, germ_limitRestrict + germ-arith bridges, stalkVle +
    exists_common_rep + stalkVle_elim, ALL 8 ValuativeRel axioms,
    stalkValuativeRel, **stalkValue : Spv (ringStalk v)**,
    comap_germ_stalkValue. Axiom-clean. PERF LESSON (binding): the germ
    API lives at the (SpaTop A).str-Opens spelling while the pair-level
    machinery is at instTopologicalSpaceSubtype — the two are defeq but
    DEFEAT rw's keyed matching; NEVER rw with germ-form lemmas — use
    term-mode Eq.trans/congrArg₂/▸-chains and let app-elaboration handle
    the defeq (also limitRestrict-of-product is DEFEQ to
    product-of-limitRestrict — explicit-toFun — so map_mul-rewrites there
    are unnecessary);
    (S4) IsLocalRing (ringStalk v) with maximalIdeal = supp(stalkValue) —
    (S4-easy) DONE 2026-07-27: StalkShrink named-claim +
    isUnit_iff_not_vle_zero + mem_nonunits_iff_vle_zero +
    isLocalRing_stalk_of_shrink + maximalIdeal_stalk_eq_supp (all
    conditional on StalkShrink; axiom-clean). REMAINING = S4-core:
    discharge StalkShrink via the Laurent route below. S4-core STEP 1
    DONE 2026-07-27: **stalkShrink_of_rationalShrink** — StalkShrink
    reduced to the named RationalShrink claim (nonzero point value on
    presheafValue D ⇒ unit after restricting to a smaller valid rational
    ∋ v). INSTANCE AUDIT RESOLVED: at PD := presheafValue D all needed
    instances exist (presheafValuePlus_isRingOfIntegralElements is an
    INSTANCE given [IsRingOfIntegralElements A⁺];
    presheafValue_isTateRing_concrete; PlusSubring-PD canonical) and the
    cofinality lemma is exists_pow_vle_of_isContinuous
    (SpaRationalOpenHomeomorph:63). REMAINING for RationalShrink (the
    Laurent argument over PD): (i) trivial/global datum over PD
    (globalLocData of presheafValue_concretePair) + laurentMinusDatum at
    u^{-k}·b (u := presheafValue_topNilUnit, k from cofinality); (ii)
    membership of pointValue-v in the Laurent-minus rational (unfold the
    product-T conditions; vle 1 b' and vle b' b' + s-nonzero); (iii) the
    ELEMENTARY unit fact (b'-inverse = s₀·(s₀b')⁻¹, no Noetherian);
    (iv) REROUTED 2026-07-27 (the keystone relativePiece_equiv is
    [IsStronglyNoetherian]-gated — circular for the campaign; DO NOT use):
    NOETHERIAN-FREE ROUTE: (1) w := pointValue ∈ basicOpen 1 c for
    c := u^{-k}·b; (2) **exists_A_level_open_presentation** (SpaRational-
    OpenHomeomorph:225, Tate+IRIE only!) at the singleton family (1, c) ⇒
    a base-open W ∋ v capturing the basic-open for ALL Spa-PD-points over
    W; (3) rational basis inside W ∩ R(D) ⇒ D'; (4) for every
    w'' ∈ Spa(presheafValue D'): pull back along restrictionMapHom D D' to
    a Spa-PD-point over R(D') ⊆ W (NEEDS THE MISSING BRICK: plus-
    functoriality (PD)⁺ ≤ ((PD')⁺).comap (restrictionMapHom D D' h) — 
    Wedhorn 8.2(3)-piece via integral-closure functoriality of the
    completedPlusSubring; then AdicSpectrum.comap_mem_spa assembles) ⇒
    capture ⇒ ¬vle (res b) 0 at every w''; (5)
    **isUnit_of_forall_not_vle_zero_of_isOpen_topologicallyNilpotent**
    (AdicSpectrum:360, Wedhorn 7.52(2)) at PD' with
    IsTateRing.isOpen_topologicallyNilpotentElements (HuberRings:324) ⇒
    IsUnit (restrictionMapHom D D' h b). PLUS-FUNCTORIALITY BRICK PLAN (2026-07-27, after finding
    **mem_plus_of_forall_spa_vle_one_huber** — Wedhorn 7.52(1)/[Hu2] 3.3(i)
    at general complete Huber, HuberLocLift:342): prove
    aplus_le_comap_restrictionMapHom via the Spa-characterization at D':
    reduce w''.vle (σx) 1 (∀ w'' ∈ Spa PD') to bounds of the continuous
    w := comap σ w'' on (PD)⁺ = IntCl(topClosure(coe-IntCl(locPlus))):
    (B1) the ≤1-locus of a continuous valuation is CLOSED (ultrametric
    translate: a + {v < v a} ⊆ {v > 1}); (B2) integral-over-a-bounded-
    subring ⇒ bounded (valuation integral bound, vle-form); (B3)
    generators: A⁺-images via the σ∘ρ-law + w''-Spa-bound;
    t/s-images via the multiplicative cancel w''(lift)·w''(ρ'(s)) =
    w''(ρ'(t)) ≤ w''(ρ'(s)) ≠ 0 from base-membership R(D') ⊆ R(D);
    (B4) assemble; (B5) comap_restrictionMapHom_mem_spa :=
    comap_mem_spa + (B4). (B1)-(B5) ALL DONE 2026-07-27 (commit: plus
    functoriality of restriction maps, axiom-clean). **S4 COMPLETE
    2026-07-27**: rationalShrink_holds + stalkShrink_holds +
    **isLocalRing_stalk** + **maximalIdeal_stalk** (Wedhorn 8.14
    unconditional, axiom-clean). GOTCHA recorded: the AdicSpectrum 7.52(2)
    lemma isUnit_of_forall_not_vle_zero_of_isOpen_topologicallyNilpotent
    sits in an [IsLinearTopology A A]-section — FALSE for Tate rings; the
    right criterion is the TATE-FREE
    **isUnit_iff_forall_not_vle_zero_of_completePair** (pair-complete, used
    via the isUnit_canonicalMap_s_huber pattern: presheafValue_isHuberRing_
    huber + presheafValue_concretePair + presheafValue_isAdicComplete). ⚡ MAJOR SIDE-DISCOVERY (architecture-relevant):
    **hasLocLiftPowerBounded_huber_instance** (HuberLocLift:622, M8
    2026-07-17) supplies HasLocLiftPowerBounded for EVERY complete Huber
    pair with [IsRingOfIntegralElements A⁺] — NO Tate. The board's
    'ambient route blocked: only Tate supplier' is STALE: if
    (Ainf, ⊤-or-ringPlus) satisfies IsRingOfIntegralElements + T2 +
    Nonarch + Complete, the WHOLE limitSections/structurePresheaf/stalk
    machinery instantiates at the AMBIENT A_inf directly (𝒪_Y by
    restriction; only the Y-local sheaf condition would still route
    through the charts). RE-EVALUATE the D-ii architecture at the next
    planning step before building cross-chart glue.
    PLAN REFINED 2026-07-27 after reconnaissance: (S4-easy, do first)
    unit ⇒ nonzero stalk-value (v(x)v(x⁻¹) = v(1) ≠ 0), nonunits-⊆-supp
    contrapositive, supp is an ideal ⇒ once the hard half lands,
    IsLocalRing via the nonunits-add criterion; REDUCTION LEMMA: germ of a
    section that becomes a UNIT on a smaller open is a stalk-unit (germ =
    ring hom); so the hard half reduces to THE SHRINK CLAIM: f ∈ 𝒪(U),
    (openValue U hv).vle f 0 false ⇒ ∃ rational D' ∋ v inside U with
    evaluation of f a unit of presheafValue D'. (S4-core route, Wedhorn
    8.14 via the repo's Laurent machinery): (a) evaluate f at a rational
    D ∋ v: fD ∈ PD := presheafValue D with pointValue-vD(fD) ≠ 0; PD is
    complete TATE (presheafValue_isTateRing_concrete ✓); (b) cofinality of
    the pseudouniformizer for the CONTINUOUS vD: ∃ N, vD(π^N) ≤ vD(fD);
    (c) the trivial datum over PD + laurentMinusDatum at π^{-N}·fD: the
    Laurent-minus piece contains vD's point and makes fD a unit — NOTE the
    packaged unit-lemmas (LaurentRefinementCore 983-1010) sit in an
    over-hypothesized [IsNoetherianRing]-section, but the fact is
    ELEMENTARY (f·(s₀·(s₀f)⁻¹) = 1 since s := s₀·f is the inverted
    denominator) — re-derive the 3-liner generically at PD; (d)
    exists_downstairs_rationalDatum (SpaRationalSubsetCorrespondence:185,
    complete-Tate, NO Noetherian) to convert the upstairs Laurent piece to
    a base-rational D' ⊆ R(D) ∋ v; unit-transport along the comparison;
    (e) assemble. INSTANCE PREREQUISITE for (c)/(d) at PD: PlusSubring PD
    = (PD)⁺ ✓, IsHuberRing ✓ from Tate; HasLocLiftPowerBounded PD via the
    faithful supplier needs IsRingOfIntegralElements ((PD)⁺) — the
    plus-reconciliation question (was load-bearing already in NT-1) —
    AUDIT what supplies it before starting (c);
    (S5) DONE 2026-07-27: **spaVObj** — Spa of a sheafy complete Tate
    pair as the FIRST inhabitant of the VObj category (spaPresheafedSpace,
    spaVPreObj with 8.14-stalks + stalkValue + val_supp, spaVObj at
    IsLimitSheaf, spaVObj_of_isSheafy). ★ THE STALK PACKAGE S1–S5 IS
    COMPLETE (StructureSheafStalks.lean, all axiom-clean, generic over
    complete Tate pairs with integrally-closed plus + HasLocLift). The FF
    charts B_n satisfy every hypothesis (Tate ✓ ID2e, IRIE-plus =
    the NT-1 plus-reconciliation instance presheafValuePlus_… if the chart
    pair is presented as a presheafValue — CHECK at instantiation;
    IsLimitSheaf from isSheafy_presheafChart via isSheafy_iff_isLimitSheaf)
    — NEXT: instantiate spaVObj at the FF charts, then the Y-object
    (architecture decision: ambient-vs-glue, see the M8 note above).
    CHART-INSTANTIATION AUDIT 2026-07-27: A_inf-side instances all present
    (AinfHuber.lean: instTopologicalSpaceAinf/instNonarchimedeanRingAinf/
    instIsHuberRingAinf/instPlusSubringAinf (⊤) + isAffinoidRing_Ainf —
    CHECK whether an IsRingOfIntegralElements ((Ainf)⁺)-INSTANCE is
    registered from it, plus T2/CompleteSpace instances for A_inf — grep
    AinfHuber tail). Chart-side: [IsSheafy B_n] is supplied by
    isSheafy_presheafChart ONLY AT THE TRANSPORTED PLUS (letI PlusSubring
    := BIPlusIn mapped through presheafChartRingEquivBISub.symm) — NOT the
    canonical presheafValuePlusSubring. THE LOAD-BEARING BRICK (already
    flagged in NT-1): **the plus-reconciliation** — canonical
    (presheafValue chartDatum)⁺ (= completedPlusSubring, the
    IntCl-closure tower) EQUALS the transported BIPlusIn unit ball
    (Kedlaya Def 4.5-side; mem_BIPlusIn_iff is the interval-side
    membership interface). With it, IsSheafy transports to the canonical
    pair and spaVObj_of_isSheafy applies verbatim at B_n. Alternatives if
    the equality resists: state spaVObj at the transported pair (letI) —
    works but pollutes downstream plus-references. ★ CHART VObj DONE
    2026-07-27 (FarguesFontaine/ChartVObj.lean, transported-pair form):
    chartPlus/chartTate (named instance-defs) + **chartVObj** =
    spaVObj_of_isSheafy at the chart pair — compiled FIRST SHOT, all
    axiom-clean. The FF Big-window charts are now objects of 𝒱 with the
    complete Wedhorn 8.14/8.20 package. REMAINING for the Y-object:
    (α) the plus-reconciliation (upgrade to the canonical pair, optional
    if downstream works transported) — PLAN REFINED 2026-07-27:
    BIPlusIn is the FULL unit ball {wI ≤ 1} (not a closure).
    (⊆-easy, canonical-into-ball): completedPlusSubring ⊆ power-bounded
    (the existing faithful chain, Presheaf.lean ~490: locPlusSubring ⊆
    (Aₛ)° + IntCl preserves power-bounded + closure) AND power-bounded =
    ball in BISub because wI is MULTIPLICATIVE ON POWERS
    (wI(xⁿ) = max(v₁,v₂)ⁿ = wI(x)ⁿ) — one small new lemma
    isPowerBounded_iff_wI_le_one — DONE 2026-07-27 (IntervalSplitting.lean:
    wI_coe_pow + isPowerBounded_iff_wI_le_one, axiom-clean). (⊆) FULLY DONE
    2026-07-27 (ChartVObj.lean: presheafChartRingEquivBISub_isOpenMap +
    **completedPlusSubring_le_chartPlus** — IRIE.subset_powerBounded over
    the affinoid A_inf + open-map transport + the ball-iff; axiom-clean).
    NOTE: Presheaf.lean's IsPowerBounded.map (line ~4175) is a SORRY and
    FALSE-as-stated (needs open) — use isPowerBounded_map_of_isOpenMap
    (Wedhorn828) instead, never the sorried one. Historical text: Remaining for
    (⊆): canonical ⊆ power-bounded — the faithful chain
    (locPlusSubring_le_powerBounded + IntCl/coe/closure-stability; the
    IRIE-field subset_powerBounded of presheafValuePlus_isRingOfIntegral-
    Elements may give it in ONE step: (PD)⁺ ⊆ (PD)° then transport through
    the comparison iso e (continuous ring equiv preserves power-bounded)
    then the new iff).
    (⊇-hard, ball-into-canonical — Kedlaya Def 4.5): a ball element is a
    limit of Bloc-approximants which are AUTOMATICALLY in the ball for
    ε ≤ 1 (ultrametric: wI(h) ≤ max(wI z, ε) ≤ 1), so it reduces to the
    DENSE-LEVEL INTEGRALITY: a Bloc element with both window-Gauss norms
    ≤ 1 is integral over the A_inf[T/s]-localization subring (Teichmüller
    truncation; the T911 norm-exact-lift machinery is the tool);
    then IntCl-closure-tower absorbs. This ⊇-half is the real new math. ⊇-REDUCTION DONE
    2026-07-27 (ChartVObj.lean): **ChartDensePlus** (the named dense claim)
    + exists_ball_approx + chartPlus_le_completedPlusSubring_of_dense —
    the reconciliation is now EXACTLY the equality
    chartPlus = canonical ⟺ ChartDensePlus (⊆-half unconditional).
    NEXT for ChartDensePlus (Kedlaya 4.5 dense integrality): h ∈ Bloc,
    both window-norms ≤ 1: write h = x/(p[ϖ]^b-chart-s)^k (ID2a); the
    norm-conditions bound the Teichmüller terms; each Laurent term
    p^i[c]-over-s^k with its bound is a product of the chart generators
    t/s (p^{a'}/s, [ϖ]^{b'}/s) and A_inf-elements — the T911 norm-exact
    lift machinery (Presentation.lean, 'norm-exact lift of p^{-i}') is the
    tool; then the element is a CONVERGENT SUM of generator-products ∈
    the closed canonical subring. r4-DESIGN 2026-07-27 (post-T911-study):
    (1) [ϖ]/p = [ϖ]^{b+1}/chartS is a locPlus GENERATOR-QUOTIENT, so the
    presentation base b = teichPowOverP = [ϖ^{jn}]/p is a generator-product
    (jn ≥ 1); (2) Ar-ball monomials p^i[d]/[ϖ]^m with window-norms ≤ 1
    have O_F-INTEGRAL a-th powers at the exact endpoint (hexact2) ⇒
    degree-a integrality over locPlus; Aloc-elements sum via
    exists_aloc_head_split + closedness; (3) z = evalAr f with
    gaussNormRPS ≤ wI ≤ 1 (exists_evalAr_eq_of_mem_BISub, Kedlaya
    strictness); partial sums are canonical-members (2)+(1);
    tendsto_evalAr + canonical-closed ⇒ ChartDensePlus. Each step is a
    compile-brick; then chartPlus = canonical and chartVObj upgrades to
    the canonical pair. DECISIVE SIMPLIFICATION (2026-07-27, exponent
    audit): the exponent bookkeeping is clean only for b = 1 — and the
    ACTUAL Y-charts are (a,b) = (·,1)-data at the twisted uniformizers
    (the dyadic/Big-window charts at frobRoot are chartS = p·[ϖ'],
    T ∋ [ϖ']² — ρ₂^a = |ϖ'| forms), where ([ϖ']/p)^a = ([ϖ']²/chartS)^a
    ∈ locPlus GIVES the monic witness directly. SPECIALIZE ChartDensePlus
    (and if convenient the whole reconciliation) to b = 1: generators
    [ϖ']²/s ⇒ [ϖ']/p; base-monomial b-presentation j·n with
    hexact1-|ϖ'| = ρ₁ forces jn = 1 ⇒ the presentation base IS [ϖ']/p.
    VERIFIED 2026-07-27: the Y-cover uses chartData p F (frobRoot ϖ n)
    1 1 p 1 — (a,b) = (p,1) ✓ b=1. FULL r4 PROOF-DESIGN (supersedes the
    evalAr route; direct Teichmüller-monomial argument using EXISTING
    ID2b machinery — mem_chartSubring_of_wI_le (≤|ϖ|^b-ball) +
    exists_p_pow_mul_mem_chartSubring (scaled) + blocEquiv_divByS_teichPi
    (the [ϖ]/p = divByS-bridge) all EXIST in ChartData.lean):
    h ∈ Bloc 1-ball, h = x/(p[ϖ])^k with x ∈ A_inf so ALL Teichmüller
    coords |c_i| ≤ 1 ⇒ the Laurent series Σ p^{i−k}[c_i/ϖ^k-shift]
    CONVERGES in wI (tails ρ^{i−k} → 0 ✓ pow_mul_gaussValue_tail_le).
    Split h = head_K + tail_K (b2-init/tail): (m1) each 1-ball monomial
    with NEGATIVE p-exponent p^{-j}[c] has |c| ≤ ρ₁^j = |ϖ|^j [hexact1]
    ⇒ c = ϖ^j·c' with c' ∈ O_F (F-valuation-ring) ⇒ = chartFracPi^j ·
    algebraMap [c'] ∈ chartSubring; (m2) the i=0 term [c₀], |c₀| ≤ 1 ⇒
    A_inf-image ∈ S; (m3) POSITIVE monomials m = p^i[c], |c| ≤ ρ₂^{-i}:
    m^a = p^{ia}[c^a] with |c^a·ϖ^{ib}| ≤ 1 [hexact2] ⇒ m^a =
    chartFracP^i · algebraMap [c^a·ϖ^{ib}] ∈ S ⇒ m integral over S with
    the monic X^a − m^a; (m4) head_K ∈ IntCl(S) (sum of m1-m3), tail_K
    wI-small ⇒ blocToBI-image of h ∈ topClosure(coe(IntCl(S-image)))
    ⊆ canonical ✓ ChartDensePlus. r4b ZONE ANALYSIS COMPLETE 2026-07-27 (b=1, s = p[ϖ], h = mk'(x, s^k),
    monomials p^i[c_i], per-monomial ball bounds from the sup-def:
    ρ₁-bound |c_i| ≤ |ϖ|^{2k−i}, ρ₂-bound |c_i|^a ≤ |ϖ|^{k(a+1)−i} via
    hexact2 ρ₂^a = |ϖ|): THREE ZONES, all closing EXACTLY —
    (M1'') i ≤ k: c_i = ϖ^k·c' (ρ₁-bound, 2k−i ≥ k) ⇒ mk'(p^i[c_i], s^k)
    = [c']·p^{−(k−i)} = the m1-form ∈ S;
    (M2'') k < i ≤ k(a+1): the a-th power collapses UNIFORMLY:
    (mk'(p^i[c_i], s^k))^a = chartFracP^{i−k}·[c''] with
    c'' := c_i^a/ϖ^{k(a+1)−i} (the ρ₂-bound is EXACTLY the divisibility;
    b=1 makes every exponent cancel: [ϖ]^{-1} = fracP·p^{-a} budget) ⇒
    integral over S with monic X^a − (S-element);
    (M3'') i > k(a+1): direct ∈ S — mk' = fracP^k·p^{i−k(a+1)}[c_i]-image;
    TAIL: both wLoc-norms of the ≥K-tail decay (ρ₁: |ϖ|^{i−2k};
    ρ₂: ρ₂^{i−k}|ϖ|^{−k}, ρ₂ < 1) ⇒ head-in-IntCl(S) + tail → 0 ⇒
    closure ⇒ ChartDensePlus at b=1. Implement (M1'')-(M3'') as
    mk'-fraction lemmas, then the init/tail head-sum, then the limit.
    (M1'') + (M3'') DONE 2026-07-27 (ChartVObj.lean: sPow +
    mk_monomial_mem_of_le + mk_monomial_mem_of_large, axiom-clean; PERF:
    omega CANNOT see k*a-vs-a*k as equal atoms — nonlinear — keep ONE
    spelling; generalize the map-atoms before ring; the final membership
    exacts must use the refine-bullet form). (M2'') DONE 2026-07-27
    (mk_monomial_pow_a_eq, commit 709e65781): (mk'(p^{k+d}[c], s^k))^a
    = chartFracP^d·[c''] given |c|^a ≤ |ϖ|^{ka−d}; mk'-power collapse
    via eq_comm+mk'_eq_iff_eq_mul with the sPow SUBTYPE-COE spelled as
    show-from-rfl bridges INSIDE the rw chain (rw only sees the
    syntactic coe form), main identity by 3-step calc with
    (k+d)*a = a*d + k*a spelling + hIT-insert + generalize-then-ring.
    REMAINING: the head-sum — the finite Teichmüller expansion EXISTS:
    mathlib WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
    (x r): p^{r+1} ∣ x − Σ_{i∈Iic r}[frobEquiv.symm^i(coeff i x)]·p^i
    (used in AinfHuber.lean:339 with eq_add_of_sub_eq: x = p^{r+1}·w + Σ).
    So head-sum = image of that identity under mk'(·, s^k); per-monomial
    bounds from gaussValue-sup ⇒ each monomial in a zone lemma;
    THEN tail-smallness + closure assembly.
    TRANSPORT BRICKS DONE 2026-07-27 (commit ab7c8ccd1, ChartVObj.lean,
    all axiom-clean): presheafChartRingEquivBISub_symm_blocToBI
    (ψ(h) = coeRingHom(blocEquivAwayChartS.symm h), via injective +
    compare_coe mirror + BIProd-defeq show), chartSubring_le_
    locPlusSubring_map (S-generators ↦ alg/divByS via blocEquiv_divByS_
    teichPi/p; A⁺ = ⊤ so Subring.mem_top), coeRingHom_mem_completedPlus
    SubringBase_of_mem, symm_blocToBI_mem_completedPlusSubring_of_mem /
    _of_pow_mem (IsIntegral.of_pow; the registered subtype.toAlgebra makes
    isIntegral_algebraMap defeq-close), monomial_symm_blocToBI_mem_
    completedPlusSubring (3-zone dispatch at b=1 from the two Gauss-term
    bounds ρ^i·|c| ≤ (ρ·|ϖ|)^k). PERF: chartData PROJECTIONS (.s/.T) are
    NOT reducible-defeq — never let ⟨w,hw⟩/rw touch a D.s-typed goal
    directly; route via ∀-quantified helper lemmas stated in the D.s
    spelling, and pin isIntegral_algebraMap's R with show-from ascription.
    ★★ (r5b) DONE 2026-07-27 — ChartDensePlus PROVEN at (a,1)
    (chartDensePlus_of_exact, commit 237ae3573, all axiom-clean):
    gaussValue_sPow + gaussTerm_le_of_wLoc_mk'_le_one (inv-cancel calc) +
    mk'_sPow_split (congrArg-alg + simp only [← mk'_eq_mul_mk'_one]) +
    wLoc_mk'_tail_le (gaussValue_le_one) + valued_BlocToHatK_sub_of_add +
    tendsto_max_const_mul_pow (include hρ₁1 hρ₂1) + the assembly
    (mk'_surjective PAIR-pattern ⟨⟨x,s⟩,rfl⟩; Submonoid.mem_powers_iff +
    Subtype.ext + subst to sPow k; choose over mathlib
    dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff — teichCoeff is
    DEFEQ to the frobEquiv-form so hwspec plugs straight in; hpair via
    Prod.ext (BIProd_fst …).symm with ALL radius args explicit;
    tendsto_subtype_rng + show-BIProd-normalization + rw [← hpair];
    per-coordinate ε-bounds by le_of_eq (by ring) into le_max_left/right).
    PERF: this mathlib's cancel lemmas are mul_le_mul_LEFT (h)(c): b*a ≤
    c*a and mul_le_mul_RIGHT (h)(a): a*b ≤ a*c — primed variants GONE.
    ★★★ (r5c) DONE 2026-07-27 (commit pending-hash): chartPlus_map_eq_
    completedPlusSubring + chartPlus_eq_canonical (b=1) — THE PLUS
    RECONCILIATION IS AN EQUALITY; chart VObj plus structure canonical.
    D-ii-3 CHART-LEVEL COMPLETE: charts of 𝒴 are 𝒱-objects with
    canonical plus. ARCHITECTURE DECIDED 2026-07-27 (after re-audit):
    the M8 ambient route is DEAD for stalks/VObj — StructureSheafStalks'
    ShrinkHolds section (isLocalRing_stalk/spaVPreObj/spaVObj) is
    [IsTateRing A]-gated (the 8.14 shrink uses a top-nilpotent UNIT), and
    A_inf is not Tate; the keystone chain (RelativePieceKeystone) is
    additionally [IsNoetherianRing]+[IsStronglyNoetherian]-gated — dead
    too. The M8 instance still gives the ambient PRESHEAF (no Tate), but
    stalk data must come from the CHARTS. The chosen Y-architecture is
    the DYADIC one already started in YPresheaf.lean: limitSectionsY
    (compatible families over dyadic-trace indices ⊆ W) as the presheaf
    on Y-subsets, limitEvalTop_bijective as the basis-identification,
    2-piece + N-piece gluing as the sheaf axiom. ★ N-PIECE CHAIN GLUE
    DONE 2026-07-27 (biResQ'_chain_glue, commit b93e8020b, axiom-clean):
    rational-level formulation (q : ℕ → ℚ chain) keeps ALL spellings
    uniform (NO DyadicIdx-projection defeq-traps); induction peels the
    top piece via biResQ'_split_existsUnique + biFstQ_biResQ'_left
    endpoint transport + biResQ'_comp; PERF: RingHom.congr_fun of a comp-
    law needs rw [RingHom.comp_apply] BEFORE the inner rw can match.
    ★ ARCHITECTURE DECISION EXECUTED 2026-07-27 (beastmode, the
    'decide when (b) lands' point): the Y-object route is (i) THE
    ENLARGED CHART-RATIONAL BASIS, not (ii) VObj-glue — mathlib's
    PresheafedSpace.GlueData is C-generic but needs [HasLimits C] and
    CompleteTopCommRingCat has NO limits infrastructure (building it =
    larger than the whole E-track); every (i)-ingredient exists in-repo
    (limitSections-generic pattern, keystone-over-Tate-B_n, S1-S5 stalk
    package per chart, spaChartHomeoBigWindow, BISub_twist equality,
    the degenerate-interval circle comparison). The dyadic strip layer
    (Y-a, landed: instances + yPresheaf bundle) remains as interval-
    ring bookkeeping feeding the strip-level sheaf facts. E-TRACK PLAN
    (spawned): (E1) DONE 2026-07-27 (YCharts.lean, commit ec5109b8e):
    windowUnif/windowRing + full instance-alias package + ChartRatIdx
    (Σ-encoded) + spaSet + trace (set-level sign dispatch). NEW PERF
    LESSON (binding): a `structure` whose field type computes through
    presheafValue sends the KERNEL through the completion machinery
    and deterministically times out even when example-level uses pass
    — encode as Σ+Subtype (elaborates as a plain def) with projection
    defs. ALSO: backticks in `git commit -m` double-quoted messages
    are command substitutions — the E1 commit message lost the word
    `structure` that way; use single-quoted or heredoc messages.
    Original: (E1) ChartRatIdx — the index structure {(n : ℤ) ×
    valid rational data D over B_n} with yTrace := the
    spaChartHomeoBigWindow-image of R(D) ⊆ Y, nesting relation via
    trace-inclusion; (E2) ANALYSIS 2026-07-27 (load-bearing, three
    routes + blockers): the keystone (RelativeDescent) is parameterized
    on hspanE : span E.T = ⊤ over the BASE — false over A_inf for
    window-interior data (A_inf-units too small; T-augmentation changes
    the open). NEW OBSERVATION: over the TATE-valued D₀ = window chart
    the IMAGE span is ⊤ concretely — the chart ring inverts p and [ϖ'],
    so the image of an Iinf^N-generating T hits the unit (p[ϖ'])^N.
    The right generalization is hspanImg-primitive (span of the image
    = ⊤; genPieceDatum accepts it directly), but the 500-line keystone
    development carries hspanE through 232 threadings. ROUTES: (a) the
    general-Huber keystone package (Wedhorn 8.4 at open-span; the
    3-line imgDatumOpen variant + replay of the keystone body); (b)
    AMBIENT REVIVAL: M8 gives structurePresheaf(A_inf) free; S1-S3
    stalk machinery generic; S4's Laurent argument runs over PD :=
    presheafValue-A_inf(D) and needs PD TATE — for window-interior
    data PD inverts the p[ϖ]-image CONCRETELY (top-nilpotent unit)
    even though A_inf is not Tate — probe
    presheafValue_isTateRing_concrete's hypotheses; if per-datum
    concrete-Tate lands, ambient stalks complete with NO cross-chart
    comparison and only the SHEAF condition still routes through the
    charts; (c) dyadic/strip route (values only on strip-generated
    opens; stalks still need (a) or (b)). NEXT PROBE decides (b) vs
    (a). ★ ROUTE (b) SELECTED AND UNBLOCKED 2026-07-27: **YB1 DONE**
    (YCharts.lean): isTateRing_presheafValue_of_rationalOpen_subset_Y
    (per-datum concrete Tate over A_inf for Y-interior rationals — the
    p[ϖ]-image unit via isUnit_iff_forall_not_vle_zero_of_completePair
    + comap_canonicalMap_mem_rationalOpen (both Tate-free), nilpotent
    via .map; supporting t2Space_Ainf + nilpotence-of-mem-Iinf). ALSO
    FOUND: NonTateRationalOpenHomeomorph.lean already provides the
    8.2(2)-homeo at a supplied completion-unit — the ambient chart-
    homeo needs no base-Tate. YB-PLAN (ambient Y-object): YB2 the M8
    HasLocLiftPowerBounded(A_inf)-instantiation audit; YB3 the
    Y-relativized S4 (replay the Laurent shrink with PD-Tate := YB1);
    YB4 the Y-VPreObj (carrier Y-subspace open in Spa, presheaf :=
    ambient structurePresheaf through the open-poset iso); YB5 stalk
    fields at Y-points; YB6 the sheaf condition (still routes through
    charts / the keystone-over-B_n with the ⊤-image-span, or the
    (a)-replay). ★ YB2 DONE 2026-07-27: completeSpace_right_Ainf +
    **hasLocLiftPowerBounded_Ainf** — the ambient machinery
    (structurePresheaf, limitSections, S1-S3 stalks) instantiates at
    Spa(A_inf, A_inf). NEXT YB3: the Y-relativized S4 (Laurent shrink
    replay with PD-Tate := YB1 at Y-interior rationals).
    YB3 DEPENDENCY AUDIT 2026-07-27: the S3a/S3b OpenValue+StalkValue
    sections are ALSO [IsTateRing A]-gated, and the root dependency is
    **exists_isRational_spaOpen_subset** (RationalBasis.lean:158,
    Wedhorn 7.35(2)) whose proof route uses the Tate principal-pair
    trick (IsTateRing.exists_principal_pairOfDefinition_le_subring +
    spa_topology_eq_generateFrom at a UNIT π ∈ I). Wedhorn proves
    7.35(2) for general f-adic rings — the Tate-gate is a route
    artifact. ORDERED SURGERY LIST for the ambient Y-object: (YB3a)
    generalize the rational-basis lemma to general Huber (or prove the
    A_inf-specific basis via I := Iinf, no unit — examine
    spa_topology_eq_generateFrom's use of the unit first); (YB3b)
    de-Tate the OpenValue/StalkValue sections (their content uses the
    basis + presheafValue-instances now available Huber-free); (YB3c)
    the shrink S4 replay at Y-points with PD-Tate := YB1. Each bounded;
    they stack — keep each its own commit. ★ YB3a DONE 2026-07-27
    (RationalBasisHuber.lean): exists_isRational_spaOpen_subset_huber
    — the general-Huber 7.35(2) with power-certificate validity
    (toDatumOpen/isRational_of_pow_le/interDatumOpen + certified fold
    + Tate-free generateFrom copy). NEXT YB3b: de-Tate OpenValue/
    StalkValue (swap exists_isRational_spaOpen_subset → _huber; check
    remaining Tate-uses in those sections), then YB3c the shrink.
    ★ YB3b DONE (S3 sections de-Tated in place, library green).
    ★ YB3c DONE 2026-07-27 (YStalks.lean): rationalShrink_Y (the 8.14
    Laurent shrink at Y-interior rationals; YB1-Tate + primed open-
    presentation + huber basis + complete-pair criterion) →
    stalkShrink_Y → **isLocalRing_stalk_Y + maximalIdeal_stalk_Y** —
    the ambient structurePresheaf(A_inf) has the full Wedhorn 8.14
    stalk package at every Y-point, axiom-clean. REMAINING for the
    Y-VObj (YB4-6): YB4 the Y-carrier VPreObj packaging (ambient
    presheaf through the open-poset iso of the open subset Y); YB5 =
    done-by-YB3c modulo the packaging; YB6 the sheaf condition (per-
    window through the charts / keystone-over-B_n route (a)).
    ★★ YB4+YB5 DONE 2026-07-27 (YStalks.lean): **yVPreObj** — 𝒴 as an
    object of 𝒱^pre: PresheafedSpace.restrict of the ambient
    structurePresheaf along the open inclusion (yPresheafedSpace),
    restrictStalkIso-based ring-stalk equivalence (point spelled via
    the inclusion for definitional stalk-type alignment), 8.14-fields
    transported (instance-explicit maximalIdeal_comap_ringEquiv).
    REMAINING for the Y-VObj: **YB6 only** — IsSheafOfTopologicalRings
    of the restricted presheaf (per-window via the charts + the
    keystone-over-B_n route (a), or a direct refinement argument);
    then D-iii (φ-action as VObj-isos, X := Y/φ^ℤ).
    ★ YB6a DONE 2026-07-27 (RelativeDescentHuber.lean): the FULL
    keystone at open-span certificates — imgDatumO + keystoneO
    (𝒪_A(E) ≃+* 𝒪_B(imgDatumO)) + continuity + squares, over any
    Huber base (systematic O-transform of RelativeDescent, ~700
    lines). NEXT YB6b: the certificate supplier
    (span_image_eq_top over a Tate B for open-ambient-span E.T — the
    p[ϖ]-unit argument) + the window-value identification (ambient
    Y-interior datum ↦ B_n-side value through keystoneO at D₀ :=
    windowChartData); then YB6c the Hom-cont sheaf assembly for
    yPresheafedSpace. ★ YB6b DONE 2026-07-27 (YStalks.lean):
    bigWindow_eq_rationalOpen_windowUnif +
    isUnit_canonicalMap_p_teichPi_window +
    **span_image_windowChart_eq_top** — keystoneO applies at any
    window chart against any valid ambient rational. YB6c REMAINING
    (the last Y-VObj brick): the IsSheafOfTopologicalRings assembly —
    per-window: ambient sections over window-interior opens vs the
    B_n-side structure presheaf through keystoneO-value-identification
    + isSheafy_presheafChart; then the Y-cover refinement. Substantial
    assembly; all substrates now exist. ★ YB6c-1 DONE (windowKeystone
    — keystoneO instantiated at the windows). ★ YB6c-2 DONE
    (exists_pow_le_of_isRational — certificates at any valid datum's
    own pair; the certificate supply is COMPLETE). REMAINING YB6c-3
    (the last Y-VObj brick, precisely scoped): (i) the Y-LOCAL
    IsLimitSheaf: valid Y-interior D + valid rational cover ⇒ the
    equalizer at presheafValue-A_inf(D) — subordinate the cover to
    window pieces (interDatumOpen at the new certificates; NO
    compactness — the generic limit-glue handles arbitrary covers;
    AVOID isCompact_spaOpen: Tate-gated AND its noHArch core is
    sorry-tracked upstream), transport through windowKeystone (the
    keystoneO squares) to the B_n-side IsLimitSheaf
    (isSheafy_presheafChart chain); (ii) replay
    StructurePresheafBundled's structurePresheaf_isSheafOfTopological-
    Rings (~599) at the restricted-to-Y site with (i) in place of
    IsLimitSheaf. Then yVObj := ⟨yVPreObj, that⟩ and D-iii (φ-action,
    X := Y/φ^ℤ) follows. ★ YB6c-3a DONE (IsSheafyOn stated, YStalks).
    NEXT bricks in order: (3b) imgCoveringO — the B_n-side covering
    from a window-interior ambient covering (base/covers via imgDatumO
    at the YB6b certificates; hsubset via imgDatumO_rationalOpen_
    subset; hcover via the comap-correspondence — rationalOpen has
    Spa-membership BUILT IN, so B-side points pull back through
    comap_canonicalMap_mem_rationalOpen (Tate-free) and push forward
    by pure comap_vle); ★ 3b DONE
    (RelativeDescentHuber: mem_imgDatumO_rationalOpen_iff +
    imgDatumOTot/imgCoversO/imgCoveringO + rationality; PERF: dite-
    guarded total function instead of dependent attach-image).
    ★ 3c GLUING DONE 2026-07-27
    (RelativeDescentHuber): **exists_glue_of_imgCovering** — the
    single-D₀ gluing transport end-to-end (imgFamily_restriction +
    the transported all-data compatibility + B-glue + keystone
    pullback + choice-coherent recovery); every hypothesis window-
    dischargeable. ★ EMBEDDING HALF DONE 2026-07-27
    (isEmbedding_productRestrictionSub_of_imgCovering — the comparison
    map + squares + IsInducing/Injective.of_comp cancellation). THE
    FULL SINGLE-D₀ SHEAF TRANSPORT IS COMPLETE (both IsSheafy-fields).
    ★ 3c′ DONE 2026-07-27 (commits c73e37a1f + 49b6ee4f7, YStalks):
    isSheafy_congr_plusSubring (PlusSubring is the only data-valued
    instance in IsSheafy's signature — subst + proof-irrelevance),
    chartPlus_instance_eq_canonical (congrArg PlusSubring.mk of the
    r5c chartPlus_eq_canonical, general (a,1)), isSheafy_canonical_window
    (isSheafy_presheafChart at (p,1)/windowUnif + the instance
    transport), **isSheafyOn_window** (both single-D₀ transports at
    D₀ := window datum, hcertAll := span_image_windowChart_eq_top).
    ★ 3d REDESIGNED 2026-07-27 — **NO adjacent-circle glue needed**:
    quasicompactness kills the straddle. Kit verified present:
    isCompact_subtype_rationalOpen₂ (SpaQCviaSpvAI, two-generator
    7.35(2)), Curve.ainf_pair_spec (private — REPLICATE ~10 lines:
    pairOfDefinition_ofAdic at Iinf, g₁ = p, g₂ = [ϖ], A⁺ = ⊤),
    rationalOpen_isOpen (RationalSubsets 154, unconditional),
    mem_rationalOpen_chartData_iff (general (u,v,a,b)), KGE_iff/KLE_iff,
    isSheafy_presheafChart + chartPlus_instance_eq_canonical at
    general (a,1), rhoRight_pow_exact general. Steps:
    (3d-1) runChart n k := chartData p F (windowUnif n) 1 1 (p^(k+1)) 1
    — κ-interval [p^(n-k), p^(n+1)] (κ(v'^t) = p^(n+1)/t); covers
    bigWindow j for n-k ≤ j ≤ n. runWindow_eq: rationalOpen (runChart
    n k) = {v ∈ Y | KGE p^(n-k) ∧ KLE p^(n+1)} — generalize
    bigWindow_eq_rationalOpen_ofNat/_neg's proof (ℤ-match on n +
    sign-split of n-k for the hab ℕ-quotient shapes; the vle-exponent
    bookkeeping through mem_rationalOpen_chartData_iff at a = p^(k+1)).
    Then bigWindow_subset_runChart (KGE_mono/KLE_mono) and
    runChart_rationalOpen_subset_Y (from the eq).
    (3d-2) isUnit_canonicalMap_p_teichPi_runChart +
    span_image_runChart_eq_top — verbatim replays of the window
    versions (their proofs are chart-generic; only the ⊆-Y input
    changes to runChart_rationalOpen_subset_Y).
    (3d-3) isSheafy_canonical_runChart + isSheafyOn_runChart —
    verbatim replays at a := p^(k+1) (hexact2 := rhoRight_pow_exact).
    (3d-4) isCompact_subtype_rationalOpen_ainf (E) (hErat) — replicate
    ainf_pair_spec + radical-from-openness (IsRational = IsOpen span T
    → ∃ m, Iinf^m ≤ span T via adic nhds-basis as in
    span_image_windowChart_eq_top's obtain; then Iinf ≤ radical by
    pow_mem_pow).
    (3d-5) **isSheafyOn_Y**: C valid, base ⊆ Y ⇒ base-trace compact
    ⊆ ⋃ (open window traces) ⇒ finite J ⇒ base ⊆ runChart (max J)
    (max J - min J) at Spv-level (rationalOpen carries Spa-membership)
    ⇒ both fields from isSheafyOn_runChart.
    ★★ 3d COMPLETE 2026-07-27 (commits c4bee684a + 0939fac00 +
    7325dd490, all axiom-clean, every step FIRST-TRY): runWindow n k
    (κ ∈ [p^n, p^{n+k+1}], NOTE runs extend UPWARD from n),
    runWindow_eq_rationalOpen (ℤ-match; ofNat mirrors
    bigWindow_eq_rationalOpen_ofNat with hmul : p^{k+1}·p^n = p^{n+k+1};
    neg case at pPow (p^m) needs NO vle_pow_iff — hteich substitutes
    directly; KLE_iff's hab at the UNREDUCED fraction p^{k+1}/p^m kills
    the sign-split), bigWindow_subset_runWindow, runWindow_subset_Y;
    isUnit_canonicalMap_p_teichPi_runChart + span_image_runChart_eq_top
    + isTateRing_runChart + isSheafy_canonical_runChart +
    isSheafyOn_runChart (verbatim window replays at a := p^(k+1));
    ainf_pair_spec' (replicated private from Curve) +
    isCompact_subtype_rationalOpen_ainf (7.35(2)₂ + radical from
    IsRational-openness via the adic nhds basis);
    exists_runChart_superset (elim_finite_subcover over window traces,
    J' := insert 0 J for nonemptiness, min'/max' + toNat) ⇒
    **isSheafyOn_Y** — the FULL Y-interior sheaf condition over the
    non-Tate ambient A_inf.
    ★★★ 3e COMPLETE 2026-07-28 (commits 56b12fe81 + 5788c6996, all
    axiom-clean) — **yVObj: 𝒴 IS AN OBJECT OF WEDHORN'S 𝒱. THE
    YB-TRACK HEADLINE IS CLOSED.** Pieces:
    (3e-1/2, RestrictedLimitSheaf.lean — NEW GENERIC FILE, cleanup
    note: could migrate next to SheafyPair): interValid (Tate-free
    interRational via exists_pow_le_of_isRational_pair certificates at
    D.P, choice-wrapped) + 4-lemma API; allData_huber (the R3 bridge
    composite re-proven on interValid — ExactIntersectionCompatible
    never needed); interCoveringPiecesV/interCoveringV;
    IsSheafyOn.separationSub; exists_finite_rational_refinement_huber
    (basis := exists_isRational_spaOpen_subset_huber, compactness a
    HYPOTHESIS); the three S-relative engines (verbatim SheafyPair
    copies, consumption sites patched to hOn.* + subset-derivations via
    RationalLocData.rationalOpen_subset_of_trace); IsLimitSheafOn
    structure (fields need explicit {V}{ι U} lambda-binders at
    construction!) + of_isSheafyOn + homGlue.
    (3e-3, FarguesFontaine/YSheaf.lean — NEW): isLimitSheafOn_Y;
    yFunctor (open-image) + trace/cov/inf lemmas (image_inter needs
    the ConcreteCategory.hom-spelled injectivity);
    limitRestrict_cross_eq_of_opens_eq (subst-transport, kills the
    reindex friction); yPresheaf_map_apply := structurePresheaf_map at
    the composed spelling (EXPLICIT morphism arg — placeholder fails);
    yPresheaf_isSheafOfTopologicalRings (homGlue at V' := image(iSup U),
    hle := leOfHom∘map so the conclusion is definitional; compat via
    pointwise trans-chains, NO rw-motives); **yVObj**.
    REMAINING ON THE Y/X-TRACK: D-iii (φ-action as VObj-isos; the
    biPhiQ interval layer is complete), X := Y/φ^ℤ (Curve.lean has the
    topological quotient + CompactSpace already).
    ★ D-iii PROGRESS 2026-07-28 (all axiom-clean):
    (D-iii-1, commits 371a67504 + 365a37beb) NEW FILE
    RingEquivPresheafTransportHuber.lean — the TATE-GATE of
    RingEquivPresheafTransport dissolved: locMapAway (datum-free
    localization pushforward) + closure-induction locSubring mapping;
    RationalLocData.mapHuber (hopen transported directly — no
    genPieceDatum/span); mapHuber_isRational (openness through the
    open map); presheafValueRingEquivHuber (pvFwd/pvBwd pattern at
    presheafValueMapOfHom — which was Huber-generic all along!) with
    continuity both ways, canonicalMap + restriction naturality (fwd
    and symm), comap-preimage description of transported opens; datum
    roundtrips via RationalLocData.ext' + pair-roundtrips. GOTCHAS:
    pass TYPED hs-lemmas (hs_fwd') not bare rfl (rw-matching needs the
    binder-shape); congrArg with EXPLICIT function at coe-mismatches;
    finset_symm_image_image has a Classical-instance mismatch — use
    Finset.image_image + image_congr + image_id.
    (D-iii-2a, commit 2da664187) FarguesFontaine/FrobeniusSpa.lean —
    frobPow k (RingAut-zpow) bicontinuous (continuity via the
    const-smul instance; symm = frobPow (-k)); comap_frobPow_eq_smul
    (alignment with the φ^ℤ-action); spaFrobHomeo; spaFrob_preimage_
    spaOpen (= spaOpen of mapHuber (frobPow k)); ySpaSet stability.
    (D-iii-2b, commit 28ee54ce2) FarguesFontaine/FrobeniusLimit.lean —
    frobOpens/frobIndex; limitFrobHom (the transport of ambient limit
    sections; Pi.ringHom-of-composites + codRestrict so ALL ring laws
    are FREE — the direct where-fields hit isDefEq walls through the
    Subring-coe instances); continuity via continuous_induced_rng +
    shallow rfl-bridges; limitRestrict-naturality DEFINITIONAL.
    (D-iii-3a, commit e8ba952d8) ambientFrobHom : the ambient
    presheafed-space endo (spaFrobTop + ambientFrobNat; naturality by
    trans-chains through structurePresheaf_map — calc FAILS across
    defeq-distinct Opens-instance spellings (SpaTop.str vs subtype),
    Eq.trans-terms unify fine).
    (D-iii-3b, commit 1ee9043e6) **yFrobHom : the Frobenius
    endomorphism of the 𝒴-presheafed space** — two-sided ySpaSet
    stability, yFrobTop, yFunctor_frobOpens (image-functor commutes
    with the Frobenius preimage), and the INDEX-BRIDGED Y-transport
    (yFrobIndexBridge casts indices along the opens-equality at the
    ⊆-Prop, so NO eqToHom algebra appears and yFrobNat's naturality
    is DEFINITIONAL — Subtype.ext∘funext∘rfl).
    NEXT (D-iii-4): the VPreHom fields for yFrobHom (isLocalHom on
    ring stalks + val-compat through yRingStalkIso) and the iso
    (k/-k roundtrips at PresheafedSpace-Hom level); then the VObj-iso
    of yVObj and X := Y/φ^ℤ packaging.
    ★ D-iii-4a DONE 2026-07-28 (commit 8460f29a2, axiom-clean):
    FarguesFontaine/FrobeniusValuation.lean —
    comap_presheafValueRingEquivHuber_pointValue (+_symm variant): the
    Huber value equivalence intertwines pointValue (proof =
    eq_pointValue_of_comap_eq + the canonicalMap-naturality chain);
    spaFrob_mem_frobIndex_datum; **comap_limitFrobHom_openValue** —
    the Frobenius transport of limit sections intertwines the open
    valuations (choice-independence at frobIndex-images + the
    composite-eval collapse + the symm-pointValue equivariance).
    ★★ MAJOR PERF LESSON (kernel `(kernel) deterministic timeout`,
    cost ~2h of bisection): (i) NEVER inline a tactic proof in a
    structure/subtype literal inside a `def` — every later
    `.1`/`.2`/field-projection makes the kernel walk the literal
    (spaFrob's Spa-membership, frobIndex's subset, mapHuber's hopen
    all extracted to named lemmas); (ii) `lake env lean` PASSED a decl
    that `lake build` kernel-rejects — the build is the ONLY gate for
    kernel-budget issues (extends the known env-lean-false-errors
    memory to false-SUCCESSES); (iii) componentwise-`rfl` composite
    collapses (RingHom.ext fun x => rfl) blow the kernel when the
    components' coercion-paths differ (RingEquiv-coe vs
    .toRingHom-coe) — chain the PROVEN component-lemmas
    (limitEvalHom_apply, limitFrobHom_component) with congrArg/trans
    instead; (iv) comap-of-comp = nested-comaps IS generic-rfl-cheap
    when stated as its own tiny lemma (comap_comp_apply) but
    over-budget inlined at fat homs; (v) rw with an instance-path
    mismatch (SubsemiringClass- vs CommRing-derived NonAssocSemiring
    on limitSections) silently fails pattern-matching — use congrArg
    with an explicit function.
    NEXT (D-iii-4b): stalk-level val_compat — conjugate
    ringStalkMap (yFrobHom k) through yRingStalkEquiv to the ambient
    stalk transport; stalkValue-equivariance from
    comap_limitFrobHom_openValue via comap_germ_stalkValue +
    stalkVle intro/elim; then isLocalHom (via the iso-route) and the
    VObj-iso; then X.
    ★ D-iii-4b AMBIENT CORE DONE 2026-07-28 (commit c4d199fbd,
    axiom-clean): ringStalkMap_ambientFrob_germ (germ naturality of
    the categorical stalk transport — the stalkFunctor_map_germ_apply
    + stalkPushforward_germ_apply chain; SPELLING DISCIPLINE: state
    everything at ConcreteCategory.hom + the (presheaf ⋙ forget)
    composite, NOT ringPresheaf/Hom.hom/spaRingPresheaf mixes — every
    mixed spelling kills the rw-unifier); frobOpens roundtrips;
    openValue_vle_frobTransport (the vle-transport core as a
    PROP-EQUALITY — comap_vle is stated with = not ↔);
    stalkVle_congr (subst-transport);
    **comap_ringStalkMap_ambientFrob_stalkValue** — the ambient
    stalk-valuation equivariance, both directions via
    exists_common_rep + stalkVle_elim + the double-restrict collapse
    (limitRestrict_comp + limitFrobHom naturality) + the transport
    core + germ_limitRestrict collapses; NO rw-at-fat-hyps — all
    Eq.mp/trans/congr chains.
    REMAINING for val_compat: the RESTRICT-side conjugation
    (ringStalkMap (yFrobHom k) vs the ambient transport through
    yRingStalkEquiv/restrictStalkIso) + the final assembly; then
    isLocalHom + the VObj-iso; then X.
    ★ D-iii-4c/4d DONE 2026-07-28 (commits f8da94013 + the val_compat
    commit, axiom-clean): ringStalkMap_yFrob_germ (restricted germ
    naturality; the hunfold-rfl + hsplit-∀-rfl + congrArg/trans
    pattern — NEVER rw on ConcreteCategory-vs-Hom.hom-mixed goals);
    yRingStalkIso_hom_germ (restrictStalkIso_hom_eq_germ_apply
    restated at the 𝒴-spellings — spaRingPresheaf for ALL ambient
    germs, defeq-bridged once at the exact-site);
    limitFrobHom_bridge (the section bridge along yFunctor_frobOpens,
    componentwise-rfl); **ringStalkMap_yFrob_conj** (the conjugation
    square via stalk_hom_ext + the three germ lemmas);
    **yFrob_val_compat** (val ∘ base = comap-of-stalk-map ∘ val:
    comap-comp rfl-chains + the square + the ambient equivariance).
    REMAINING: isLocalHom_stalkMap for yFrobHom (iso-route: the stalk
    map is an iso since components are isos — or direct units-reflect
    through the germ-naturality + the k/-k roundtrip); the VPreHom
    bundle + the VObj-auto-iso; X := Y/φ^ℤ packaging.
    ★★ D-iii-4e DONE 2026-07-28 (commit 3048f0582, axiom-clean):
    yFrob_isLocalHom — the VALUATION ROUTE (20 lines, no iso/roundtrip
    machinery!): units correspond exactly through yFrob_val_compat +
    yVPreObj.val_supp (supp = maximalIdeal) + supp_comap; the
    mem_maximalIdeal-sites need @-EXPLICIT IsLocalRing instances
    ((yVPreObj).isLocalRing_stalk — TC can't find them across the
    ringStalk/ringPresheaf.stalk carrier spellings).
    **yFrobVPreHom k : VPreHom yVPreObj yVPreObj — THE FROBENIUS IS A
    MORPHISM OF WEDHORN'S 𝒱^pre ON 𝒴** (toHom := yFrobHom k;
    isLocalHom + val_compat proven). φ^ℤ acts by k ↦ yFrobVPreHom k.
    REMAINING (D-iii tail): the k/-k composite-identity (the VPreHom
    iso — OPTIONAL packaging, parked).
    ★ D-iv PLAN (2026-07-28, the X-object as quotient descent —
    the definition-layer capstone). ARCHITECTURE: 𝒪_X(V) := the
    φ-INVARIANT sections of 𝒪_Y(π⁻¹V) — (π_* 𝒪_Y)^{φ^ℤ}; invariance
    CAST-FREE via the stability equality: for an ambient W' :=
    yFunctor(π⁻¹V) one has frobOpens 1 W' = W' (saturation), and s is
    invariant iff limitFrobHom 1 W' s = limitRestrict (le_of_eq
    hstab.symm) s — both sides in limitSections (frobOpens 1 W'), NO
    casts. Generator-invariance suffices for the definition.
    Sub-tickets:
    (D-iv-1) saturation infra: curveOpens V ↦ the saturated Y-open
    π⁻¹V (isOpenQuotientMap_toCurve gives openness); ySpa-level: the
    ambient image W' and its Frobenius stability frobOpens k W' = W'
    (from the π-saturation: w ∈ W' ⟺ spaFrob k w ∈ W' — orbit-wise);
    the Galois correspondence opens(X) ≅ saturated-opens(Y).
    (D-iv-2) frobFixedSubring W' hstab : Subring (limitSections W');
    CLOSED (equalizer of the continuous limitFrobHom and the
    continuous cast-restrict into the T2 target) hence complete;
    restriction maps preserve invariance (limitFrobHom_limitRestrict
    + le_of_eq-squares); the X-presheaf xStructurePresheaf :
    Presheaf CompleteTopCommRingCat (CurveTop) with obj V :=
    .of (frobFixed (π⁻¹V)); functoriality from limitRestrict.
    (D-iv-3) stalks: at c = π(y) the invariants-stalk ≅ 𝒪_Y-stalk at
    y through the window local sections (injOn_toCurve_windowU/V +
    curve_eq_image_window_zero; each germ has a unique invariant
    extension along the orbit — freeness+wandering). Local rings +
    stalk valuations transport.
    (D-iv-4) the sheaf condition for xStructurePresheaf from
    isSheafyOn_Y/yVObj (saturated covers pull back; the invariants
    form an equalizer that commutes with the sheaf equalizers).
    (D-iv-5) xVObj : VObj — THE ADIC FARGUES–FONTAINE CURVE AS A
    𝒱-OBJECT; plus CompactSpace (done in Curve.lean).
    STATUS: D-iv-1 DONE + D-iv-2 CORE DONE 2026-07-28 (CurveObject.lean,
    axiom-clean): yTopToY/yTopToCurve carrier bridges (double-subtype:
    y.1.1/y.2 spellings), yTopToY_yFrobTop (= the ofAdd(-k)-action via
    spaFrob_coe), yTopToCurve_yFrobTop (fiber preservation via
    Quotient.sound), curvePreimage (saturated opens),
    map_yFrobTop_curvePreimage + frobOpens_yFunctor_curvePreimage
    (stability, carrier + ambient — the ambient one is a 2-line rw of
    yFunctor_frobOpens), **frobFixed** := RingHom.eqLocus of the
    transport against limitRestrict (le_of_eq stability) — CAST-FREE —
    + mem-iff + isClosed (isClosed_eq of the two continuities).
    NEXT (D-iv-2 tail): restriction maps preserve invariance
    (limitFrobHom_limitRestrict + the le_of_eq-square) → the
    X-presheaf functor xStructurePresheaf on Opens (Curve) with
    CompleteTopCommRingCat-values (subring topology; completeness
    from isClosed_frobFixed + completeSpace of limitSections —
    check the limitSections-CompleteSpace instance's availability);
    then D-iv-3 stalks.
    ★★ D-iv-2 COMPLETE 2026-07-28 (commit aa71704e2, axiom-clean):
    frobFixed_restrict (invariance survives restriction — the two
    limitRestrict_comp collapses MEET IN THE MIDDLE by
    proof-irrelevance of the composite ≤'s, 1st try);
    frobFixedRestrict (codRestrict) + continuity (induced_rng +
    shallow hfun-rfl); frobFixed.completeSpace (closed-in-complete) +
    frobFixed.isUniformAddGroup (the IsUniformInducing.subtype pattern
    from StructurePresheafBundled 65); **xStructurePresheaf : the
    STRUCTURE PRESHEAF OF THE ADIC FARGUES–FONTAINE CURVE** — obj :=
    .of (frobFixed V) (letI the two instances — the section-variable
    instances do NOT fire through TC at the .of-site, letI them),
    map := frobFixedRestrict, functor laws by
    Subtype.ext∘Subtype.ext∘funext∘rfl.
    NEXT (D-iv-3, stalks): at c = π(y) the invariants-stalk ≅ the
    𝒴-stalk at y — design: the germ-map xStalk c → yStalk y by
    forgetting invariance (restrict the invariant section to the
    saturated preimage then germ at y — as a colimit-map along
    curvePreimage: Opens(X) ∋ V ↦ yFunctor(curvePreimage V) is a
    functor into Opens(Spa) with y-membership ⟺ c-membership);
    inject+surject via the window sections: any 𝒴-germ at y extends
    uniquely to an invariant section on a small saturated open
    (spread the section along the orbit through the yFrobVPreHom
    transports; freeness/wandering gives disjoint windows —
    injOn_toCurve_windowU/V); then local rings + valuations pull
    back and (D-iv-4) the sheaf condition; (D-iv-5) xVObj.
    ★ D-iv-3(i) DONE 2026-07-28: curveSpace : TopRingPresheafedSpace
    (CurveTop + xStructurePresheaf); piYHom : yPresheafedSpace ⟶
    curveSpace (base := the quotient projection, c := the subtype
    inclusion of invariants — continuity is plain
    continuous_subtype_val since frobFixed carries the induced
    topology; naturality by the double-Subtype.ext-rfl). The stalk
    comparison ringStalkMap piYHom y : xStalk(π y) ⟶ yStalk(y) is now
    FREE from the generic machinery.
    NEXT (D-iv-3(ii) — the DEEP core): the stalk map is bijective.
    Surjectivity = the invariant-extension lemma: a germ at y is
    represented on a small W ∋ y with W inside a window and the
    translates (yFrobTop k)⁻¹ W pairwise disjoint
    (exists_nhd_smul_disjoint, Curve.lean 90); spread the section by
    the transports to the disjoint union ⋃ₖ translates = a SATURATED
    open (the preimage of the open image π(W) — π open!); the spread
    family glues by the 𝒴-sheaf condition (yVObj/isLimitSheafOn_Y at
    the DISJOINT cover — compatibility trivial on empty overlaps
    modulo the k-th self-overlaps where the transport-coherence
    (the k+l composite law of limitFrobHom!) enters — NOTE: the
    composite law limitFrobHom (k+l) = limitFrobHom k ∘ limitFrobHom l
    modulo frobOpens-composite-casts is NOT YET PROVEN — it is the
    one missing algebraic identity; prove it componentwise from
    presheafValueRingEquivHuber-functoriality in e (mapHuber-comp:
    mapHuber e₂ ∘ mapHuber e₁ vs mapHuber (e₂∘e₁) — datum-level via
    RationalLocData.ext' + value-level via the dense-image
    uniqueness). Injectivity = separation on the saturated cover.
    This is a multi-step arc: (3ii-a) mapHuber-comp + pvHuber-comp
    functoriality; (3ii-b) limitFrobHom-comp; (3ii-c) the disjoint
    translate cover + invariant extension; (3ii-d) stalk bijectivity;
    then local rings/valuations transport (3ii-e).
    ★ (3ii-a) DATUM LEVEL DONE 2026-07-28: mapRingEquiv_comp (pair;
    the ideal-HEq via ideal_map_heq_of_targets_eq — subst + RingHom
    -ext with coercion-agreement fun _ => rfl) + mapHuber_comp
    (RationalLocData.ext' + Finset.image_image), axiom-clean.
    ★★ DESIGN SIMPLIFICATION (3ii-c): the pv-level composite law is
    NOT needed! Spread the germ by ITERATING the GENERATOR transport
    (Function.iterate of limitFrobHom 1) piece-by-piece; with W small
    enough (exists_nhd_smul_disjoint) the distinct translates are
    PAIRWISE DISJOINT, so the gluing-compatibility over the saturated
    union is VACUOUS off the diagonal — the 𝒴-sheaf gluing
    (isLimitSheafOn_Y.glue at the translate cover, all inside Y-trace)
    produces the extension; its INVARIANCE follows from gluing
    separation (the transport permutes the pieces by one shift).
    The value-level composite (pvHuber-comp via dense-image
    uniqueness + restrictionMap_cast) stays PARKED as nice-to-have.
    ★ (3ii-c) SETUP DONE 2026-07-28 (CurveObject.lean, axiom-clean):
    yTopToY_bijective + yTopToY_isInducing (the two subtype
    presentations of 𝒴 — Spa-side double-subtype vs Spv-side —
    topologically agree; the val-congrArg needs the EXPLICIT
    ↥Y-lambda) → yTopToYHomeo; isOpenQuotientMap_yTopToCurve
    (factors through the homeo); xImage (open images on the curve);
    **curvePreimage_xImage : the saturation identity — preimage of
    the image = ⨆ k, the k-th Frobenius translate** (orbit chase with
    the sign -(toAdd g); Quotient.eq'' + MulAction.orbit both ways).
    NEXT (3ii-c core): (α) the wandering separation at the yTop-level:
    for y exists W ∋ y with translates pairwise disjoint (mirror
    exists_nhd_smul_disjoint through yTopToYHomeo); (β) the invariant
    extension: for s over such W, the family (iterated generator
    transports on the translates) glues over curvePreimage (xImage W)
    (= ⨆ translates by the saturation identity) via
    isLimitSheafOn_Y.glue — compat VACUOUS on disjoint pieces; the
    glued section is generator-invariant by separation; (γ) stalk
    surjectivity/injectivity of ringStalkMap piYHom from (β).
    ★★★ (3ii-c β) COMPLETE 2026-07-29 (commits through 5b4c39f5c, all
    axiom-clean): the FULL INVARIANT-EXTENSION LEMMA. The engine:
    limitFrobHom_add (additivity of the limit transport — componentwise
    through presheafValueRingEquivHuber_comp_apply/_symm (dense-image
    uniqueness) + congr_e + the composed-restriction/section-compat
    collapse; TRANS-SPELLED continuity bridges (Continuous ⇑(e₁.trans
    e₂)-typed haves) defuse the ∘-vs-trans coercion mismatches);
    piece_shift/translateFam_succ (SUBTRACTION-FREE indexing at 1+m —
    the k−1-form makes rw-motives type-incorrect); limitFrobHom_double
    (inverted additivity); glue_piece_eq (the 7-step calc: comp-
    collapse, naturality, hg m, succ.symm, roundtrip-id, hg (1+m),
    comp-collapse — FIRST TRY); **glue_invariant** (sheaf separation
    over the shifted translate cover, ULift-indexed, membership-form
    covering to dodge the Opens-instance spellings; SetLike.coe for
    the iUnion); **exists_invariant_extension** (bundled: a section
    over a wandering-separated W extends to ↥(frobFixed (xImage W))
    restricting back on the zero translate).
    ★★ (γ i/ii) DONE 2026-07-29 (commits a52bad1b9 + 1a49ef29b,
    axiom-clean): ringStalkMap_piYHom_germ (the projection germ
    naturality — the established hunfold/hsplit/trans pattern held
    first-try); yRingPresheaf_map_apply + yGerm_limitRestrict (the
    restricted-presheaf germ-restriction collapse via the generic
    TopCat.Presheaf.germ_res_apply); **ringStalkMap_piYHom_surjective
    — STALK SURJECTIVITY of the curve projection**: represent the
    germ (TopCat.Presheaf.exists_germ_eq — GENERIC, works for any
    presheaf), shrink into a wandering neighbourhood (Disjoint.mono
    for the translate-disjointness of the inf), apply the invariant
    extension, and chase both germs to the zero translate
    (fully-parenthesized germ-applications — bare `.germ V y h t`
    across linebreaks misparses in calc).
    REMAINING (γ iii): injectivity — invariant_piece_determined
    (ℤ-induction via translateFam_succ both directions) +
    invariant_sections_agree + the germ-level conclusion; then the
    stalk RingEquiv (ofBijective), local/val transport, D-iv-4 sheaf
    condition, xVObj (D-iv-5).
    ★★★ D-iv COMPLETE 2026-07-30 (commits 91520683b..60a4d10e8, all
    axiom-clean). (γ iii) INJECTIVITY: invariant_piece_transport/step
    (the (1+m)-piece of an invariant section is the transport of its
    m-piece); the INVERSION TOOLKIT (frobOpens_inv_collapse,
    limitFrobHom_eq_zero_of — INDEX-GENERALIZED (c)(hc : c = 0) to
    dodge the hetero-index rw, limitFrobHom_leftInv,
    limitRestrict_eq_injective, limitFrobHom_injective);
    invariant_piece_step'/back' (hk : 1 + m = k index-flexible forms —
    Int.induction_on's pred-case is at -n-1 NOT -(n+1), pass
    m := -(n:ℤ)-1); invariant_pieces_eq (full ℤ-determination);
    invariant_sections_eq_of_zero_piece (separation at the translate
    cover, ULift-indexed, V := explicit + inline yFunctor_trace — the
    Opens-ascription across SpaTop/Spa spellings FAILS, state hcov at
    single-coe + SetLike.coe); **ringStalkMap_piYHom_injective**
    (germ-shrink via TopCat.Presheaf.germ_eq — NO rw at the
    base-point-spelling germs, trans-chain through
    ringStalkMap_piYHom_germ both sides; U ⊓ W₀ wandering shrink;
    frobFixedRestrict collapse by germ_res_apply, curve-side map is
    rfl = curveRingPresheaf_map_apply). (γ iv) PACKAGING: fiberPoint
    (Classical section of the quotient), xStalkEquiv (stalkCongr along
    Inseparable.of_eq + RingEquiv.ofBijective of the stalk map),
    isLocalRing_xStalk, yStalkValue/yStalkValue_supp (STANDALONE —
    yVPreObj.val-projections DON'T UNFOLD at coercion-elaboration
    transparency; inline the comap-form), **xVPreObj**. (D-iv-4)
    xPresheaf_isSheafOfTopologicalRings: homGlue at the saturated
    preimages (curvePreimage_inf/iSup — preimage commutes with
    inf/iSup; hoisted-have opens-eqs, NEVER curvePreimage-of-⊓ inside
    rw patterns — the Opens-instance spelling of the binder's U kills
    the reducible unifier), invariance of the glued section by
    separation over the SAME saturated cover (stability
    frobOpens 1 U'ᵢ = U'ᵢ makes the pieces themselves stable — no
    shifts needed, unlike glue_invariant); uniqueness through
    piComponent + huniq. (D-iv-5) **xVObj : VObj — THE ADIC
    FARGUES–FONTAINE CURVE IS AN OBJECT OF WEDHORN'S CATEGORY 𝒱**
    (CurveObject.lean; the definition-layer capstone of the D-track).
    ★ (3ii-c α + compat unblocking) DONE 2026-07-28 (commit 4258ce942,
    axiom-clean): presheafValue_subsingleton_of_rationalOpen_empty_huber
    (generic Huber via the Spa-point criterion at f := 0 — IsUnit 0 ⟺
    no Spa-points since vle 0 0 always holds; a point would comap into
    the empty rational; 0 = 1 by isUnit_zero_iff) — the disjoint-piece
    gluing compat is now dischargeable by Subsingleton.elim;
    exists_disjoint_translates (yTop-level wandering; needs open
    Pointwise; ofAdd-cancel by ← ofAdd_add + simp).
    NEXT (β, r75 plan): (1) limitSections-subsingleton over ⊥/disjoint
    infs (componentwise from the empty-value subsingleton); (2)
    mapHuber_one + presheafValueRingEquivHuber-at-one = id
    (dense-image uniqueness); (3) spaFrob_zero/frobOpens_zero/
    limitFrobHom_zero; (4) invariantExtension := isLimitSheafOn_Y.glue
    at the translate cover (hle/hcov from curvePreimage_xImage +
    image-preserves-sups; fam k := restrict∘limitFrobHom k; compat:
    diagonal refl, off-diagonal Subsingleton.elim). Non-critical parked:
    T908(c), T910 Moreover + A^r iso, T909 V₀ notes, PERF-1, E2/E3
    (dormant — the ChartRatIdx/E-track is SUPERSEDED by the ambient
    yVObj route for the sheaf condition; keep E1 as chart index infra). (superseded: the EMBEDDING-half transport
    (productRestrictionSub through the keystone equivalences — same
    square machinery, topological); then (3c′) the window-instantiation
    of both halves (IsSheafyOn-single-window). (3c-orig) the single-window transport of embedding+
    gluing through keystoneO + keystone_restriction_squareO to the
    B_n IsSheafy (isSheafy_presheafChart); (3d) the straddling case
    (window-piece refinement + the adjacent-circle glue via
    BISub_twist); (3e) the Bundled-599 replay at the restricted site;
    yVObj.
    Original: (E2) THE CROSS-CHART COMPARISON: for
    an index of chart n whose trace sits inside the overlap circle
    κ = p^{n+1}, the keystone-over-B_n identification with a chart-
    (n+1)-index value — through the circle ring and the degenerate
    interval B^{[τ,τ]} (BISub_twist + ID2d at both sides); gives the
    inter-chart restriction maps; (E3) the limit presheaf over
    ChartRatIdx-traces (mirror limitSectionsY topology block verbatim);
    (E4) values-on-basis (limitEval at a top index = presheafValue of
    the chart datum, the RationalIndex-cofinality) + stalks: chart-
    rational traces ARE a neighbourhood basis of Y (chart homeos +
    B_n-side rational basis), so stalk-at-v = chart-stalk =
    StructureSheafStalks stalkValue at B_n — transport the S1-S5
    fields; (E5) IsSheafOfTopologicalRings for the E3-presheaf (per-
    chart IsLimitSheaf from isSheafy_presheafChart via
    isSheafy_iff_isLimitSheaf + basis refinement; cross-chart overlap
    sections agree by E2); (E6) yVObj := the VObj of Y. THEN D-iii
    (φ-action, X := Y/φ^ℤ).
    NEXT (Y-OBJ pipeline): (Y-a) the Opens-functor packaging of
    limitSectionsY on the subspace Y (presheaf-on-Y in TopCat.Presheaf
    form or hand-rolled contravariant functor); (Y-b) sheaf condition for
    trace-covers via chain-glue (cover of a dyadic trace by dyadic traces
    refines to a finite chain — compactness/order argument on ℚ-
    intervals); (Y-c) stalk package at v ∈ Y from the CHART spaVObj data
    (cofinality of dyadic traces ∋ v + limitEvalTop + BIQ-level stalk =
    chart-stalk); then (D-iii) φ-action as VObj-isos and X := Y/φ^ℤ.
    Bricks: (r4a) DONE 2026-07-27
    (ChartVObj.lean: exists_eq_toOF_pow_mul + teich_div_p_pow_mem_
    chartSubring (m1) + p_div_teich_pow_a_mem_chartSubring (m3);
    m2 = A_inf-images are generators, no lemma needed; axiom-clean); (r4b) the head/tail split of
    x/(p[ϖ])^k with per-monomial 1-ball bounds (sup-def gives termwise
    bounds); (r4c) the limit assembly (mirror
    chartPlus_le_completedPlusSubring_of_dense's structure). (β) the ARCHITECTURE DECISION
    (ambient-vs-glue, M8-note above) and the cross-chart assembly of the
    Y-VObj from the chartVObj chain + the D-ii-2 split fiber-product; then
    (D-iii) the φ-action as VObj-isos and X := Y/φ^ℤ.
    Then Y := glue the ℤ-chain of chart VObjs (cocycle-free, adjacent
    circles only; transitions from BISub_twist + the ID2 comparisons + the
    D-ii-2 split fiber-product) — architecture note above stands. Original:
    stalks + valuations (stalk theory over the sheafy charts); (D-iii) φ-action:
    FOUNDATION DONE 2026-07-27 (FrobeniusGauss.lean — teichCoeff_frob/
    gaussTerm_frob/gaussValue_frob: w_{ρ^p}(φx) = w_ρ(x)^p; frobBloc +
    frobBloc_algebraMap + wLoc_frobBloc; uniformContinuous_frobToBI with the
    power modulus; biPhi : B^{[ρ₁,ρ₂]} →+* B^{[ρ₁^p,ρ₂^p]} + dense-layer
    identity biPhi_blocToBI). Direction note: on vpiQ-exponents biPhi is
    exponent-times-p (W_n-ring → W_{n-1}-ring, the function-side of κ↦pκ).
    biPhi ISO DONE 2026-07-27: frobBlocSymm (unit condition
    via the Teichmüller-root x·x^{p-1} = x^p trick) with algebraMap-identity
    and both Bloc round-trips; wLoc_frobBlocSymm (inverse radius-change,
    free from the forward law + round-trip); uniformContinuous_frobSymmToBI
    (root modulus, le_of_pow_le_pow); biPhiInv + dense-layer identity;
    biPhi/biPhiInv continuity; the round-trips by dense equalizer; and
    **biPhiEquiv : B^{[ρ₁,ρ₂]} ≃+* B^{[ρ₁^p,ρ₂^p]}** — the Frobenius
    equivalence of interval rings, bicontinuous. biPhiQ DONE 2026-07-27
    (FrobeniusGauss.lean — the BIQ-level Frobenius hom in ABSTRACT-TARGET
    form: biPhiQ (q₁ q₂) {σ} (hσ : vpiQ q^p = σ) : BIQ q₁ q₂ →+* B^{[σ₁,σ₂]}
    with dense-layer identity; vpiQ_pow_p + mulQ_pos support. PERF NOTES
    from this stretch, binding for the presheaf phase: (1) vpiQ is now
    @[irreducible] (radius atoms; full library green with it); (2) the
    composite-radius instance search times out when composite radii appear
    in def HEADERS — state defs at ABSTRACT σ-radii with EQUATION-args
    (hσ : expr = σ) and let consumers instantiate; (3) the .trans-packaged
    equiv-form of biPhiQ ground on the BIQ-vs-BISub spelling — the
    RingHom-comp + biCongr form with explicit-toFun-style shows is the
    compiling pattern; the ISO-form of biPhiQ is deferred (round-trips at
    the Q-level need the σ-abstract statement of biPhiInvQ — same recipe).
    biPhiInvQ + Q-LEVEL ROUND-TRIPS DONE 2026-07-27
    (biPhiInvQ with dense-layer identity, biPhiQ/biPhiInvQ continuity —
    with FULLY EXPLICIT radius-proof args, the mvar-holes were the grind —
    and both round-trips biPhiInvQ_biPhiQ / biPhiQ_biPhiInvQ by dense
    equalizer). The φ-machinery on the interval-ring layer is COMPLETE:
    Frobenius is a bicontinuous bijection BIQ q₁ q₂ ↔ B^{[σ]} at
    σ = vpiQ(q)^p, with everything reaching the presheaf substrate.
    φ-SQUARE DONE 2026-07-27: biPhiQP (the
    BIQ-endpoint instantiation) with dense-layer identity and continuity;
    mulQ_mem/mulQ_lt; and **biPhiQP_biResQ'_comm** — Frobenius commutes with
    the interval restrictions (dense equalizer; compiled first-try under the
    explicit-args discipline). The φ-EQUIVARIANT INTERVAL-PRESHEAF SUBSTRATE
    IS NOW COMPLETE: values BIQ, restrictions biResQ' (functorial), φ a
    bicontinuous bijection commuting with restrictions. REMAINING D-iii:
    X := Y/φ^ℤ via Curve.lean + descent — needs the D-ii presheaf-on-opens
    assembly first (the substrate → Y-VObj step). DEFERRED
    (profiler task): composite chartRingEquivBIQ-continuity (step-3 kernel
    grind) and hence windowResBIQ-continuity — needed by D-ii-2's topology
    half; the unfolded four-step comp restatement is the likely fix. Negative-side mirror DONE 2026-07-27
    (chartRingEquivBIQNeg via the pPowM abbreviation — presheafValue of the
    (-m)-window chart ≃+* ↥(BIQ (p^m) (p^m/p)); the twist enters through
    BISub_twist.symm since the power relation points the other way). BOARD-HYGIENE LESSON: two
    silent no-op board edits this stretch (unasserted python replaces) —
    ALWAYS `assert old in src`. Original design: a ℚ-exponent wrapper layer —
    `BIQ (q₁ q₂ : ℚ)` := BISub at the radii `vπ^{qᵢ}` (NNReal-rpow of the
    rational exponents, 0 < q₁ ≤ q₂ say), with restriction maps
    `biResQ : BIQ q₁ q₂ →+* BIQ r₁ r₂` for [r₁,r₂]-exponent-intervals inside
    [q₁,q₂] (the interpolation θ's are affine ℚ-solutions
    θ = (q₂ - r)/(q₂ - q₁), done ONCE in the wrapper); functoriality
    (biResQ_id, biResQ_comp) via dense-extension uniqueness
    (DenseRange.equalizer on blocToBI + biRes_blocToBI) — no casts, the
    ℚ-exponents pin the types. Then the interval-presheaf on the basis
    {κ-intervals with attainable dyadic endpoints} has values BIQ and the
    Y-object glues over it; the chart homeomorphisms (ChartSpa) provide the point-set
    layer, isSheafy_presheafChart + ID2d the sheaf-condition per chart;
  (D-ii) VPreObj-level gluing machinery for a ℤ-chain of charts (new
    infrastructure — the repo has no presheafed-space gluing; alternatively
    build the Y-presheaf directly on the rational-basis of the union);
  (D-iii) stalks/valuations (VPreObj fields) from the chart sides;
  (D-iv) the φ-action as VObj-isos `Spa(B_n) ≅ Spa(B_{n+1})`-shifts
    (FrobeniusAction + the twisted-uniformizer bookkeeping), then X := Y/φ^ℤ
    via the free-wandering point-set layer (Curve.lean, done) + descent of the
    glued sheaf.
  ALTERNATIVE kept open: prove HasLocLiftPowerBounded (Ainf p F) directly
  (every valid A_inf-datum is p[ϖ]-adically manageable; would unlock the
  ambient route and Wedhorn Rem 8.27 verbatim). Decide at D-ii if gluing
  infrastructure proves heavier than the direct class proof.
- **AUDIT REFINED (2026-07-27, second pass — good news)**: the point-set
  BIJECTION `spaPresheafValueEquivRationalOpen` (SpaRationalOpenComparison)
  is HUBER-BASE-GENERIC (signature: CommRing+TopologicalSpace+IsTopologicalRing
  +PlusSubring+IsHuberRing only — NO IsTateRing, NO CompatiblePlusSubring) and
  axiom-clean. It INSTANTIATES at (A_inf, ⊤) today: DONE 2026-07-27
  `spaChartEquivBigWindow` / `spaChartEquivBigWindowNeg` (BigWindows.lean) —
  `Spa(B_n, B_n⁺-canonical) ≃ bigWindow-trace ∩ Spa(A_inf, A_inf)`.
  Tate-gated is ONLY the HOMEOMORPH-upgrade (forward-openness,
  `spaPresheafValueEquivRationalOpen_isOpenMap`; continuity of the forward map
  is generic comap-continuity) and the RationalSubset-CORRESPONDENCE file.
  [NT-1] DONE 2026-07-27 (NonTateRationalOpenHomeomorph.lean: the primed
  open-map chain; FarguesFontaine/ChartSpa.lean: isTateRing_presheafChart /
  isTateRing_bigWindowChart + the chart homeomorphisms spaChartHomeoBigWindow
  /-Neg : Spa(B_n, B_n⁺-canonical) ≃ₜ bigWindow-trace, both sides, over the
  non-Tate A_inf base). Original plan text (executed as written):
  the open-map chain
  (SpaRationalOpenHomeomorph 225-421) uses [IsTateRing A] ONLY to supply
  (i) the completion's topologically nilpotent unit (presheafValue_topNilUnit
  maps A's unit; steps 1-2 of the proof are already parameter-level in
  (u, hu)) and (ii) instance-resolution of
  [IsRingOfIntegralElements ((presheafValue D)⁺-canonical)]. PLAN: new file
  with primed variants exists_A_level_open_presentation' /
  spaPresheafValueEquivRationalOpen_isOpenMap' /
  spaPresheafValueHomeomorphRationalOpen' taking
  (u : (presheafValue D)ˣ) (hu : IsTopologicallyNilpotent u)
  [IsRingOfIntegralElements ((presheafValue D)⁺)] instead of [IsTateRing A];
  proof = copy + audit each inferInstance site. Chart-side suppliers: the
  unit from IsTateRing (presheafValue chart) (= isTateRing_congr of ID2e —
  already constructed) via exists_topologicallyNilpotent_unit; the CANONICAL-
  plus integral-elements instance is the plus-reconciliation task (canonical
  ringPlus(presheafValue) vs ID2e's transported BIPlusIn) — now load-bearing:
  find/derive `IsRingOfIntegralElements (ringPlus (presheafValue chart))`
  (check what the PlusSubring (presheafValue D)-instance IS in Presheaf.lean
  and whether its integral-elements proof is Tate-gated). Plus-ring note: the equiv lands on the
  CANONICAL `ringPlus (presheafValue …)`, not the transported BIPlusIn of
  ID2e — reconcile the two plus-structures when the VObj-level gluing needs
  it (they should agree by the §5-correction argument; ticket when reached).
- Content: 𝒴 pre-adic structure + chart identifications respecting restrictions
  (Wedhorn Rem 8.27); then EITHER 𝒪_X(W) := 𝒪_Y(q⁻¹W)^{φ^ℤ} descent (with plus
  sheaf and stalk valuations) OR two-chart gluing along the Frobenius transitions
  (overlap pieces: κ = c identity; κ = 1 ↔φ↔ κ = p), cocycle condition, and the
  local-isomorphism property of q — only then is 𝒳 an adic space.
- **STATUS UPDATE 2026-07-30 (beastmode)**: the FIRST branch is executed —
  D-iv delivered 𝒪_X := (π_*𝒪_Y)^φ with stalks, valuations, and the sheaf
  condition: **xVObj** (CurveObject.lean). The 𝒱-LEVEL "adic space"
  predicate (Wedhorn 8.22: locally 𝒱-isomorphic to Spa-objects) awaits the
  canonical Spa object of 𝒱 (the recorded open P5 leaf,
  StructurePresheafBundled.lean:736 note) — NOT taken here. The available
  honest form of the local-isomorphism property is the TOPOLOGICAL chart
  layer (AdicSpacePresentation, same file):
  ### [X-ADIC-1] The curve as an AdicSpacePresentation (spawned 2026-07-30)
  Statement: an `AdicSpacePresentation` with carrier `Curve p F ϖ` — every
  curve point has an open neighbourhood homeomorphic to the spectrum of an
  affinoid adic presentation. Route: (A1) the wandering-image homeo
  ↥W ≃ₜ ↥(xImage W) for W with pairwise-disjoint translates (yTopToCurve
  restricted: injective by wandering — orbit-collision w' ∈ frob-translate
  ∩ W₀ forces k = 0 — + continuous + isOpenMap ⟹ open embedding onto the
  image); (A2) chart-side localization: y ∈ window n (Y_eq_iUnion_bigWindow),
  transport the open W₀-constraint through spaChartHomeoBigWindow, pick a
  rational-open nbhd inside Spa(B_n) (the SpaRationalOpenHomeomorph
  rational-basis trick), NT-1'-homeo Spa(presheafValue D_{B_n}) ≃ₜ its
  trace, Homeomorph.image-restriction back; (A3) the affinoid presentation
  at the sub-rational value ring over B_n: IsTateRing
  (presheafValue_isTateRing_concrete), **IsStronglyNoetherian via
  presheafValue_isStronglyNoetherian_faithful over B_n** (B_n-instances by
  the isSheafy_presheafChart letI-package + isStronglyNoetherian_BISub
  transport), completeSpace_right_presheafValue, the canonical-plus
  integral-elements supplier (the one spaChartHomeoBigWindow already
  consumes), then AffinoidAdicPresentation.ofIsSheafy with
  isSheafy_of_stronglyNoetherian_828b; (A4) assembly over all x via
  fiberPoint + exists_disjoint_translates.

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
- **T908(c) EXECUTION PLAN (2026-07-30, beastmode; AD-8 = option (ii), the
  board's stated preference — coordinates by limit construction, no
  BrSub = A^r[1/p] claim)**. New file FarguesFontaine/IntervalCoordinates.lean.
  Sub-steps:
  (c1) blocCoeffF (u : Bloc) (n : ℤ) : F — the ℤ-indexed Teichmüller
  coordinates on the dense layer, via a chosen mk'(a, sPow k)-representation
  (IsLocalization.surj + powers-exponent choice); the WORKHORSE
  representation-independence lemma blocCoeffF_mk' (any representation
  computes it: (ϖ⁻¹)^k-scale of teichCoeffF (map a) (n+k)) from
  W(F)-level combined shift+scale (teichCoeffF_p_mul iterated +
  teichCoeffF_teichmuller_mul; (p[ϖ])^k·a ↦ p^k·[ϖ^k]·map a) + mk'-equality
  cancellation over the domain Ainf (mathlib WittVector domain instance;
  powers(p[ϖ]) ≤ nonZeroDivisors).
  (c2) the per-term Gauss bound: ρ^n(zpow)·v(blocCoeffF u n) ≤ wLoc ρ u
  (wLoc_mk' + gaussValue_p_teichPi + gaussTerm_le_gaussValue at n+k).
  (c3) the pair ε-δ on Bloc (the deferred T902(b4)): common-denominator
  reduction of u'−u to numerator form + exists_delta_teichCoeffF_sub at the
  W(F) level (mirror the tendsto_teichCoeffAr Cauchy core's hkey step).
  (c4) blocCoeffBr (x : hatK) (n : ℤ) := limUnder along the
  BlocToHatK-approximant filter; neBot_comap_of_mem_BrSub +
  eventually_pair_wLoc_le + exists_eventually_wLoc_le (verbatim mirrors of
  the ArSub trio) + tendsto_blocCoeffBr on BrSub (mirror
  tendsto_teichCoeffAr with the c3 input).
  (c5) the value bound ρ^n·v(blocCoeffBr x n) ≤ Valued.v x on BrSub
  (mirror gaussTerm_teichCoeffAr_le via eventually_wLoc_eq).
  (c6) BI-level: teichCoeffBI z n := blocCoeffBr (z.1) n; the two-factor
  agreement blocCoeffBr z.1 n = blocCoeffBr z.2 n for z ∈ BISub (both
  filters share the Bloc-approximants of exists_BIProd_wI_le; limUnder
  uniqueness).
  (c7) per-term wI-bounds both endpoints + interior two-sided decay
  (ρ ∈ (ρ₁,ρ₂): ρ^n·v(zₙ) ≤ (ρ/ρ₂)^n·wI → 0 as n → ∞, mirror n → −∞).
  (c8) the series realization (Def 4.2 honest form): z = wI-limit of the
  two-sided partial sums Σ_{n=−K}^{N} pⁿ[zₙ] — additivity of the
  coordinates + Teichmüller-monomial evaluation + tail bound by (c7).
- **AD-8 RESOLVED + T908(c) CLOSED AS-SCOPED (2026-07-30, beastmode).**
  LANDED (IntervalCoordinates.lean, axiom-clean, commit 4648c3c7a): (c1)
  blocCoeffF — the ℤ-indexed Teichmüller coordinates on the FULL dense
  layer Bloc, with representation independence (repCoeff_eq_of_cross:
  the W(F)-level combined shift-and-scale teichCoeffF_map_p_teichPi_pow_mul
  + below-shift vanishing + mk'-cancellation over the domain Ainf), and
  (c2) the per-term Gauss bound zpow_mul_valuation_blocCoeffF_le
  (ρ^n·|coeff_n u| ≤ wLoc ρ u, ℤ-zpow form). These give Kedlaya's
  line-144 expansions with the Gauss-norm formula (2.2.1/eq:Gauss norm
  formula) on B_{L,E} = Bloc — the layer the paper actually computes on.
  (c3)-(c8) NOT EXECUTED — OBSTRUCTION FINDING (concrete): the planned
  T903-verbatim ε-δ transfer is impossible. The Ainf/Aloc-side Cauchy
  core (exists_delta_teichCoeffF_sub, used by tendsto_teichCoeffAr)
  terminates because support ≥ 0 bounds the carry-recursion depth by the
  target index n. On Bloc the depth is the distance to the bottom of
  support, UNBOUNDED over wI-balls; the twisted carry is genuinely
  Hölder-p^{-depth} (tight already at depth 1: the S₁ Witt addition
  polynomial gives v(teichCoeff([x]+[y]) 1 − teichCoeff [x] 1)
  ≈ v(y)^{1/p}·v(x)^{(p-1)/p}), so a depth-K perturbation family
  u' := u + p^{-K}[η], |η| = δ·ρ₁^K (wI-distance δ) moves the level-n
  coordinate by ~ c^{-K}·(c^K·δ·ρ₁^K)^{p^{-K}} — NOT o(1) in δ uniformly
  over K: coordinate functionals are NOT uniformly continuous on
  wI-balls, and the comap-filter limit construction (c4) cannot
  converge. Repair attempts explored and rejected: (i) common-
  denominator reduction — the per-pair exponent K is unbounded over the
  ball; (ii) deep/shallow splitting at threshold −L (exists_wLoc_split
  + the (τ/σ)^L-gain via the (p[ϖ])^L-scaling trick) — the deep parts
  are support-disjoint (Teichmüller expansions concatenate, no carries)
  so coordinates at n ≥ −L see only the shallow parts, BUT the shallow
  DIFFERENCE picks up the deep-part discrepancy (≤ B·(ρ₁/ρ₂)^L at ρ₂),
  and damping it needs L → ∞ while the W(F)-δ at index n+L degrades
  double-exponentially (ε^{p^{n+L}}) — the race fails structurally.
  SOURCE AUDIT (refs/paper.tex): Kedlaya asserts unique ℤ-expansions
  only for the ALGEBRAIC B_{L,E} (line 144, "uniquely ... zero for n
  sufficiently small"); A^r-expansions come from the inclusion
  A^r ↪ W(L)_E (support ≥ 0 — our teichCoeffAr, DONE in T903); B^r is
  the LOCALIZATION A^r[1/p] (bounded per-element denominators — NOT our
  closure BrSub, which contains wLoc-convergent deep series
  Σ_{m≥1} p^{-m}[x̄_m], |x̄_m| ≤ ρ^m·2^{-m}, of unbounded-below support;
  whether BrSub = ArSub[1/p] — the p^m[ϖ^{-m/2}] demon — stays open and
  UNUSED). The paper NEVER forms ℤ-coordinates of general B^I-completion
  elements: §2's y_l-recursions run in B^r via A^r ⊂ W(L); Lemma 4.4
  reduces to single terms on the dense layer and closes by continuity of
  the NORMS (not coordinates); §4's T-expansions are restricted-series
  coordinates over B^I, not Teichmüller. Newton-polygon/leading-term
  semicontinuity for extended Robba rings (KL15 §5-scale) would be the
  machinery for a per-element expansion theory — outside this paper and
  this campaign, and consumed by nothing downstream (T909–T912, TC1–TC2,
  the curve chain are complete without it). VERDICT: T908(c) = (c1)+(c2)
  as landed; the completion-level coordinate functionals are struck from
  the deliverable as not-source-backed and obstructed as designed.

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
- **Status**: in_progress (beastmode 2026-07-27) | **File**: FarguesFontaine/RobbaPresentation.lean (new) | **Depends**: T907, T908
- **OPENING PLAN (2026-07-27, after the D-track wall audit)**. The D-track's next
  steps (Y-b sheaf-on-Y, VObj-glue) hit two genuine infra walls: (i) Spa(A_inf)
  quasicompactness — the Tate-case closed-image route does not apply (A_inf not
  Tate) and even the Tate noHArch variant is a recorded sorry
  (isClosed_image_spa_ιSpv_bool_noHArch, SpaCompactNoHArch:312); (ii) gluing
  infrastructure for TopRingPresheafedSpace/VObj does not exist. Both are
  coordinator-scale planning items. Meanwhile T910 is CONTRACTUAL, has met
  dependencies, and its cases 1–2 are exactly the rational-localization
  presentations 𝒪_{B^I}(sub-opens) ≅ B^{I∩…} that the chart-local sheaf theory
  of the D-track needs (keystone-free). So T910 now.
- **Pinned repo statement (case 1, untwisted radius-1 form)**: coefficients
  BI⟨T⟩ := restrictedMvPowerSeriesSubring 1 ↥(BISub ρ₁ ρ₂) (instances exist —
  T912 already states over it). Generator: T − b with b the image in B^{I′} of
  the p-unit-scaled Teichmüller (teichPowOverP-family: [z̄^e]/p^m; p is a unit
  of B^I). The cut endpoint: ρ₁′ pinned by an hexact-style hypothesis
  (|ϖ|-power = the radius where |p^{-m}[z̄^e]|_t = 1), I′ = [ρ₁′, ρ₂].
  Mirror of the T911 pipeline (Presentation.lean):
  (P1) DONE 2026-07-27 (commit bf7b26fcf, RobbaPresentation.lean, all
  axiom-clean): wI_resIHom_le + isRestricted_iff_wI + tendsto_wI_coeffSeq
  + exists_evalBI_series + evalBITerm/evalBI/evalBIHom with full hom laws.
  DESIGN: the carrier is an ABSTRACT contracting RingHom φ (hφ : wI-
  contraction) — the resIHom interpolant-radii (ρ₁^θρ₂^{1−θ} rpow-
  compounds) NEVER enter the eval signatures; instantiate φ := resIHom +
  wI_resIHom_le only at the presentation site. PERF (new entries):
  (i) section-variable hypotheses used only in BODIES need `include hφ
  in` BEFORE the docstring (a docstring must immediately precede its
  decl); (ii) rw-unfolding a def (rw [evalBITerm]) and even coe-add rfl
  can blow the per-decl budget in fat contexts — hoist per-term
  identities into standalone lemmas and close them with TERM-MODE calc
  (congrArg of the subtype-level fact + a standalone BISub_coe_add
  micro-lemma + add_mul), no kabstract;
  (P2) ANALYSIS DONE 2026-07-27 — b is FREE, reuse T911's family: in the
  repo's untwisted conventions |p|_ρ = ρ VARIES with the radius while
  |[z̄]|_ρ = |z̄| is CONSTANT (gaussVal_p_pow vs gaussVal_teichPi_pow) —
  so Kedlaya's ρ-cut generator is realised as g := p^{-m}[z̄^e] ∈ B^I
  (p is a unit of B^I), with v_ρ(g) = ρ^{-m}|z̄|^e ≤ 1 ⟺ ρ ≥ |z̄|^{e/m}:
  a LEFT-endpoint cut, exactly T911's teichPowOverP p F ϖ (ϖ^j) n
  (= p^{-1}[ϖ^{jn}]) shape with hexact : vπ^{jn} = σ₁ pinning the cut
  radius; frobRoot-ϖ's give the full c^ℚ grid. b := BIProd-σ-image,
  hbmem/hb discharged by the same AD-9 satisfiability lemmas
  (isSheafy_BISub_AD9 side). The case-1 presentation map is therefore
  evalBIHom (φ := resIHom …) at b := BIProd-σ (teichPowOverP (ϖ^j) n),
  with σ₁ = vπ^{jn} (cut) and σ₂ = ρ₂ (θ := interpolation exponent of
  vπ^{jn} in [ρ₁, ρ₂], η := 0);
  (P3) surjectivity with (4.9.1)-norm control: per-monomial lift — for a
  Bloc-monomial x with wLoc-σ-data, pick j minimal with |x̄|-vs-|z̄|^j
  comparison, lift to y·T^j with y := the z̄^{-j}-twisted monomial IN THE
  BIG ring B^I; then the density/completeness assembly (mirror
  exists_evalAr_eq_of_mem_BISub 2215-2398, which reduces to Bloc via
  exists_blocApprox + successive approximation — REREAD its skeleton
  before writing; the coefficients here live in ↥BISub-ρ not ArSub so
  the gaussNormRPS-analogue is the sup-wI-norm on restricted series —
  DEFINE wIRPS first, mirroring gaussNormRPS — wIRPS layer SHIPPED
  2026-07-27 as P3a (commit 5decd9108: wIRPS + bddAbove_wIRPS +
  wI_coeff_le_wIRPS + wIRPS_zero). P3 SKELETON MAP (from the T911
  engine, Presentation.lean): surjectivity = exists_correction_sequence
  (successive approximation producing u : ℕ → series with geometric
  wIRPS-decay and residual-shrink) + exists_evalAr_eq_of_correction
  (the summed limit); the case-1 mirrors are evalBI-versions of both,
  with the FIRST-approximation step (the actual Kedlaya per-monomial
  content, eq:Robba-localization-lift): for z in the cut ring, approximate
  by a Bloc-element (exists_blocApprox-analogue at the σ-radii — check
  exists_blocApprox in IntervalSplitting), write it as mk'(x, s^k),
  per-monomial ϖ-twisted lift y·T^j with j minimal s.t. |x̄|-vs-|z̄|^j,
  head/tail-split as in ChartDensePlus's r5b machinery (mk'_sPow_split
  is REUSABLE — the head monomials' lifts are FINITE sums). Also
  needed for P4 later: multiplicativity bound wI(y) ≥ wI-of-(T−g)·x
  (strictness) — locate wI_evalAr_le-analogues.
  P3 DEPENDENCY DISCOVERED 2026-07-27: exists_evalAr_eq_of_correction
  rests on (i) exists_rps_series_limit — completeness of the restricted-
  series space (a Groebner.lean heavyweight, stated over ArSub) — the
  case-1 mirror needs the ↥BISub-coefficient analogue (series of
  restricted series with geometrically-decaying wIRPS converge; proof
  mirrors the ArSub one: coefficientwise completeness of BISub +
  uniform-decay bookkeeping), and (ii) wI_z_sub_evalAr_add_le (evalBI-
  additivity residual estimate — cheap mirror via evalBI_add). Sequence
  the P3 work as: (P3b) exists_rps_series_limit_BI — DONE 2026-07-27
  (commit ab2e79302, RobbaPresentation.lean, axiom-clean, NO heartbeat
  raises unlike the ArSub original's 2M: exists_wI_series_limit
  (residual form via isClosed_wI_ball + wI_sum_le + eventually_ge_atTop
  + Finset.sum_Ico_eq_sub), RPS_BI_coe_sub/coeff_sub_eq_BI micro-lemmas,
  coeff_partial_sum_BI (PERF: the induction-rw route times out — use
  AddSubmonoidClass.coe_finsetSum + map_sum + coe_finsetSum, three
  lemma-head rewrites), isRestricted_column_limits (PERF: rw
  [isRestricted_iff_wI] needs the series bound via `set Ufun :
  MvPowerSeries … := (fun K => S K)` — the raw lambda does not match the
  pattern at reducible transparency — plus an hSK rfl-bridge), and the
  assembly); (P3c) wI_z_sub_evalBI_add_le (mirror Presentation:2041-2071:
  needs wI_evalBI_le — the eval-value bound, mirror wI_evalAr_le at
  Presentation ~1990-2040 — check its exact statement first); (P3d) the
  first-approximation lemma (the per-monomial Kedlaya lift on the
  Bloc-dense layer). ⚠⚠ DESIGN CORRECTED (2026-07-27, second analysis —
  supersedes the note below, which transliterated Kedlaya's λ_t-norms
  (coordinate enters with t-POWER) into our gaussValue (coordinate
  LINEAR, |p| = ρ varies) incorrectly): in OUR normalization,
  NUMERATOR-monomials alg(p^i[c]) have wI-ρ = wI-σ (max at the shared
  top radius ρ₂) — NO twist, K = 1, constant-lift. The twist is needed
  exactly for DENOMINATOR-dominant monomials mk'(p^i[c], s^k) with
  i < k (ρ-max at ρ₁ exceeds the σ-norm by (σ₁/ρ₁)^{k−i}); the twist
  depth j needed is ⌈(k−i)/m⌉-ish, and THE DIVISIBILITY zb^j ∣ c IS
  SUPPLIED BY THE σ-GAUSS-BOUND on the element being lifted (v_{σ₁}-
  boundedness forces v(c) ≤ σ₁^{k−i}·stuff = c₀^{(k−i)/m}·stuff —
  exactly the ChartDensePlus zone-M1 mechanism, r5b machinery reusable:
  gaussTerm ≤ gaussValue at σ₁ + exists_eq_toOF_pow_mul-style dvd).
  So P3d = per-monomial dispatch on i vs k (numerator-zone constant
  lift; denominator-zone twisted lift y·T^j via teichPowGen_pow_mul_
  twist + the σ-bound-derived divisibility), head/tail-split of the
  Bloc-approximant via mk'_sPow_split (ChartVObj), tail smallness,
  finite-head assembly. K = 1 likely achievable (both zones bound by
  the σ-norm directly); re-verify during implementation.
  P3d PROGRESS: (ii) exists_twist_deep SHIPPED (6aa457abb); (iii)
  SHIPPED (gaussValue_p_pow_mul_teichmuller + wLoc_mk'_monomial +
  mk'_monomial_twist_factor + exists_monomial_twist_data; ChartVObj now
  imported by RobbaPresentation for sPow/gaussValue_sPow; PERF: a bare
  rw [mk'_eq_mul_mk'_one, mk'_eq_mul_mk'_one] REWRITES THE mk'(1,s)-TERM
  the first rewrite created — use show-from-targeted rewrites per mk';
  ← rw of the twist identity mis-associates — forward calc instead).
  ⚠ (iv)-DESIGN CORRECTED AGAIN (2026-07-27): the MAXIMAL twist
  (exists_twist/exists_twist_deep) OVERSHOOTS — for very divisible c the
  twisted exponent e := i+mj can exceed k arbitrarily and B_{ρ₂}/A_{σ₁}
  = (ρ₂/σ₁)^{e−k} is unbounded. THE RIGHT j IS THE FLOOR-DIV
  j := (k−i)/m (Nat division), giving e ∈ (k−m, k] (deficit = (k−i) mod
  m < m, NO overshoot). Divisibility for that j comes DIRECTLY from the
  σ₁-Gauss bound: v(c) ≤ W·σ₁^{k−i}·vπ^k ≤ σ₁^{k−i} ≤ (σ₁^m)^{j} =
  v(zb)^j (pow-antitone, m·j ≤ k−i), then dvd_of_le. KEY IDENTITY
  c₀^j = σ₁^{mj} makes A_{σ₁} = σ₁^{e}·v(c')·((σ₁V)^k)⁻¹ = B_{σ₁}
  EXACTLY; then B_{ρ₁}/B_{σ₁} = (σ₁/ρ₁)^{k−e} ≤ (σ₁/ρ₁)^m =: K and
  B_{ρ₂}/B_{σ₁} = (σ₁/ρ₂)^{k−e} ≤ 1. Numerator zone (i ≥ k): j = 0,
  profile increasing, K = 1 both radii. exists_twist/exists_twist_deep
  stay shipped (unused by the assembly; potentially useful elsewhere).
  (iv) DONE 2026-07-27: exists_monomial_twist_div (6b1b16d73),
  pow_mul_pow_le_of_le (ec1b80dde), perfectoidValuation_twist_factor +
  twisted_formula_le (the denominator-zone comparison, formula level —
  B_{ρ₂} ≤ A_{σ₁} exact and B_{ρ₁} ≤ σ₁^m(ρ₁^m)⁻¹·A_{σ₁} — via
  div_le_div_iff₀ POSITIVITY-form args + mul_le_mul_left for right-
  constant factors). (v)-PROGRESS 2026-07-27: numerator_formula_le (73612a071),
  exists_monomial_lift_package (607abaed1 — the FULL per-monomial lift:
  zone-dispatched factorization + both outer-radius bounds),
  monomial_dvd_of_wLoc_le_one (the σ₁-Gauss bound ⇒ floor-div
  divisibility; W = 1 normalized). (v-c1..c3) SHIPPED 2026-07-27
  (1660b21b2, 4b8c1f01c, + wIRPS monomial/add/sum bounds):
  resIHom_blocToBI (interval restriction carries Bloc-images to
  Bloc-images via resI_BIProd + BIProd_fst/snd), wLoc_mk'_monomial_le
  (monomial ≤ element via gaussTerm-sup), isRestricted_monomial_BI,
  evalBI_monomial (y·T^l ↦ φ(y)·b^l, stabilization), wIRPS_monomial/
  _add_le/_finset_sum_le. ★★ (v-d) DONE 2026-07-27 — exists_evalBI_approx_bloc PROVEN
  (RobbaPresentation.lean, axiom-clean, compiled FIRST SHOT; the port
  incident 6d6958bb1 → fixed 9d6c3f95b, lesson logged above PERF-1).
  P3d IS COMPLETE: the Kedlaya first-approximation lift for case 1.
  Statement: abstract contracting φ with the Bloc-image law hφb, eval
  point b = BIProd-σ(teichPowGen zb m), w/k with both σ-wLoc ≤ 1, any
  ε > 0 → a T-polynomial f with residual ≤ ε and wIRPS f ≤ K :=
  σ₁^m(ρ₁^m)⁻¹. P3e PROGRESS 2026-07-27: W-generalized approx (f230e7a3d),
  exists_correction_step_BI (61f6338ea), exists_correction_chain_BI +
  telescope mini-lemmas (8c2804cea; PERF: the fat-φ-context accumulates
  per-declaration cost — SPLIT chain-extraction and telescope into
  separate declarations, one-step exact-terms per induction branch,
  set-K compression; the raw-chain-form conclusion (∃ u r, hr0 ∧ hrrec
  ∧ bounds) defers the telescope), exists_correction_sequence_BI
  (telescoped wrapper, own budget). ★★ P3e COMPLETE 2026-07-27 (commits through the capstone):
  exists_evalBI_eq_of_correction_BI (4b19f75da; abstract-K limit; PERF:
  congrArg-le_of_eq beats rwa-kabstract in the fat context) and
  exists_evalBI_eq_of_le_one — CASE-1 STRICT SURJECTIVITY on the unit
  ball with the (4.9.1)-K-constant. ⇒ T910 P3 (the surjectivity half)
  IS COMPLETE. NEXT: (P4) the kernel. DESIGN NOTES (2026-07-27, from the ln
  527-546 re-read in our conventions): the generator RPS-element is
  Gelt := (monomial (single 0 1) 1) − (monomial 0 (blocToBI-ρ g)) with
  g := teichPowGen zb m₀ ∈ Bloc; (P4-a) STRICTNESS — TELESCOPE ROUTE (2026-07-27 refinement; NO
  Gauss multiplicativity needed; repo has only gaussValueF_mul_le
  submult): with y = (T − Cg)·x the coefficients obey y_n = x_{n−1} −
  g·x_n. Per component (hatK-τ a FIELD): if v_τ(g) ≤ 1 (at/above the
  cut) the DOWNWARD telescope x_m = Σ_{j>m} y_j·g^{j−m−1} (converges by
  x-decay) gives v_τ(x_m) ≤ N_τ(y)·1 ⇒ N_τ(x) ≤ N_τ(y); if v_τ(g) > 1
  the UPWARD telescope x_n = −Σ_{i≤n} y_i·(g⁻¹)^{n+1−i} (g-inverse in
  the FIELD component) gives v_τ(x_n) ≤ N_τ(y)·v_τ(g)⁻¹ ≤ N_τ(y).
  Either way N_τ(y) ≥ N_τ(x); sup over the two radii: wIRPS(Gelt·x) ≥
  wIRPS x — strictness + closed ideal. (P4-a1) DONE (b0904b3e8:
  NfstRPS/NsndRPS + wIRPS_eq_max); (P4-a2) DONE 2026-07-27:
  coeffSeq_Gelt_mul (57325f8e8; the shift-minus-scale recursion via
  MvPowerSeries.coeff_monomial_mul + Finsupp.single_tsub +
  Finsupp.single_le_iff; PERF: open NNReal shadows the canonical
  zero_le for Finsupp-≤ — ascribe (zero_le : (0 : Fin 1 →₀ ℕ) ≤ …)),
  telescope_down_bound (4a9cb05ca; finite telescope + per-M ultrametric
  + vanishing-tail contradiction; Tendsto.comp tendsto_add_atTop_nat
  needs a .congr add_comm-flip), telescope_up_bound (induction-only
  field-inverse route, no sums — v(X n) ≤ v(g)⁻¹·NY; inv_le_one₀-iff;
  hcancel v(x) = v(g)⁻¹·v(g·x) pattern). ★ P4-a3 COMPLETE 2026-07-27 (commits c5d5f9298/278d7bb00/strictness):
  BISub_coe_sub/mul + RPS_BI_coe_mul + GeltElt(+_coe) +
  NfstRPS/NsndRPS_eq_iSup_coeffSeq (range-equality-sSup route, NO
  BddAbove juggling; Subsingleton.elim for Fin-1) +
  coeffSeq_GeltElt_mul_fst/snd (PERF: per-branch plain-rfl after
  if-resolution — coe-lemma rw's and show-reshapes both blow whnf) +
  telescope_iSup_le (the dispatch corollary in the LEAN hatK-context) +
  NfstRPS/NsndRPS_le_GeltElt_mul (set-free slim bodies — `set X :=
  big-lambda with h` ITSELF can blow the decl budget by occurrence-
  scanning) + **wIRPS_le_GeltElt_mul** — THE STRICTNESS (Kedlaya ln
  527-533). ★★ P5 CASE 1 COMPLETE 2026-07-27 (commits d5157f244..6107c42a1):
  **robba_case1_presentation** — B^I⟨T⟩/(T − [z̄]/p^m₀) ≃+* B^{[σ₁,ρ₂]}
  for a STRICT interior cut ρ₁ < σ₁ ≤ ρ₂ with |z̄| = σ₁^m₀, AXIOM-CLEAN
  END-TO-END. Chain: P5a surjective_evalBIHom (p-power rescale into the
  ball: exists_p_scaling via wI_pow/wI_p_image/NNReal.exists_pow_lt,
  scale-back constant GeltEltM0(blocToBI(p-inv^k)), congrArg-composed
  because rw [hU'eq] kabstract blows whnf); P5b
  nonempty_case1_quotient_equiv (Ideal.quotEquivOfEq ∘
  RingHom.quotientKerEquivOfSurjective); P5c instantiation φ :=
  **resIHomTop** (NEW: top-anchored restriction — fst-slot resI at the
  θ-interpolant, snd-slot LITERAL z.2 so resIHomTop_snd is rfl and the
  shared-top kernel machinery needs NO radius transport) +
  exists_interpolant (log-scale linear solve) + isUnit_teichPowGen
  (Valuation.Integers.dvd_of_le: zb ∣ ϖ^j ⇒ Teichmüller image inverted)
  + endpoint valuations wLoc_teichPowGen/valued_blocToBI_teichPowGen_*
  + the two NNReal bounds; final assembly by term-style Exists.elim +
  subst (NEW PERF LESSON: tactic-obtain/rcases motive-INFERENCE in
  front of a fat quotient/RingEquiv goal blows isDefEq-200k; the
  term-elim chain `(h).elim fun x hx => …` takes the motive from the
  expected type directly and is cheap; subst itself is fine).
  SCOPE NOTE: the degenerate cut ρ₁ = σ₁ (presentation of B^I itself)
  is EXCLUDED — hg1 needs 1 < |g|_{ρ₁} strict; the fst-decay at
  |g| = 1 would need the le_one-variant fed by fst-vanishing (same
  route as snd) — only add if the sheafy-cover glue ever needs it.
  ★★★ CASE 2 COMPLETE 2026-07-27 (commits cb1afa764..HEAD):
  **robba_case2_presentation** — B^I⟨T⟩/(T − p^m₀/[z̄]) ≃+* B^{[ρ₁,σ₂]}
  for ρ₁ ≤ σ₂ < ρ₂ with |z̄| = σ₂^m₀, AXIOM-CLEAN END-TO-END. Executed
  M1–M5/Z1–Z9 mirror plan: shared-bottom kernel machinery (fst-
  transport, swapped-regime decay, ker = span₂), mirrored zone theory
  (teichPowGen₂ = p^m·Ring.inverse([z̄]); the twist MULTIPLIES the
  coordinate so no divisibility input; K₂ = ρ₂^m(σ₂^m)⁻¹; same
  pow_mul_pow_le_of_le core), approx₂ + correction₂ + capstone₂ by
  SYSTEMATIC MIRROR-TRANSFORM of the case-1 text (target four-tuple,
  generator, K-constant, hK-calcs, extraction sides — transform then
  compile-fix residue; Z7+Z8 compiled on first/second try), resIHomBot
  (fst literal; KERNEL-PERF: Prod.ext with bare rfl component forces
  kernel defeq through subring-coe-mul and times out — use
  congrArg-of-BISub_coe_mul/add), final assembly term-elim + subst.
  T910 STATUS: both B-level cases DONE. REMAINING (follow-ups, assess
  T911-consumer need first): the ρ ∈ p^ℚ plus-ring integral-closure
  statement + the A^r-level third iso (A^r{T}/(pT−[z̄^n])). Historical:
  the case-2 plan follows. (needed: Kedlaya's 4.10/4.11 subdivision
  induction presents BOTH halves — top-half by case 1, bottom-half by
  case 2). Paper: B^I{T/ρ⁻¹}/(T − [z̄⁻¹]) ≅ B^{I∩(0,log_c ρ]}; repo
  normalization: generator g₂ := p^m·[z̄]⁻¹ (alg(p)^m · unit-inv of the
  Teichmüller image — a UNIT of Bloc via isUnit_teichmuller_image),
  |g₂|_ρ = ρ^m·σ₁^{-m}: ≤ 1 on [ρ₁,σ₁] (kept side), > 1 above. Target
  B^{[ρ₁,σ₁]} = SHARED-BOTTOM. Mirror plan: M1 transport-mirror
  tendsto_fst_partial_sums_of_evalBI_eq_zero (hφfst + hb1, fst-proj);
  M2 decay-mirror kerSolElt_wI_decay₂ (le_one-regime on fst with
  hvan-fst, one_lt-regime on snd with snd-BddAbove — decay lemmas are
  radius-generic, roles swap); M3 kernel-mirror exists_factor₂ +
  ker_eq_span₂ (span side identical); M4 THE DEEP MIRROR: case-2
  surjectivity exists_evalBI_eq_of_le_one₂ — the zone theory
  (twisted_formula/monomial-lift, Kedlaya ln 552-558) with the j-twist
  on the opposite side; re-derive in repo norms, do NOT transliterate;
  M5 resIHomBot (snd-slot resI, fst LITERAL — mirror of resIHomTop) +
  isUnit for g₂ + endpoint valuations + robba_case2_presentation
  (σ₁ < ρ₂ strict this time, ρ₁ ≤ σ₁). THEN: the plus-ring statement
  (ρ ∈ p^ℚ integral-closure claim) + the A^r-level third iso — file as
  follow-ups after case 2; assess T911-consumer need first. ★ P4 COMPLETE 2026-07-27 (commits 70901e5d9..a05953d5f):
  ker_evalBIHom_eq_span = le_antisymm(span_GeltElt_le_ker,
  ker_le_span_GeltElt). Full chain: kerSolElt_coe_fst/snd component
  bridges (AddMonoidHom.fst/snd map_sum + congrArg close) ->
  kerSolElt_wI_decay (both component regimes, Tendsto.max + max_self) ->
  tendsto_snd_partial_sums_of_evalBI_eq_zero (the ker->hvan transport:
  phi fixes the shared top coordinate hphisnd, b agrees with gB there
  hb2, snd-projection by continuity + map_sum-trans, range-reindex by
  tendsto_add_atTop_nat) -> coefficient-decay glue trio
  (tendsto_v_fst/snd_coeffSeq + bddAbove_v_fst_coeffSeq, squeeze
  tendsto_of_tendsto_of_tendsto_of_le_of_le from wIRPS-decay) ->
  exists_factor_of_evalBI_eq_zero -> slim mem_span_GeltElt_of_factor.
  Easy inclusion: GeltElt_add_M0 (slim ADDITIVE split via GeltEltM1/M0
  defs) -> evalBI_GeltEltM1/M0 -> evalBIHom_GeltElt (product-level
  add_right_cancel route) -> Ideal.span_le + singleton_subset_iff.
  NEW PERF LESSONS (binding): (i) bare RPS-subtype SUBTRACTION in the
  fat phi-context deterministically blows whnf-200k even as a lone
  have-term (probe7) — slim-hoist every sub; state fat-context facts
  ADDITIVELY; (ii) Ideal.mem_span_singleton.mp and obtain-destructuring
  of a fat existential both blow whnf — use Ideal.span_le +
  Set.singleton_subset_iff + Ideal.mul_mem_right, and slim helpers that
  take the compiled existential as a hypothesis (pure application is
  cheap; re-elaboration/destructuring is not); (iii) rw with generic
  map_sub/map_mul dies at 20k-typeclass in fat contexts — use
  RingHom.map_* explicitly or .trans terms; (iv) statement-only probe
  then have-by-have bisection localizes any such site in minutes;
  (v) squeeze lemma is tendsto_of_tendsto_of_tendsto_of_le_of_le
  (le_OF_le). Historical plan notes follow (P4-b PLAN RESOLVED
  2026-07-27, supersedes the componentwise-split
  notes below): THE UNIT INSIGHT — at every instantiation the generator's
  Teichmüller content zb is a ϖ-power, so gB := blocToBI-ρ(teichPowGen
  zb m) is a UNIT of B^I-ρ ([ϖ]⁻¹ = vt ∈ Bloc, p⁻¹ = vp ∈ Bloc); with
  hgu : IsUnit gB as a hypothesis Kedlaya's up-formula works verbatim at
  the subring level: x_n := −(gB⁻¹)^{n+1}·Σ_{i≤n} y_i·gB^i (positive-
  power spelling). Sub-steps: (b2) the formal identity (T − C gB)·x = y
  coefficientwise (pure algebra from the x_n-definition); (b3) fst-decay
  from hg1 : 1 < v_ρ₁(gB) (head/tail split of the up-formula: fixed-i
  factors v₁(g)^{i−n−1} → 0, y-decay kills large i); (b4) snd-decay:
  up = down + (g⁻¹)^{n+1}·(Σ_{ALL i} y_i-snd·(g-snd)^i) and THE FULL
  SERIES VANISHES because it is the snd-component of eval(y) = 0 (the
  σ-pair shares the top radius ρ₂, and φ-snd at η = 0 is the identity
  component — needs a small resI-at-same-radius = id lemma); then the
  down-form decays from hg2 : v_ρ₂(gB) ≤ 1 + y-decay; (b5)
  restrictedness from the two decays (isRestricted_iff_wI-side) and
  y = GeltElt·⟨x, _⟩ by coefficient-ext ⇒ ker ⊆ span. span ⊆ ker is
  EASY: eval(GeltElt gB) = b − φ(gB) = 0 by hφb + hbg. Sequence: (b0) DONE (9ed3bb3c4 resI_eq_snd/fst via
  limUnder-uniqueness on the comap filter, interpolant-free); (b1) DONE
  (kerSol_rec_generic — the formal recursion over an ABSTRACT CommRing;
  PERF: NEVER run `ring` over the ↥BISub subtype — its instance-whnf
  alone blows 200k; state ring-algebra generically and instantiate);
  (b2) DONE 2026-07-27 (b9b1f6ed5 + 286c35d30):
  kerSol_decay_of_le_one (contracting scale: the vanishing turns S_n
  into the tail via v(S n) ≤ max(v(S M), Ico-bound) with M → ∞ through
  valued_ball_mem_nhds_zero; then (v(V)v(g))^{n+1} = 1 cancels) and
  kerSol_decay_of_one_lt (expanding scale: split sum bound at N, the
  head constant dies under v(V)^{n+1} → 0, the tail rides (vVvg)^n = 1;
  PERF: mul_max_of_nonneg needs its nonneg-arg ASCRIBED — bare zero_le
  is the argless NNReal variant). (b3) PROGRESS 2026-07-27:
  (β) DONE (faf01abfd: kerSolElt + isRestricted_kerSol — set-ascribed
  MvPowerSeries + single-injective preimage-finiteness); (γ) DONE
  (82f968572: kerSol_coeff_identity + GeltElt_mul_kerSol — PERF
  BREAKTHROUGH: Nat-CASES makes both the ite-Decidable and the
  (m+1)−1-subtraction reduce DEFINITIONALLY, so the per-coefficient
  identity needs ZERO rewrites, just two exact's of the generic
  recursion; coe-of-mk coefficient bridge = congrArg single_eq_same).
  REMAINING: (α) the vanishing-transport (the decay-inputs hd1/hd2 for
  isRestricted_kerSol derived from y ∈ ker: snd via resI_eq_snd-
  transport of eval-vanishing + kerSol_decay_of_le_one; fst via
  kerSol_decay_of_one_lt with 1 < v-ρ₁(gB) at instantiation) and
  (δ) ker = span assembly. THE OLD PLAN TEXT: for y ∈ ker(evalBI φ b) — (α) the componentwise vanishing
  inputs: hvan-snd from resI_eq_snd + the φ-instantiation (the σ-pair's
  snd IS the ρ₂-component and eval y = 0 projects to the snd-series
  vanishing — NEEDS the eval-as-series-limit at the component:
  tendsto_evalBI-snd-projection + the coefficient-identification
  y_i-comp·(g-comp)^i = the evalBITerm-snd — work out: evalBITerm φ b
  f l = φ(coeff-l)·b^l; its snd = φ(coeff)-snd·(b-snd)^l; with
  φ(z)-snd-component and b-snd = (BIProd-σ g).snd = BlocToHatK-ρ₂ g —
  vs the ρ-level series y_i-snd·(gB-snd)^i: gB-snd = BlocToHatK-ρ₂ g ✓
  SAME and φ(z)-snd = resI-at-ρ₂(z-coe) = z-coe-snd [resI_eq_snd!] ✓ —
  so the snd-projection of the eval-partial-sums IS the ρ-level partial
  sums S_n-snd EXACTLY — the vanishing transports ✓ no extra hypothesis
  needed at instantiation, but the ABSTRACT kernel theorem should take
  hvan-snd as an input and the instantiation discharges it); (β) X n :=
  kerSol-pair ∈ BISub-ρ: the pair (X-fst-formula, X-snd-formula) — WAIT
  the kerSol-definition is ALREADY at the SUBRING level (X n :=
  −(V^{n+1}·Σ y_i gB^i) with V := unit-inverse IN ↥BISub-ρ ✓ membership
  free!) — the decays then give restrictedness via isRestricted_iff_wI
  (wI = max of the two component-v's, both → 0 cofinitely... careful
  isRestricted needs the cofinite-finiteness form — from the two
  tendsto's: wI(X n) = max(v₁, v₂) → 0 ⇒ eventually ≤ ε ⇒ cofinite ✓
  single-variable reindex); (γ) y = GeltElt·⟨X, restr⟩ by coefficient
  ext (kerSol_rec_generic instantiated at A := ↥BISub-ρ, g := gB,
  V := unit-inv, hinv from unit.mul_inv — NO ring-tactic needed, the
  generic lemma applies); (δ) ker = span + the easy inclusion. ORIGINAL NOTES: per component τ, the coefficient
  sequences X := component-of-coeffSeq x, Y := component-of-coeffSeq
  (Gelt·x) satisfy hrec (from coeffSeq_Gelt_mul projected to the
  component), hbdd (restrictedness), hX0 (decay); dispatch v_τ(g-comp)
  ≤ 1 → down / > 1 → up (up gives ≤ v(g)⁻¹NY ≤ NY); combine via
  wIRPS_eq_max both sides. Then (P4-b) the kernel-inclusion per the
  componentwise design above.
  (P4-b) KERNEL-INCLUSION: y ∈ ker(evalBIHom) ⇒ y = Gelt·x with
  x_n := −Σ_{i≤n} y_i·(blocToBI-ρ g)^{i−n−1}-POWERS — CAREFUL: g is
  NOT invertible in B^I-ρ globally (only its σ-image is unit-adjacent);
  Kedlaya's x_n-formula uses [z̄]^{i−n−1} with NEGATIVE exponents —
  in his field-coefficient world fine; ours: [z̄]-inverses do NOT exist
  in B^I-ρ... BUT the formula only needs g-POSITIVE-powers after
  re-indexing: x_n = −Σ_{i=0}^{n} y_i·g^{i−n−1} has exponents ≤ −1 —
  his convention allows [z̄^{-1}]-Teichmüllers (L a field). OUR case-1
  kernel argument must instead follow the per-radius split he gives:
  at radii τ with v_τ(g) > 1 (below the cut: τ < σ₁-side) T − g is
  a UNIT of the τ-component-RPS (geometric series in g⁻¹T?? g-inverse
  again... his 'T − [z̄] invertible in B^{[t,t]}{T/ρ}' inverts via
  [z̄]⁻¹(1 − [z̄]⁻¹T)⁻¹ — the component B^{[t,t]} = hatK-τ is a FIELD
  ✓ g-inverse EXISTS per-component!). So P4-b works COMPONENTWISE
  (hatK-fields) + the coefficientwise-completeness reassembly
  (isRestricted from the two component-decays — the C:Banach-to-Fréchet
  analogue = our isRestricted_iff_wI). Substantial; sequence as:
  (P4-a1) N_τ + wIRPS = max-lemma; (P4-a2) hatK-Gauss multiplicativity
  (or the ≥-bound directly via leading-index); (P4-a3) strictness;
  (P4-b1) the componentwise inverse-formula x-construction — NOTE the
  subtle heart: at the generic cut position v_{ρ₁}(g) > 1 > v_{ρ₂}(g)
  the fst-component needs the UP-telescope and snd the DOWN-telescope;
  the two must define the SAME x-pair, which is exactly where the
  eval-vanishing hypothesis enters (Kedlaya ln 534-546); (P4-b2)
  decay + reassembly (isRestricted from the two component-decays);
  (P4-b3) ker = span. Then (P5) the case-1 iso package
  B^I⟨T⟩/(T − C g) ≅ B^{I′} + the ρ ∈ p^ℚ plus-ring statement (via the
  ChartVObj plus-technique), and the [z̄⁻¹]-variant case 2 (mirrored
  cut on the right — the geometry swaps ρ₂ and σ₁-roles). THE ORIGINAL P3e NOTE: mirror exists_correction_sequence (Presentation:2131,
  via the generic exists_chain + exists_BIProd_approx at the σ-radii —
  note the K-rescaling: approximate to ε/(2K)-style per round so the
  K-normed corrections telescope; W ≤ 1-normalization via p-power
  scaling at the outer statement) + exists_evalBI_eq_of_correction
  (mirror :2073 with exists_rps_series_limit_BI + wI_z_sub_evalBI_add_le
  — both SHIPPED) ⇒ surjective-with-norm-control ⇒ (P4) kernel =
  (T − C g) strictness/injectivity ⇒ (P5) the case-1 iso package.
  The original (v-d)-plan sketch: x = mk'(w, sPow k) with both
  σ-wLoc ≤ 1; head/tail split at N (mk'_sPow_split + choose over
  dvd_sub_sum); f := Σ_{i≤N} ⟨monomial (single 0 j_i) (blocToBI-ρ
  Y_i), isRestricted_monomial_BI⟩ (RPS-subring sum); eval f =
  Σ φ(blocToBI Y_i)·b^{j_i} (evalBIHom = evalBI on subring-sums via
  map_sum + evalBI_monomial) = Σ BIProd-σ(Y_i·g^{j_i}) (resIHom_
  blocToBI + BIProd-mult) = BIProd-σ(head) (package hfact); residual
  = BIProd-σ(tail-term), wI-σ ≤ max of two wLoc_mk'_tail_le-bounds
  (σ-radii geometric in N); wIRPS f ≤ K := σ₁^m(ρ₁^m)⁻¹ via
  wIRPS_finset_sum_le + wIRPS_monomial + the package bounds +
  wLoc_mk'_monomial_le + the element bounds ≤ 1.
  (exists_evalBI_approx_bloc: finite T-polynomial lift of the head via
  mk'_sPow_split + per-monomial dispatch, tail small; NOTE the plan is
  APPROXIMATE-lift (residual ≤ ε), not exact — the correction machinery
  only needs first-approximations, avoiding the infinite T-regrouping).
  P3d(i) SHIPPED 2026-07-27 (commit 7111e8ef1): teichPowGen +
  algebraMap_p_pow_mul_vp_pow + teichPowGen_pow_mul_twist (the exact
  substitution identity) + exists_twist (maximal-twist normalization
  via Nat.findGreatest; PERF: set-bound lambdas need show-beta at every
  P-use site; NNReal.exists_pow_lt_of_lt_one needs namespace
  disambiguation). NOTE RobbaPresentation now imports ChartVObj? NO —
  NOT yet: sPow/gaussValue_sPow live in ChartVObj.lean; when P3d(ii)
  needs mk'-monomials either import ChartVObj into RobbaPresentation
  or work at the alg(p^i[c])·u_k-factored form (u_k := mk'(1, s^k)
  unit) — DECIDE at implementation. STALE-BELOW:
  case 1's lift is NOT norm-≤ like case 3's — Kedlaya (4.9.1) is
  |z|_ρ ≤ c^{t₀−t}·λ_{I′}(x), a CONSTANT blow-up (the far endpoint vs
  the cut endpoint). In our radius-1 conventions: monomial x = p^n[x̄],
  j minimal with |x̄| ≥ c^j (c := |z̄^e|-content), lift y·T^j with
  y := p^{n+mj}[x̄·z̄^{-ej}] (twist INSIDE the Teichmüller — field F),
  eval(y·T^j) = p^n[x̄]-image exactly (Teichmüller multiplicativity);
  norms: v_τ(y) = v_τ(x)·(τ^m c^{-e})^j — at τ = σ₁ (cut) it is ≤
  v_{σ₁}(x) (ratio ≤ 1 there), at τ = ρ₂ bounded by CONST·v_{σ₁}(x)
  via j-minimality (|x̄| < c^{j−1}). So the P3d statement is
  wIRPS f ≤ K·wI-σ(x-image) with an explicit constant K = K(radii),
  and P3e's correction-iteration approximates to ε/K per round
  (statement shapes must carry K; exists_chain is generic enough).
  The constant-K form still gives STRICT surjectivity (open mapping)
  which is all Lemma 4.9 needs. (P3e) exists_correction_sequence_BI +
  exists_evalBI_eq_of_correction + surjectivity, K-scaled.
  ALSO note wI_finite_of_isRestricted (Presentation:2265) already
  covers the BISub-restricted-finiteness (isRestricted_iff_wI overlaps
  it — dedupe when porting: keep both names, they differ in direction
  packaging);
  (P4) kernel = (T − b), closed, strict: multiplicativity bound wI(y) ≥
  |T−b|-factor + the x_n = −Σ y_i [z̄]^{i−n−1} coefficient-decay injectivity
  (Kedlaya ln 527–546; per-t case split t < t₀ geometric unit / t ≥ t₀
  quotient-iso);
  (P5) the Banach-iso package + the ρ ∈ p^ℚ plus-ring statement (integral
  closure of the image of B^{I,+} = B^{I′,+} — reuse the ChartVObj
  plus-reconciliation technique: three-zone/power-integrality).
  Case 2 ([z̄⁻¹]-variant, right cut) mirrors with the endpoint swapped.
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
