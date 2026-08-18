# `/mathlibable` report — `PadicLFunctions.integerRing.ballIdeal`

**Final verdict: `NO-mathlib-has-it`** (via re-aim to `Valuation.Integers.leIdeal`).

Mode A, full 10-phase workflow, exhaustive literature search. ChatGPT MCP and the
Lean search MCPs (Lean-Finder / Loogle / LeanSearch / state-search) are unavailable
in this environment; recorded `n/a` per channel with reason and compensated with
extra WebSearch queries (≥6 distinct, at three generality levels) and an exhaustive
grep of the local mathlib source tree (`.lake/packages/mathlib`).

---

### Baseline (Phase 0)
- lake build:               not re-run; reasoned from source (per task instruction — build is stale/slow). The declaration and all its dependencies were read directly from `Coefficients.lean` and the local mathlib tree under `.lake/packages/mathlib`.
- decl `PadicLFunctions.integerRing.ballIdeal`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:68` (unique grep match)
- kind:                      `def` (`noncomputable def`)
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) `integerRing L` of a nonarchimedean complete normed `ℚ_[p]`-algebra field `L`, with its ultrametric/complete/algebra structure, plus root-of-unity norm lemmas (W1/W2/W3).

---

### Statement (Phase 1)

`PadicLFunctions.integerRing.ballIdeal` is a **definition** of the following:

Let `L` be a complete nonarchimedean normed field that is a normed `ℚ_p`-algebra, with
integer ring `𝒪_L = integerRing L = {x ∈ L : ‖x‖ ≤ 1}` (a `Subring L`). For a real
radius `ε`, `ballIdeal L ε` is the **closed ball of radius `max ε 0`** inside `𝒪_L`,
i.e. `{x ∈ 𝒪_L : ‖x‖ ≤ max ε 0}`, packaged as an **ideal** of `𝒪_L`. It is an ideal
because the norm is ultrametric (closure under `+`: `‖x+y‖ ≤ max ‖x‖ ‖y‖ ≤ max ε 0`)
and multiplicative with `𝒪_L` being the unit ball (absorption: for `r ∈ 𝒪_L`,
`‖r·x‖ = ‖r‖‖x‖ ≤ 1·‖x‖ ≤ max ε 0`). The `max ε 0` clamp makes the construction total
for every real `ε` (a negative radius gives the zero ideal).

Mathematically this is the standard **valuation ideal of bounded valuation**: in the
ring of integers of a nonarchimedean field, `{x : v(x) ≤ γ}` (equivalently
`{x : ‖x‖ ≤ r}` for `r ≤ 1`) is an ideal, and as `r` ranges over `(0,1]` these ideals
form a fundamental system of neighbourhoods of `0` — the linear (adic) topology.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]`, `[CompleteSpace L]` — the ambient nonarchimedean field. Only `NormedField` + `IsUltrametricDist` are actually *used* by `ballIdeal`'s proof; `NormedAlgebra ℚ_[p] L` and `CompleteSpace L` are inherited section variables (see Phase 4).
- `ε : ℝ` — the radius.

Hypotheses (Lean side): none beyond the typeclasses (`ε` is unconstrained; negative `ε` handled by `max ε 0`).

Conclusion (math): the closed ball of radius `max ε 0` in `𝒪_L` is an ideal of `𝒪_L`.

Conclusion (Lean): `Ideal (integerRing L)` — n/a (definition; the `Ideal` structure is the payload).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a helper construction (a bundled set-with-closure-predicate), not a named
theorem and not a `## Main declarations` entry. The module docstring lists `integerRing`,
`IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one` as the main
declarations; `ballIdeal` is infrastructure feeding the in-file `IsLinearTopology` instance
(its docstring: "Needed for `PowerSeries.eval₂`-substitution into `(integerRing L)⟦T⟧`").

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~6 substantive lines (`carrier`, `add_mem'`, `zero_mem'`, `smul_mem'`
with a 3-line tactic block). This is a **bundled-structure definition** (an `Ideal … where`
with field proofs), not a one-line `:=` alias.

One-liner verdict: **MULTI-LINE** — the one-liner exemption table is therefore skipped
(the def carries real proof obligations: ultrametric `add_mem'` + multiplicative `smul_mem'`).

Conclusion: MULTI-LINE.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "ring of integers nonarchimedean field ideal … closed ball radius norm topology base of neighborhoods" | yes | `𝒪 = {‖x‖≤1}` is a local ring; open unit ball `𝔭 = {‖x‖<1}` is its maximal ideal; closed balls `{‖x‖≤r}` are ideals; uniformizer `π`, `𝔭ⁿ = πⁿ𝒪` | MIT 18.785 §8, Harvard Math 571, uchicago notes — completely standard |
| 2 | WebSearch (general form) | "linearly topologized ring" ideals of bounded norm valuation ring neighborhood basis ultrametric Banach algebra | yes | LT ring = topological ring with a neighbourhood basis of `0` made of (left) ideals; power-bounded subring `A°`, topologically-nilpotent ideal `A°°`; Huber/adic rings | Warner *Topological Rings*; nLab "linear topological ring"; Kedlaya condensed notes — this is exactly mathlib's `IsLinearTopology` |
| 3 | WebSearch (named-after / aliases) | "fractional ideal"/"valuation ideal" `pⁿ` integer ring p-adic field ball radius linear topology adic | yes | "valuation ideal" = maximal ideal of the valuation ring; `{‖x‖≤r}` for `r≤1` are the standard bounded-valuation ideals; `pℤ_p = {‖x‖_p<1}` | aliases: "valuation ideal", "ideal of bounded valuation", "fractional ideal `cI ⊆ 𝒪`" |
| 4 | ChatGPT MCP | (intended: "standard definition + generality + historical evolution of the bounded-valuation ideal / closed-ball ideal in the ring of integers of a nonarchimedean field") | n/a | — | **MCP unavailable in this environment.** Compensated by extra WebSearch rows (#1–3, #9–10) covering specific form, most-general form, aliases, and the abstract LT-ring/adic-ring generalisation. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | n/a | (no references dir) | Project has no `.mathlib-quality/references/` and no `refs/` symlink; recorded n/a. The `--refs=` arg pointed at the **skill's own** `references/` (workflow docs), which were read for Phase 5/7 method + verdict definitions. |
| 6 | nLab ("linear topological ring") | fetched `ncatlab.org/nlab/show/linear+topological+ring` | yes | "A topological ring `R` is said to have a (left) **linear topology** if it has a topological base of neighbourhoods of `0` consisting of (left) **ideals**." + Gabriel's uniform-filter characterization | Confirms `IsLinearTopology` is the standard modern abstraction. nLab gives no normed/valuation example (examples section empty). |
| 7 | nCatLab (categorical) | (same page; categorical content) | partial | Gabriel filter / Gabriel topology characterization of linear topologies | The categorical home is "Gabriel topology / linear topology"; no extra ball-specific content. |
| 8 | Stacks Project (alg geom) | "linear topology ideal of definition adic ring weakly admissible neighborhood basis ideals" → Tag 0AMQ §87.4 | yes | "linearly topologized ring"; weak ideal of definition = open ideal of topologically-nilpotent elements; weakly-pre-adic = closures of `Iⁿ` form a fundamental system of open ideals; hierarchy adic ⇒ weakly adic ⇒ admissible | Stacks 0AMQ — the algebraic-geometry framing of exactly the same linear-topology structure |
| 9 | MathOverflow / Math.StackExchange | valuation ring "ideal of bounded valuation" balls form neighborhood basis ring of integers complete nonarchimedean linear topology adic | yes | "the valuation ring and its maximal ideal are clopen"; "all open balls and spheres are clopen in nonarchimedean valued fields"; balls form the nhd basis → locally compact / linear topology | Ivanov adic-spaces notes, Conrad Perfectoid seminar L5 (Huber rings), Gathmann §12 — consistent; no single "named" object beyond "valuation ideal" |
| 10 | recent arXiv (last 5y) | p-adic / nonarchimedean + bounded-valuation ideal + linear/adic topology | yes (context) | reified valuations & adic spectra (arXiv:1309.0574); completions of valuation rings (arXiv:math/0310192) — confirm the construction is standard background, not a recent named result | No recent paper *names* `{‖x‖≤ε}`-as-ideal as a new object; it is classical infrastructure |

Protocol pass check:
- WebSearch ran **6** distinct queries (#1, #2, #3, #9, #10, plus the initial recon) at three generality levels (specific norm-ball form, most-general LT-ring/adic form, named aliases) — ✓ ≥3.
- ChatGPT MCP — `n/a` with reason (tool absent); compensated as noted — recorded honestly, not skipped silently.
- Local references — checked (`n/a`, directory absent).
- nLab — checked (fetched, verbatim definition quoted) — ✓.
- nCatLab / Stacks / MathOverflow / arXiv — each checked with a result, not blank.

### Literature summary (Phase 3)

Concept identified as: **the valuation ideal of bounded valuation / the closed ball of
radius `r ≤ 1` in the ring of integers of a nonarchimedean field, as an ideal** — and,
collectively over `r`, the **linear (adic) topology** with a neighbourhood basis of ideals.

Sources agree on the standard form: **yes**. Universal across MIT/Harvard/uchicago number-
theory notes, nLab, Stacks (0AMQ), Warner's *Topological Rings*. The object is classical
infrastructure; it has the common names "valuation ideal" / "ideal of bounded valuation",
but `{x : ‖x‖ ≤ ε}`-as-an-ideal is not a *separately-named* object — it is the obvious
specialisation of "ideal `{v(x) ≤ γ}` of the valuation ring".

Most general standard form: for a (possibly higher-rank) valuation `v : K → Γ₀` with
integer ring `𝒪 = {v ≤ 1}`, and `γ ∈ Γ₀`, the set `{x ∈ 𝒪 : v(x) ≤ γ}` is an ideal of `𝒪`.
The rank-one (real-valued / norm) case `{‖x‖ ≤ ε}` is the analytic specialisation.

Generality dimensions where the literature varies:
- **Value target**: real norm `‖·‖ ∈ ℝ≥0` (analytic) ⟷ general value group `Γ₀` (algebraic, higher rank). Most general is `Γ₀`.
- **Ambient structure**: complete normed field ⟷ arbitrary valued/Huber ring. Most general is any linearly-topologized / valued ring.
- **Radius range**: `ε ≤ 1` gives an honest ideal of `𝒪`; `ε > 1` collapses to `⊤` (the whole `𝒪`). `ballIdeal` accepts any `ε : ℝ` and clamps the lower end with `max ε 0`.

Disagreement with the literature: **none** — `ballIdeal` is a faithful (real-valued)
instance of the standard "ideal of bounded valuation". The only non-canonical wrinkle is
the `max ε 0` clamp, which is a Lean totality device, not a mathematical feature.

---

### Generality analysis — `PadicLFunctions.integerRing.ballIdeal`

Literature-standard form (from Phase 3): `{x ∈ 𝒪 : v(x) ≤ γ}` is an ideal of the valuation
integer ring `𝒪 = {v ≤ 1}`, for a valuation `v : K → Γ₀` and `γ : Γ₀`. The norm case is
`v = ‖·‖₊ : L → ℝ≥0`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | `[NormedField L]` + `[IsUltrametricDist L]` | rank-one nonarchimedean normed field | arbitrary valuation `v : K → Γ₀` (any value group) | yes | The ideal proof uses only multiplicativity + the ultrametric `+` bound — both supplied by any `Valuation`. Mathlib's `Valuation.Integers.leIdeal` is stated at exactly this generality (`Γ₀`). |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_p`-algebra | — | yes (unused) | `ballIdeal`'s body never mentions `ℚ_p` or the algebra. Pure inherited section variable; irrelevant to the construction. |
| 3 | `[CompleteSpace L]` | complete | — | yes (unused) | Completeness is not used to build the ideal (it is needed elsewhere, e.g. the `CompleteSpace (integerRing L)` instance and the topology-basis lemma, but not by `ballIdeal` itself). |
| 4 | `(ε : ℝ)` with `max ε 0` | real radius, clamped | `γ : Γ₀` (already ≥ 0) | yes | With a `Γ₀ = ℝ≥0` radius the clamp is unnecessary (`ℝ≥0` is already non-negative). The `max ε 0` is a totality artifact of choosing `ℝ` instead of `ℝ≥0`. |
| 5 | carrier on `integerRing L` (project `Subring`) | project-local `Subring` | `v.integer` (mathlib `Subring`) | yes | `integerRing L` and `(NormedField.valuation).integer` have the **same carrier** `{x : ‖x‖ ≤ 1}` (`mem_integer_iff`); the project re-declared what mathlib already provides. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rank-one / norm specialisation
of the `Γ₀`-valued `leIdeal`; plus three unused/avoidable hypotheses).
Number of weakening opportunities found: K = 5 (rows 1–5).

Proposed restatement (if pursued as a *new* contribution): drop to a bare `Valuation`,
which is exactly mathlib's existing `Valuation.Integers.leIdeal (v : Valuation R Γ₀) (γ : Γ₀)`
— i.e. the "restatement" already exists in mathlib (see Phase 5). So this is not a
generalise-then-PR case; it is a **the-general-form-is-already-in-mathlib** case.

Cost of restatement: CHEAP — but moot, because the general form is `leIdeal`, already shipped.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let `L` be a foo" → typeclasses/instances? | no | already typeclass-based (`NormedField`/`IsUltrametricDist`) | — |
| 2 | sequences/metric → filters/topology? | no | `ballIdeal` is algebraic (an ideal), not a limit notion | — |
| 3 | construct an object → universal-property class? | partial | the *purpose* (linear topology) is already a universal-style class: `IsLinearTopology` (nLab/Stacks confirm this is the right abstraction). But that is the *instance* decl, not `ballIdeal`. | the in-file `IsLinearTopology (integerRing L)` instance; mathlib has the class but no instance for valued/normed integer rings |
| 4 | set-with-closure-predicate → bundled-substructure type? | **yes** | the carrier `{x : ‖x‖ ≤ 1}` should be the bundled `Valuation.integer` (which `ballIdeal`'s parent `integerRing` re-implements); and `{x : ‖x‖ ≤ ε}`-as-ideal should be `Valuation.Integers.leIdeal` | `leIdeal_mono`, `mem_leIdeal_iff`, `leIdeal_zero`, `leSubmodule_*` API; lattice/quotient API on ideals |
| 5 | vector-space/metric/field-specific → weakened typeclass (module/ring)? | **yes** | weaken `NormedField` to a `Valuation` (the norm is `NormedField.valuation`, a rank-one `Valuation`); mathlib's `NormedField.toValued`/`setOf_mem_integer_eq_closedBall` already bridge norm↔valuation | the whole `Valuation` API: `leIdeal`, `ltIdeal`, `Integers`, valuation-topology lemmas |
| 6 | 1-categorical → higher/∞-categorical? | no | n/a (point-set / ideal-theoretic) | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | **yes** | radius `ε : ℝ` → value-group element `γ : Γ₀`; this is precisely `leIdeal (γ : Γ₀)` | unifies with the higher-rank valuation API; removes the `max ε 0` clamp |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is not a *new* modernisation to be authored: the
modern, bundled, typeclass-weakened form **already exists in mathlib** as
`Valuation.Integers.leIdeal` (plus the `NormedField.valuation` / `NormedField.toValued`
bridge). The mathlib-idiomatic move is therefore to **reuse `leIdeal`**, not to add a
norm-stated `ballIdeal`. Rows 4, 5, 7 all point at the same already-shipped target.

- Cost of switching to the mathlib idiom: CHEAP (re-aim at `leIdeal`; see Phase 6).
- Real mathematical improvement: eliminates a rank-one re-derivation of an existing general
  construction and connects to the full `Valuation` API. This pushes the verdict to a NO
  bucket (mathlib has it), not a YES-but-generalise (which would apply only if mathlib
  lacked the general form — it does not).

---

### Diamond / defeq risk — `PadicLFunctions.integerRing.ballIdeal`

(Kind is `def`, so Phase 4.5 runs. Risk is assessed for the *hypothetical* of adding the
norm-stated `ballIdeal` to mathlib; since the verdict is NO, this is informational.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | `ballIdeal` is a plain `Ideal` value, not an instance; it introduces no typeclass-search path. No diamond. |
| 2 | Reducibility leak | none | Not `@[reducible]`; sealed `noncomputable def`. Body is a bundled `Ideal` with proof fields — semireducible, won't leak into defeq-checking. |
| 3 | Non-canonical unfolding | low | `simp [ballIdeal]` unfolds the carrier to `{x | ‖x‖ ≤ max ε 0}` (used at `Coefficients.lean:87`). The `max ε 0` means `simp` users must carry `max_eq_left hε.le`; mildly surprising but local and handled. |
| 4 | Instance priority collision | none | Not an instance. |
| 5 | Universe-polymorphism issues | none | `L : Type*` monomorphic per use; no forced universe annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (one LOW row, #3, fully local and already mitigated in the file).
Top risks: none. No mitigations required.

---

### Mathlib search-status: `PadicLFunctions.integerRing.ballIdeal`

[A] Lean-Finder       — n/a: Lean-Finder MCP not available in this environment. Compensated by [D] exhaustive source grep.
[B] Loogle            — n/a: `lean_loogle` MCP not available. Type-pattern intent (`Ideal (Subring _)` from a `‖·‖ ≤ _` carrier; `Valuation _ _ → _ → Ideal _`) executed via [D] grep instead; hit (`leIdeal`).
[C] LeanSearch        — n/a: `lean_leansearch` MCP not available. NL intent ("ideal of elements of bounded valuation/norm in the ring of integers") executed via web (Phase 3) + [D] grep; hit (`leIdeal`).
[D] Grep mathlib src  — terms: `: Ideal`/`Ideal … where` in `Analysis/`, `Valuation/Integers.lean`, `unitBall`/`unitClosedBall`, `leIdeal`/`ltIdeal`, `NormedField.valuation`, `setOf_mem_integer_eq_closedBall`, `IsLinearTopology` across `Valuation/`+`Valued/`+`Analysis/`. **Multiple hits** (see below).
[E] Name pattern      — terms: `ballIdeal`, `leIdeal`, `ltIdeal`, `unitClosedBall`, `integer`, `closedBall`-as-substructure → mathlib has `Valuation.Integers.leIdeal`/`ltIdeal`, `Subsemigroup.unitBall`/`unitClosedBall`, `Submonoid.unitClosedBall`, `Valuation.integer`, `NormedField.valuation`.

Searched for both:
- the user's current form (norm-stated `{‖x‖ ≤ ε}` ideal of `integerRing L`), and
- the literature-standard / general form (`{v(x) ≤ γ}` ideal of `v.integer`).

Key mathlib decls found (read, not merely cited):
- `Valuation.Integers.leIdeal (v) (γ : Γ₀) : Ideal v.integer` — `RingTheory/Valuation/Integers.lean:365` — "The ideal of elements of the valuation subring whose valuation is ≤ a certain value." Full API: `mem_leIdeal_iff` (`x ∈ leIdeal v γ ↔ v x ≤ γ`), `leIdeal_mono`, `leIdeal_zero` (`leIdeal v 0 = ⊥`), `ltIdeal_le_leIdeal`, `leIdeal_v_le_of_mem`, the `leSubmodule_*` connections. **This is the abstract `ballIdeal`.**
- `Valuation.Integers.ltIdeal (v) (γ : Γ₀ˣ) : Ideal v.integer` — Integers.lean:373 — the strict-inequality companion (open-ball ideal).
- `Valuation.integer v : Subring R` = `{x | v x ≤ 1}` — Integers.lean:32; `mem_integer_iff : r ∈ v.integer ↔ v r ≤ 1`. **Same carrier as `integerRing L`.**
- `NormedField.valuation : Valuation K ℝ≥0` = `nnnorm` — `Topology/Algebra/Valued/NormedValued.lean:48`; `valuation_apply : valuation x = ‖x‖₊` (rfl); `RankLeOne` instance; `NormedField.toValued : Valued K ℝ≥0` (line 67). **The norm↔valuation bridge.**
- `NormedField.setOf_mem_integer_eq_closedBall : {x | x ∈ Valued.v.integer} = Metric.closedBall 0 1` — NormedValued.lean:259. Confirms `v.integer` carrier = norm unit ball.
- `Submonoid.unitClosedBall (𝕜) [SeminormedRing][NormOneClass]` / `Subsemigroup.unitClosedBall` — `Analysis/Normed/Field/UnitBall.lean:139,96` — the norm-unit-ball-as-substructure (radius 1), the analytic analogue of `integerRing`/`Valuation.integer`.

Concluded: **"found in mathlib as `Valuation.Integers.leIdeal` (more general form — `ballIdeal` is the rank-one/norm specialisation); the norm↔valuation identification is supplied by `NormedField.valuation` + `setOf_mem_integer_eq_closedBall`."**

Caveat surfaced for the verdict: mathlib has the *def* (`leIdeal`) but **not** the
`IsLinearTopology` *instance* for valued/normed integer rings — grep over
`RingTheory/Valuation/`, `Topology/Algebra/Valued/`, and `Analysis/` for `IsLinearTopology`
returned **no** instance on `v.integer`/normed integer rings. That gap concerns the
*separate* `instance : IsLinearTopology (integerRing L) (integerRing L)` decl
(`Coefficients.lean:80`), not `ballIdeal` itself.

---

### Call sites — `PadicLFunctions.integerRing.ballIdeal`

Internal use count: **K = 0** (no use anywhere in the project outside the declaring file).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| Coefficients.lean:83 | `(s := fun ε => ballIdeal L ε) ?_ fun s r m hm => s.smul_mem r hm` — inside the `IsLinearTopology` instance (same file) |
| Coefficients.lean:87 | `simp [ballIdeal, Metric.mem_closedBall, …]` — proving the nhds basis, same instance, same file |

Both uses are **within `Coefficients.lean` itself**, inside the single
`instance : IsLinearTopology (integerRing L) (integerRing L)` that immediately follows
`ballIdeal`. There are zero uses in any other file and zero uses outside that one instance.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `ballIdeal`?):
- (none) — the norm-ball-ideal is constructed only here; the project's only consumer is the
  in-file linear-topology instance. No other file re-derives a bounded-norm ideal.

Composability signal (per the call-sites table): K = 0 internal uses, single in-file
consumer, no external callers → the def is **a private helper for one local instance**, not
a public API surface. Combined with Phase 5 finding mathlib's `leIdeal`, this points firmly
at a **NO** verdict (the helper duplicates a mathlib construction and has no consumers that
mathlib would inherit).

### Composition check (Phase 6)

Can `ballIdeal` be obtained from mathlib in ≤3 chained calls? The question is whether the
*ideal value* `ballIdeal L ε` equals a mathlib `leIdeal` value (up to the
`integerRing L ↔ (NormedField.valuation).integer` identification).

Attempt 1 — re-aim at `leIdeal` through the norm↔valuation bridge:
```lean
-- with v := NormedField.valuation (L) : Valuation L ℝ≥0,  valuation_apply : v x = ‖x‖₊
-- and  (NormedField.valuation).integer  having carrier {x | ‖x‖ ≤ 1} = integerRing L  (mem_integer_iff)
-- ballIdeal L ε   ↔   Valuation.Integers.leIdeal (NormedField.valuation) ⟨max ε 0, le_max_right ε 0⟩
example (x : (NormedField.valuation (K := L)).integer) {ε : ℝ} :
    x ∈ Valuation.Integers.leIdeal (NormedField.valuation) ⟨max ε 0, le_max_right ε 0⟩
      ↔ ‖(x : L)‖ ≤ max ε 0 := by
  rw [Valuation.Integers.mem_leIdeal_iff]; simpa using (NNReal.coe_le_coe).symm
```
  - Mathlib decls used: `Valuation.Integers.leIdeal`, `Valuation.Integers.mem_leIdeal_iff`, `NormedField.valuation` (`valuation_apply`), `Valuation.mem_integer_iff`, `NNReal.coe_le_coe`.
  - Result: **succeeds** mathematically — `ballIdeal` is the same ideal as `leIdeal` for the rank-one valuation `‖·‖₊`, with `γ = max ε 0` coerced into `ℝ≥0`.
  - Notes: the one genuine friction is *defeq of the subring*: the project's `integerRing L` is a **distinct `Subring` term** from `(NormedField.valuation).integer`, even though their carriers are equal (`{‖x‖ ≤ 1}`). Identifying `Ideal (integerRing L)` with `Ideal ((NormedField.valuation).integer)` needs the `Subring.copy`/carrier-equality glue, or — cleaner — replacing the project's `integerRing` def by `Valuation.integer` upstream. So this is not a literal ≤3-call drop-in *as long as `integerRing` stays a separate def*; it is a ≤3-call drop-in *once* `integerRing` is identified with `Valuation.integer` (a one-time, file-level refactor that the report recommends below).

Attempt 2 — derive the downstream `IsLinearTopology` instead, bypassing a bespoke `ballIdeal`:
the in-file instance uses `IsLinearTopology.mk_of_hasBasis'` with `s := fun ε => ballIdeal L ε`.
Re-aimed at `leIdeal`, the same `mk_of_hasBasis'` call goes through with
`s := fun γ : ℝ≥0 => Valuation.Integers.leIdeal (NormedField.valuation) γ` and the metric
nhds basis — no separate `ballIdeal` needed.
  - Result: **succeeds** in outline; the bespoke `ballIdeal` is an avoidable intermediate.

Conclusion: **COMPOSABLE / mathlib-has-it** — `ballIdeal` is the rank-one specialisation of
`Valuation.Integers.leIdeal`; the norm↔valuation identification is mathlib's
(`NormedField.valuation`, `setOf_mem_integer_eq_closedBall`). The only obstruction to a
literal one-line replacement is that the project re-declared `integerRing` instead of using
`Valuation.integer`. This is a NO verdict, classified as **NO-mathlib-has-it** (re-aimed at
the strictly-more-general `leIdeal`), not NO-composable-from-disparate-blocks: the result is
one existing mathlib def, not a multi-block assembly.

---

## Verdict: `PadicLFunctions.integerRing.ballIdeal`

**Category:** `NO-mathlib-has-it` (via re-aim to the more general `Valuation.Integers.leIdeal`)

**Evidence:**
- Literature search (Phase 3): the object is the standard "ideal of bounded valuation / closed-ball ideal" in the ring of integers of a nonarchimedean field; universal across MIT/Harvard/uchicago notes, nLab, Stacks 0AMQ. Most general form is `{v(x) ≤ γ}` for a `Γ₀`-valued valuation; the norm case is the rank-one specialisation.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (rank-one norm specialisation; two unused hypotheses `[NormedAlgebra ℚ_[p] L]`, `[CompleteSpace L]`; an `ε : ℝ` + `max ε 0` clamp that `ℝ≥0` removes). Phase 4c confirms the modern/general form is *already in mathlib*, so this resolves to NO-has-it rather than YES-but-generalise.
- Mathlib search (Phase 5): **found in mathlib as `Valuation.Integers.leIdeal`** (`RingTheory/Valuation/Integers.lean:365`), strictly more general (`Γ₀`-valued), with full API; the norm↔valuation bridge is `NormedField.valuation` + `setOf_mem_integer_eq_closedBall` (`Topology/Algebra/Valued/NormedValued.lean:48,259`).
- Composition check (Phase 6): COMPOSABLE / has-it — `ballIdeal L ε ↔ leIdeal (NormedField.valuation) ⟨max ε 0, _⟩` once `integerRing L` is identified with `(NormedField.valuation).integer` (equal carriers).
- Call sites (Phase 6.0): **K = 0** external; the only two uses are in-file, both inside the single `IsLinearTopology` instance — a private helper, not a public API.

**Rationale:**

`ballIdeal` is the real-norm spelling of a construction mathlib already ships in greater
generality. Mathlib's `Valuation.Integers.leIdeal (v : Valuation R Γ₀) (γ : Γ₀)` is "the
ideal of elements of the valuation subring whose valuation is ≤ a given value" — exactly
`ballIdeal`'s mathematical content, for any value group `Γ₀`, with the supporting API
(`mem_leIdeal_iff`, `leIdeal_mono`, `leIdeal_zero`, the submodule connections) that the
project would otherwise have to rebuild. For a nonarchimedean normed field, mathlib supplies
the rank-one valuation `NormedField.valuation = ‖·‖₊` and proves
`setOf_mem_integer_eq_closedBall`, so `integerRing L` and `(NormedField.valuation).integer`
have the *same* carrier `{x : ‖x‖ ≤ 1}` and `ballIdeal L ε` is `leIdeal` of that valuation
at `γ = max ε 0 : ℝ≥0`. The `max ε 0` clamp is a Lean totality device that disappears once
the radius lives in `ℝ≥0 = Γ₀`. Phase 4c rows 4/5/7 (bundle the carrier; weaken
field→valuation; index ℝ→`Γ₀`) all point at the same already-shipped target, so the
"generalise first" path is closed: there is nothing to generalise *to* that mathlib lacks.
The decl also has zero external consumers (K = 0; its only client is the in-file
`IsLinearTopology` instance), so removing it costs the project only a local rewrite.

One honest nuance, recorded so it is not lost: the genuinely missing mathlib piece is not
`ballIdeal` but the **`IsLinearTopology` instance** for the integer ring of a valued/normed
field — grep confirms mathlib has the `IsLinearTopology` *class* (and instances for adic
topologies and `WithIdealFilter`) but **no** instance routing through `Valued`/`leIdeal`.
That instance (`Coefficients.lean:80`) is a separate declaration and is itself a strong
**YES-but-generalise-first** candidate (it should be stated for `Valued R Γ₀` / via `leIdeal`,
giving mathlib `IsLinearTopology` for every rank-one valued ring, not just `ℚ_p`-algebras).
But that does not rescue `ballIdeal`: the right way to feed that instance is mathlib's
`leIdeal`, not a bespoke norm-ball ideal.

**WHY not (refactor-actionable):** Mathlib already has the construction as
`Valuation.Integers.leIdeal`, strictly more general. The named gap is **not** "mathlib lacks
a bounded-valuation ideal" — it has one; the gap that *does* exist is the downstream
`IsLinearTopology` instance for valued rings, which should be built **on `leIdeal`**, making
`ballIdeal` redundant either way. `ballIdeal`'s carrier lives on the project-local
`integerRing` `Subring`, which itself re-implements mathlib's `Valuation.integer` /
`Submonoid.unitClosedBall` — so the cleanest refactor identifies `integerRing` with
`Valuation.integer` first.

Existing mathlib decl:        `Valuation.Integers.leIdeal` (companion `Valuation.Integers.ltIdeal`)
Located at:                   `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Integers.lean:365` (`:373`)
Bridge decls:                 `NormedField.valuation`, `NormedField.toValued`, `NormedField.setOf_mem_integer_eq_closedBall` (`.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:48, 67, 259`); `Valuation.integer` + `mem_integer_iff` (`…/RingTheory/Valuation/Integers.lean:32, 40`)

Our form follows in ≤1 line (modulo the `integerRing ↔ v.integer` carrier identification):
```lean
-- after identifying integerRing L with (NormedField.valuation).integer (equal carrier {‖x‖ ≤ 1}):
example {ε : ℝ} :
    ballIdeal L ε = Valuation.Integers.leIdeal (NormedField.valuation) ⟨max ε 0, le_max_right ε 0⟩ :=
  Ideal.ext fun x => by
    simp [ballIdeal, Valuation.Integers.mem_leIdeal_iff, NormedField.valuation_apply,
      ← NNReal.coe_le_coe]
```

Call sites in our project (from Phase 6.0): **K = 0** external; 2 in-file (both inside the one `IsLinearTopology` instance).

**Refactor plan (the load-bearing action):**
1. **Identify `integerRing L` with mathlib's valuation integer ring.** The cleanest move is
   to make `integerRing L` defeq/equal to `(NormedField.valuation (K := L)).integer`
   (same carrier `{x : ‖x‖ ≤ 1}`). Either replace the local `integerRing` def by
   `Valuation.integer (NormedField.valuation)` (best — also retires the `integerRing`
   re-derivation), or keep `integerRing` but add `integerRing L = (NormedField.valuation).integer`
   via carrier equality, used to transport ideals. (This step is shared with the separate
   mathlibable assessment of `integerRing` itself — see that report.)
2. **Delete `ballIdeal`.** Replace its sole consumer — the `IsLinearTopology` instance at
   `Coefficients.lean:80–88` — with the `leIdeal`-based basis: feed
   `IsLinearTopology.mk_of_hasBasis'` with
   `s := fun γ : ℝ≥0 => Valuation.Integers.leIdeal (NormedField.valuation) γ` and the metric
   `closedBall` nhds basis (`Metric.nhds_basis_closedBall`), using `mem_leIdeal_iff` +
   `valuation_apply` in place of the current `simp [ballIdeal, …]`. The `s.smul_mem` argument
   becomes `(leIdeal _ γ).smul_mem` (or `mul_mem_left`), exactly as now.
3. **Strongly recommended companion (separate decl):** lift the resulting
   `IsLinearTopology (integerRing L) (integerRing L)` to a mathlib instance stated for
   `Valued R Γ₀` (rank one) via `leIdeal`, since mathlib currently has **no** linear-topology
   instance on valuation/normed integer rings. Track that as its own `YES-but-generalise-first`
   item; it is the genuine upstreaming opportunity in this file.

Next action: identify `integerRing` with `Valuation.integer` (step 1); then delete
`ballIdeal` and rewrite the in-file `IsLinearTopology` instance on `Valuation.Integers.leIdeal`
(step 2). Do **not** open a mathlib PR for `ballIdeal` — open one (later) for the generalised
`IsLinearTopology`-for-valued-rings instance instead.

---

## Next step

Identify `integerRing L` with mathlib's `Valuation.integer (NormedField.valuation)` (equal
carrier `{x : ‖x‖ ≤ 1}`), then **delete `ballIdeal`** and re-state its sole consumer — the
in-file `IsLinearTopology (integerRing L) (integerRing L)` instance — directly on
`Valuation.Integers.leIdeal (NormedField.valuation)`. Separately, pursue the genuinely-missing
mathlib piece as its own `YES-but-generalise-first` ticket: an `IsLinearTopology` instance for
the integer ring of a rank-one `Valued`/nonarchimedean field, built on `leIdeal`.
