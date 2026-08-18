# `/mathlibable` report — `PadicLFunctions.master_bridge`

**Final verdict: `YES-but-generalise-first`** (reason: MODERN-IDIOM / Bourbaki 2.0 — the analytic content is genuinely missing from mathlib, but it should ship as a reusable nonarchimedean evaluation-vs-substitution API over `IsUltrametricDist` complete normed algebras, not as a bare `tsum` identity with a hand-passed product-summability hypothesis).

---

### Baseline (Phase 0)
- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — build is stale/slow here). The declaration, its five sibling dependency lemmas (`hasSum_pow_fin`, `summable_eval_pow`, `tsum_eval_pow`, `summable_coeff_pow_scalar`, `tsum_coeff_pow_eq_coeff_subst`), its two call sites (`padicExp_padicLog`, `padicLog_padicExp`), and all mathlib substitution/evaluation dependencies were read directly from source.
- decl `PadicLFunctions.master_bridge`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:669`
- kind:                      `theorem`
- has sorry:                 no (verified: 0 `sorry` in the file; 0 in the decl body, lines 669–688)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp`/`log` convergence and isometry on matched ultrametric balls, plus the formal-substitution ↔ convergent-evaluation bridge that realises `x^s := exp(s·log x)` on `1 + pℤ_p`. `master_bridge` sits in `section Inversion` (lines 461–993, which carries `open PowerSeries`).

---

### Statement (Phase 1)

`master_bridge` is a theorem asserting that **evaluation commutes with formal substitution** for one-variable power series over `ℚ_p`, evaluated in a complete nonarchimedean normed `ℚ_p`-algebra field `L`:

> Let `F, G ∈ ℚ_p⟦X⟧` be formal power series and `y ∈ L`. Suppose `G` is formally substitutable (`HasSubst G`, i.e. its constant coefficient is "small"/zero), the evaluation series `∑ₘ [Xᵐ]G · yᵐ` converges, and the full double family `(n,k) ↦ ([Xⁿ]F · [Xᵏ](Gⁿ)) · yᵏ` is summable over `ℕ × ℕ`. Then
> `∑ₙ [Xⁿ]F · (∑ₘ [Xᵐ]G · yᵐ)ⁿ  =  ∑ₖ [Xᵏ](F.subst G) · yᵏ`,
> i.e. evaluating `F` at the value `G(y)` equals evaluating the formally-substituted series `F∘G` at `y`. In functional notation: `(eval_y) (F.subst G) = (eval_{G(y)}) F`, the composition/chain law `F(G(y)) = (F∘G)(y)` at the level of convergent values.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric (nonarchimedean) normed field that is a `ℚ_p`-algebra. This is the analytic ground ring; the norm topology, **not** an adic/linear topology, governs convergence.
- `F G : PowerSeries ℚ_[p]` — formal power series whose coefficients are coerced `ℚ_p → L` via `algebraMap` (written `(coeff … : ℚ_[p]) • _`).
- `y : L` — the point of evaluation.

Hypotheses (Lean side):
- `hG : HasSubst G` — `G` is formally substitutable (`PowerSeries.HasSubst`; here always discharged by `constantCoeff G = 0`). Needed so `F.subst G` and the coefficient identity `[Xᵏ](F∘G) = ∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)` make sense.
- `hGsum : Summable fun m => (coeff m G : ℚ_[p]) • y ^ m` — the inner evaluation series `G(y)` converges in `L`.
- `hprod : Summable fun nk : ℕ × ℕ => ((coeff nk.1 F)·(coeff nk.2 (G^nk.1))) • y^nk.2` — the entire reindexed double family is summable; this is the ultrametric hypothesis that licenses the Fubini swap (`Summable.tsum_comm`).

Conclusion (math): the chain law `F(G(y)) = (F∘G)(y)` holds for convergent nonarchimedean power-series evaluation.

Conclusion (Lean): `(∑' n, (coeff n F : ℚ_[p]) • (∑' m, (coeff m G : ℚ_[p]) • y ^ m) ^ n) = ∑' k, (coeff k (F.subst G) : ℚ_[p]) • y ^ k`.

Proof skeleton (read from source): rewrite the LHS as the iterated sum `∑ₙ ∑ₖ ([Xⁿ]F·[Xᵏ](Gⁿ))·yᵏ` using the sibling `tsum_eval_pow` (value identity `G(y)ⁿ = ∑ₖ [Xᵏ](Gⁿ)·yᵏ`) and `Summable.tsum_const_smul`; rewrite the RHS as the opposite iterated order using `tsum_coeff_pow_eq_coeff_subst` (formal-coefficient identity `[Xᵏ](F∘G) = ∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)`) and `Summable.tsum_smul_const`; then equate the two orders by ultrametric Fubini `hprod.tsum_comm`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the central "bridge" of the project's Inversion section (docstring: "**Evaluation bridge** (RJW Lem 5.14 / decomposition E4, Washington Prop 5.3 route)"), and it formalises a *named classical theorem* — the composition/chain law for convergent power series — in the nonarchimedean setting. It is the linchpin that transfers formal-power-series identities (`exp_subst_log`, `log_subst_exp_sub_one`) to analytic values.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~14 substantive lines (two `have` blocks each rewriting via a sibling lemma, then a `tsum_comm` finish).
One-liner verdict: **n/a — kind is `theorem`, not `def`**. Phase 2b exemption table skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "evaluation of formal power series substitution composition F(G(y)) equals evaluation theorem convergent p-adic nonarchimedean" | yes  | `F(G(y)) = (F∘G)(y)` for convergent substitutable `G`; valuation condition `v(g)≥1` | Conrad *Infinite series in p-adic fields*; Lubin/Berger p-adic dynamics (arXiv 1702.06037); arXiv 2311.02906 ("On preimages") all treat composition under convergence as standard |
|  2 | WebSearch (general form)         | "substitution power series f(g(x)) evaluation continuous ring homomorphism composition law analytic convergence" | yes  | composition = double-series rearrangement: `T(S(x)) = ∑ⱼ(∑ᵢ bᵢcᵢⱼ)xʲ`; "limit of compositions = composition of limits, provided inner series has valuation ≥ 1" | arXiv 1403.3623 "Double series over a non-Archimedean field" — the precise mechanism (= the project's `tsum_comm`); also MIT OCW, LibreTexts |
|  3 | WebSearch (named-after / aliases)| "composition formal power series associativity F.subst G evaluation Bourbaki Algebra IV substitutability continuous algebra homomorphism" | yes  | Bourbaki *Algebra* IV §4: "substitutability"; composition/substitution of series as the canonical operation; continuous algebra-hom universal property | Bourbaki *Algebra* II ch.4–7; arXiv 2205.00879 "An invitation to formal power series"; the operation is `f∘g = f(g(x))` with the continuous-homomorphism characterisation |
|  4 | ChatGPT MCP                      | (intended) "standard form + generality + historical evolution of evaluation-commutes-with-substitution for power series" | n/a  | —                                | **ChatGPT MCP server not configured in this environment** (no `mcp__…chatgpt`/openai tool surfaced via ToolSearch). Compensated with two extra WebSearch queries (#5 below) + nLab + the deep sibling-report corpus, so the protocol's "ask for standard form + generality" requirement is met across ≥5 sources. |
|  5 | WebSearch (mechanism / source)   | "double series non-archimedean field rearrangement Fubini summable power series composition Bosch Güntzer Remmert evaluation substitution" | yes  | BGR *Non-Archimedean Analysis* §2: nonarchimedean double-series convergence ⇔ terms → 0; sum independent of order (Fubini) | Bosch–Güntzer–Remmert (Grundlehren 261) is the canonical reference; "Tate algebra / restricted power series" is the standard analytic object |
|  6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` for the concept                          | n/a  | (no references dir)              | `…/.mathlib-quality/` contains only `overview/`; no `references/` PDF store present (and no `refs/` symlink in this checkout). Recorded n/a. The decomposition cites RJW Lem 5.14 (TeX 1892–1897, Cassels §12), Washington §5.1 Prop 5.3 as the paper-side anchors. |
|  7 | nLab                             | "power series" → "Functional substitution and inversion" | yes  | substitution `p(q₁,…,qₙ)` as clone/operad multiplication; invertibility criterion | nLab treats only the **formal** case ("no additional convergence conditions"); explicitly does **not** state evaluation-commutes-with-substitution in a convergent/normed setting. Confirms: the *analytic* statement is not the formal one. |
|  8 | nCatLab / categorical            | (covered by #7; "continuous algebra homomorphism" characterisation) | yes  | the categorical idiom is: evaluation is a *continuous algebra homomorphism* `R⟦X⟧ → S`, substitution is its universal-property factorisation | This is exactly mathlib's `PowerSeries.aeval`/`substAlgHom_eq_aeval` framing — see Phase 4c/5. The modern idiom = "eval and subst are continuous algebra homs, and the chain law is their composition." |
|  9 | Stacks Project                   | (substitutability / restricted power series) | n/a  | —                                | Not an algebraic-geometry / scheme-theoretic statement; Stacks covers completed/adic rings but not analytic nonarchimedean evaluation. Recorded n/a after a brief look. |
| 10 | MathOverflow / Math.StackExchange| "composition of convergent power series chain rule p-adic / when does F(G(y)) = (F∘G)(y)" | yes  | standard answer: holds when both series converge and the substitution is admissible (constant term in the disk of convergence) | Consistent with #1/#2; the convergence side-condition (here `hGsum` + `hprod`) is the crux everyone flags |
| 11 | recent arXiv (≤5 yr)             | "double series over a non-Archimedean field" (arXiv 1403.3623); "An invitation to formal power series" (arXiv 2205.00879); p-adic dynamics arXiv 1702.06037, 2311.02906 | yes  | contemporary treatments still phrase composition via continuous homomorphisms + double-series rearrangement | Reinforces the modern/formalisation idiom (Phase 4c): evaluation/substitution as morphisms, chain law = composition |

### Literature summary (Phase 3)

Concept identified as: the **composition / chain law for power series under convergent evaluation** — "`F(G(y)) = (F∘G)(y)`" — equivalently "evaluation commutes with (formal) substitution". Classical names: *substitutability* (Bourbaki Algebra IV §4), *composition of power series*, the analytic chain law; in the nonarchimedean case it rests on **nonarchimedean double-series rearrangement / Fubini** (BGR §2). In the project it is RJW Lemma 5.14's mechanism and "Washington Prop 5.3 route".

Sources agree on the standard form: **yes**. Every source states the same fact: when `G` is substitutable (constant term small, here `= 0`) and the relevant series converge, the value of `F` at `G(y)` equals the value of the composite `F∘G` at `y`. The nonarchimedean version's distinguishing feature is that *summability ⇔ terms tend to 0*, so the Fubini swap (the `hprod.tsum_comm` step) is clean — exactly the project's proof.

Most general standard form: the literature states it for any complete nonarchimedean field (or complete normed/Tate algebra), `F, G` power series with `G` admissible, evaluation in the disk of convergence. The modern (categorical / formalisation) idiom packages evaluation as a **continuous algebra homomorphism** `R⟦X⟧ → S` and substitution as its factorisation, so the chain law is just composition of homomorphisms.

Generality dimensions where the literature varies:
  - Ground/value ring: from `ℚ_p` specifically → any complete nonarchimedean field → any complete ultrametric normed algebra / Tate algebra. The most general analytic form is "complete normed algebra with admissible evaluation point" — and `IsUltrametricDist` is exactly what makes the double-series Fubini free.
  - Convergence packaging: classical texts state a *disk-of-convergence* side-condition; the project instead takes the convergence facts (`hGsum`, `hprod`) as explicit hypotheses. The modern idiom replaces both with a single `HasEval`-style topological-nilpotence/summability predicate on the evaluation point.
  - Number of variables: one-variable here; Bourbaki/mathlib state the multivariate version. (Out of scope for this single decl.)

Disagreement with the literature: **none** mathematically. The only gap is *packaging*: the literature/modern idiom uses a morphism + a single admissibility predicate; the project uses a bare `tsum` equation with two hand-passed summability hypotheses (one of which, `hprod`, is a strong and slightly redundant assumption — see Phase 4).

---

### Generality analysis — `PadicLFunctions.master_bridge`

Literature-standard form (from Phase 3): `F(G(y)) = (F∘G)(y)` for `F, G` over a complete nonarchimedean field/algebra, `G` admissible, evaluation in the disk of convergence — modern idiom: as composition of continuous algebra homomorphisms with one summability/topological-nilpotence side condition.

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | coefficient ring `ℚ_[p]` (of `F`, `G`) | `PowerSeries ℚ_[p]`        | any complete nonarch. field / any normed commutative ring mapping into `L` | **yes** | The proof uses only `algebraMap ℚ_[p] L` (the `(coeff … : ℚ_[p]) • _` coercion) and ring arithmetic — never a `ℚ_p`-specific fact. Could be `PowerSeries R` for `[CommRing R] [Algebra R L]` (or any normed `R`). `ℚ_p` is a needless specialisation. |
| 2 | value field `L` (`NormedField`)        | normed **field**           | complete normed/ultrametric **algebra** (need not be a field) | **yes (partly)** | The proof never inverts an element of `L`; it uses `smul`, `pow`, `Summable`, and ultrametric Fubini. `NormedField` could weaken to a normed commutative ring / `NormedRing` + `IsUltrametricDist` + `CompleteSpace`. (Tate-algebra generality.) |
| 3 | `[IsUltrametricDist L]`                | ultrametric                | nonarchimedean (the natural hypothesis) | **NO** | Load-bearing: `Summable.tsum_comm`/the unconditional double-summability and the sibling `tsum_eval_pow`'s nonarchimedean Cauchy-product (`Summable.mul_of_nonarchimedean`) genuinely need ultrametricity. Correctly the most general usable hypothesis. |
| 4 | `[CompleteSpace L]`                    | complete                   | complete (required for `tsum`/`HasSum`) | **NO** | Required for the sums to exist/be manipulated. Standard. |
| 5 | `hprod : Summable (ℕ×ℕ family)`        | explicit double-summability hypothesis | a single admissibility/topological-nilpotence predicate on `G(y)` (modern idiom) | **yes** | This is the main weakening: in the literature/modern idiom one assumes only that the evaluation point is admissible (e.g. `‖G(y)‖<1` / `HasEval`-style), from which the double summability is *derived* (cf. the project's own `summable_prod_family`, which is exactly the lemma that produces `hprod` at both call sites). Taking `hprod` as a hypothesis is narrower and slightly redundant. |
| 6 | `hGsum` + `hG : HasSubst G`            | two separate hypotheses    | one admissibility predicate implies both | **yes** | Same point as #5: the modern packaging derives `hGsum` (inner convergence) from admissibility of the point, and `HasSubst G` is the formal-side admissibility. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **K = 4** (coefficient ring `ℚ_p`→`R`; value type field→normed algebra; the `hprod` double-summability hypothesis → a single admissibility predicate that *implies* it; bundling `hGsum`+`HasSubst` likewise).
Proposed restatement (literature-weakening axis):

```lean
-- Coefficient ring and value type weakened; the double-summability still a hypothesis
-- (the cleaner admissibility-predicate version is the Phase-4c modern-idiom target).
theorem eval_subst_eq {R : Type*} [CommRing R] {L : Type*} [NormedCommRing L]
    [Algebra R L] [IsUltrametricDist L] [CompleteSpace L]
    (F G : PowerSeries R) (y : L) (hG : HasSubst G)
    (hGsum : Summable fun m => (algebraMap R L) (coeff m G) • y ^ m)
    (hprod : Summable fun nk : ℕ × ℕ =>
      ((algebraMap R L) (coeff nk.1 F) * (algebraMap R L) (coeff nk.2 (G ^ nk.1))) • y ^ nk.2) :
    (∑' n, (algebraMap R L) (coeff n F) • (∑' m, (algebraMap R L) (coeff m G) • y ^ m) ^ n)
      = ∑' k, (algebraMap R L) (coeff k (F.subst G)) • y ^ k := by
  sorry -- current proof should survive verbatim (it never used ℚ_p- or field-specific facts)
```

Cost of restatement: **CHEAP** — mechanical (`ℚ_[p] → R`, `NormedField → NormedCommRing`, `(coeff … : ℚ_[p])` coercions → `algebraMap R L (coeff …)`); the proof body uses no `ℚ_p`- or field-specific lemma. (EXPENSIVE is not a downgrade per the skill, but here it's genuinely cheap.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances? | **yes** | Replace the three bundled convergence/admissibility hypotheses with a single predicate on the evaluation point — an ultrametric analogue of mathlib's `PowerSeries.HasEval` (topological nilpotence), call it `HasEvalUltrametric y` (or reuse a `‖·‖<1`/in-the-ball predicate). From it derive `hGsum`, `hprod`, and the chain law. | All of the project's `summable_prod_family`/`summable_eval_pow` plumbing folds into one admissibility predicate; downstream `padicExp_padicLog`/`padicLog_padicExp` call sites stop hand-constructing `hprod`. |
|  2 | sequences/metric → filters/topology? | **partly** | Convergence is already `Summable`/`HasSum` (filter-based `tsum`), so the *sum* side is modern. The *admissibility* side could be phrased as topological nilpotence of the evaluation point (mathlib's `IsTopologicallyNilpotent`/`HasEval`) rather than ad-hoc summability hypotheses. | Aligns with mathlib's `MvPowerSeries`/`PowerSeries` `HasEval` evaluation API; would let the result interoperate with `PowerSeries.aeval` once an ultrametric-normed `HasEval` bridge exists. |
|  3 | construct an object where a universal-property class would characterise it? | **yes (the central one)** | Package evaluation as a **continuous algebra homomorphism** `evalₐ y : R⟦X⟧ →ₐ[R] L` (defined on admissible points), the ultrametric-normed analogue of `PowerSeries.aeval`. Then `master_bridge` is exactly the composition law `evalₐ y ∘ substAlgHom hG = evalₐ (evalₐ y G)` — i.e. the normed-field analogue of mathlib's existing `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst`. | This is the load-bearing modernisation: it would mirror mathlib's `comp_aeval`/`eval₂_subst` (which currently exist **only** in the linear/adic-topology setting) into the normed-field/Tate setting, so every "evaluate a substituted series" step in p-adic analysis becomes a one-line `comp_aeval`-style call instead of a bespoke `tsum_comm` proof. |
|  4 | set-with-predicate → bundled substructure? | no | The admissible points already form an ideal in the adic case (`hasEvalIdeal`); a bundled version is a nice-to-have but not the core move. | — |
|  5 | vector-space/field-specific → module/(semi)ring weakening? | **yes** | Covered by Phase 4b rows #1–2: `ℚ_p`→`R`, `NormedField`→`NormedCommRing`. | full module/algebra API; scalar restriction/extension; reuse for `ℂ_p`, finite extensions, Tate algebras. |
|  6 | 1-categorical → higher-categorical? | no | Plain analytic identity; no higher-categorical content. | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | The `ℕ` index is the (one-variable) power-series degree; the genuine generalisation is multivariate (`MvPowerSeries`), which mathlib already has on the formal side. Out of scope for this single decl. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
  - Proposed mathlib-idiomatic restatement: define an ultrametric-normed evaluation algebra hom `aeval`-analogue on admissible points, and state the bridge as its **composition law**, mirroring `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst`:
    ```lean
    -- schematic target (the real PR would build the HasEval-analog first):
    theorem ultrametric_eval_subst {R} [CommRing R] {L} [NormedCommRing L] [Algebra R L]
        [IsUltrametricDist L] [CompleteSpace L] {G : PowerSeries R} (hadm : HasEvalUltrametric (eval y G))
        (hG : HasSubst G) (hy : HasEvalUltrametric_point y) (F : PowerSeries R) :
        eval y (F.subst G) = eval (eval y G) F := …
    ```
  - Cost: **MODERATE** — building the `HasEval`-style admissibility predicate + the `aeval`-analogue (an `AlgHom` whose existence over a non-linear topology is the new infrastructure) is real work; the bridge itself is then `comp_aeval`-shaped.
  - Mathlib downstream this enables: every nonarchimedean "evaluate a substituted/composed series" step (p-adic `exp`/`log` inversion, formal groups, Lubin–Tate, Coleman maps, Iwasawa-theoretic power-series evaluation) becomes a one-call composition; it would be the **normed-field counterpart of the adic-only `comp_aeval`/`eval₂_subst`**, closing a real and currently-load-bearing gap (mathlib's evaluation API stops at linear topologies — see Phase 5).
  - Real mathematical improvement (not just "looks cooler"): it removes the redundant `hprod` hypothesis (derivable from admissibility) and the bespoke `tsum_comm` proof, and unifies the project's analytic evaluation with mathlib's existing morphism-based substitution/evaluation framework.

Because Phase 4b is STRICTLY NARROWER **and** Phase 4c finds a real modern idiom, Phase 7 selects `YES-but-generalise-first` (both reasons fire).

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or typeclass-search paths). Skipped.

---

### Mathlib search-status: `PadicLFunctions.master_bridge`

[A] Lean-Finder       (not invoked as a live service in this run; substituted with exhaustive source grep [D]+[E] over the pinned mathlib tree `rev 005f0aa67b69`, v4.32) — n/a: tool not wired; covered by [D]/[E]
[B] Loogle            type pattern `eval _ (PowerSeries.subst _ _) = eval _ _` / `_⟦X⟧ → _ → _` chain laws — conceptually targeted via the source grep; the only chain-law decls are `comp_aeval`, `eval₂_subst`, `substAlgHom_comp_substAlgHom` (all linear-topology)  → no analytic hit
[C] LeanSearch        "evaluation of a substituted power series equals evaluation at the evaluated series", "power series composition chain law tsum normed" — resolved via source reading of `PowerSeries/Evaluation.lean` + `Substitution.lean`  → only the `aeval`/`HasEval` (linear-topology) framework
[D] Grep mathlib src  `tsum.*subst`, `subst.*tsum`, `Summable.*subst`, `eval₂_subst`, `comp_subst`, `comp_aeval`, `substAlgHom_comp_substAlgHom`, `seriesEval`, `eval_subst`, `subst_eval`, `IsLinearTopology` over `Analysis/Normed`, `NumberTheory/Padics`, `Topology/Algebra/Valued`  → **no analytic/normed hit**; chain-law lemmas exist only in `RingTheory/{PowerSeries,MvPowerSeries}/{Evaluation,Substitution}.lean`; **no `IsLinearTopology` instance for any normed field**
[E] Name pattern      `seriesEval`, `eval_subst`, `subst_eval`, `evalBridge`, `tsum_subst` in mathlib  → **empty** (no such names in mathlib)

Searched for both:
  - the user's current form (`∑' n, [Xⁿ]F • (∑' m, [Xᵐ]G • yᵐ)ⁿ = ∑' k, [Xᵏ](F∘G) • yᵏ` over a normed field) — not present.
  - the literature-standard / modern-idiom form (`eval (F.subst G) = eval F` via a continuous algebra hom; `comp_aeval`) — **present in mathlib, but only for the linear/adic topology**: `PowerSeries.comp_aeval` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:241`), `MvPowerSeries.eval₂_subst` / `comp_subst` / `substAlgHom_comp_substAlgHom` (`Mathlib/RingTheory/MvPowerSeries/Substitution.lean:378,439`), and `PowerSeries.substAlgHom_eq_aeval` (`Substitution.lean:180`). All require `[IsLinearTopology S S]` + `[DiscreteUniformity R]` + `[IsTopologicalRing S]` — the adic/formal topology. **A `p`-adic normed field `L` is not linearly topologized** (a field's only ideals are `0` and `L`, so there is no basis of ideal-neighbourhoods of `0`; grep confirms zero normed-field `IsLinearTopology` instances). Mathlib's `aeval`/`eval₂`/`HasEval` evaluation API (`PowerSeries.hasSum_aeval`, `aeval_eq_sum`, `Evaluation.lean:177–247`) is likewise gated on `[IsLinearTopology S S]`, so it does **not** specialise to convergent evaluation in a normed field.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard/modern-idiom form). Mathlib has the *formal/linear-topology* chain law (`comp_aeval`, `eval₂_subst`) and the analytic *single-series* evaluation primitives (`HasSum`, `Summable.tsum_comm`, `tsum_mul_tsum_eq_tsum_sum_antidiagonal`, `Summable.mul_of_nonarchimedean`), but **not** the analytic-evaluation chain law over a (non-linearly-topologized) nonarchimedean normed field.

---

### Call sites — `PadicLFunctions.master_bridge`

Internal use count: **K = 2** (within the project, NOT counting the declaring statement at line 669).
External-to-file callers: **0 distinct files** (both uses are in `PadicExp.lean`, but in *different theorems* from `master_bridge` itself).

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| PadicExp.lean:942 (`padicExp_padicLog`) | `master_bridge p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x-1) HasSubst.log hGsum (summable_prod_family …)` — then `exp_subst_log`, `eval_oneAddX` to conclude `exp(log x) = x` |
| PadicExp.lean:966 (`padicLog_padicExp`) | `master_bridge p (PowerSeries.log ℚ_[p]) (exp ℚ_[p]-1) x HasSubst.exp_sub_one hGsum (summable_prod_family …)` — then `log_subst_exp_sub_one`, `eval_X` to conclude `log(exp x) = x` |

Inline-derivation grep (was the equivalent re-derived elsewhere without `master_bridge`?): **(none)** — no other site re-derives the chain law inline; the two consumers both go through `master_bridge`. Note both call sites also supply `hprod` via the project's `summable_prod_family` lemma — direct confirmation of the Phase-4 finding that `hprod` is *derivable from an admissibility predicate* and need not be a hypothesis of the general form.

Signal: K = 2 internal uses, both in distinct downstream theorems, no inline re-derivation → **real API** (the two inversion theorems `exp∘log = id`, `log∘exp = id` depend on it essentially). This is the bridge that makes the whole `Inversion` section work. Leans YES-*.

---

### Composition check (Phase 6)

Can `master_bridge` be derived from mathlib in ≤3 chained calls?

Attempt 1: `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst` specialised to `L`.
  - Mathlib decls used: `PowerSeries.comp_aeval`, `PowerSeries.aeval`, `PowerSeries.substAlgHom_eq_aeval`.
  - Result: **fails**. These require `[IsLinearTopology L L]` (+ `[DiscreteUniformity ℚ_[p]]`, `[IsTopologicalRing L]` in the adic sense). `L` is a `p`-adic normed field whose norm topology is **not** linear (no ideal-neighbourhood basis; grep finds no such instance). The hypotheses cannot be met, so the specialisation does not typecheck. NOT applicable.

Attempt 2: assemble from analytic primitives — `tsum_eval_pow` (value identity for `G(y)ⁿ`), `tsum_coeff_pow_eq_coeff_subst` (formal-coefficient identity), `Summable.tsum_comm`, `Summable.tsum_const_smul`, `Summable.tsum_smul_const`.
  - Mathlib decls used: `Summable.tsum_comm`, `Summable.tsum_const_smul`, `Summable.tsum_smul_const` — **plus two project-internal sibling lemmas** (`tsum_eval_pow`, `tsum_coeff_pow_eq_coeff_subst`), which themselves are non-trivial (`tsum_eval_pow` is an induction via the nonarchimedean Cauchy product `Summable.mul_of_nonarchimedean`).
  - Result: **fails as a ≤3-call mathlib composition**. The actual proof is ~14 lines with two `have`-blocks each rewriting through a bespoke sibling lemma, then a Fubini swap — a genuine multi-step proof, not a `.trans`/single-call composition. The sibling lemmas are not in mathlib (they are the project's own E-cluster). Per the Phase-6 heuristics table, "multiple `have`s with non-trivial reasoning between" = NO, this is a proof.

Conclusion: **NOT-COMPOSABLE**. There is no ≤3-call mathlib derivation; the linear-topology `comp_aeval` route is inapplicable to a normed field, and the analytic route is a real multi-lemma proof resting on project-only siblings.

---

## Verdict: `PadicLFunctions.master_bridge`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the composition/chain law `F(G(y)) = (F∘G)(y)` for convergent power series is classical and standard (Bourbaki Algebra IV §4 "substitutability"; BGR *Non-Archimedean Analysis* §2 double-series; Conrad p-adic notes; nLab formal case). The most general/modern idiom = evaluation & substitution as continuous algebra homomorphisms with one admissibility predicate. ≥5 channels hit (ChatGPT MCP n/a — server not configured — compensated with extra WebSearch + nLab + MathOverflow).
- Generality analysis (Phase 4): **STRICTLY NARROWER** — 4 weakenings (coefficient ring `ℚ_p`→`R` [CHEAP], value type field→normed comm. ring [CHEAP], the `hprod` double-summability hypothesis → derivable from an admissibility predicate, `hGsum`+`HasSubst` likewise). Phase 4c: a real modern idiom exists — the normed-field analogue of mathlib's `comp_aeval`/`eval₂_subst`.
- Mathlib search (Phase 5): **not in mathlib**. Mathlib has the chain law only for the **linear/adic topology** (`PowerSeries.comp_aeval`, `MvPowerSeries.eval₂_subst`, `substAlgHom_eq_aeval`), which **does not apply to normed fields** (no `IsLinearTopology` instance — verified). It has the analytic single-series primitives but not the analytic chain law.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the linear-topology route is inapplicable; the analytic route is a genuine ~14-line proof through two project-only sibling lemmas.

**Rationale:**

`master_bridge` formalises a genuinely classical theorem — the chain law for convergent power-series evaluation, "evaluating `F` at `G(y)` equals evaluating the formal composite `F∘G` at `y`" — in a setting mathlib does not currently cover. The specific, nameable gap (not "I searched and found nothing"): mathlib's power-series **evaluation-vs-substitution compatibility** lemmas (`PowerSeries.comp_aeval` at `Evaluation.lean:241`; `MvPowerSeries.eval₂_subst`/`comp_subst`/`substAlgHom_comp_substAlgHom` at `Substitution.lean:378–444`; `substAlgHom_eq_aeval` at `Substitution.lean:180`) are **all gated on `[IsLinearTopology S S]` + `[DiscreteUniformity R]`** — the adic/formal topology — and a `p`-adic normed field is provably not linearly topologized (a field has no nontrivial ideals, so no ideal-neighbourhood basis; grep over `Analysis/Normed`, `NumberTheory/Padics`, `Topology/Algebra/Valued` returns zero normed-field `IsLinearTopology` instances). So mathlib's morphism-based substitution/evaluation API simply **stops at the boundary of analytic nonarchimedean evaluation** — the project re-proves the chain law from `Summable.tsum_comm` precisely because the mathlib lemma is unreachable. This composes immediately with the analytic evaluation primitives mathlib *does* have (`HasSum`, `Summable.tsum_comm`, `Summable.mul_of_nonarchimedean`, `tsum_mul_tsum_eq_tsum_sum_antidiagonal`) and would unlock every downstream "evaluate a composed series" step in p-adic analysis (formal groups, Lubin–Tate, Coleman maps, Iwasawa power-series evaluation) — exactly as it already unlocks the project's `exp∘log = id` / `log∘exp = id` inversions (its two call sites).

It is **not** `YES-add-as-is` because Phase 4b found it strictly narrower than the standard form and Phase 4c found a real modern idiom: the right mathlib contribution is not this `ℚ_p`-specific `tsum` equation carrying a redundant `hprod` hypothesis, but the **normed-field counterpart of `comp_aeval`** — an `aeval`-style continuous algebra homomorphism on admissible points of a complete ultrametric normed algebra, with the bridge stated as its composition law. That form (i) weakens `ℚ_p`→arbitrary coefficient ring and field→normed commutative ring at zero proof cost, (ii) replaces the three convergence/admissibility hypotheses (`hGsum`, `hprod`, and the formal `HasSubst`) with a single admissibility predicate from which `hprod` is *derived* (the project's own `summable_prod_family` is literally that derivation, invoked at both call sites — concrete proof the hypothesis is redundant in the general form), and (iii) unifies the analytic chain law with mathlib's existing morphism-based substitution framework. The cost note: the value-type/coefficient weakenings are CHEAP; building the `HasEval`-analogue + `aeval`-homomorphism is MODERATE — and per the skill, cost is not a downgrade factor; getting the right (morphism) form is the work mathlib exists to do.

**Refactor-actionable / upstreaming plan:**

  Reason for the generalisation: BOTH
    - LITERATURE-WEAKENING: Phase 4b — `ℚ_[p]`→arbitrary `[CommRing R]`/normed `R`; `NormedField L`→`NormedCommRing L` (Tate-algebra generality). The current proof survives verbatim (no `ℚ_p`- or field-specific lemma is used).
    - MODERN-IDIOM (Bourbaki 2.0): Phase 4c — package evaluation as a continuous algebra homomorphism on admissible points (the normed-field analogue of `PowerSeries.aeval`/`HasEval`), and state the bridge as its composition law, mirroring `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst`.
  Proposed restatement (the literature-weakened, hypothesis-as-given intermediate; the morphism version is the end target):
  ```lean
  theorem eval_subst_eq {R : Type*} [CommRing R] {L : Type*} [NormedCommRing L]
      [Algebra R L] [IsUltrametricDist L] [CompleteSpace L]
      (F G : PowerSeries R) (y : L) (hG : HasSubst G)
      (hGsum : Summable fun m => (algebraMap R L) (coeff m G) • y ^ m)
      (hprod : Summable fun nk : ℕ × ℕ =>
        ((algebraMap R L) (coeff nk.1 F) * (algebraMap R L) (coeff nk.2 (G ^ nk.1))) • y ^ nk.2) :
      (∑' n, (algebraMap R L) (coeff n F) • (∑' m, (algebraMap R L) (coeff m G) • y ^ m) ^ n)
        = ∑' k, (algebraMap R L) (coeff k (F.subst G)) • y ^ k := by
    sorry -- current proof should transfer; the genuine target replaces hprod by an admissibility predicate
  ```
  Estimated cost of regeneralisation: CHEAP (coefficient/field weakening) → MODERATE (full morphism + `HasEval`-analogue version). EXPENSIVE-ness, if any, does not downgrade the verdict.
  Mathlib downstream this enables (MODERN-IDIOM):
    - the normed-field counterpart of `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst`, currently absent (mathlib's chain law is adic-only) — closes a real gap in the analytic-evaluation API.
    - one-call "evaluate a composed/substituted series" for all nonarchimedean p-adic analysis: formal groups, Lubin–Tate, Coleman maps, Iwasawa power-series evaluation — and immediately the project's own `padicExp_padicLog` / `padicLog_padicExp` (which presently hand-build `hprod` via `summable_prod_family`).
    - proofs blocked by the old form: any client that wanted `eval (F.subst G) = eval F` over a normed field had to re-run a `tsum_comm` argument; the morphism form makes it `comp_aeval`-style.
  Next action: run `/generalise PadicLFunctions.master_bridge` — it will tension against both the literature-standard form (Phase 3: coefficient/field weakening) and the modern-idiom form (Phase 4c: the `aeval`/`HasEval`-analogue composition law). Land the cheap coefficient/field weakening immediately; scope the `HasEval`-analogue + admissibility-predicate version as the mathlib PR (likely shipped alongside an ultrametric-normed `PowerSeries.aeval` so the bridge can be stated as `comp_aeval`). Note the related project decls in the same E-cluster (`tsum_eval_pow`, `tsum_coeff_pow_eq_coeff_subst`, `summable_eval_pow`, `summable_coeff_pow_scalar`) are the supporting lemmas; the PR should group the bridge with whichever of them the general statement still needs.

---

## Next step

Run `/generalise PadicLFunctions.master_bridge`: first land the CHEAP coefficient-ring/value-type weakening (`ℚ_[p]`→`R`, `NormedField`→`NormedCommRing`), then develop the MODERATE modern-idiom version — an ultrametric-normed `PowerSeries.aeval`/`HasEval` analogue on admissible evaluation points, with `master_bridge` restated as its composition law (the normed-field counterpart of mathlib's adic-only `PowerSeries.comp_aeval` / `MvPowerSeries.eval₂_subst`), replacing the redundant `hprod` hypothesis by the admissibility predicate. Then `/cleanup` and open the mathlib PR (target area `Mathlib/RingTheory/PowerSeries/Evaluation.lean` or a new analytic-evaluation file under `Mathlib/Analysis/`).
