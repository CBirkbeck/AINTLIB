# `/mathlibable` report — `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`

**Final verdict: `BORDERLINE-needs-human`.** This is the "R7.6a c₀-pin", a
~125-line *construction-internal* identity in RJW §7's residue computation,
stated **entirely** in project-local objects that mathlib does not have
(`mahlerK`, `rhoA`, `seriesEval`, `FtildeA`, `phiSeries`, `extLog`, the whole
`PadicMeasure`/`MeasureR` p-adic-measure substrate). It is therefore neither
"in mathlib" (Phase 5: nothing), nor a ≤3-call mathlib composition (Phase 6:
the proof is long and its building blocks are themselves project decls), nor
upstreamable as-stated (it cannot even be phrased in mathlib's vocabulary).
The verdict turns on a judgment the skill cannot make alone: whether the
*general* trace identity it specialises (`sum_seriesEval_mahlerK`) and the
underlying RJW §3–§7 measure / Amice–Mahler / `seriesEval` layer are an
upstreaming target — in which world this specific specialisation would still
be single-use internal bookkeeping. Numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source** (Phase-0 fallback)
- decl `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:913`
- kind:                     `theorem`
- has sorry:                no (`ResidueZeta.lean` contains 0 `sorry`/`admit`; the proof is complete, lines 913–1037)
- module docstring summary: "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — continuity/simple-pole of `ζ_{p,i}` at `s=1`, residue `1 − p⁻¹`, via the §6 c₀-design applied to the explicit antiderivative `F̃_a`, run in a field `K ⊇ ℚ_p(μ_p)` (ℂ_p) and descended by injectivity.

---

### Statement (Phase 1)

`PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA` is **a theorem** stating the
following "constant-coefficient pin" (RJW's `c₀`-design, the project's T615
pattern).

Let `p` be prime and `K` a complete characteristic-zero ultrametric normed
`ℚ_p`-algebra containing a primitive `p`-th root of unity `ξ` (in the intended
application `K = ℂ_p`). For a natural number `a` with `p ∤ a` and `a ≠ 0`,

  p · 𝓐(ρ_a)(0)  =  p · F̃_a(0)  −  Σ_{i ∈ Fin p}  F̃_a(ξ^i − 1).

Here:
- `𝓐(ρ_a) = mahlerK p K (rhoA p K a)` is the Mahler/Amice transform power
  series (in `K⟦T⟧`) of the base-changed numerator measure `ρ_a` (RJW §4's
  `x⁻¹·Res_{ℤ_p^×}(μ_a)`, pushed to `ℤ_p` and base-changed to `K`);
- `F̃_a = FtildeA p K a` is RJW's explicit antiderivative
  `log(T/(1+T) · (1+T)^a/((1+T)^a−1))` (TeX 2268);
- `(·)(0) = PowerSeries.constantCoeff (·)` is the constant coefficient;
- `F̃_a(ξ^i − 1) = seriesEval (FtildeA p K a) (ξ^i − 1)` is the *analytic*
  evaluation `Σ_n coeff_n(F̃_a)·(ξ^i−1)ⁿ` (a `tsum`, convergent because
  `‖ξ^i−1‖ < 1`).

Mathematically this is the residue/trace extraction step: summing the
antiderivative over the `p`-torsion shifts `ξ^i − 1` of the argument isolates
`p` times the relevant constant term (the `φψ`-difference `W = F̃_a − 𝓐(ρ_a)`
is killed by the operator `(1+T)d/dT` up to a constant `c₀`, and the
`p`-fold sum of `seriesEval` at the roots evaluates `φ`-parts to `0` and the
constant `c₀` to `p·c₀`). It feeds the mass formula `∫x⁻¹μ_a = −(1−p⁻¹)log_p(a)`
(`constantCoeff_mahlerK_rhoA`, RJW Lemma 7.5, TeX 2320).

Variables / typeclasses involved (Lean side; `section mass`, `ResidueZeta.lean:430–433`):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime / residue characteristic.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]` — the coefficient field (the ℂ_p stand-in).
  All five are genuinely used: `seriesEval`'s `tsum` needs the norm +
  completeness; `mahlerK`/`MeasureR K ℤ_[p]`/`baseChange` need the
  complete-ultrametric-Banach structure (the Mahler `RingEquiv` only exists
  over such `K`); `CharZero` for the rational scalars in `formalLog`/`F̃_a`.
- `a : ℕ` — the index of the measure family `μ_a` (RJW §4).
- `{ξ : K}` — a primitive `p`-th root of unity (the trace/torsion variable).

Hypotheses (Lean side):
- `ha : ¬ (p : ℕ) ∣ a` — `p ∤ a` (so `μ_a`/`ρ_a` are the right interpolating
  objects; ensures `(a:K)` is a unit and the `F̃_a` substitutions are legal).
- `ha0 : a ≠ 0` — `uA 0 = 0` makes the formal composition in `F̃_a` junk
  (`HasSubst` fails); needed throughout the `F̃_a` API.
- `hξ : IsPrimitiveRoot ξ p` — `ξ` is a primitive `p`-th root of unity.

Conclusion (math): the `p`-scaled constant coefficient of `𝓐(ρ_a)` equals the
`p`-scaled constant coefficient of `F̃_a` minus the trace-sum of `F̃_a` over the
`p`-torsion shifts — RJW's `c₀`-pin (no Gauss clearing on this route).

Conclusion (Lean):
`(p : K) * PowerSeries.constantCoeff (mahlerK p K (rhoA p K a))
  = (p : K) * PowerSeries.constantCoeff (FtildeA p K a)
    - ∑ i : Fin p, seriesEval (FtildeA p K a) (ξ ^ (i : ℕ) - 1)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (a sub-result, not a headline).
Reason: it is the "R7.6a" *step* of the project's decomposition — a
bookkeeping identity feeding the §7 mass/residue computation — not a new
mathematical structure, not the file's `## Main results` headline (that is the
residue/continuity of `zetaPBranch`, RJW Thm 7.1), and not named after a
person/place. The docstring tag "R7.6a (the c₀-pin, T615-pattern)" marks it as
an internal step. It is, however, a *substantive* lemma (a ~125-line proof),
not a one-liner — which matters for Phase 6 (it is **not** a 3-call
composition).

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~125 substantive lines (lines 913–1037: a long sequence of
`have`s assembling the operator-kernel argument).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** The
one-liner/exemption machinery applies to `def`/`abbrev`/`structure`. Skipped.
(Note for Phase 6/7: this is emphatically a multi-step proof, so the
"inline-the-one-liner" reasoning that drove the sibling `rhoA` does **not**
apply — the composition route is closed here for a different reason: the
building blocks are project decls and the assembly is real reasoning.)

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `Kubota-Leopoldt p-adic L-function residue s=1 Iwasawa logarithm antiderivative constant coefficient measure Mahler transform` | yes | The Kubota–Leopoldt p-adic ζ has a **simple pole at s=1 with residue 1 − p⁻¹**; the value/residue is extracted from the interpolating *measure* via its Mahler/Amice transform power series. | Top hits: **arXiv:2309.15692 (RJW)**; C. Williams' Warwick notes; Iwasawa, *Lectures on p-adic L-functions* (AM-74). The residue `1−p⁻¹` is classical; the *route* (explicit antiderivative `F̃_a`, `c₀`-pin) is RJW's, not a separately-named theorem. |
| 2 | WebSearch (general form / trace) | `p-adic measure sum of power series evaluated at primitive p-th roots of unity constant coefficient phi psi operator Coleman` | yes | Evaluating a `(‖coeff‖≤1)` power series at the `p`-torsion points `ζ−1` and summing is the **trace/`φ`-`ψ`** operation underlying the **Coleman/Amice** theory; `Σ_{ζ^p=1} f(ζ−1)` recovers `p`×(the `ψ=φ`-part). | de Shalit, *Mahler bases & elementary p-adic analysis* (JTNB); Coleman memorial notes; UT-Austin thesis "Power series in p-adic roots of unity". The sum-over-roots = `p`·(trace) identity is folklore in Coleman/Iwasawa theory, **never isolated as a named lemma** in this `F̃_a − 𝓐(ρ_a)` form. |
| 3 | WebSearch (named-after / aliases — Amice/Mahler) | `Amice transform p-adic measure power series evaluation sum over roots of unity trace phi operator residue Iwasawa main conjecture descent` | yes | **Amice transform** `µ ↦ A_µ(T)` is the isomorphism `D⁰(ℤ_p,ℤ_p) ≅ ℤ_p⟦T⟧` (the project's `mahlerK`); evaluations at roots of unity relate to special values (Amice–Vélu–Višik). | Confirms `mahlerK` = **Amice/Mahler transform** (classical, standard framework); the `seriesEval`-at-roots is the standard evaluation. But the *specific identity* (this `c₀`-pin) is construction-internal. de Shalit (JTNB jtnb.955), Williams notes, Sharifi's *Iwasawa Theory*. |
| 4 | ChatGPT MCP | (intended) "standard form + generality + historical evolution of: the sum-over-p-torsion-shifts trace identity that pins the constant coefficient of a p-adic measure's Amice transform" | n/a | — | **n/a — no ChatGPT/OpenAI MCP server is available/authenticated in this environment** (consistent with the sibling reports `rhoA.md`, `constantCoeff_FtildeA.md`, which record the same). Compensated by extra WebSearch (#1–#3) at three generality levels + direct read of the project's RJW citations (the authoritative channel) + mathlib-source grep (#5/Phase 5). |
| 5 | Local references | `ls/grep projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/` | n/a | (directory absent) | `projects/PadicLFunctions/.mathlib-quality/references/` does **not** exist; there is no `refs/` symlink in this checkout (PDFs are local-only, never committed). Same as the sibling reports. The in-file RJW citations (TeX 2181–2360; "RJW Thm 7.1", "Lemma 7.5 TeX 2320", "T615-pattern") give the source form directly. |
| 6 | nLab | `Iwasawa algebra`, `p-adic L-function`, `Amice transform` | partial | nLab/Wikipedia: `Λ(ℤ_p) ≅ ℤ_p⟦T⟧` = measures = dual of `C(ℤ_p,ℤ_p)`; p-adic L-functions as measures; residue at `s=1`. | Confirms the **ambient framework** (Iwasawa algebra = measures = power series via Amice/Mahler) is classical and standard. No nLab entry for this specific `c₀`-pin identity. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept: a concrete `tsum`/constant-coefficient identity in a concrete coefficient field. No 1-/∞-categorical content. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry concept (no schemes/sites/cohomology); Stacks has no p-adic measure / Amice transform / residue material. |
| 9 | MathOverflow / Math.SE | (folded into #1–#3, #6: Iwasawa-algebra / Coleman-map / Amice-transform threads) | partial | Same as #2/#3: `Σ_{ζ^p=1} f(ζ−1)` trace and `D⁰(ℤ_p) ≅ ℤ_p⟦T⟧` are routine in Iwasawa-theory discussion. | No dedicated thread on this exact `F̃_a − 𝓐(ρ_a)` pin; construction-internal. |
| 10 | recent arXiv (last 5 years) | arXiv:2309.15692 (RJW); arXiv:1701.05729 (cyclotomic multi-zeta, root-of-unity evaluations) | yes | **RJW = Rodrigues Jacinto–Williams, "An introduction to p-adic L-functions"** (arXiv:2309.15692; Essential Number Theory 4(1), 2025). §7 (Thm 7.1) computes the residue of ζ_p at `s=1` as `1−p⁻¹` via the measure `μ_a` and the explicit antiderivative `F̃_a`. | The source. `F̃_a`, the `c₀`-design, and the trace-over-roots step are **internal computational steps** in RJW's §6–§7, not standalone named theorems. The base-change to `K ⊇ ℚ_p(μ_p)` + descent is the project's own §5/§7 device (RJW works directly). |

**Protocol pass check.** WebSearch ran 3 distinct queries at three generality
levels (specific residue/Mahler form #1; general trace/Coleman form #2;
named-after Amice/Mahler aliases #3). ChatGPT MCP genuinely unavailable
(recorded `n/a` + compensating channels). Local references checked (`n/a`,
absent). nLab checked (partial hit — confirms the framework). nCatLab / Stacks
/ MO–MSE / arXiv each checked or `n/a` with a one-line reason. ✓

### Literature summary (Phase 3)

Concept identified as: an **internal computational step** ("the `c₀`-pin",
RJW's `F̃_a(0)`/residue extraction, TeX §6–§7) in **RJW (Rodrigues
Jacinto–Williams, arXiv:2309.15692)**'s measure-theoretic construction of the
Kubota–Leopoldt p-adic ζ and its residue `1−p⁻¹` at `s=1`. It rests on three
standard, classical *frameworks* — (a) the **Amice/Mahler transform**
`D⁰(ℤ_p) ≅ ℤ_p⟦T⟧` (the project's `mahlerK`), (b) **analytic evaluation** of a
unit-norm power series at `‖z‖<1` (the project's `seriesEval`), and (c) the
**trace/Coleman** identity that summing over the `p`-torsion shifts `ξ^i−1`
isolates `p`×(constant/`ψ`-part). All three are textbook in Coleman/Iwasawa
theory; the *specific identity* assembling them on `F̃_a − 𝓐(ρ_a)` is
RJW-internal bookkeeping.

Sources agree on the standard form: **yes** for the three frameworks (Amice
transform, evaluation, sum-over-roots trace). **No independent literature
life** for this specific `p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ F̃_a(ξ^i−1)` pin — it is a
step inside one proof.

Most general standard form: there is no "more general standard `c₀`-pin" to aim
at. The generality lives in the *primitives* (the Amice transform of any
measure; evaluation of any unit-norm series; the trace over any cyclotomic
extension). The project already factors that generality out: the trace half is
the **general** lemma `sum_seriesEval_mahlerK` (over an *arbitrary*
`μ : MeasureR K ℤ_[p]`, `FormalPsi.lean:1072`); the target is its
**specialisation** to the difference `mahlerK(rhoA) − FtildeA` plus the
operator-kernel argument.

Generality dimensions where the literature varies:
  - measure `µ`: general `MeasureR K ℤ_[p]` (as in `sum_seriesEval_mahlerK`) vs.
    the specific `ρ_a`/`F̃_a` pair here — the target is at the *specific* end.
  - coefficient ring: any p-adic coefficient ring containing `µ_p`; here a
    complete ultrametric `ℚ_p`-Banach field of char 0 (ℂ_p). Standard.
  - These are dimensions of the *primitives*, not of this composite identity.

Disagreement with the literature: **none** — the literature simply does not
isolate this pin as an object; it is a step (treating "the source doesn't name
it" as a signal: construction-internal, not a standalone standard result; cf.
the verdicts-reference anti-pattern "treating literature absence as YES").

---

## PHASE 4 — Generality analysis

### Generality analysis — `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`

Literature-standard form (Phase 3): there is **no separately-named standard
form** of this `c₀`-pin. The relevant generality lives in (i) the three
primitive frameworks (Amice transform / evaluation / sum-over-roots trace) and
(ii) the project's own *general* trace lemma `sum_seriesEval_mahlerK`. So the
"compare to the literature-standard form" exercise reduces to: *is each input
applied at the right generality, and is the composite the right thing to
state?* — and the honest answer is that the composite is a deliberate
**specialisation** of an already-general project lemma, tied to project objects.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` + 4 analytic instances | char-zero complete ultrametric normed `ℚ_p`-algebra (ℂ_p stand-in) | the coefficient field of an Amice-transform / `seriesEval` computation over `ℚ_p(µ_p)` | **NO** | All genuinely used: `seriesEval`'s `tsum` needs norm+completeness; `mahlerK`/`MeasureR`/`baseChange` need the complete-ultrametric-Banach structure (the Mahler `RingEquiv`); `CharZero` for `formalLog`/`F̃_a`'s rational scalars. None is dead weight (unlike `uA`/`constantCoeff_FtildeA`, none is `omit`-ted). |
| 2 | `(ha : ¬ p ∣ a)` | `p ∤ a` | the interpolation hypothesis on `µ_a` (RJW §4) | **NO** | needed so `(a:K)` is a unit and the `F̃_a` substitutions / `extLog` witnesses are legal; matches RJW. |
| 3 | `(ha0 : a ≠ 0)` | `a ≠ 0` | n/a | **NO** | `uA 0 = 0` makes `F̃_a` junk (`HasSubst` fails). Forced. |
| 4 | `(hξ : IsPrimitiveRoot ξ p)` | primitive `p`-th root | the trace/torsion variable (Coleman/Amice) | **NO** | the whole sum-over-`p`-torsion-shifts mechanism requires a primitive `p`-th root; this is the natural hypothesis, matching `sum_seriesEval_mahlerK`. |
| 5 | the objects `mahlerK`, `rhoA`, `FtildeA`, `seriesEval` | project-specific Amice transform / numerator measure / antiderivative / evaluation | no literature-standard form (RJW-internal) | **NO** | project objects; mathlib has no counterpart toward which to generalise (Phase 5). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within an intrinsically project-local
scope.** Every hypothesis is tight and genuinely used (none `omit`-ted, unlike
the coefficient-formula siblings), `a ≠ 0`/`p ∤ a`/primitive-root are all
forced, and the *statement itself* is bound to project objects
(`mahlerK`/`rhoA`/`FtildeA`/`seriesEval`), so there is **no "more general
literature form of this theorem"** to aim at.

Number of weakening opportunities found: **0** for the theorem as stated.

Important nuance feeding Phase 7: the *one* real generalisation in the
neighbourhood is **not** a weakening of *this* theorem but the recognition that
its trace half is already the **general** project lemma
`sum_seriesEval_mahlerK` (arbitrary `µ`). This theorem is the deliberate
*specialisation* (to `ρ_a`/`F̃_a`) plus the operator-kernel `c₀` argument. That
is an argument for the specialisation being **single-purpose** (→ BORDERLINE /
NO), not for restating it more generally.

Proposed restatement (if STRICTLY NARROWER): n/a — not strictly narrower than a
*literature* standard (there is none); the more-general sibling is a different
(already-existing) project lemma, not a restatement of this one.

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | already fully typeclass-based (`[NormedField K]`, `[NormedAlgebra ℚ_[p] K]`, …) | — |
|  2 | sequences/metric → filters/topology? | no | the only limit is the `tsum` inside `seriesEval`, which is already the idiomatic `Summable`/`tsum` framework (mathlib's) | — |
|  3 | construct an object → universal-property class? | no | this is a value identity, not a construction | — |
|  4 | set+closure-predicate → bundled substructure? | no | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses? | no | the field/Banach/char-0 hypotheses are all genuinely required (Phase 4b row 1); nothing to weaken | — |
|  6 | 1-categorical → higher-categorical? | no | no categorical content | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | partial | the sum is over `Fin p` (the `p`-torsion) — already the natural index for a primitive-`p`-th-root trace; the `a : ℕ` is the natural `µ_a`-family index | — (no genuine generalisation axis) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The statement is already a contemporary,
typeclass-based, `tsum`/`Summable`-idiomatic identity at the right generality.
The only "modernisation" that would matter — formalising the whole RJW §3–§7
**Amice/Mahler-transform + p-adic-measure + `seriesEval`** layer idiomatically
— is *upstream* of this theorem (it is exactly the work the project is doing),
not a reformulation of this one identity. There is no
filter-ise/categorify/weaken-typeclass move that improves *this* statement.
One-line reason: this is a construction-internal value identity in
already-idiomatic project primitives; nothing about the identity itself is to
be modernised.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities and no typeclass-search paths; the six-row risk table is skipped.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`

[A] **Lean-Finder**  — natural-language + type queries — **n/a: no Lean-Finder MCP tool surfaced** in this environment. Compensated by [D] direct grep over the pinned mathlib clone (`./.lake/packages/mathlib/Mathlib`, confirmed present), which is authoritative.
[B] **Loogle**       — type-pattern `(p : K) * constantCoeff _ = (p : K) * constantCoeff _ - ∑ _, seriesEval _ _` / `∑ _ : Fin p, (tsum _) = (p:K) * constantCoeff _` — **n/a as MCP** (no `lean_loogle`); emulated via [D]. **No hit**: mathlib has no `seriesEval` (analytic `tsum coeff·zⁿ`) and no Amice-transform constant-coefficient identity.
[C] **LeanSearch**   — "sum of a p-adic power series over primitive p-th-root shifts equals p times constant coefficient minus …" — **n/a as MCP** (no `lean_leansearch`); covered by the WebSearch literature channels (#1–#3) + [D].
[D] **Grep mathlib src** — over `./.lake/packages/mathlib/Mathlib/`:
  - `mahlerK`, `mahlerTransform`, `MeasureR`, `seriesEval`, `phiSeries`, `extLog`, `FtildeA`, `rhoA`, `zetaNum` → **0 hits** (all project-only objects).
  - `baseChange` → hits exist but are **all unrelated** (`WeierstrassCurve.baseChange`, `VariableChange.baseChange`, scheme-morphism `baseChange`); none is a measure base-change.
  - p-adic **measure** / **Amice/Mahler transform** / Iwasawa-algebra-as-measures / `D⁰(ℤ_p) ≅ ℤ_p⟦T⟧` → **0 hits**. Mathlib's only p-adic-functional-analysis content is one layer down: `Mathlib/NumberTheory/Padics/MahlerBasis.lean` (Mahler's theorem / orthonormal basis of `C(ℤ_p, E)`) and the binomial-ring structure on `ℤ_[p]` — **not** a measure (dual) theory, and no Amice transform.
  - `PowerSeries` evaluation: mathlib has **formal** substitution/evaluation (`PowerSeries.eval₂`, `HasEval`, `subst`, `Mathlib/RingTheory/PowerSeries/{Evaluation,Substitution}.lean`) — but **not** the analytic `seriesEval` (`∑' n, coeff_n F · zⁿ` as a `tsum` in a normed field), which is the project's own `FormalPsi.lean:577` definition.
  - roots-of-unity: mathlib has `IsPrimitiveRoot` + `RootsOfUnity/*` (incl. `geom_sum`, cyclotomic units) but **no** "sum over primitive-root shifts extracts the constant/`ψ`-part of a measure's transform" lemma — that lemma is the project's `sum_seriesEval_mahlerK`/`seriesEval_phi_at_root` (`FormalPsi.lean:882,1072`).
[E] **Name pattern** — grep mathlib for any `*_mul_constantCoeff_*`, `*constantCoeff*rho*`, `sum_seriesEval*`, `*mahlerK*` — **0 hits**. Nothing named like a p-adic-measure constant-coefficient trace pin.

Searched for both:
  - the **user's current form** (`p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ F̃_a(ξ^i−1)`, with
    `𝓐 = mahlerK`, `seriesEval`, `FtildeA`, `rhoA`): **not in mathlib** — every
    object in the statement is project-only.
  - the **literature/framework form** (Amice transform of a measure; analytic
    evaluation at `‖z‖<1`; sum-over-`p`-torsion-shifts trace = `p`·(`ψ`-part)):
    the **frameworks themselves are absent from mathlib** — mathlib has Mahler's
    theorem on `C(ℤ_p)` and `IsPrimitiveRoot`, but no p-adic-measure / Amice-
    transform theory, no analytic `seriesEval`, and hence no such trace identity.

Concluded: **not in mathlib (all methods exhausted, both the composite form and
every framework component).** Moreover the building blocks of the *proof* are
themselves **project decls** (`sum_seriesEval_mahlerK`, `seriesEval_phi_at_root`,
`one_add_mul_derivative_FtildeA`, `one_add_mul_derivative_mahlerK_rhoA`,
`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`, `psi_rhoA`,
`mahlerK_*`/`phiSeries_*` API), not mathlib decls — so there is no mathlib
composition to inline (this is what closes the `NO-composable` route; see
Phase 6).

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`

Internal use count (within the project, **excluding** the declaring line): **K = 1.**
External-to-file callers: **0 distinct files.**

A repo-wide word-boundary grep `\bp_mul_constantCoeff_mahlerK_rhoA\b` over
`projects/**/*.lean` returns exactly two lines: the declaration
(`ResidueZeta.lean:913`) and one use (`ResidueZeta.lean:1594`). No other file —
in PadicLFunctions or any sibling project — references it.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ResidueZeta.lean:1594` | `have hp_mul := p_mul_constantCoeff_mahlerK_rhoA (p := p) K ha ha0 hξ` (inside `constantCoeff_mahlerK_rhoA`, RJW Lemma 7.5: the mass `−(1−p⁻¹)·log_p(a)`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this
lemma?): **(none).** The `p·constantCoeff(𝓐ρ)` pin is computed in exactly one
place — this theorem — and consumed in exactly one place — its immediate
caller, which divides by `p` to get the mass formula.

What the call-sites pattern tells you: **K = 1 internal use, 0 external, no
inline re-derivation.** Per the Phase-6 / verdicts-reference table this is the
"single-consumer corollary — possibly the wrong *standalone* abstraction; leans
toward a NO/BORDERLINE bucket" signal. It is a "feeds-exactly-one-lemma" step in
the §7 residue chain, not reusable cross-project API. (It is *not* dead code:
the one consumer is live and important; but it is not API anyone else uses.)

### Composition check (Phase 6)

Can `p_mul_constantCoeff_mahlerK_rhoA` be derived from **mathlib** in ≤3 chained
calls? **No.**

**Attempt 1 — direct mathlib composition.** There is none: every object in the
statement (`mahlerK`, `rhoA`, `seriesEval`, `FtildeA`) is project-only and absent
from mathlib (Phase 5). Mathlib cannot even express the statement, let alone
discharge it in ≤3 calls. **Fails** (no mathlib vocabulary).

**Attempt 2 — composition from the *project's* building blocks.** The actual
proof (lines 913–1037, ~125 lines) is a genuine multi-step argument:
  1. obtain a bounded antiderivative `C₁` of the `ψ`-part (`MeasureR.exists_antideriv_bounded`);
  2. three operator identities `(1+X)·∂(·)` for `F̃_a`, `𝓐(ρ_a)`, and `φ C₁`
     (`one_add_mul_derivative_FtildeA`, `one_add_mul_derivative_mahlerK_rhoA`
     + `MeasureR.res_units_eq`, `one_add_mul_derivative_phiSeries`);
  3. deduce `(1+X)·∂(W − φC₁) = 0` for `W = F̃_a − 𝓐(ρ_a)`, hence
     `W − φC₁ = C c₀` (`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`);
  4. evaluate `W = φC₁ + C c₀` at each torsion shift `ξ^j−1`, using
     `seriesEval_phi_at_root_of_summable` (φ-part → 0) and `seriesEval_C`
     (constant → c₀), summing to `p·c₀`;
  5. the `𝓐(ρ_a)`-trace vanishes via `sum_seriesEval_mahlerK` + `psi_rhoA`
     (ρ_a supported on units ⇒ `ψ ρ_a = 0`);
  6. expand `c₀ = F̃_a(0) − 𝓐(ρ_a)(0)` at `0` and `linear_combination`.

This is **a proof**, not a composition: multiple `have`-steps with non-trivial
operator-theoretic reasoning, `rw`/`ring`/`linear_combination` glue, and — most
decisively — **every** non-trivial input is a *project* lemma, not a mathlib
lemma. Per the Phase-6 heuristics table this is firmly in the "multiple `have`s
with reasoning between ⇒ NO, this is a proof" / "anything requiring
`rw`/`ring`/`linear_combination` glue ⇒ NO, real proof" rows.

**Conclusion: NOT-COMPOSABLE** (neither from mathlib — no vocabulary, no
building blocks — nor as a ≤3-call assembly of *project* primitives; it is a
substantive ~125-line proof).

This closes **both** NO buckets: `NO-mathlib-has-it` (Phase 5: nothing) and
`NO-composable-from-mathlib` (Phase 6: NOT-COMPOSABLE, and the gate's required
≤3-line mathlib sketch cannot be honestly produced — the substrate is
project-only). It also rules out the YES buckets (the statement is unphrasable
in mathlib). What remains is a synthesis judgment → Phase 7.

---

## Verdict: `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified as an **internal computational step**
  (the "c₀-pin", RJW arXiv:2309.15692 §6–§7) in the measure-theoretic
  construction of the Kubota–Leopoldt p-adic ζ and its residue `1−p⁻¹` at
  `s=1`. Rests on three classical *frameworks* (Amice/Mahler transform;
  analytic evaluation; sum-over-`p`-torsion trace) but is **not a
  separately-named standard result**; the project already factors the trace
  generality into `sum_seriesEval_mahlerK`, and this theorem is its
  specialisation to `ρ_a`/`F̃_a`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL within an intrinsically
  project-local scope** (0 weakenings; all hypotheses forced/used; none
  `omit`-ted); modern-idiom **none** (already idiomatic; the only modernisation
  is upstreaming the whole RJW measure/Amice layer, which is *upstream* of this
  theorem).
- Mathlib search (Phase 5): **not in mathlib** under both the composite form and
  every framework component; mathlib's p-adic content stops at Mahler's theorem
  on `C(ℤ_p)` + `IsPrimitiveRoot`, with **no** p-adic-measure / Amice-transform
  theory, **no** analytic `seriesEval`, and hence no such trace identity.
- Composition check (Phase 6): **NOT-COMPOSABLE** — no mathlib vocabulary or
  building blocks (so no `NO-composable` ≤3-line sketch is honestly possible);
  the actual proof is a substantive ~125-line operator-kernel argument whose
  every non-trivial input is a *project* lemma. K = 1 internal caller, 0
  external, no inline re-derivation.

**Rationale.**
`p_mul_constantCoeff_mahlerK_rhoA` is the project's "R7.6a c₀-pin": the identity
`p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ_{i<p} F̃_a(ξ^i−1)` that, after dividing by `p`,
yields RJW Lemma 7.5's mass `∫x⁻¹μ_a = −(1−p⁻¹)·log_p(a)`. Its content is
genuinely classical Coleman/Iwasawa mathematics (summing an Amice transform over
`p`-torsion shifts extracts `p`×the constant/`ψ`-part; the operator
`(1+T)d/dT` has a one-dimensional kernel of constants). But **as a Lean object
it is irreducibly project-local**: its *statement* names `mahlerK` (the Amice
transform), `rhoA` (the base-changed numerator measure), `seriesEval` (the
analytic `tsum`), and `FtildeA` (RJW's explicit antiderivative) — and **none of
these exists in mathlib**, which has no p-adic-measure/Amice-transform layer at
all. So mathlib cannot contain this theorem as stated, it is not a ≤3-call
composition (the proof is ~125 lines and every building block is a project
lemma — `sum_seriesEval_mahlerK`, `seriesEval_phi_at_root`,
`one_add_mul_derivative_*`, `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`,
`psi_rhoA`), and there is no mathlib decl to cite for `NO-mathlib-has-it`.

Three of the five buckets are therefore mechanically excluded (YES-*: unphrasable
in mathlib; NO-mathlib-has-it: nothing to cite; NO-composable: no mathlib sketch
honestly producible). The remaining choice — between recording it as
"not-mathlib-bound" (the elastic `NO-composable` reading the sibling `rhoA.md`
used for a *one-line def*) and `BORDERLINE` — turns on a **judgment the skill
cannot make alone**, because this is a *substantive theorem*, not a one-liner:
the honest answer to "should mathlib have this?" depends entirely on whether the
project intends to upstream the **whole** RJW §3–§7 Amice-transform /
p-adic-measure / `seriesEval` layer (the only world in which the theorem becomes
meaningful), and, if so, whether the right upstream object is the **general**
trace lemma `sum_seriesEval_mahlerK` (which this specialises) rather than this
single-use `ρ_a`/`F̃_a` pin. That is a project-policy + mathematical-taste call,
which is exactly what `BORDERLINE-needs-human` is for. (Per the verdicts
reference, "audience-narrow result / project policy / generality-vs-packaging
tradeoff" are textbook BORDERLINE triggers, and "treating literature absence as
YES" / forcing a NO with an un-producible sketch are the anti-patterns to avoid.)

**Numbered questions (≤5):**

  1. **Upstreaming intent.** Do you intend to upstream the RJW §3–§7
     **p-adic-measure + Amice/Mahler-transform + analytic `seriesEval`** layer
     (`PadicMeasure`, `MeasureR`, `mahlerK`/`mahlerTransform`, `seriesEval`,
     `phiSeries`) to mathlib at all? If **no**, this theorem is settled as
     *project-local, not mathlib-bound* (keep it where it is) and no further
     action is needed. If **yes**, proceed to Q2–Q4.
  2. **Right grain for the trace.** Given that the *general* trace identity is
     already the project lemma `sum_seriesEval_mahlerK` (over an arbitrary
     `µ : MeasureR K ℤ_[p]`, `FormalPsi.lean:1072`), is **that** general lemma
     (plus `seriesEval_phi_at_root`) the intended mathlib contribution, with the
     present `ρ_a`/`F̃_a` pin staying project-internal as a specialisation? (Yes
     ⇒ this specific theorem is *not* a mathlib target; the upstream work moves
     to `sum_seriesEval_mahlerK`, assessed separately.)
  3. **`seriesEval` vs mathlib evaluation.** For any upstreaming, should the
     analytic evaluation be the project's bespoke `seriesEval`
     (`∑' n, coeff_n F · zⁿ`), or reformulated against mathlib's existing
     `PowerSeries.eval₂`/`HasEval` evaluation framework
     (`RingTheory/PowerSeries/Evaluation.lean`) where applicable? (This decides
     whether the contribution is "new `seriesEval` API" or a `HasEval`-based
     restatement.)
  4. **Statement packaging.** If a residue-extraction identity is upstreamed, is
     the `p·(·) = p·(·) − Σ(·)` packaging (with `rhoA`/`FtildeA` baked in) the
     right form, or should it be the abstract operator-kernel statement ("the
     constant of `W` with `(1+T)∂W = φB` is recovered as `p⁻¹·Σ W(ξ^i−1)`")
     decoupled from the specific `ρ_a`/`F̃_a` instances?
  5. **Naming.** The name `p_mul_constantCoeff_mahlerK_rhoA` encodes
     project-specific objects (`mahlerK`, `rhoA`). If anything graduates, what is
     the intended mathlib-namespaced name (e.g. under a future
     `PadicMeasure`/`Amice` namespace)?

**Refactor-actionable detail (interim, until the questions are answered).**
Treat the theorem as **project-local glue** in `ResidueZeta.lean`, next to its
single consumer `constantCoeff_mahlerK_rhoA` (line 1587) — do **not** open a
mathlib PR, and do **not** inline it (its ~125-line proof at the one call site
would only obscure the mass-formula lemma). The likely resolution, given the
sibling assessments (`rhoA` → NO-composable; `constantCoeff_FtildeA` →
NO-composable; `psi_rhoA` → BORDERLINE) and the answers to Q1–Q2: **not
mathlib-bound** (the substrate is project-only; the general trace lemma
`sum_seriesEval_mahlerK`, not this specialisation, is the only plausible
upstream candidate, and only after the whole measure/Amice layer is upstreamed).

**Note on the rejected alternatives.**
- *Not `YES-add-as-is` / `YES-but-generalise-first`:* the statement cannot be
  phrased in mathlib (every object is project-only), and Phase 4b found 0
  weakenings + no literature-standard target; the only "generalisation" nearby
  is a *different, already-existing* project lemma (`sum_seriesEval_mahlerK`),
  not a restatement of this one. (Verdicts-reference: do not treat literature
  absence as YES.)
- *Not `NO-mathlib-has-it`:* Phase 5 found nothing in mathlib to cite — the gate
  requires an existing mathlib decl, which does not exist.
- *Not `NO-composable-from-mathlib` (despite the sibling `rhoA` using that
  bucket):* `rhoA` is a **one-line `def`** that literally *is* a 3-call
  composition, so its "not mathlib-bound" conclusion fit the NO-composable
  template. **This is a substantive ~125-line theorem**: Phase 6 is
  NOT-COMPOSABLE, and the `NO-composable` gate's required ≤3-line mathlib
  composition sketch **cannot be honestly produced** (no mathlib vocabulary, no
  mathlib building blocks). Forcing this theorem into `NO-composable` would
  violate that gate; the honest bucket for "not mathlib-bound, but the call is a
  project-policy/grain judgment on a real theorem" is `BORDERLINE-needs-human`.

---

## Next step

Answer the five questions in Phase 7 (the gating one is Q1: do you intend to
upstream the RJW p-adic-measure / Amice-transform / `seriesEval` layer at all?),
then re-run `/mathlibable PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA` to
resolve. Expected resolution: **not mathlib-bound** — keep
`p_mul_constantCoeff_mahlerK_rhoA` project-local in `ResidueZeta.lean` next to
its sole consumer `constantCoeff_mahlerK_rhoA`; if any upstreaming happens, the
target is the **general** trace lemma `sum_seriesEval_mahlerK` (assessed
separately), not this `ρ_a`/`F̃_a` specialisation, and only after the underlying
p-adic-measure / Amice-transform substrate is itself upstreamed. No mathlib PR
and no call-site refactor in the interim.
