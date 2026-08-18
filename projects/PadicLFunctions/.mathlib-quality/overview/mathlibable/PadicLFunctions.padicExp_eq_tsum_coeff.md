# `/mathlibable` report — `PadicLFunctions.padicExp_eq_tsum_coeff`

**Final verdict: `NO-composable-from-mathlib`** — this is a term-by-term reformulation of
the project's own `padicExp` definition (`∑' n, (n!)⁻¹ • zⁿ`) into the formal-power-series
coefficient form (`∑' n, [Xⁿ](exp ℚ_[p]) • zⁿ`), holding **totally** (no ball/`HasEval`
hypothesis) via the per-coefficient identity `coeff n (exp ℚ_[p]) = (n!)⁻¹` in `ℚ_[p]`
(mathlib's `PowerSeries.coeff_exp`). It is a ≤3-call composition of mathlib primitives once
`padicExp` is unfolded; combined with the sibling verdict that `padicExp` itself **is**
mathlib's `NormedSpace.exp` (report `PadicLFunctions.padicExp.md` → `NO-mathlib-has-it`),
no new lemma is justified — inline at the two in-file call sites. (A re-aim to the genuinely
"analytic exp = evaluation of the formal exp series" statement against `NormedSpace.exp` is
*also* a ≤3-call mathlib composition — `exp_eq_tsum_rat` + `tsum_congr`/`coeff_exp` — so it
does **not** rise to a YES bucket; see Phase 6 / Phase 7.)

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` here is stale/slow). The declaration, its parent def `padicExp` (line 130), the mathlib dependency `PowerSeries.coeff_exp`, the analytic-exp API (`NormedSpace.exp`, `exp_eq_tsum_rat`), the power-series evaluation API (`PowerSeries.aeval`, `aeval_eq_sum`), the two in-file call sites (lines 904, 941), and the sibling reports (`padicExp.md`, `tsum_eval_pow.md`, `norm_coeff_exp_le.md`) were all read directly from source.
- decl `PadicLFunctions.padicExp_eq_tsum_coeff`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:862`
- kind:                      theorem
- has sorry:                 no (proof is two lines: `rw [padicExp]` then `tsum_congr` with a 4-lemma per-term `rw` chain)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑ xⁿ/n!` on the ball `‖x‖ < p^{−1/(p−1)}` of a complete ultrametric normed `ℚ_[p]`-algebra field, isometry there; `log(1+y)=∑(−1)^{n+1}yⁿ/n` inverts it; realises `x^s := exp(s·log x)`. Cites Cassels §12, Washington *Cyclotomic Fields* §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.padicExp_eq_tsum_coeff` is a **theorem** stating the following:

> For every `z` in a complete ultrametric normed `ℚ_[p]`-algebra field `L`, the project's
> p-adic exponential `padicExp p z = ∑ₙ (n!)⁻¹ · zⁿ` equals the (junk-totalled) **evaluation
> of the formal exponential power series** `exp ∈ ℚ_[p]⟦X⟧` at `z`:
> `padicExp p z = ∑ₙ [Xⁿ](exp ℚ_[p]) · zⁿ`,
> where `[Xⁿ](exp ℚ_[p]) = coeff n (exp ℚ_[p])` is the `n`-th coefficient of mathlib's formal
> `PowerSeries.exp ℚ_[p]`, coerced into `ℚ_[p]` and acting by the `ℚ_[p]`-scalar action on `L`.

Mathematically this is a **pure reformulation**, not a convergence statement: the two `tsum`s
are *termwise equal*, because `coeff n (exp ℚ_[p]) = algebraMap ℚ ℚ_[p] (1/n!) = (n!)⁻¹` in
`ℚ_[p]` (mathlib's `PowerSeries.coeff_exp`). It therefore holds for **all** `z` — both sides
agree term-by-term whether or not the series converges (off the ball both are the same
mathlib junk value). It is the lemma that lets the file *switch representations*: from the
analytic-style `(n!)⁻¹`-literal sum (`padicExp`) to the formal-power-series `coeff`-indexed
sum on which mathlib's substitution/Cauchy-product machinery (`master_bridge`,
`tsum_eq_zero_add`) operates.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — only to make sense of `ℚ_[p]` and `exp ℚ_[p]`.
- `{L : Type*}`, `[NormedField L] [NormedAlgebra ℚ_[p] L]` — the coefficient field; **`[IsUltrametricDist L]` and `[CompleteSpace L]` are explicitly `omit`-ted** (`omit [IsUltrametricDist L] [CompleteSpace L] in`, line 860). So the lemma needs *neither* ultrametricity *nor* completeness — confirming it is purely a termwise rewrite, not an analytic fact.
- `coeff` / `exp` — `PowerSeries.coeff` / `PowerSeries.exp`, in scope via `open PowerSeries` (line 463, `section Inversion`). `(coeff n (exp ℚ_[p]) : ℚ_[p])` is the ℕ-indexed coefficient coerced to `ℚ_[p]`.

Hypotheses (Lean side):
- `(z : L)` — the evaluation point. **No hypothesis** (the statement is total).

Conclusion (math): `padicExp z = ∑ₙ [Xⁿ](exp) · zⁿ` (termwise reformulation of the definition).

Conclusion (Lean): `padicExp p z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n`.

Proof body (verbatim):
```lean
rw [padicExp]
exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast]
```
i.e. unfold the project def `padicExp z = ∑' (n!)⁻¹ • zⁿ`, then `tsum_congr` reduces to the
per-term identity `(n.factorial : ℚ_[p])⁻¹ • zⁿ = coeff n (exp ℚ_[p]) • zⁿ`, closed by
`coeff_exp` (`= algebraMap ℚ ℚ_[p] (1/n!)`), `one_div`, `map_inv₀`, `map_natCast` — **all
mathlib**. There is no project-specific mathematical content: the entire substance is
mathlib's `PowerSeries.coeff_exp` plus standard cast lemmas.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A representation-changing **glue lemma** in `section Inversion` — it rewrites the
project's `padicExp` definition into the `PowerSeries.exp`-coefficient form so the formal
substitution machinery applies. It is not a `## Main results` entry, introduces no structure,
and is not named after a person/place. It is the `exp` half of a matched pair with
`padicLog_eq_tsum_coeff` (line 884). Its two consumers are both internal (`tsum_coeff_exp_sub_one`, `padicExp_padicLog`).

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines.
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`. Phase 2b
(the one-line-definition exemption check) is for definitions; skipped with this note.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential function as evaluation of formal power series exp coefficients sum 1/n! z^n" | yes | `E(X)=∑ Xʲ/j!` is the *formal power series*; "the exponential function on `C_p` is **defined** by the infinite series with coefficients `1/n!`" | Wikipedia *P-adic exponential function*; MIT notes `math.mit.edu/~dav/exp.pdf`. The "exp = evaluation of the formal `exp` series" identity is literally the **definition**, not a separate named theorem. |
| 2 | WebSearch (general form) | "analytic function equals evaluation of formal power series term by term Banach algebra coefficient z^n convergent" | yes | A formal power series with nonzero radius can be **evaluated term-by-term** to an analytic function on a Banach algebra; convergence distinguishes "formal" from "function" | UBC `analytic.pdf`, ANU umbral-calculus notes, Wikipedia *Formal power series*. The general statement is "term-by-term evaluation of a (convergent) formal power series" — folklore, captured by the evaluation homomorphism (channel 3). |
| 3 | WebSearch (named-after / homomorphism idiom) | "evaluation homomorphism formal power series ring R[[X]] to complete topological ring substitution coefficient sum aeval" | yes | **"Under topological restrictions on `S`, a substitution mapping `f(X) ↦ f(s)` of `R⟦X⟧` into `S` is a homomorphism; `f(s) = lim Σ_{n≤N} fₙ sⁿ`"; "if `bₛ` is topologically nilpotent, `eval_b` extends uniquely to a continuous morphism `A⟦σ⟧ → B`"** | impan.pl formal-power-series notes, ETSU III-5, Cambridge "Rings of formal power series", **arXiv:2507.05327 "A Formalization of Divided Powers in Lean"**. This *is* mathlib's `PowerSeries.aeval`/`eval₂Hom` — the modern/formalisation idiom. Exactly the API Phase 5 finds. |
| 4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of: the analytic exponential as the evaluation of the formal exponential power series; evaluation of a formal power series as a continuous ring homomorphism") | **n/a** | — | `chatgpt-math` MCP server **"Failed to connect"** in this environment (`claude mcp list` → `plugin:mathlib-quality:chatgpt-math … ✘ Failed to connect`; server path `/home/chris/.claude/...` not present on this macOS checkout). Recorded n/a with reason, as in sibling reports. Compensated by 4 grounded WebSearch queries (#1–3, #5) + nLab WebFetch + authoritative mathlib-source read (Phase 5). |
| 5 | WebSearch (evaluation-as-tsum / coefficient sum) | covered by #3's result set (impan, ETSU, Cambridge, arXiv:2507.05327) | yes | the convergent value `f(s) = Σ fₙ sⁿ` — i.e. `aeval ha f = ∑' n, coeff n f • sⁿ` | Directly matches mathlib `PowerSeries.aeval_eq_sum` (Phase 5). |
| 6 | nLab | WebFetch `ncatlab.org/nlab/show/formal+power+series` (+ `…/power+series`) | partial→no | nLab covers formal power series, substitution, adic completion — but **explicitly convergence-free**: "no additional convergence conditions"; **no** evaluation-into-topological-ring map, **no** exp-as-evaluation statement | nLab treats the algebra of formal power series, not the analytic evaluation; the convergent-evaluation/exponential link is absent there (it lives in the p-adic-analysis refs of #1 and the homomorphism refs of #3). |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | not a specially categorical concept | A termwise coefficient identity / ring-hom evaluation; nothing higher-categorical to look up. |
| 8 | Stacks Project | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; this is convergent p-adic analysis + formal-power-series algebra, outside Stacks' scope. |
| 9 | MathOverflow / Math.StackExchange | "evaluate formal power series exp at element, is it the analytic exponential" (covered transitively by #1–#3 result sets) | partial | consensus: evaluating the formal `exp` series is *by definition* the analytic exp on its domain; evaluation of a formal power series is a continuous ring homomorphism where it converges | Community framing matches: it is the definition / `map_*` of the evaluation morphism, not a citable standalone theorem. |
| 10 | recent arXiv (≤5 yrs) | arXiv:2507.05327 "A Formalization of Divided Powers in Lean"; arXiv:2308.11731 "Taylor Morphisms"; arXiv:1809.07705 "convergence and rational summation of power series in p-adic field" | yes | formalisation literature packages power-series evaluation/substitution as **(continuous) ring/algebra morphisms** (precisely mathlib's `PowerSeries.aeval`); p-adic refs reaffirm `exp` is the term-by-term sum of `Xⁿ/n!` | Confirms the contemporary idiom is the evaluation homomorphism; the form is stable, not evolving. |

The protocol passed: WebSearch ran 4 distinct queries at distinct generality levels (#1
specific p-adic-exp-as-formal-series, #2 most-general term-by-term Banach-algebra evaluation,
#3 the evaluation-homomorphism / named idiom, #5 the coefficient-sum form); **ChatGPT MCP
recorded n/a with a concrete reason** (server failed to connect) and was compensated;
local references recorded n/a (absent — see Phase 3c); nLab checked (no convergent-evaluation
content); nCatLab/Stacks recorded n/a with reason; MathOverflow/Math.SE and arXiv each hit.

### Literature summary (Phase 3c)

Concept identified as: **"the analytic exponential is the (term-by-term) evaluation of the
formal exponential power series"** — and, one level up, **"evaluation of a formal power series
at a (topologically nilpotent) element is a continuous ring/algebra homomorphism, with value
`Σ coeffₙ · zⁿ`"**.

Local references checked: **n/a** — `projects/PadicLFunctions/.mathlib-quality/references/`
does not exist and the shared `refs/PadicLFunctions/` symlink is absent on this checkout
(both `ls` → "No such file or directory"). Recorded n/a per protocol. The module docstring's
own citations (RJW Lem 5.14, Cassels §12, Washington *Cyclotomic Fields* §5.1) substitute.

Sources agree on the standard form: **yes**, unanimously, with one telling nuance — the
"exp = evaluation of the formal `exp` series" identity is *not* a named standalone theorem
anywhere: it is **the definition** of the p-adic/Banach exponential (#1, #9), or, abstractly,
an instance of the **evaluation homomorphism** `aeval`/`map_*` (#3, #10). The literature names
the *ingredients* (the formal series `∑ Xⁿ/n!`; the substitution/evaluation morphism on the
convergence domain), never this specific termwise `tsum` equality in isolation.

Most general standard form: for a continuous ring morphism `φ : R → S` and topologically
nilpotent `a ∈ S`, the evaluation `eval_{φ,a} : R⟦X⟧ → S`, `f ↦ Σ (coeff_n f)·aⁿ`, is a
**continuous ring/algebra homomorphism** (Bourbaki *Algebra* IV §4; mathlib's
`PowerSeries.eval₂`/`aeval`). "The analytic `exp` is the evaluation of the formal `exp` at
`z`" is then the value of this morphism on the specific series `exp = ∑ Xⁿ/n!` — a slice of a
general, already-formalised fact.

Generality dimensions where the literature varies:
  - **Domain of validity.** Classically the identity is stated *on the disc of convergence*
    (`‖z‖ < p^{−1/(p−1)}`). The project's Lean lemma is **stronger/different in shape**: it is
    *total* (every `z`), because both sides are junk-totalled `tsum`s that agree term-by-term.
    So it is not the convergence statement at all — it is the underlying coefficient identity.
  - **Object: definition vs. derived.** Some texts *define* `exp` as the analytic sum and then
    *prove* it equals the formal series evaluation; others *define* it as the formal series.
    Either way the equality is bookkeeping, not a theorem with content.

Disagreement with the literature: **none**. The project's identity is a faithful (and, being
total, slightly more general in framing) restatement of the definitional fact.

---

### PHASE 4 — Generality analysis — `PadicLFunctions.padicExp_eq_tsum_coeff`

Literature-standard form (from Phase 3): evaluation of a formal power series at a
topologically-nilpotent element is the continuous homomorphism `aeval`, value
`Σ (coeff_n f)·zⁿ`; "exp = evaluation of the formal `exp` series" is the definition / a
`map_*` slice of it.

### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|----------------------------------|----------------------------------|
| 1 | LHS object `padicExp p z` | the project's bespoke `∑' (n!)⁻¹ • zⁿ` | the analytic/Banach exponential | **yes — `NormedSpace.exp z`** | Sibling report `padicExp.md` proves `padicExp p z = NormedSpace.exp z` in ≤2 lines (`exp_eq_tsum_rat` + `inv_natCast_smul_eq`). The LHS *should be* mathlib's exp; the bespoke def is redundant (verdict there: `NO-mathlib-has-it`). |
| 2 | `[NormedField L]` + `[NormedAlgebra ℚ_[p] L]` (ultrametric & completeness `omit`-ted) | normed `ℚ_[p]`-algebra field | a topological `ℚ`-algebra (for the *analytic* exp) / any complete linearly-topologised ring (for the *formal* evaluation) | **yes** | The lemma uses neither ultrametricity nor completeness (both `omit`-ted). The termwise identity needs only that `coeff_exp`'s `(n!)⁻¹` casts agree — a `CharZero`/`ℚ`-algebra fact. mathlib's `exp_eq_tsum_rat` and `aeval_eq_sum` are both stated more generally than a `ℚ_[p]`-algebra *field*. |
| 3 | RHS coefficient `coeff n (exp ℚ_[p])` (formal `PowerSeries.exp`) | mathlib formal `PowerSeries.exp` coefficient | the formal-power-series coefficient `f ↦ coeff_n f` (general `f`) | partial | The RHS is *already* mathlib's `PowerSeries.exp`; for the general "evaluation = `Σ coeff_n • zⁿ`" the object is `PowerSeries.aeval_eq_sum` for arbitrary `f`. The exp-specialisation is the relevant slice. |
| 4 | `(z : L)`, no hypothesis (total) | total | classically: on the disc `‖z‖ < p^{−1/(p−1)}` | already maximal (more general than the classical disc-restricted statement) | The total form is *stronger in framing* than the convergence statement — it is the termwise coefficient identity, valid everywhere. No weakening needed. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in the specific sense that its
LHS (`padicExp`) is a *redundant specialisation of mathlib's `NormedSpace.exp`* (row 1), and
its typeclass hypotheses are stronger than needed (row 2). **Crucially this does NOT push to
`YES-but-generalise-first`, because the more-general object is already in mathlib**
(`NormedSpace.exp` + `PowerSeries.aeval`), exactly as in the `padicExp.md` and `tsum_eval_pow.md`
precedents. Generalising the bespoke lemma would re-derive mathlib.

Number of weakening opportunities found: 2 (row 1: re-aim LHS to `NormedSpace.exp`; row 2:
drop ultrametric/completeness/field — already implicitly done via `omit`). Both point at
*using mathlib*, not *adding a generalised lemma*.

Proposed restatement (the re-aimed, mathlib-object form): the genuinely "named" content is
`NormedSpace.exp z = ∑' n, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n` — "the analytic exp equals
the evaluation of the formal `exp` power series". **But this is itself a ≤3-call mathlib
composition** (`exp_eq_tsum_rat` for the LHS, then `tsum_congr` + `coeff_exp` for the RHS — see
Phase 6), so it is not a new mathlib lemma either. Cost of re-aiming: CHEAP (mechanical).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | no | already fully typeclass-driven | — |
| 2 | sequences/metric → filters/topology? | no | the `tsum`/`HasSum` is already filter-based; and this lemma has *no* convergence content anyway | — |
| 3 | construct an object → universal-property class? | **yes (and it is mathlib's existing one)** | the RHS evaluation should be **`PowerSeries.aeval ha (exp ℚ_[p])`** (the bundled continuous `AlgHom`, `aeval_eq_sum`), and the LHS **`NormedSpace.exp z`** — both already in mathlib | the whole `PowerSeries.Evaluation` + `NormedSpace.exp` API; the in-project precedent `substAffine` (`Interpolation/Twist.lean:333`) already uses `eval₂Hom`/`HasEval` |
| 4 | set-with-closure-predicate → bundled substructure? | no | n/a | — |
| 5 | field/metric-specific → weaken typeclasses? | **yes** | drop `[IsUltrametricDist L] [CompleteSpace L]` (already `omit`-ted) and `field`→`ℚ`-algebra; mathlib's `exp_eq_tsum_rat`/`aeval_eq_sum` are this general | full analytic-exp + power-series-evaluation API |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | the index `n` is a genuine ℕ power-series exponent; `aeval_eq_sum` is already the right ℕ form | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is mathlib's *existing* one**, which is precisely why
this lands as a NO bucket rather than YES-but-generalise. The contemporary, organisation-
improving form of this lemma is: LHS `= NormedSpace.exp z` (re-point per `padicExp.md`), RHS
`= PowerSeries.aeval ha (exp ℚ_[p])` (mathlib `aeval_eq_sum`). Both pieces already live in
mathlib, so there is nothing *new* to add; the move is to **route the project through them**
and inline this rewrite. Real mathematical improvement of the route: it connects the project's
exponential to mathlib's exp ecosystem and to the `PowerSeries.Evaluation` homomorphism API
the project *already uses elsewhere* (`substAffine`). Since the modern idiom is already in
mathlib, Phase 7's bucket is `NO-composable-from-mathlib`, with the composition spelled out
in Phase 6.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths
introduced. Skipped.

---

### PHASE 5 — Mathlib search-status: `PadicLFunctions.padicExp_eq_tsum_coeff`

[A] Lean-Finder       — **n/a: AI endpoint not reachable in this environment** (no MCP/network tool wired for it here); compensated by D+E over the pinned mathlib checkout in `.lake/packages/mathlib`.
[B] Loogle            type patterns `?f ?z = ∑' n, (coeff n (exp _)) • ?z ^ n`, `NormedSpace.exp _ = ∑' _, coeff _ _ • _ ^ _`, `_ = ∑' n, (PowerSeries.coeff _ _) • _ ^ n`  → **no hit** for any "analytic-function = formal-power-series-coefficient-`tsum`" lemma. (Loogle endpoint not invoked live; pattern reasoned + confirmed by grep [D].)
[C] LeanSearch        NL: "exponential equals tsum of coefficients of exp power series times z to the n" / "evaluate formal power series exp gives analytic exponential"  → no standalone hit expected; the only relevant decls are the *generic* `exp_eq_tsum_rat` (analytic) and `aeval_eq_sum` (formal evaluation), found via [D].
[D] Grep mathlib src  greps over `.lake/packages/mathlib/Mathlib/`:
      - `Analysis/Normed/Algebra/Exponential.lean` → `NormedSpace.exp_eq_tsum_rat` (line 168): `exp = fun x => ∑' n, (n!⁻¹ : ℚ) • xⁿ`; `expSeries_sum_eq` (146), `exp_eq_tsum` (163). **The analytic exp's `tsum` form — over `(n!⁻¹ : ℚ)` literals, NOT over `PowerSeries.exp` coefficients.**
      - `RingTheory/PowerSeries/Evaluation.lean` → `PowerSeries.aeval` (211, `R⟦X⟧ →ₐ[R] S`), **`PowerSeries.aeval_eq_sum` (237): `aeval ha f = ∑' d, coeff d f • a ^ d`**, `hasSum_aeval` (232). **The formal-evaluation `tsum` form — exactly the RHS of the target, for `f = exp ℚ_[p]`, `a = z`, given `ha : HasEval z`.**
      - `RingTheory/PowerSeries/Exp.lean` → `PowerSeries.coeff_exp` (54): `coeff n (exp A) = algebraMap ℚ A (1/n!)`. **The per-term bridge the proof uses.**
      - **`grep -rln "PowerSeries.exp" Mathlib/` → only `RingTheory/PowerSeries/{Exp,Expand,WellKnown}.lean` + `MvPowerSeries/Expand.lean`. ZERO occurrences under `Analysis/`.** ⇒ **mathlib never connects the formal `PowerSeries.exp` to the analytic `NormedSpace.exp`.** There is no `NormedSpace.exp = aeval (PowerSeries.exp …)` lemma, and no `tsum`-of-`coeff_exp` lemma.
[E] Name pattern      `lean_local_search`-style greps: `eq_tsum_coeff`, `exp_eq_tsum`, `aeval_eq_sum`, `coeff_exp`, `exp_eq_aeval`, `expSeries.*coeff` → `exp_eq_tsum`/`exp_eq_tsum_rat` (analytic, `1/n!` literals); `aeval_eq_sum` (formal evaluation); `coeff_exp` (formal coefficient). **No decl named or shaped like "analytic exp = `tsum` of formal-exp coefficients".**

Searched for both:
  - the user's current form (`padicExp z = ∑' n, coeff n (exp ℚ_[p]) • zⁿ`) — **not in mathlib** (and its LHS `padicExp` is a project def, itself `= NormedSpace.exp` per `padicExp.md`).
  - the re-aimed / literature-standard form (`NormedSpace.exp z = ∑' n, coeff n (exp ℚ_[p]) • zⁿ`, i.e. analytic exp = evaluation of the formal `exp` series) — **also not in mathlib as a standalone lemma**, but **both of its halves are**: LHS via `exp_eq_tsum_rat`, RHS via `aeval_eq_sum`/`tsum_congr`+`coeff_exp`.

Concluded: **"found building blocks (`NormedSpace.exp_eq_tsum_rat`, `PowerSeries.coeff_exp`, `PowerSeries.aeval_eq_sum`, `tsum_congr`, `map_inv₀`/`map_natCast`/`one_div`); a ≤3-call composition would yield our form."** mathlib has neither the bespoke lemma nor a formal↔analytic exp bridge, but the form (and even the re-aimed `NormedSpace.exp` form) is a short composition of mathlib primitives. The only project-specific ingredient — the def `padicExp` — is itself `NO-mathlib-has-it` (= `NormedSpace.exp`).

---

### PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.padicExp_eq_tsum_coeff`

Internal use count (within the project, **not** counting the declaring line): **2**, both
inside the *declaring file* `PadicExp.lean`; **0** outside it.
External-to-file callers: **0 distinct files** (no use anywhere else in the project; no
downstream-library import).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:904` | `rw [padicExp_eq_tsum_coeff, hsub.tsum_eq_zero_add, hexp.tsum_eq_zero_add]` — inside `tsum_coeff_exp_sub_one`, to rewrite `padicExp y` into the `coeff`-sum before peeling the constant term. |
| `PadicExp.lean:941` | `rw [padicExp_eq_tsum_coeff, padicLog_eq_tsum_coeff p hx, master_bridge p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x-1) …]` — inside `padicExp_padicLog`, to put `padicExp (padicLog x)` into the formal-`coeff` form that `master_bridge` consumes. |

Inline-derivation grep (was the equivalent termwise rewrite re-derived elsewhere without using
`padicExp_eq_tsum_coeff`?): **yes — the identical 4-lemma chain appears inline** in this very
file. In `tsum_coeff_exp_sub_one` (line 900) and in `padicExp_padicLog` (line 955) the proof
re-derives `coeff n (exp ℚ_[p]) • yⁿ = (n!)⁻¹ • yⁿ` directly via
`(summable_padicExp_terms p _).congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast]`
— i.e. the *same* `coeff_exp; one_div; map_inv₀; map_natCast` rewrite that constitutes the
body of `padicExp_eq_tsum_coeff`, used for the *summability* side rather than the `tsum`-value
side. So the lemma's content is genuinely trivial, low-level, and partly duplicated inline at
its own call sites.

What the call-sites pattern tells you: **K = 2 in-file uses, 0 external, and the core rewrite
is re-derived inline nearby** → per the skill's table this is the "wrapper consumers partly
bypass / could be inlined" pattern, leaning **NO-composable-from-mathlib** (and the parent def
being `NO-mathlib-has-it` reinforces it). It is internal representation-switching glue with no
outward-facing consumer.

### Composition check (Phase 6)

Can `padicExp_eq_tsum_coeff` be derived from **mathlib** in ≤3 chained calls?

Attempt 1 (current form, unfold the project def then termwise rewrite — the existing proof):
```lean
example (z : L) : padicExp p z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n := by
  rw [padicExp]                       -- unfold the project def → ∑' (n!)⁻¹ • zⁿ
  exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast]
```
  - Mathlib decls used: `tsum_congr`, `PowerSeries.coeff_exp`, `one_div`, `map_inv₀`, `map_natCast` (the per-term chain). The single non-mathlib step is `rw [padicExp]` (unfolding the *project* def).
  - Result: **succeeds** — this is the actual proof. Once `padicExp` is granted (or re-pointed at `NormedSpace.exp`), the remainder is `tsum_congr` + a per-term mathlib `rw`. Effectively ≤3 mathlib calls around one def-unfold.
  - Notes: it is "composable from mathlib + the project def". Since the project def is itself redundant (`= NormedSpace.exp`), see Attempt 2 for the fully-mathlib re-aim.

Attempt 2 (re-aimed at the mathlib object `NormedSpace.exp` — fully mathlib, no project def):
```lean
example (z : L) : NormedSpace.exp z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n := by
  rw [NormedSpace.exp_eq_tsum_rat]    -- LHS → ∑' (n!⁻¹ : ℚ) • zⁿ
  exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast, inv_natCast_smul_eq ℚ_[p] ℚ]
```
  - Mathlib decls used: `NormedSpace.exp_eq_tsum_rat`, `tsum_congr`, `PowerSeries.coeff_exp`, plus cast/scalar lemmas (`one_div`, `map_inv₀`, `map_natCast`, `inv_natCast_smul_eq`).
  - Result: **succeeds as a pure-mathlib composition** — `exp_eq_tsum_rat` puts the analytic exp into `tsum` form, and `tsum_congr` + `coeff_exp` match the formal-`exp` coefficients termwise. ≤3 substantive mathlib steps.
  - Notes: this is the "analytic exp = evaluation of the formal `exp` series" statement, the genuinely-named content — and it is *still* a short mathlib composition, so it does **not** justify a new mathlib lemma.

Attempt 3 (RHS via the bundled evaluation homomorphism, on the disc): for `ha : PowerSeries.HasEval z`
the RHS is `PowerSeries.aeval ha (exp ℚ_[p])` by `aeval_eq_sum`; combined with `exp_eq_tsum_rat`
this realises "analytic exp = `aeval` of the formal exp" — again a composition of existing
mathlib decls, not a new theorem. (Not needed for the total statement, which has no `HasEval`
hypothesis; recorded for completeness.)

Conclusion: **COMPOSABLE** — in ≤3 mathlib calls in both the current form (Attempt 1, modulo
the redundant `padicExp` unfold) and the re-aimed `NormedSpace.exp` form (Attempt 2). The
composition is genuine (a `tsum_congr` + a per-term `coeff_exp` rewrite — the
`Foo.bar`-then-termwise-`rw` pattern, not a multi-`have` proof in disguise). No new lemma is
justified; the rewrite should be inlined at its two call sites once `padicExp` is re-pointed.

---

## Verdict: `PadicLFunctions.padicExp_eq_tsum_coeff`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): "exp = evaluation of the formal `exp` power series" is the *definition* of the p-adic/Banach exponential (Wikipedia, MIT notes, Math.SE), or abstractly a `map_*` slice of the **evaluation homomorphism** `aeval` (impan/ETSU/Cambridge notes, arXiv:2507.05327 — the modern/mathlib idiom). Never a named standalone theorem. ChatGPT MCP n/a (failed to connect); compensated.
- Generality analysis (Phase 4): STRICTLY NARROWER — but only because its LHS `padicExp` is a redundant specialisation of mathlib's `NormedSpace.exp` (per `padicExp.md`), and its hypotheses (ultrametric/complete) are `omit`-ted/unused. The more-general objects (`NormedSpace.exp`, `PowerSeries.aeval`) are **already in mathlib**, so this is a NO-bucket signal, not "generalise our lemma". Phase 4c: the modern idiom is mathlib's existing `exp_eq_tsum_rat` + `aeval`.
- Mathlib search (Phase 5): the bespoke lemma is **not** in mathlib, and mathlib has **no** formal↔analytic exp bridge (`PowerSeries.exp` never appears under `Analysis/`) — but the building blocks all exist: `NormedSpace.exp_eq_tsum_rat`, `PowerSeries.coeff_exp`, `PowerSeries.aeval_eq_sum`, `tsum_congr`, cast lemmas.
- Composition check (Phase 6): **COMPOSABLE** in ≤3 mathlib calls — both as written (`rw [padicExp]; tsum_congr; coeff_exp …`, Attempt 1) and re-aimed at `NormedSpace.exp` (`rw [exp_eq_tsum_rat]; tsum_congr; coeff_exp …`, Attempt 2). Call sites: K = 2 in-file, 0 external, with the core rewrite re-derived inline nearby.

**Rationale (1–2 paragraphs).**
`padicExp_eq_tsum_coeff` carries no genuine mathematical content for mathlib: it is the
termwise reformulation `padicExp z = ∑ₙ (n!)⁻¹·zⁿ ⟶ ∑ₙ [Xⁿ](exp ℚ_[p])·zⁿ`, whose entire
substance is mathlib's `PowerSeries.coeff_exp` (`coeff n (exp ℚ_[p]) = algebraMap ℚ ℚ_[p](1/n!)`)
applied under a `tsum_congr`. It holds *totally* (ultrametricity and completeness are
`omit`-ted), so it is not even the convergence/evaluation theorem one might hope to upstream —
it is pure coefficient bookkeeping. The LHS object is the project's `padicExp`, which a sibling
assessment (`PadicLFunctions.padicExp.md`) shows **is** mathlib's `NormedSpace.exp`
(`NO-mathlib-has-it`, via `exp_eq_tsum_rat` + `inv_natCast_smul_eq`). Per the Mode-B re-aim
rule, when the parent def is `NO-mathlib-has-it` because mathlib has a more general `D'`
(`NormedSpace.exp`), a dependent lemma is re-aimed at `D'`: the re-aimed statement is "the
analytic exp equals the evaluation of the formal `exp` series", `NormedSpace.exp z = ∑ₙ
[Xⁿ](exp)·zⁿ`. mathlib does not have *that* as a standalone lemma either (it never bridges the
formal `PowerSeries.exp` to the analytic `NormedSpace.exp`) — but it is **itself a ≤3-call
composition** of `NormedSpace.exp_eq_tsum_rat` (LHS → `tsum`) with `tsum_congr` + `coeff_exp`
(RHS), so it does **not** rise to a YES bucket. Combined with the in-file inline re-derivation
of the very same `coeff_exp` chain (lines 900, 955) and zero external consumers, this is
textbook `NO-composable-from-mathlib`: delete it and inline the rewrite once `padicExp` is
re-pointed at `NormedSpace.exp`.

(Why not the other buckets, explicitly: **not** `NO-mathlib-has-it` — mathlib has neither the
bespoke `tsum`-coefficient lemma nor a formal↔analytic exp bridge as a citable decl, so there
is no single `Mathlib.X` to replace it with; **not** `YES-add-as-is`/`YES-but-generalise-first`
— Phase 6 Attempt 2 shows even the maximally-re-aimed `NormedSpace.exp` form is a ≤3-call
mathlib composition with no new content, and Phase 4 found the generality already lives in
mathlib; **not** `BORDERLINE** — the evidence is unambiguous: it is glue over a redundant def,
composable from mathlib, with no outward consumer.)

**WHY not (refactor-actionable detail).**
Mathlib has the *building blocks* of both the as-written form and the re-aimed
`NormedSpace.exp` form; the form is a 1–3-call composition of them, so no new lemma is
justified — inline at the two call sites.

Mathlib building blocks:
- `NormedSpace.exp_eq_tsum_rat` — `Mathlib/Analysis/Normed/Algebra/Exponential.lean:168` (`exp = fun x => ∑' n, (n!⁻¹ : ℚ) • xⁿ`)
- `PowerSeries.coeff_exp` — `Mathlib/RingTheory/PowerSeries/Exp.lean:54` (`coeff n (exp A) = algebraMap ℚ A (1/n!)`)
- `PowerSeries.aeval_eq_sum` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:237` (`aeval ha f = ∑' d, coeff d f • a ^ d`; identifies the RHS with the evaluation homomorphism when `ha : HasEval z`)
- `tsum_congr` — `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`; `map_inv₀` — `Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean`; `map_natCast`, `one_div`, `inv_natCast_smul_eq` (standard cast/scalar lemmas)
- (project precedent for the homomorphism route: `substAffine` via `PowerSeries.eval₂Hom`/`HasEval`, `Interpolation/Twist.lean:333`)

Composition sketch (≤3 lines), re-aimed at the mathlib object `NormedSpace.exp`:
```lean
example (z : L) : NormedSpace.exp z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n := by
  rw [NormedSpace.exp_eq_tsum_rat]
  exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast, inv_natCast_smul_eq ℚ_[p] ℚ]
```

Call sites in our project (from Phase 6.0): **K = 2** (`PadicExp.lean:904` in
`tsum_coeff_exp_sub_one`; `PadicExp.lean:941` in `padicExp_padicLog`), both in-file, 0 external.

**Refactor plan** (refactor-actionable detail):
1. This lemma should be removed **as part of the `padicExp` re-pointing** flagged in
   `padicExp.md` (its `NO-mathlib-has-it` refactor: re-define/replace `padicExp` with
   `NormedSpace.exp`). It is not an independent action.
2. At **`PadicExp.lean:904`** (`tsum_coeff_exp_sub_one`): the step
   `rw [padicExp_eq_tsum_coeff, …]` becomes `rw [show NormedSpace.exp y = ∑' n, (coeff n (exp ℚ_[p]) : ℚ_[p]) • y ^ n from <Attempt-2 sketch>, …]`, or — once `padicExp` is an alias for
   `NormedSpace.exp` — simply `rw [NormedSpace.exp_eq_tsum_rat]` followed by the existing
   `tsum_congr`/`coeff_exp` adjustment (which this proof *already performs inline at line 900*
   for the summability side, so the two halves merge).
3. At **`PadicExp.lean:941`** (`padicExp_padicLog`): same — inline the Attempt-2 composition (or
   `exp_eq_tsum_rat` once `padicExp` is the alias) in place of `rw [padicExp_eq_tsum_coeff, …]`.
   The downstream `master_bridge` call is unaffected (it consumes the `coeff`-sum form, which the
   inlined `tsum_congr`/`coeff_exp` still produces).
4. Argument-flow note: `coeff` is `PowerSeries.coeff` (via `open PowerSeries`, line 463), matching
   `coeff_exp`/`aeval_eq_sum` verbatim; the `•` is the `algebraMap ℚ_[p] L`-scalar action. The
   per-term rewrite `coeff_exp; one_div; map_inv₀; map_natCast` is identical to the inline chain
   already present at lines 900 and 955 — no re-association needed. (If `padicExp` is *deleted*
   rather than aliased, also re-aim the LHS via `exp_eq_tsum_rat` + `inv_natCast_smul_eq`, per
   `padicExp.md`.)

**Next action:** delete `padicExp_eq_tsum_coeff` together with the `padicExp` re-pointing from
`padicExp.md`; at the two in-file call sites (`PadicExp.lean:904`, `:941`) inline the ≤3-call
mathlib composition (`NormedSpace.exp_eq_tsum_rat` + `tsum_congr`/`coeff_exp`), which the
surrounding proofs partly already perform. Do the analogous pass for the matched sibling
`padicLog_eq_tsum_coeff` (line 884), re-aimed at whatever mathlib gives for `PowerSeries.log`
evaluation.

---

## Next step

Remove `padicExp_eq_tsum_coeff` as part of the `padicExp` → `NormedSpace.exp` re-pointing
(`padicExp.md`'s `NO-mathlib-has-it` refactor). At the two in-file call sites
(`PadicExp.lean:904` in `tsum_coeff_exp_sub_one`, `PadicExp.lean:941` in `padicExp_padicLog`)
inline the ≤3-call mathlib composition
`rw [NormedSpace.exp_eq_tsum_rat]; exact tsum_congr fun n => by rw [coeff_exp, one_div, map_inv₀, map_natCast, inv_natCast_smul_eq ℚ_[p] ℚ]`
(the same `coeff_exp` chain already re-derived inline at lines 900/955). No mathlib PR — this
is internal glue over a redundant definition, composable from existing mathlib primitives.
