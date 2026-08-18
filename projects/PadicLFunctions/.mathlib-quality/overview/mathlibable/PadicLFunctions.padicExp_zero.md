# `/mathlibable` report — `PadicLFunctions.padicExp_zero`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); reasoned from source — the file elaborates as part of `main`, the target and all its dependencies were read directly from source.
- decl `PadicLFunctions.padicExp_zero`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:133`
- kind:                      theorem (a `@[simp]` lemma)
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field and is an isometry there; the matching `log` inverts it. `padicExp_zero` is the elementary normalisation `exp(0)=1` of the project's exponential `padicExp` (decomposition node E3).

---

### Statement (Phase 1)

`padicExp_zero` is a **theorem** (`@[simp]`) stating the following:

> For a complete nonarchimedean (ultrametric) normed `ℚ_p`-algebra field `L`, the `p`-adic exponential
> evaluated at `0` equals `1`: `exp_p(0) = 1`.

This is the universal *normalisation* of the exponential: the constant (`n=0`) term of the defining
series `∑_{n} xⁿ/n!` is `0⁰/0! = 1`, and every other term vanishes at `x = 0`. The statement is the
`p`-adic instance of the textbook fact `exp(0) = 1` that holds verbatim for the classical, complex,
formal-power-series, normed-algebra, and Lie-group exponentials.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (used only to give `ℚ_[p]`/`L` their structure; the proof
  does not touch primality).
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L]` — a normed `ℚ_p`-algebra field. **Note:** the two
  hypotheses needed elsewhere in the file, `[IsUltrametricDist L]` and `[CompleteSpace L]`, are **`omit`-ed**
  for this lemma (line 132: `omit [IsUltrametricDist L] [CompleteSpace L] in`) — the identity `exp(0)=1`
  needs neither completeness nor the ultrametric inequality, because the series is a *finitely-supported*
  sum at `x = 0` (only the `n = 0` term survives).

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): `exp_p(0) = 1`.

Conclusion (Lean): `padicExp p (0 : L) = 1`.

**Proof shape (2 lines).**
```lean
rw [padicExp, tsum_eq_single 0 fun n hn => by simp [zero_pow hn]]
simp
```
Unfold `padicExp` to the `tsum`; `tsum_eq_single 0` collapses it to the `n = 0` term (every `n ≥ 1` term
is `(n!)⁻¹ • 0ⁿ = 0` via `zero_pow`); the residual `(0!)⁻¹ • 0⁰ = 1 • 1 = 1` closes by `simp`. The proof
is purely about the **definition** `padicExp`, not about any convergence/analytic property.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step `@[simp]` normalisation lemma about a `def` (decomposition node E3). It is not a
`def`/structure, not a named-after-a-person theorem, and not a `## Main results` headline (the main
results of the file are the isometry `norm_padicExp_sub_padicExp`, the functional equation `padicExp_add`,
and the `exp`/`log` inversion). Its mathlib fate is **governed by the BIG object it is about** — the
project's `padicExp`, a p-adic exponential mathlib does not have (see Phase 7).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem` (a `@[simp]` lemma), **not** a `def`/`abbrev`/`structure`. One-liner check **n/a**
(one-line note). The 2b def-exemption analysis does not apply to a lemma.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic exponential function value at zero `exp(0)=1` power series constant term                          | yes  | `exp_p(z)=∑ zⁿ/n!`; at `z=0` only `n=0` term `0⁰/0!=1` survives ⇒ `exp_p(0)=1` | Wikipedia "P-adic exponential function"; PlanetMath "p-adic exponential and p-adic logarithm"; MIT/Vogan "Exponential and logarithm in p-adic fields" (math.mit.edu/~dav/exp.pdf); arXiv 2106.09315 "Fast evaluation of some p-adic transcendental functions" |
|  2 | WebSearch (general form)         | formal exponential power series constant coefficient `exp(0)=1` normed-algebra exponential identity      | yes  | over any char-0 field `exp(X)=Σ Xⁿ/n! ∈ K[[X]]` has **constant coefficient 1**; "the exponential is characterised by … the normalisation `exp 0 = 1`" | arXiv 2205.00879 "An invitation to formal power series"; ProofWiki "Power Series Expansion for Exponential Function"; the `exp(0)=1` normalisation is what makes `exp` a group homomorphism (`exp(z+w)=exp z·exp w`) |
|  3 | WebSearch (named-after / aliases / abstraction) | exponential map `exp(0)` equals identity element nLab nonarchimedean group                              | yes  | for the exponential map of a (Lie/matrix) group, `exp(0) = e` (identity); the same normalisation across all exponential maps | nLab "exponential map" (`exp(0)=Id`, `d exp₀ = id`); confirms the statement is the universal `exp ↦ unit` normalisation, not a p-adic peculiarity |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + history of `exp(0)=1`, especially p-adically — is it ever non-trivial?") | n/a  | —                                | ChatGPT MCP server (`plugin:mathlib-quality:chatgpt-math`) is in `~/.claude/mcp-needs-auth-cache.json` (needs-auth) and is **not callable** in this environment; `/setup-chatgpt` not run. Recorded n/a — the same as the sibling `summable_padicExp_terms` report. WebSearch (3 queries) + Wikipedia/PlanetMath/MIT + the module's own citations (RJW Lem 5.14, Cassels §12, Washington §5.1) settle the (trivial) standard-form question. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) are the literature anchor. |
|  6 | nLab                             | exponential map / `exp(0)`                                                                              | yes  | nLab "exponential map": `exp(0)` is the identity/unit — the universal normalisation | not a categorical subtlety; the `exp(0)=unit` fact is taken as definitional everywhere |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (a one-point evaluation of a concrete factorial series). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic/series evaluation, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| p-adic `exp(0)` constant term; is `exp(0)=1` ever non-trivial                                            | yes (implicit) | community treats `exp_p(0)=1` as immediate from the series; never disputed | the constant term being 1 is textbook-trivial; no Q&A treats it as a hard fact |
| 10 | recent arXiv (last 5 years)      | p-adic exponential transcendental functions normalisation                                               | partial | modern p-adic-exp papers (e.g. arXiv 2106.09315) restate the series with constant term 1 verbatim; `exp(0)=1` is assumed | confirms no modern reformulation changes the trivial normalisation |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (specific p-adic
`exp(0)=1` / the general formal-power-series constant-coefficient form / the named "exp of the unit is the
identity" abstraction); ChatGPT MCP recorded n/a with reason (server not callable); local references
recorded n/a with reason (no dir); nLab checked (hit); nCatLab / Stacks recorded n/a with reason;
MathOverflow and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **the normalisation `exp(0) = 1`** — the value of the exponential function at the
origin, equivalently the constant term of the exponential power series `∑ xⁿ/n!`.

Sources agree on the standard form: **yes, unanimously and trivially.** Every source — Wikipedia (p-adic),
PlanetMath, MIT/Vogan's p-adic notes, ProofWiki, "An invitation to formal power series", nLab — states
the exponential series as `∑_{n≥0} xⁿ/n!` whose constant (`n=0`) term is `1`, so `exp(0) = 1`. This is
the *defining normalisation* of the exponential and is identical in the classical, complex,
formal-power-series, normed-algebra, and p-adic settings. The p-adic case is **not special**: Wikipedia's
"P-adic exponential function" gives `exp_p(z) = ∑ zⁿ/n!` and the value at `0` falls straight out of the
constant term (the restricted radius `p^{-1/(p-1)}` is irrelevant — `0` is the centre of the disc).

Most general standard form: for the exponential of *any* object built from a `∑ xⁿ/n!`-type series (or any
exponential map of a group), `exp(0) = unit`. The target states exactly this for `padicExp` over the
maximal nonarchimedean setting.

Generality dimensions where the literature varies:
- **Underlying object**: classical/complex `exp` / `PowerSeries.exp` (formal) / `NormedSpace.exp`
  (Banach algebra) / p-adic `exp` / Lie-group `exp`. In *every* case the `exp(0)=unit` normalisation holds;
  it is the one fact that is uniform across all of them.
- **Hypotheses**: none are needed beyond "the constant term is `1` and is the only one surviving at `0`".
  The target correctly `omit`s `[IsUltrametricDist L]` and `[CompleteSpace L]`.

Disagreement with the literature: **none.** The target *is* the universal normalisation, at the maximal
generality (it drops the analytic hypotheses), proved by the canonical observation (only the constant term
survives).

---

### Generality analysis — `padicExp_zero`

Literature-standard form (from Phase 3): `exp(0) = unit`, holding for any exponential, with **no analytic
hypotheses** required.

| # | Parameter / hypothesis            | Current Lean form        | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------|---------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                 | normed field             | "any object the exp series lives in" | NO (within this def) | `padicExp` is *defined* on a `[NormedField L] [NormedAlgebra ℚ_[p] L]`; the lemma is maximally general **for this def** — it already drops the two analytic typeclasses |
| 2 | `[NormedAlgebra ℚ_[p] L]`         | normed `ℚ_p`-algebra      | extension of `ℚ_p`              | NO (within this def) | needed only so `(n!)⁻¹` is a scalar; part of `padicExp`'s signature, not strengthenable away |
| 3 | `[IsUltrametricDist L]` **(omitted)** | — (dropped via `omit`)   | not needed                      | already dropped     | the proof is finitely-supported at `x=0`; the ultrametric inequality is not used. ✓ the lemma already takes the weakest hypotheses. |
| 4 | `[CompleteSpace L]` **(omitted)** | — (dropped via `omit`)   | not needed                      | already dropped     | no convergence is invoked (single surviving term); completeness not used. ✓ already weakest. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *(relative to the `padicExp` definition it is about).* The lemma
is stated with the fewest hypotheses the def admits — it explicitly `omit`s the completeness and ultrametric
typeclasses, exactly mirroring the literature fact that `exp(0)=1` needs no analytic input. There is no
weakening left to make *for a statement about `padicExp`*.
Number of weakening opportunities found: **0.**
Proposed restatement: none (already maximal for this def).
Cost of restatement: n/a.

The only "generalisation" imaginable — stating `exp(0)=1` for a *more general exponential object* — is not a
weakening of this lemma but a consequence of choosing a more general **def** (see Phase 4c / Phase 7): it is
the `padicExp`-upstreaming question, not a parameter-weakening of `padicExp_zero`.

→ Phase 7 therefore considers `YES-add-as-is` vs the NO buckets vs BORDERLINE (and runs 4c).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already typeclasses |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | the proof is a finite-support `tsum` collapse; no limit to filter-ise |
|  3 | construct an object → universal-property class?                                                            | partial  | the *deep* modern-idiom move is at the **def layer**: replace the bespoke `padicExp` `tsum` with mathlib's `NormedSpace.exp` (Banach-algebra exponential) — then `exp(0)=1` would be exactly mathlib's existing `NormedSpace.exp_zero`. **But** mathlib's `NormedSpace.exp` is archimedean-only (`expSeries_radius_eq_top`), so this is **infeasible** today (see Phase 5/6 and the sibling `summable_padicExp_terms` report). | would let `padicExp_zero` *be* `NormedSpace.exp_zero` — i.e. delete it — once a nonarchimedean `exp` exists in mathlib |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | no       | — | already at the weakest typeclasses the def allows |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | `n : ℕ` is intrinsic to the factorial series |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this lemma as a standalone statement). The proof is already a trivial,
hypothesis-minimal `tsum`-collapse. The one organisational lever (row 3) lives **one layer down** at the
`padicExp` *definition*: if the project's bespoke `padicExp` were replaced by — or shown defeq to — a
mathlib nonarchimedean exponential, then `padicExp_zero` would simply *be* mathlib's `NormedSpace.exp_zero`
and be deleted. That replacement is **currently infeasible** (mathlib has no nonarchimedean `exp`; its
`NormedSpace.exp` rests on `expSeries_radius_eq_top`, which is false p-adically — established in detail in
the sibling `summable_padicExp_terms` Phase 4c/5). One-line reason this is not itself a modernisation move:
it is a trivial normalisation lemma already in idiomatic form; the only modernisation question is the
def-layer one, which is the `padicExp`-upstreaming decision deferred to Phase 7.

---

### Diamond / defeq risk — `padicExp_zero`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `padicExp_zero`

[A] Lean-Finder       "p-adic exponential at zero equals one", "exp 0 = 1 padic"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) for every candidate `exp_zero`/`constantCoeff_exp` shape, plus reading the candidate decls' actual statements.
[B] Loogle            `?exp 0 = 1`, `padicExp _ 0 = 1`, `_ (0 : _) = 1`   no p-adic hit: `padicExp` does not exist in mathlib, so no lemma can mention it. Generic `exp 0 = 1` shapes return the archimedean / formal / WithZero family (see [D]).
[C] LeanSearch        "exponential of zero is one", "p-adic exp at 0", "constant term of exp series is 1"   no p-adic hit: surfaces `Complex.exp_zero`, `Real.exp_zero`, `NormedSpace.exp_zero`, `PowerSeries.constantCoeff_exp` — all about *other* exponential objects; nothing nonarchimedean / `padicExp`.
[D] Grep mathlib src  `grep -rn "exp_zero\|constantCoeff_exp\|coeff_zero_exp\|padic.*[Ee]xp"` over `.lake/packages/mathlib/Mathlib/`   hits (ALL about other objects): `Complex.exp_zero`/`Real.exp_zero` (`Analysis/Complex/Exponential.lean:95,207`), `Circle.exp_zero` (`Analysis/Complex/Circle.lean:124`), `EReal.exp_zero` (`SpecialFunctions/Log/ERealExp.lean:43`), `NormedSpace.exp_zero` (`Analysis/Normed/Algebra/Exponential.lean:185`, `@[simp]`), `WithZero…exp_zero` (`Algebra/GroupWithZero/WithZero.lean:402`), `PowerSeries.constantCoeff_exp` = "constant term of `exp A` is `1`" (`RingTheory/PowerSeries/Exp.lean:58`). **NONE** in `Mathlib/NumberTheory/Padics/` — there is **no p-adic exponential in mathlib**.
[E] Name pattern      `padicExp`, `padicExp_zero`, `InExpBall`   `padicExp`/`padicExp_zero`/`InExpBall` do **not** exist in mathlib (confirmed by grep; the only `padic`+`exp` hits in `NumberTheory/Padics/` are `padicValRat` and an unrelated `tactic.interactive.padic_index_simp`).

Searched for both:
- the user's current form (`padicExp p (0:L) = 1`) — **impossible to be in mathlib**: it mentions
  `padicExp`, a project-only def absent from mathlib.
- the literature-standard form (`exp(0)=1` for *some* mathlib exponential) — mathlib **does** have the
  analogues `NormedSpace.exp_zero`, `Complex.exp_zero`, `PowerSeries.constantCoeff_exp` (all `@[simp]` /
  trivial), **but each is about a different exponential object**, none of which is (or is known defeq to)
  `padicExp`.

**Why the close mathlib analogues do NOT settle this as `NO-mathlib-has-it`.** Mathlib's
`NormedSpace.exp_zero` proves `exp (0:𝔸) = 1` for the **Banach-algebra exponential** `NormedSpace.exp`,
which is built on `expSeries` with `expSeries_radius_eq_top` — i.e. it is the **archimedean** exponential
(`𝕂 = ℝ`/`ℂ`). The project's `padicExp` is a *different function*: a concrete `tsum ∑ (n!)⁻¹•xⁿ` that is
**junk-total** outside the disc `p^{-1/(p-1)}` and is **not** mathlib's `NormedSpace.exp` (mathlib cannot even
compute that exp's radius p-adically — see the sibling `summable_padicExp_terms` report, Phase 5/6).
Likewise `PowerSeries.constantCoeff_exp` is about the **formal** series, not its p-adic evaluation.
So `padicExp_zero` is **not** a specialisation of any existing mathlib lemma: you cannot get
`padicExp p 0 = 1` by calling `NormedSpace.exp_zero`, because `padicExp ≠ NormedSpace.exp` (and the bridge
does not exist).

Concluded: **not in mathlib** — `padicExp` itself is absent (all five methods exhausted, plus the
literature-standard form). Mathlib has *analogous* `exp_zero` lemmas for every *other* exponential object
(`NormedSpace.exp_zero`, `Complex.exp_zero`, `PowerSeries.constantCoeff_exp`), but none is about, or
applicable to, `padicExp`.

---

### Call sites — `padicExp_zero`

Internal use count: **1** (within the project, NOT counting the declaring theorem)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`)

| Caller file:line               | Usage pattern (one-line excerpt)                                                          |
|--------------------------------|-------------------------------------------------------------------------------------------|
| PadicExp.lean:1126             | `rw [… PadicInt.coe_zero, padicExp_zero]` — proving `pZpExp p 0 = 1` (the `ℤ_p`-valued exp at 0), inside the `pZpExp` plumbing |
| ResidueZeta.lean:1729          | `rw [pZpExp_coe …, PadicInt.coe_zero, padicExp_zero, PadicInt.coe_one]` — establishing `map_zero_eq_one'` for the additive character `κ : AddChar ℤ_[p] ℤ_[p]` built from `exp`, used in the residue/ζ-value proof (RJW §7) |

Inline-derivation grep (was `exp(0)=1` re-derived elsewhere without using the lemma?):
  - (none) — both places that need `padicExp _ 0 = 1` route through this `@[simp]` lemma; there is no
    inline `tsum_eq_single 0 …` re-derivation elsewhere.

What the call-sites pattern tells you: **K = 1 internal use + 1 external-to-file caller, no inline
re-derivation.** Per the Phase-6 signal table this is a *modest* API signal: it has a genuine downstream
consumer (the `AddChar` `map_zero_eq_one'` obligation in `ResidueZeta`), so it is **not** dead code; but
with K = 1 it is also not a heavily-reused load-bearing lemma (contrast the sibling `summable_padicExp_terms`
at K = 8 + 1). As a `@[simp]` normalisation lemma its true role is mostly *automation* (it fires inside
`simp` calls that don't show up as explicit `padicExp_zero` tokens), so the literal call count understates
its utility. Either way, its existence is justified **within the project** — the question is purely whether
it (with its parent def) belongs in *mathlib*.

---

### Composition check (Phase 6)

Can `padicExp_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `NormedSpace.exp_zero` (mathlib's `exp (0:𝔸) = 1`).
  - Mathlib decls used: `NormedSpace.exp_zero`.
  - Result: **fails** — `NormedSpace.exp_zero` is about `NormedSpace.exp`, **not** `padicExp`. The goal
    `padicExp p 0 = 1` cannot be closed by it because `padicExp` is a *different* (project-defined)
    function and there is no `padicExp = NormedSpace.exp` bridge in scope (nor can there be — mathlib's
    exp is archimedean). Not a composition; not even applicable.

Attempt 2: unfold + a generic `tsum`-of-single mathlib lemma.
  - Mathlib decls used: `tsum_eq_single` (mathlib) + `zero_pow` + `simp`.
  - Result: **this IS the project's proof** (`rw [padicExp, tsum_eq_single 0 …]; simp`). It is a 2-line
    proof *about the def `padicExp`*. It is not a composition of mathlib lemmas yielding a mathlib statement
    — the statement it proves (`padicExp p 0 = 1`) is **not a mathlib statement at all** (it mentions a
    project-only def). The mathlib pieces (`tsum_eq_single`, `zero_pow`) are generic; the *thing being
    proved* is project-specific. You cannot "inline this composition at mathlib call sites" because there
    is no mathlib object `padicExp` to talk about.

Conclusion: **NOT-COMPOSABLE** *(in the sense relevant to the NO-composable verdict).* The proof uses only
trivial mathlib glue, but the **statement is parasitic on the project def `padicExp`**, which mathlib does
not have. There is therefore nothing to compose *in mathlib* — `NO-composable-from-mathlib` (which means
"inline the composition at the call sites and delete the lemma") does **not** apply: deleting
`padicExp_zero` and inlining `tsum_eq_single 0 …` at the 2 call sites is a *project-internal* golf decision
(and a poor one — it would duplicate the `@[simp]` normalisation and remove the `simp` lemma), **not** a
mathlib-composability finding. The mathlib question is governed entirely by whether `padicExp` is upstreamed.

---

## Verdict: `padicExp_zero`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** the universal exponential normalisation `exp(0)=1`,
  trivial and unanimous across every source and every exponential object (classical, complex, formal,
  Banach-algebra, p-adic, Lie). The p-adic case is *not* special; the restricted radius is irrelevant at
  the centre `0`. Maximal generality (the lemma already `omit`s completeness + ultrametricity).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** *for a statement about `padicExp`* — stated with the
  weakest hypotheses the def admits (analytic typeclasses dropped). Modern-idiom check (4c): the only lever
  is the *def-layer* replacement of `padicExp` by a (non-existent) mathlib nonarchimedean `exp`, which is
  infeasible today.
- Mathlib search (Phase 5): **`padicExp` is not in mathlib**, so the statement cannot be. Mathlib has
  *analogous* `exp_zero` lemmas for **other** exponential objects (`NormedSpace.exp_zero` `@[simp]`,
  `Complex.exp_zero`, `PowerSeries.constantCoeff_exp`), **none applicable** to `padicExp` (different
  function; no bridge; mathlib's exp is archimedean).
- Composition check (Phase 6): **NOT-COMPOSABLE in the mathlib sense** — the 2-line proof is trivial mathlib
  glue, but the *statement* is parasitic on the project-only def `padicExp`; there is no mathlib object to
  compose. Call sites: **K=1 internal + 1 external** (modest, but a real `AddChar` consumer; not dead code).

**Rationale (why BORDERLINE, not a NO and not a clean YES):**

`padicExp_zero` is the elementary, maximally-general, `@[simp]` normalisation `exp(0)=1` of the project's
p-adic exponential `padicExp`. On the mechanics it sits between buckets, and the deciding factor is a
judgment the skill cannot make alone — exactly the situation BORDERLINE exists for.

It is **not `NO-mathlib-has-it`.** Mathlib has `exp_zero`/`constantCoeff_exp` for *other* exponentials, but
the verdict gate forbids citing those: `padicExp p 0 = 1` does **not** follow in ≤1 line from
`NormedSpace.exp_zero`, because `padicExp` is a *different function* (a junk-total `tsum`, not mathlib's
archimedean `NormedSpace.exp`, with no defeq bridge — mathlib cannot even compute the p-adic exp radius, per
the sibling `summable_padicExp_terms` report). Inventing such a citation is precisely the "Loogle returned
*something*" anti-pattern.

It is **not `NO-composable-from-mathlib`.** That bucket means "delete the lemma and inline a ≤3-call mathlib
composition at the call sites". But the statement mentions `padicExp`, a project-only def — there is no
mathlib object to compose, and "delete + inline `tsum_eq_single 0`" is a *project-internal* golf
(duplicating the normalisation, dropping a `@[simp]` lemma), not a mathlib finding. The trivial proof body
is mathlib glue, but a `NO-composable` verdict would mis-describe the situation.

It is **not a clean `YES-add-as-is` either** — and this is the crux. The lemma is genuinely missing from
mathlib and is maximally general, which mechanically *looks* like YES. But `padicExp_zero` is **100 %
parasitic on `padicExp`**: it has no meaning in mathlib until `padicExp` is in mathlib. And `padicExp` is a
**BIG, undecided upstreaming question** — mathlib has *no* nonarchimedean/p-adic exponential at all, and the
sibling foundational lemma `summable_padicExp_terms` was itself ruled **`BORDERLINE-needs-human`** with the
governing decision being "do you intend to upstream the project's whole nonarchimedean-`exp` development as a
unit?" `padicExp_zero` is a trivial **companion** of that development: if `padicExp` goes to mathlib,
`padicExp_zero` ships *with it* as the obligatory `@[simp]` normalisation (at which point it is a clean,
as-is, maximally-general addition — `exp(0)=1` is the canonical first lemma any exp gets); if `padicExp`
stays project-local, so does this. The skill's own **def-first** principle is decisive here: a lemma's
verdict follows its parent def's, and the parent `padicExp` has **no assessment yet** and an **undecided**
mathlib fate. Committing this lemma to YES while its parent def is unresolved would put the cart before the
horse. Per the skill's anti-pattern guidance ("treating literature absence / a whole-development cost as a
self-resolving verdict"), the right move is to **surface the dependency as a question**, not to silently
pick YES.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exponential development** to mathlib as
   a unit — i.e. the def `PadicLFunctions.padicExp` itself, together with its core lemmas
   (`summable_padicExp_terms`, the isometry `norm_padicExp_sub_padicExp`, the functional equation
   `padicExp_add`, and the matching `padicLog`)? This is the **same governing decision** already flagged for
   `summable_padicExp_terms` (BORDERLINE) — `padicExp_zero` is a trivial `@[simp]` companion that travels
   with that development, never alone.
2. If **yes** to (1): `padicExp_zero` ships as the obligatory `@[simp]` normalisation alongside the def
   (`exp(0)=1`), exactly like mathlib's `NormedSpace.exp_zero` / `Circle.exp_zero` / `EReal.exp_zero`. It is
   already maximally general and needs no change. Do you agree it is **YES-add-as-is *as part of that
   PR*** (not as a standalone PR)?
3. If you do **not** plan to upstream the p-adic-exp machinery: then `padicExp_zero` stays a (correct,
   minimally-reused) project-local `@[simp]` lemma about a project-local def, and should be **dropped from
   mathlib consideration**. Is that the case?
4. (Def-layer, only if you want to pursue the mathlib-idiomatic route in Q2's PR.) Would you want `padicExp`
   reconciled with mathlib's `NormedSpace.exp` (so that `padicExp_zero` *becomes* `NormedSpace.exp_zero` and
   is deleted)? Note this is currently **infeasible** — it needs a p-adic radius-of-convergence computation
   mathlib lacks (see the `summable_padicExp_terms` report) — but it determines whether `padicExp_zero`
   survives as a named lemma at all.

**Next action:** user answers the questions; re-run `/mathlibable PadicLFunctions.padicExp_zero` —
**together with `/mathlibable PadicLFunctions.padicExp`** (the def whose upstreaming decision governs this
lemma) and the sibling `/mathlibable PadicLFunctions.summable_padicExp_terms` — to resolve. Likely
resolutions:
  - "Upstream the nonarchimedean-`exp` development" → flips to **YES-add-as-is**, shipped *with* the
    `padicExp` PR as its `@[simp]` `exp(0)=1` companion (already maximal; no change needed).
  - "Keep project-local" → **drop from mathlib consideration**; it stays the correct project-local `@[simp]`
    normalisation of `padicExp`.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable PadicLFunctions.padicExp_zero` —
preferably alongside `/mathlibable PadicLFunctions.padicExp` and
`/mathlibable PadicLFunctions.summable_padicExp_terms`, since this lemma's verdict is entirely governed by
the (BIG, undecided) upstreaming decision on the p-adic exponential definition it is a `@[simp]` companion
to — resolving to either **YES-add-as-is** (ship with the `padicExp` development as its `exp(0)=1`
normalisation) or **drop-from-consideration** (keep as a project-local `@[simp]` lemma).
