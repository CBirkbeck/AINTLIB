# /mathlibable report — `PadicLFunctions.FtildeA`

**Final verdict: `NO-composable-from-mathlib`** — `FtildeA` is RJW §7's transient
antiderivative `F̃_a`, a 3-term assembly whose two power-series terms are exactly
mathlib's `PowerSeries.logOf` / `PowerSeries.log` and whose third term is the
*project-local* constant `extLog p (a:K)` (the Iwasawa-branch `log_p`, not in
mathlib). Zero external call sites; the source paper treats `F̃_a` as a step
inside one proof, not a named object. Keep it project-local; do not PR.

---

### Baseline (Phase 0)
- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.FtildeA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:469`
- kind:                      `def` (`noncomputable`)
- has sorry:                 **no** (the whole file `ResidueZeta.lean` has 0 `sorry`/`admit`; the `FtildeA` region 460–560 is sorry-free)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" —
  continuity/pole of `zetaPBranch` + the mass `∫x⁻¹μ_a = −(1−p⁻¹)·log_p(a)` via the
  explicit antiderivative `F̃_a`.

---

### Statement (Phase 1)

`PadicLFunctions.FtildeA` is **a definition** of a formal power series over `K`.

For a natural number `a` and coefficient field `K`, `FtildeA p K a` is RJW's
antiderivative

  F̃_a(T) = log( T/(1+T) · (1+T)^a / ((1+T)^a − 1) )   (RJW arXiv:2309.15692, TeX 2268)

realised through the factorisation `(1+T)^a − 1 = a·T·u_a` (with `u_a = uA K a` the
unit cofactor, constant term 1) as the three-term sum

  F̃_a = −log_p(a) − log(u_a) + (a−1)·log(1+T)
       = C(−extLog p a) − (formalLog).subst(u_a − 1) + (a−1)•formalLog.

Here `log` is the **formal** logarithmic power series `Σ_{n≥1}(−1)^{n−1}n⁻¹Tⁿ`, its
substitution into `u_a − 1` is legal because `u_a − 1` has zero constant term, and
`log_p(a) = extLog p (a:K)` is the **p-adic Iwasawa-branch logarithm** (normalised
`log_p p = 0`) of the *integer constant* `a`. `F̃_a` is the formal antiderivative of
`F_a` (RJW Lemma 7.3, `∂F̃_a = F_a`); evaluating `F̃_a` at the `p`-th roots of unity
and summing produces the residue mass.

Variables / typeclasses involved (Lean side):
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]`
  `[CompleteSpace K] [CharZero K]` — the ambient coefficient field (declared once for
  the whole `section mass`). The four analytic instances are **not used by the `def`
  itself**; they matter only for the downstream *analytic* lemmas (`norm_coeff_FtildeA_le`,
  `summable_seriesEval_FtildeA`, …) that evaluate `F̃_a`.
- `p : ℕ` with `[Fact p.Prime]` — the prime (enters only through `extLog p`).
- `a : ℕ` — the exponent in `(1+T)^a`.

Hypotheses (Lean side): none on the `def` itself (it is junk for `a = 0`/`p∣a`; the
hypotheses `a ≠ 0`, `¬p∣a` live on the *theorems about* `F̃_a`, e.g.
`constantCoeff_FtildeA`, `one_add_mul_derivative_FtildeA`).

Conclusion (math): the formal antiderivative power series `F̃_a` of RJW §7.

Conclusion (Lean): `PowerSeries K` — n/a, it is a definition.

Body (3 substantive lines):
```lean
noncomputable def FtildeA (a : ℕ) : PowerSeries K :=
  PowerSeries.C (-(extLog p ((a : K))))
    - (formalLog (K := K)).subst (uA K a - 1)
    + ((a - 1 : ℕ)) • formalLog (K := K)
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a presentation-level bookkeeping power series internal to the §7 residue
computation. It is not listed under `## Main results` (the file's headline results are
the continuity/pole of `zetaPBranch` — RJW Thm 7.1), it introduces no new mathematical
*structure*, and it carries no person/place name. It is an intermediate object exactly
analogous to its own ingredient `uA` (which the sibling report classified SMALL).

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **3 substantive lines** (a `C(...)`, a `.subst`, and an `nsmul`, summed).
One-liner verdict: **MULTI-LINE** — the Phase-2b one-liner heuristic does not apply.
(One-line note only; the exemption table is for ONE-LINER defs.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic L-function residue logarithmic derivative power series antiderivative measure F_a Iwasawa` | partial | "The p-adic zeta function has a simple pole at s=1 with residue 1−1/p, expressed via x⁻¹ and the residue of μ_a; measures on ℤ_p correspond to formal power series, the measure related to derivatives of the power series" | Surfaced RJW (arXiv:2309.15692) "An introduction to p-adic L-functions", Warwick notes, and the measure↔power-series dictionary. No source *names* `F̃_a` as a standalone object — it is a step in the residue proof. |
| 2 | WebSearch (general form) | `formal power series logarithm "log(1+X)" definition coefficients (-1)^(n+1)/n standard` | yes | `log(1+X) = Σ_{n≥1}(−1)^{n−1}n⁻¹Xⁿ` (Mercator series), the reverse of `exp(X)−1` | Confirms the formal-log component (the project's `formalLog`, ≡ mathlib `PowerSeries.log`) is the canonical Mercator series. |
| 3 | WebSearch (residue / named source) | `p-adic zeta function residue s=1 simple pole "1 - 1/p" Mahler transform measure mu_a antiderivative power series` | yes (background) | `ζ_{p,p−1}` has a simple pole at s=1 with residue `(1−p⁻¹)`; ζ_p expressed via `x⁻¹` and the residue of `μ_a`; pseudo-measure formulation | Confirms the *target theorem* this antiderivative serves (RJW Thm 7.1). `F̃_a` itself is internal machinery, not a headline object. |
| 4 | WebSearch (named-after / Coleman aliases) | `Coleman power series logarithmic derivative measure Z_p "F_a" "(1+T)^a - 1" formal logarithm p-adic` | partial | Coleman power series ↔ measures on ℤ_p; logarithmic-derivative operator `DL(f) = (1−[p]σ)·(Df/f)`; `Df/f` is the recurring shape | The construction `F̃_a` is a *specific* antiderivative in the Coleman/logarithmic-derivative tradition; the operator `f ↦ Df/f` (logarithmic derivative) is the named concept, not this particular `F̃_a`. |
| 5 | ChatGPT MCP | (intended: standard-form + generality + historical-evolution prompt) | **n/a** | — | **ChatGPT MCP server not authenticated/available in this environment** (`~/.claude/mcp-needs-auth-cache.json`; no matching `chatgpt` tool exposed). Compensated with the extra WebSearch queries (#1–#4) and the **source paper identified via the sibling `uA` report** (#9). |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/` | **n/a** | — | `projects/PadicLFunctions/.mathlib-quality/references/` does not exist; no `refs/` symlink in the checkout; no `*.tex`/`*.bib`/`*.md` source under the project. NB: the **file header itself** cites the source as "RJW §7, TeX 2181–2360". |
| 7 | nLab | `formal logarithm power series` / `logarithmic derivative` | yes (component) | nLab has the formal `log`/`exp` power series and the logarithmic-derivative operator; **no** `F̃_a`-specific entry | Confirms the *components* (formal log, log-derivative) are standard; the assembled antiderivative is not an nLab concept. |
| 8 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept — a concrete formal power series tied to one p-adic measure computation. No higher-categorical statement applies. |
| 9 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry concept; Stacks has no antiderivative of a measure-attached power series. |
| 10 | Source paper (arXiv) — decisive | identify "RJW"; read §7 framing | **yes** | **RJW = Rodrigues Jacinto–Williams, "An introduction to p-adic L-functions", arXiv:2309.15692, §7** (residue of ζ_p at s=1). `F̃_a` is introduced (TeX 2268) as the **antiderivative `log(T/(1+T)·(1+T)^a/((1+T)^a−1))`** used to compute the mass, then factored (eq. tilde F_a) into `−log_p(a) − log(u_a) + (a−1)log(1+T)`. | **Decisive.** Sibling report `PadicLFunctions.uA.md` established this identification (the lecture-notes author C. Williams overlaps the repo owner). `F̃_a` is a transient device inside one proof — not a standalone named object in the source. |
| 11 | MathOverflow / Math.SE | (folded into #1–#4) | partial | `((1+T)^a−1)/T` and logarithmic derivatives are routine in Iwasawa-theory threads | No dedicated treatment of this particular antiderivative `F̃_a`. |

### Literature summary (Phase 3)

Concept identified as: **RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692) §7's
antiderivative `F̃_a`** in the computation of the residue of the Kubota–Leopoldt p-adic
zeta function at `s=1`. Its *ingredients* are all standard and named:
- the formal logarithm `log(1+X) = Σ(−1)^{n−1}n⁻¹Xⁿ` (Mercator series),
- substitution / composition of formal power series,
- the p-adic (Iwasawa-branch) logarithm `log_p`,
- the logarithmic-derivative tradition (Coleman power series).

But the **assembled object `F̃_a` is not separately named** in the literature — RJW
introduces it only as an intermediate antiderivative inside the residue proof
(`∂F̃_a = F_a`, Lemma 7.3).

Sources agree on the standard form: **yes** for each *ingredient*; **no separately-named
standard form** for the assembled `F̃_a` (it is bookkeeping inside one proof).

Most general standard form: there is none for `F̃_a` qua named object. The closest
standard concept is the **logarithmic-derivative / Coleman-power-series** machinery, and
the **formal log** (mathlib `PowerSeries.log`).

Generality dimensions where the literature varies:
  - the formal-log component: over any ℚ-algebra (mathlib `PowerSeries.log`, ℚ-algebra);
    here `K` is a complete ultrametric `ℚ_p`-Banach field — far more than the *formal*
    construction needs.
  - the constant `log_p(a)`: the p-adic logarithm exists over any complete `ℚ_p`-algebra;
    the *Iwasawa-branch* normalisation (`log_p p = 0`) is one of several conventions.

Disagreement with the literature: none — but the literature treats `F̃_a` as a
proof-internal antiderivative, not an exported object.

---

### Generality analysis — `PadicLFunctions.FtildeA`

Literature-standard form (Phase 3): there is no separately-named standard `F̃_a`; the
relevant standard objects are the **formal log** and the **logarithmic derivative**, both
already maximally general elsewhere.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` | normed field | (the *formal* `F̃_a` needs only a ℚ-algebra; `extLog` needs a normed `ℚ_p`-algebra) | partial | The two power-series terms (`log`, `logOf`) need only `[CommRing K] [Algebra ℚ K]`; the **`extLog` term genuinely needs the normed/ultrametric `ℚ_p`-Banach structure** (its definition uses `padicLog` and norms). So the def cannot be stated over a bare ℚ-algebra without dropping the constant term. |
| 2 | `[NormedAlgebra ℚ_[p] K]` | `ℚ_p`-Banach algebra | needed by `extLog` | **NO** | `extLog p (a:K)` is defined only for normed `ℚ_p`-algebras; load-bearing for term 1. |
| 3 | `[IsUltrametricDist K]` | ultrametric | needed by `extLog`/`padicLog` machinery | **NO** | The p-adic log domain (`InExpBall`, `ExtLogDomain`) is ultrametric-specific. |
| 4 | `[CompleteSpace K]` | complete | needed by `extLog` (convergence of `padicLog`) | **NO** | `padicLog` is a convergent series; completeness is essential. |
| 5 | `[CharZero K]` | char 0 | char 0 (for the inverses in `log`/`uA`) | partial | Needed for `n⁻¹` (formal log) and `a⁻¹` (`uA`); the natural home is char 0 anyway. |
| 6 | `a : ℕ` | natural exponent | — | no | `a` is intrinsically the natural-number argument of `extLog p (a:K)` and `(1+T)^a`; the residue computation is over `a ∈ ℕ`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what the *assembled* object needs.** Unlike
its ingredient `uA` (whose four analytic instances were pure dead weight on the
definition), `FtildeA`'s `extLog` term **genuinely consumes** the normed / ultrametric /
complete `ℚ_p`-algebra structure (rows 2–4 are load-bearing, NOT removable). So there is
no clean weakening of `FtildeA` as a whole.
Number of weakening opportunities found: **0 that keep the object intact** (rows 1, 5 are
cosmetic char-0/field framing; the analytic instances are required by the constant term).

Proposed restatement: **none** — the def is not strictly narrower than a literature
standard, because there is no separately-named literature standard for `F̃_a` to compare
against. (Cf. `uA`, where the literature *did* have `binomialSeries` to weaken toward.)

Cost of restatement: n/a.

**This MAXIMALLY-GENERAL finding does NOT push toward `YES-add-as-is`**, because (Phases
5–6) the two power-series terms are *already in mathlib* (`PowerSeries.logOf`,
`PowerSeries.log`) and the third is a project-local constant — `FtildeA` is a thin
assembly, not a novel object, exactly like its ingredient `uA`.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclasses? | no | already typeclass-based | — |
| 2 | sequences/metric → filters/topology? | no | it is a formal (algebraic) power series; no topology in the def | — |
| 3 | construct object → universal-property class? | no | an explicit 3-term sum, not a universal object | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | field-specific → weaken typeclasses? | partial | the two power-series terms could be stated over `[CommRing K][Algebra ℚ K]` (mathlib's `PowerSeries.log`/`logOf` already are), but the `extLog` term forbids weakening the *whole* object | the mathlib-idiomatic form of terms 2–3 **is** `PowerSeries.logOf`/`PowerSeries.log` — i.e. the modern idiom says *delete the re-definition and compose*, not *generalise `FtildeA`* |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index → arbitrary monoid/group? | no | `a:ℕ` is intrinsic to `(1+T)^a` and `extLog p (a:K)` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it does not yield a new object** — it yields the
instruction to **compose from mathlib's `PowerSeries.logOf` / `PowerSeries.log`** (which
the project itself already uses elsewhere — see `PadicExp.lean`, which imports and uses
mathlib's `PowerSeries.log`). The contemporary mathlib form of "−log(u_a) + (a−1)log(1+T)"
is `−PowerSeries.logOf (uA K a) + (a−1)•PowerSeries.log K`. This reinforces
NO-composable: the modern idiom replaces `FtildeA`'s two log terms with mathlib calls
rather than promoting `FtildeA` itself to mathlib.
One-line reason this is *not* a "ship the modernised `FtildeA`" move: the residual term
`C(−extLog p a)` is a *project-local* constant (the Iwasawa-branch `log_p`, not in
mathlib), so the assembled object is inherently project-bound.

---

### Diamond / defeq risk — `PadicLFunctions.FtildeA`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Returns a bare `PowerSeries K`; introduces no instance, so nothing for typeclass search to disambiguate. |
| 2 | Reducibility leak | none | Plain `noncomputable def`, not `@[reducible]`/`abbrev`; body exposed only via explicit `rw [FtildeA]` (as in `constantCoeff_FtildeA`, `one_add_mul_derivative_FtildeA`, `seriesEval_FtildeA_at_root`). |
| 3 | Non-canonical unfolding | low | No `@[simp]`; `simp` will not unfold it. Proofs unfold deliberately via `rw [FtildeA, ...]`. No surprise. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `K : Type*`; `PowerSeries K` is monomorphic in `K`'s universe; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`; `PowerSeries.C`, the casts `(a:K)`, and `(a-1:ℕ)•` are ordinary. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW**
Top risks: none HIGH.
Recommended mitigations: none required.

---

### Mathlib search-status: `PadicLFunctions.FtildeA`

[A] Lean-Finder       n/a: LSP/MCP Lean-Finder not available in this environment
                      (recorded n/a per `mathlib-search.md`); compensated by [D] grep over the
                      actual mathlib source tree at `.lake/packages/mathlib/Mathlib/`.
[B] Loogle            `PowerSeries.subst PowerSeries.log _` / `_ - PowerSeries.subst _ _ + _ • _`
                      — n/a (LSP unavailable); emulated via [D] source grep. The relevant mathlib
                      decls `PowerSeries.logOf`/`PowerSeries.log` were located directly.
[C] LeanSearch        "antiderivative power series log of unit factor p-adic L-function residue"
                      — n/a (LSP unavailable); covered by the Phase-3 WebSearch channels #1–#4.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib`:
                      • `PowerSeries.log` / `logOf` → **HIT**: `Mathlib/RingTheory/PowerSeries/Log.lean`
                        — `log A = mk fun n => if n=0 then 0 else algebraMap ℚ A ((-1)^(n+1)/n)` (≡ project `formalLog`),
                        `logOf f = (log A).subst (f - 1)` (≡ project `(formalLog).subst (uA K a − 1)` since
                        `constantCoeff (uA K a) = 1`).
                      • `extLog` / `iwasawaLog` / `branchLog` → **NO HIT** (project-specific).
                      • `padicLog` / `Padics/*Log*` → **NO HIT**: mathlib has **no p-adic logarithm**
                        (no `Padics/Log.lean`; the lone `grep -l` on `ProperSpace.lean` was a
                        substring false positive — the identifier `padicLog` is absent there).
                      • `Coleman` / `antideriv` / `MahlerTransform` / `measureToPowerSeries` / `FtildeA`
                        → **NO HIT** (no measure-attached-power-series / antiderivative object).
[E] Name pattern      grep for `FtildeA`/`Ftilde`/`F_tilde` in mathlib — no decl named anything like it.

Searched for both:
  - the user's current form (the 3-term `C(−extLog) − subst(log,uA−1) + (a−1)•log`) — **not in mathlib**;
  - the literature-standard form — there is no separately-named `F̃_a`; its *ingredients*:
    `PowerSeries.log` / `PowerSeries.logOf` are **in mathlib**; the p-adic `extLog` and the
    cofactor `uA` are **not** (the latter is itself NO-composable, per its sibling report).

Concluded: **found building blocks** —
`PowerSeries.log` and `PowerSeries.logOf` (`Mathlib/RingTheory/PowerSeries/Log.lean:42,82`)
supply exactly the two power-series terms; the third term `C(−extLog p a)` is a
project-local constant with **no mathlib counterpart** (mathlib has no p-adic logarithm).
The assembled `FtildeA` is not a mathlib decl in any form.

---

### Call sites — `PadicLFunctions.FtildeA`

Internal use count (within project, **excluding** the declaring file `ResidueZeta.lean`): **K = 0.**
External-to-file callers: **0 distinct files.**

A repo-wide `grep -rn "FtildeA" projects/ --include="*.lean"` returns **45 hits, every one
of them inside `ResidueZeta.lean`** (lines 469, 479–488, 529–617, 869–986, 1001–1033,
1325–1502, 1595). No other project file references `FtildeA`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none outside `ResidueZeta.lean`) | — |

In-file uses (declaring file `ResidueZeta.lean`): the antiderivative is consumed by the
theorems `constantCoeff_FtildeA` (479), `one_add_mul_derivative_FtildeA` (529),
`norm_coeff_FtildeA_le` (869), `summable_seriesEval_FtildeA` (905),
`seriesEval_FtildeA_at_root` (1325), `sum_seriesEval_FtildeA` (1481), and the final
residue assembly (1595) — i.e. the entire `section mass` `∫x⁻¹μ_a` computation.

Inline-derivation grep (was an equivalent re-derived elsewhere without `FtildeA`?):
**no** — `F̃_a` is used only here, but its *ingredients* are: the project re-defines the
formal log as `formalLog` (`FormalPsi.lean`) even though it elsewhere uses mathlib's
`PowerSeries.log` directly (`PadicExp.lean`), and `uA` is the un-named cofactor. So the
*assembly* is unique to `ResidueZeta.lean`; its parts are shared/duplicated.

What the pattern tells us: **K = 0 external uses, lives entirely inside its declaring file,
serving one proof (the residue mass), with mathlib already supplying two of its three
terms** → strong NO-composable signal (a proof-internal assembly, not an exported API
object). Identical posture to its ingredient `uA` (sibling report: NO-composable).

---

### Composition check (Phase 6)

Can `PadicLFunctions.FtildeA` be obtained in ≤3 chained calls from mathlib (plus the
already-existing project objects it is built from)?

**Attempt 1 — substitute mathlib `logOf`/`log` for the two power-series terms.**
Since `constantCoeff (uA K a) = 1` (project `constantCoeff_uA`), mathlib's
`PowerSeries.logOf (uA K a) = (PowerSeries.log K).subst (uA K a − 1)`. And the project's
`formalLog K` is **definitionally the same series** as mathlib's `PowerSeries.log K`
(coefficients `(−1)^{n−1}n⁻¹` vs `algebraMap ℚ K ((−1)^{n+1}/n)`; `K` is a `NormedField`,
hence a `DivisionRing`, hence `Algebra ℚ K` via `DivisionRing.toRatAlgebra`, and
`(−1)^{n−1} = (−1)^{n+1}`). Hence:
```lean
example : FtildeA p K a
    = PowerSeries.C (-(extLog p (a:K)))
      - PowerSeries.logOf (uA K a)
      + (a - 1 : ℕ) • PowerSeries.log K := by
  -- formalLog ≡ PowerSeries.log (same coeffs) and logOf folds the .subst
  simp [FtildeA, PowerSeries.logOf_eq, formalLog_eq_powerSeriesLog, ...]
```
Mathlib decls used: `PowerSeries.logOf`, `PowerSeries.log` (and a coeff-equality glue
`formalLog = PowerSeries.log`). Result: **succeeds** as a definitional rewrite — the two
power-series terms become two direct mathlib calls. Remaining: the constant
`PowerSeries.C (−extLog p (a:K))`, which is a `PowerSeries.C` of a **project-local**
scalar `extLog p (a:K)`.

Conclusion: **COMPOSABLE** (in the NO-composable sense: no *new mathlib lemma* is
warranted). `FtildeA` is the 3-term assembly
`C(−extLog p a) − PowerSeries.logOf (uA K a) + (a−1)•PowerSeries.log K`, in which mathlib
supplies `logOf` and `log` directly. The two non-mathlib ingredients — the scalar
`extLog p (a:K)` and the cofactor `uA K a` — are **themselves project-local and not
separately mathlib-bound** (`uA`'s sibling report is NO-composable; `extLog` is a
project-specific p-adic Iwasawa logarithm absent from mathlib). So the *whole* object is
inherently project-side glue: there is nothing about `FtildeA` to upstream beyond what
`PowerSeries.log`/`logOf` already provide.

(Heuristics check: this is two mathlib calls plus the project's own `extLog`/`uA`, summed
with `−`/`+` — an assembly, not a `by rw; ring_nf; aesop` proof-in-disguise. It does not
meet the bar for a *new* mathlib lemma.)

---

## Verdict: `PadicLFunctions.FtildeA`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): identified as **RJW (Rodrigues Jacinto–Williams,
  arXiv:2309.15692) §7's transient antiderivative `F̃_a`** in the residue-of-ζ_p-at-s=1
  proof (TeX 2268; factored at "eq. tilde F_a"). The source does not name `F̃_a` as a
  standalone object; its *ingredients* (formal log, logarithmic derivative, p-adic log)
  are the named/standard concepts. 4 WebSearch channels + nLab + the source paper;
  ChatGPT MCP and local refs recorded n/a with reasons.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for the assembled object (the
  `extLog` term genuinely consumes the normed/ultrametric/complete `ℚ_p`-algebra
  structure, so no clean weakening exists), but Phase 4c's modern idiom is "compose from
  mathlib `log`/`logOf`", not "ship a generalised `FtildeA`".
- Mathlib search (Phase 5): **found building blocks** — `PowerSeries.log` and
  `PowerSeries.logOf` (`Mathlib/RingTheory/PowerSeries/Log.lean:42,82`) are exactly the two
  power-series terms; the third term's scalar `extLog`/`padicLog` has **no mathlib
  counterpart** (mathlib has no p-adic logarithm). The assembled `FtildeA` is not in
  mathlib in any form.
- Composition check (Phase 6): **COMPOSABLE** — `FtildeA = C(−extLog p a) −
  PowerSeries.logOf (uA K a) + (a−1)•PowerSeries.log K`, two of three terms being direct
  mathlib calls; the rest is project-local glue. No new mathlib lemma warranted.

**Rationale.**
`FtildeA` is a presentation-level bookkeeping antiderivative — RJW §7 writes
`F̃_a = log(T/(1+T)·(1+T)^a/((1+T)^a−1))`, factored into `−log_p(a) − log(u_a) +
(a−1)log(1+T)`, purely to compute the residue mass via `∂F̃_a = F_a`. It has **zero
external call sites** (all 45 references are inside `ResidueZeta.lean`), the source paper
treats it as a transient step rather than a named object, and **two of its three terms are
already in mathlib** as `PowerSeries.logOf (uA K a)` and `(a−1)•PowerSeries.log K` — indeed
this very codebase already imports and uses mathlib's `PowerSeries.log` (in
`PadicExp.lean`). The only ingredient mathlib lacks is the constant `extLog p (a:K)` (the
Iwasawa-branch `log_p`), but that is a *separate* project-specific scalar (no mathlib
p-adic logarithm exists), not something that makes the *assembly* `FtildeA` worth
upstreaming. Every signal — zero external use, transient-in-source, mathlib-supplied log
terms, a project-local residual constant — points the same way: this is proof-internal
glue to keep project-local, not a mathlib contribution. This mirrors the sibling verdict on
its own ingredient `uA` (NO-composable).

**WHY not (refactor-actionable):**
Mathlib has the building blocks for the two power-series terms; the third is a project-local
constant. No new mathlib lemma is warranted, and `FtildeA` itself is not mathlib-bound.

Mathlib building blocks:
- `PowerSeries.logOf` — `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Log.lean:82`
  (with `logOf_eq:85`, `constantCoeff_logOf:87`); `PowerSeries.logOf (uA K a) =
  (PowerSeries.log K).subst (uA K a − 1)` since `constantCoeff (uA K a) = 1`.
- `PowerSeries.log` — `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Log.lean:42`
  (≡ the project's `formalLog`; identical coefficients over the ℚ-algebra `K`).
- `PowerSeries.C` (constant series) — standard.
Non-mathlib (project-local, *not* upstreamable here): the scalar `extLog p (a:K)`
(`projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:286`, the Iwasawa-branch `log_p`,
absent from mathlib) and the cofactor `uA K a` (`ResidueZeta.lean:437`, sibling verdict
NO-composable).

Composition sketch (≤3 mathlib calls; remainder is project-local glue):
```lean
example : FtildeA p K a
    = PowerSeries.C (-(extLog p (a:K)))            -- project-local scalar (Iwasawa log_p)
      - PowerSeries.logOf (uA K a)                 -- mathlib logOf  (uA: project cofactor)
      + (a - 1 : ℕ) • PowerSeries.log K := by      -- mathlib log
  -- formalLog ≡ PowerSeries.log; logOf folds the .subst at uA−1 (constantCoeff (uA K a)=1)
  simp [FtildeA, PowerSeries.logOf_eq, /- formalLog = PowerSeries.log -/]
```

Call sites in our project (from Phase 6.0): **K = 0 external; 45 internal** to
`ResidueZeta.lean`.
Refactor plan: **mathlib action = none — do NOT submit `FtildeA` to mathlib.** It is a
legitimate *project-local* antiderivative used in exactly one proof. Because it has zero
external consumers, no cross-file refactor is needed. If desired purely for
mathlib-hygiene inside the file, the two log terms can be re-expressed against mathlib's
`PowerSeries.logOf`/`PowerSeries.log` (the project already uses `PowerSeries.log` in
`PadicExp.lean`), and the duplicate `formalLog` definition could be retired in favour of
`PowerSeries.log` — but this is optional file hygiene, not a mathlib-quality obligation.
The actionable mathlibability conclusion is: **not mathlib-bound** (the log terms are
composable from mathlib; the residual `extLog` constant is a separate, project-specific
object).
Next action: keep `FtildeA` private/local to `ResidueZeta.lean`; do not open a mathlib PR
for it. (Optional hygiene: fold its two log terms onto mathlib `logOf`/`log`.)

**Note on the alternative (BORDERLINE).** One could argue that, because the composition
also relies on the *project-local* `extLog`/`uA` (not on mathlib alone), the strict
"≤3 *mathlib*-call" composition bar isn't met and the verdict should be BORDERLINE
("is this proof-internal antiderivative worth promoting to a named mathlib object?"). I
rejected that for the same reasons the sibling `uA` report rejected its own BORDERLINE
alternative: (a) the source paper treats `F̃_a` as a transient step, not a named object;
(b) mathlib already supplies the only genuinely-reusable parts (`log`/`logOf`), and the
residual `extLog` is a *separate* mathlibability question (the project-specific p-adic
Iwasawa logarithm), not part of `FtildeA`'s; (c) zero external use + transient-in-source +
mathlib-supplied log terms all reinforce "project-local glue" over "novel exported object."
The refactor-actionable conclusion (keep local; optionally fold onto `logOf`/`log`) is
concrete and needs no human judgment.

---

## Next step

Keep `PadicLFunctions.FtildeA` as a private/local definition in `ResidueZeta.lean`; **do
not open a mathlib PR**. Its two logarithmic-power-series terms are exactly mathlib's
`PowerSeries.logOf (uA K a)` and `(a−1)•PowerSeries.log K`
(`Mathlib/RingTheory/PowerSeries/Log.lean`), and its third term is a project-local
constant (`extLog p (a:K)`, the Iwasawa-branch `log_p`, which mathlib does not have). No
mathlib-side refactor is required since `FtildeA` has zero external call sites; optional
in-file hygiene could fold the two log terms onto mathlib's `logOf`/`log` and retire the
duplicate `formalLog`, but this is not necessary for mathlib-quality purposes.
