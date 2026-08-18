# `/mathlibable` report — `PadicLFunctions.padicExp_padicLog`

**Final verdict: `YES-add-as-is`** (ships as part of the `padicExp` / `padicLog` API batch).

Mode A, full 10-phase workflow, exhaustive literature sweep. ChatGPT-MCP and the
Loogle/LeanSearch/Lean-Finder MCP servers are **not configured in this
environment**; those channels are recorded `n/a` with reason and compensated by
deeper WebSearch + WebFetch (literature) and deeper grep + name-pattern search
over the local mathlib checkout (mathlib).

---

### Baseline (Phase 0)
- lake build:               **not re-run; reasoned from source** (per task note: build stale/slow; Phase-0 source-fallback used)
- decl `PadicLFunctions.padicExp_padicLog`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:935`
- kind:                      theorem
- has sorry:                 no (proof body lines 935–946 are sorry-free)
- module docstring summary:  the p-adic exponential `exp(x)=∑xⁿ/n!` and logarithm `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n` on a complete ultrametric `ℚ_[p]`-algebra field; they are mutually-inverse isometries on the matched ball, realising RJW Lemma 5.14 (cf. Washington §5.1, Cassels §12).

---

### Statement (Phase 1)

`PadicLFunctions.padicExp_padicLog` is a theorem stating the following:

Let `L` be a field that is complete with respect to an **ultrametric** norm and is
a normed `ℚ_[p]`-algebra (so `L` is a complete nonarchimedean field of residue
characteristic `p`). For `x ∈ L` with `x − 1` in the open convergence ball
`‖x − 1‖^{p−1} < p⁻¹` (i.e. `‖x−1‖ < p^{−1/(p−1)}`), the p-adic exponential and
p-adic logarithm are inverse on the matched ball:
`exp(log x) = x`. This is one half of the statement that `exp` and `log` are
mutually-inverse bijections between the additive ball `‖·‖ < p^{−1/(p−1)}` and the
multiplicative ball `1 + {‖·‖ < p^{−1/(p−1)}}` (the other half is the sibling
`padicLog_padicExp`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / base prime.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]`,
  `[CompleteSpace L]` — a complete ultrametric (nonarchimedean) normed field that
  is a `ℚ_[p]`-algebra. This is the abstract "complete nonarchimedean field of
  residue char `p`" hypothesis cluster.
- `padicExp p`, `padicLog p : L → L` — the junk-total series functions
  `∑ (n!)⁻¹•xⁿ` and `∑ (−1)ⁿ(n+1)⁻¹•(x−1)ⁿ⁺¹`.

Hypotheses (Lean side):
- `hx : InExpBall p (x − 1)`, unfolding to `‖x − 1‖^{p−1} < (p:ℝ)⁻¹` — membership of
  `x − 1` in the open convergence ball (rpow-free formulation of `‖x−1‖ < p^{−1/(p−1)}`).

Conclusion (math): `exp(log x) = x` on the matched ball.

Conclusion (Lean): `padicExp p (padicLog p x) = x`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named-after-the-classical-result inversion theorem (RJW Lem 5.14 /
Washington Prop 5.3 route) and one of the project's primary R5.E-cluster goals — it
feeds the multiplicativity of `log` (`padicLog_mul`) and the `x^s := exp(s·log x)`
construction `onePAdicPow`. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is theorem, not def. (Body is a multi-line `rw … ; ring` proof composing
`master_bridge`, `exp_subst_log`, `eval_oneAddX`; not a glue/`rfl` lemma.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential logarithm inverse exp(log x)=x convergence ball" | yes | `exp`/`log` mutually inverse on `‖·‖<p^{−1/(p−1)}`; `log` on `‖z−1‖<1` | PlanetMath, KConrad, MIT notes, Wikipedia all agree on radius `p^{−1/(p−1)}` |
| 2 | WebSearch (general form) | "…Iwasawa / complete nonarchimedean field… generality" | yes | `log∘exp = id` on `p'·G_a⁺`, `exp∘log = id` on `1+p'·G_a⁺` — stated for general complete nonarch. fields | confirms the result is not ℚ_p-specific; abstracted over the additive group of a complete valued field |
| 3 | WebSearch (named-after / aliases) | "p-adic logarithm exponential mutually inverse isometry 1+pZ_p Washington cyclotomic fields" | yes | `log` is an **isometry** `1+𝔪 ≅ 𝔪` and inverse to `exp` | matches the project's `norm_padicExp_sub_padicExp` isometry + this inversion; Washington is the cited textbook |
| 4 | ChatGPT MCP | "standard form, generality, historical evolution of p-adic exp(log)=x" | **n/a** | — | **no ChatGPT MCP server configured in this environment**; compensated by extra WebSearch (#1–3, #9–10) + 2 WebFetch (#5, #6) |
| 5 | WebFetch — Wikipedia "P-adic exponential function" | precise statement + generality | yes | verbatim: *"For z in the domain of exp_p, we have exp_p(log_p(1+z)) = 1+z and log_p(exp_p(z)) = z."* radius `p^{−1/(p−1)}` for exp, `‖z−1‖<1` for log | textbook treatment stated over `C_p`; exactly `padicExp_padicLog` (and its sibling) |
| 6 | WebFetch — KConrad "Infinite series in p-adic fields" | theorem #, radius, field generality | partial (binary PDF; could not extract text) | — (radius/inverse facts already confirmed by #1, #5) | KConrad notes are a standard exposition; the inversion + radius are corroborated by the readable sources |
| 7 | Local references | `refs/PadicLFunctions/` + `.mathlib-quality/references/` | **n/a** | — | shared store `AINTLIB/refs/PadicLFunctions/` is **empty** (no PDFs); project has no `references/` dir |
| 8 | nLab | "p-adic exponential / logarithm; exponential map" | partial | nLab "exponential map" + formal-group `log` as the unique iso to `G_a`, `exp` its inverse | confirms the abstract formal-group framing (exp inverts log); no dedicated p-adic-analytic page |
| 9 | nCatLab / categorical | (formal group `log`/`exp` inverse) | yes | formal logarithm = unique iso `F → G_a`; exponential is its inverse (arXiv 1201.4023, 1907.06437) | the formal-group viewpoint matches the project's `exp_subst_log` / `log_subst_exp_sub_one` formal identities |
| 10 | Stacks Project | (p-adic exp/log analytic inversion) | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; Stacks has no p-adic-analytic exp/log inversion |
| 11 | MathOverflow / Math.SE | "p-adic logarithm exp inverse complete nonarchimedean field generality" | yes | confirms `exp`/`log` inverse on the matched ball for fields complete under a nonarch. absolute value with residue char `p` | corroborates the maximal analytic generality |
| 12 | recent arXiv (≤5 yr) | "p-adic exp/log inverse ultrametric / nonarchimedean field isometry" | yes | rigid-spaces paper (arXiv 2012.07918) states *"exp ∘ log = id and log ∘ exp = id"* abstractly; BGR & Schikhof are the standard monographs | the general-field statement (BGR *Non-Archimedean Analysis* §; Schikhof *Ultrametric Calculus*) is the literature anchor for the Lean generality |

### Literature summary (Phase 3)

Concept identified as: **the p-adic exponential–logarithm inversion** — `exp` and
`log` are mutually-inverse (and isometric) bijections between the additive ball
`‖x‖ < p^{−1/(p−1)}` and the multiplicative ball `1 + {‖x‖ < p^{−1/(p−1)}}` of a
complete nonarchimedean field of residue characteristic `p`. Classical;
appears in Koblitz (*p-adic Numbers…*, ch. IV), Washington (*Cyclotomic Fields*
§5.1), Cassels (*Local Fields* §12), Neukirch, BGR (*Non-Archimedean Analysis*),
Schikhof (*Ultrametric Calculus*), KConrad's notes, and Wikipedia.

Sources agree on the standard form: **yes**. The half `exp(log x) = x` is exactly the
declaration; Wikipedia states it verbatim (`exp_p(log_p(1+z)) = 1+z`).

Most general standard form: for **any** field `L` complete with respect to a
nontrivial nonarchimedean absolute value extending the `p`-adic one (residue char
`p`), `exp` and `log` are inverse isometries between the two matched balls of radius
`p^{−1/(p−1)}`. The result is **not** ℚ_p-specific — the modern formulation abstracts
over the additive group / valued field.

Generality dimensions where the literature varies:
  - **Underlying field**: ranges from `ℚ_p` (elementary texts) → a fixed finite
    extension → `C_p` (Wikipedia/Koblitz) → **any complete nonarchimedean field of
    residue char `p`** (BGR/Schikhof; rigid-geometry literature). The most general
    standard form is the last one. The Lean `L` (complete ultrametric normed
    `ℚ_[p]`-algebra field) realises exactly this maximal analytic generality.
  - **Convergence radius**: uniformly `p^{−1/(p−1)}` across all sources (the project
    states it rpow-free as `‖x‖^{p−1} < p⁻¹`, which is equivalent).

Disagreement with the literature: **none**. The Lean statement is the literature's
`exp(log x) = x` at the literature's most general analytic level.

---

### Generality analysis — `PadicLFunctions.padicExp_padicLog` (Phase 4)

Literature-standard form (from Phase 3): `exp(log x) = x` for `x ∈ 1 + 𝔪` (matched
ball, radius `p^{−1/(p−1)}`) over **any** complete nonarchimedean field of residue
char `p`.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | normed field | nonarchimedean field (complete valued field) | NO | exp/log are field-valued series; the field structure is genuinely used (inverses `(n!)⁻¹`, `(n+1)⁻¹`). Literature also takes a field. |
| 2 | `[IsUltrametricDist L]` | ultrametric (nonarchimedean) norm | nonarchimedean absolute value | NO | the whole convergence/inversion theory is nonarchimedean; the proof uses ultrametric Fubini (`Summable.tsum_comm`) and `HasSum.mul_of_nonarchimedean`. Archimedean ⇒ the radius/inversion is a different (real/complex) theorem. |
| 3 | `[CompleteSpace L]` | complete | complete | NO | the value of the series requires completeness; standard hypothesis. |
| 4 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_[p]`-algebra | residue char `p`, contains `ℚ_p` | NO (already maximal in the analytic setting) | exactly pins "complete nonarchimedean field of residue char `p`" — the literature's general hypothesis. Weakening to a bare `ℚ`-algebra would lose the `p`-adic valuation bounds (Legendre) that the convergence ball depends on. |
| 5 | `hx : InExpBall p (x−1)` (`‖x−1‖^{p−1}<p⁻¹`) | open ball radius `p^{−1/(p−1)}` | open ball radius `p^{−1/(p−1)}` | NO | this is the exact (sharp) radius of mutual convergence; cannot be widened. |

#### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: **0**.
Proposed restatement: none — the typeclass cluster `[NormedField L] [NormedAlgebra
ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` is precisely the modern abstraction
of "complete nonarchimedean field of residue characteristic `p`", which is the
literature's most general analytic setting. The radius is the sharp one.
Cost of restatement: n/a.

#### 4c. Modern-idiom check — Bourbaki 2.0

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" preambles → typeclasses? | **already done** | the field-completeness-ultrametric-algebra hypotheses are *already* typeclasses, not bundled hyps | composes with all of mathlib's `NormedField`/`IsUltrametricDist` API |
| 2 | sequences/metric → filters/topological? | no | series already use `Summable`/`tsum` (filter-based) | n/a — already filter-idiomatic |
| 3 | construction → universal-property class? | no | this is an equation between two analytic functions, not a constructed object | n/a |
| 4 | set+closure predicate → bundled substructure? | no | `InExpBall` is a ball-membership `Prop`, the natural form | n/a |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | already the maximal nonarchimedean field setting; cannot weaken to a (semi)ring (needs `(n!)⁻¹`, completeness, ultrametric) | n/a |
| 6 | 1-categorical → higher-categorical? | no | analytic identity over a field; no categorification target | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general group/monoid? | no | the conclusion is an equation in `L`; the only index is the abstract field element `x` | n/a |

#### 4c verdict
Modern idiom available: **no**. The declaration is already stated in the contemporary
mathlib idiom (typeclass hypotheses, `tsum`/`Summable`, the abstract nonarchimedean
field). One-line reason: it is the maximally-general analytic statement in the
existing mathlib typeclass language — there is no further-modernising move.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       — **n/a: AI search MCP server not configured in this environment**
[B] Loogle (`lean_loogle`) — **n/a: Loogle MCP not configured** (compensated by D/E grep over the pinned mathlib checkout)
[C] LeanSearch (`lean_leansearch`) — **n/a: LeanSearch MCP not configured**
[D] Grep mathlib src  — terms: `padicExp`, `padicLog`, `p-adic exp/log`, `expSeries`, `NormedSpace.exp`, `log.*exp`, `exp.*log`, `subst.*log` — see below — **no hit for any p-adic exp/log**
[E] Name pattern (local grep) — `exp_log`, `log_exp`, `exp_subst`, `log_subst`, `_padic` exp/log inverse — **no hit for a nonarchimedean exp/log inverse**

Searched for both:
  - the user's current form `padicExp (padicLog x) = x` over a complete ultrametric field;
  - the literature-standard general form (any complete nonarchimedean field).

Detailed grep findings (over `./.lake/packages/mathlib/Mathlib/`):
  - **No `padicExp` / `padicLog` / p-adic exponential or logarithm exists anywhere
    in mathlib** — whole-tree grep for `padicExp|padicLog|p.?adic.?exp|p.?adic.?log`
    returns nothing. `NumberTheory/Padics/` contains only `padicValNat`, `Nat.log`,
    and `WithZero.exp`/`Valuation.exp` (valuation notation) — unrelated.
  - Mathlib's **Banach-algebra exponential** `NormedSpace.exp` /
    `NormedRing.exp` (`Analysis/Normed/Algebra/Exponential.lean`) is the
    **Archimedean** exponential — it converges on the whole algebra via the *real*
    factorial bound and has **no logarithm at all** (grep for `log` in that file is
    empty). It is not the p-adic exp and has no inverse-pair lemma; mathematically
    distinct.
  - The `exp_log` / `log_exp` lemmas in `Analysis/` are all the **real/complex**
    `Real.exp_log : exp (log x) = x` (for `x>0`) / `Complex.log_exp` — the
    Archimedean inversion, unrelated to the p-adic one.
  - Mathlib has the **formal power series** `PowerSeries.exp`, `PowerSeries.log`,
    `logOf`, and a `subst`/`HasSubst` API (`RingTheory/PowerSeries/Exp.lean`,
    `Log.lean`), including `logOf_one_add_X : logOf (1+X) = log A`. But it does
    **not** contain the formal identity `(exp A).subst (log A) = 1 + X` nor
    `(log A).subst (exp A − 1) = X` — these are the project's own contributions
    (`exp_subst_log`, `log_subst_exp_sub_one`). And those are *formal* (`ℚ`-algebra
    power-series) identities — they are **not** the analytic theorem
    `padicExp(padicLog x) = x` over a complete ultrametric field. They are inputs to
    this theorem's proof, not the theorem itself.

Concluded: **not in mathlib** (all available methods exhausted — D/E grep over the
pinned mathlib tree under both the user's form and the literature-standard general
form; A/B/C MCP servers unavailable and recorded `n/a`). Mathlib has neither the
p-adic exp/log functions nor any analytic exp/log inversion over a nonarchimedean
field.

---

### Call sites — `PadicLFunctions.padicExp_padicLog` (Phase 6.0)

Internal use count: **3** (within the project, excluding the declaring line 935).
External-to-file callers: 0 distinct *other* files (all uses are in `PadicExp.lean`
itself, but in **distinct downstream results**, not the declaration's own proof).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| PadicExp.lean:988 | `have hea : padicExp p a = x := padicExp_padicLog p hx` (inside `padicLog_mul`) |
| PadicExp.lean:989 | `have heb : padicExp p b = y := padicExp_padicLog p hy` (inside `padicLog_mul`) |
| PadicExp.lean:1157 | `refine padicExp_padicLog (L := ℚ_[p]) p ?_` (inside the `pZpExp`/`onePAdicPow` identification, `hκone`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`padicExp_padicLog`?): **(none)** — no site re-proves `exp(log x)=x` by hand;
every consumer goes through this lemma.

Signal (per the call-sites table): **K = 3 internal uses, no inline re-derivation →
real API; consumers depend on it → YES-* bucket.** Concretely it is the engine of
`padicLog_mul` (multiplicativity of the p-adic log, RJW Lem 5.14 Step C) and of the
`x^s = exp(s·log x)` ⇄ `PadicInt.onePAdicPow` identification — both primary project
goals.

### Composition check (Phase 6)

Can `padicExp_padicLog` be derived from mathlib in ≤3 chained calls?

Attempt 1: there is no mathlib `padicExp` / `padicLog` to compose at all, so there is
nothing to chain. The proof genuinely requires: `padicExp_eq_tsum_coeff` +
`padicLog_eq_tsum_coeff` (rewrite both as power-series evaluations) → the
**master evaluation bridge** `master_bridge` (regroup the double series by
ultrametric Fubini `Summable.tsum_comm`, with `summable_prod_family` providing the
ℕ×ℕ summability) → the **formal identity** `exp_subst_log : (exp).subst(log)=1+X`
→ `eval_oneAddX` (evaluate `1+X` at `x−1` to get `x`) → `ring`. This is a multi-step
analytic proof (double-series rearrangement + a formal-power-series coefficient
recursion), **not** a 1–3 mathlib-call composition.
  - Mathlib decls used: `Summable.tsum_comm`, `HasSum.mul_of_nonarchimedean`,
    `PowerSeries.subst`/`HasSubst`, `derivative_subst`, `derivative_exp` — but only
    as *building blocks deep inside* the proof, not as a short surface composition.
  - Result: **fails** (no short composition; this is a real theorem).

Conclusion: **NOT-COMPOSABLE**.

---

## Verdict: `PadicLFunctions.padicExp_padicLog`

**Category:** `YES-add-as-is` (group with the surrounding `padicExp`/`padicLog` API).

**Evidence:**
- Literature search (Phase 3): exhaustive sweep (10 effective channels; ChatGPT-MCP
  + Loogle/LeanSearch/Lean-Finder unavailable, recorded `n/a` and compensated).
  Universal agreement: `exp(log x)=x` on the matched ball, radius `p^{−1/(p−1)}`, is
  *the* standard p-adic exp/log inversion (Wikipedia states it verbatim; Koblitz,
  Washington, Cassels, BGR, Schikhof). The general standard form is over any
  complete nonarchimedean field of residue char `p`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — the typeclass cluster is the
  modern abstraction of the literature's most general analytic setting; the radius is
  sharp; 0 weakenings; no modern-idiom move available (4c = no).
- Mathlib search (Phase 5): **not in mathlib** — no p-adic exp/log of any kind exists;
  the Banach `NormedSpace.exp` is Archimedean and logarithm-free; the only `exp_log`
  in mathlib is the real/complex one; the formal `PowerSeries.exp/log` lacks even the
  formal `exp(log(1+X))=1+X` identity, and in any case is a different (formal) object.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine multi-step analytic
  proof (ultrametric Fubini + formal-coefficient recursion), 3 real internal
  consumers, no inline re-derivation.

**Rationale (1–2 paragraphs):**

`padicExp_padicLog` is the analytic half of the classical fact that the p-adic
exponential and logarithm are mutually-inverse isometries between the additive and
multiplicative balls of radius `p^{−1/(p−1)}`. Every literature channel returns it as
a standard, named result (Wikipedia quotes `exp_p(log_p(1+z)) = 1+z` verbatim; it is
Washington §5.1 / Koblitz ch. IV / Cassels §12 territory). Mathlib, however, has **no
p-adic exponential or logarithm at all** — its only exponential infrastructure is the
*Archimedean* Banach-algebra `NormedSpace.exp` (which converges on the whole algebra
via the real factorial bound and has no logarithm), and its only `exp(log x)=x` lemma
is the *real/complex* `Real.exp_log`. The p-adic theory (the sharp `p^{−1/(p−1)}`
convergence ball, Legendre's valuation bound on `n!`, ultrametric summability) is
entirely absent. So this is a real gap, not a reskin of existing mathlib.

The Lean statement is also already at the right level of generality and in the right
idiom: it is stated for an abstract complete ultrametric normed `ℚ_[p]`-algebra field
— precisely the literature's most general analytic setting (BGR / Schikhof state it
for any complete nonarchimedean field of residue char `p`), with the sharp radius and
filter-based `tsum`/`Summable` machinery. Phase 4 finds zero weakenings and Phase 4c
finds no modern-idiom improvement, so `YES-add-as-is` (not `YES-but-generalise-first`)
is correct. The proof is a genuine multi-step analytic argument (double-series
rearrangement via ultrametric Fubini, plus a formal-power-series coefficient recursion
for `exp(log(1+X))=1+X`), and the lemma is load-bearing API — used 3× downstream to
prove multiplicativity of `log` and to identify `x ↦ exp(s·log x)` with the continuous
character `PadicInt.onePAdicPow`. It is exactly the kind of canonical result mathlib is
missing.

**WHY add it (refactor-actionable detail):**

- *New mathematical content mathlib is missing:* the p-adic exponential/logarithm
  inversion. **Mathlib has zero p-adic analytic exp/log** — confirmed by a whole-tree
  grep (no `padicExp`/`padicLog`/`p-adic exp` anywhere). The naming gap is concrete:
  `NumberTheory/Padics/` has `padicValNat` and `Nat.log` but no analytic `exp`/`log`;
  `Analysis/Normed/Algebra/Exponential.lean` provides `NormedSpace.exp` with **no
  `log`** companion (the file has no `log` token at all). There is no
  `NumberTheory/Padics/Exponential.lean` (or analogue). This theorem (with its
  siblings `padicLog_padicExp`, `padicExp_add`, `norm_padicExp_sub_padicExp`,
  `norm_padicLog`, `padicLog_mul`) would seed that missing file.
- *How it composes with mathlib's existing API:* it sits directly on top of
  mathlib's brand-new `PowerSeries.exp`/`PowerSeries.log`/`subst` API
  (`RingTheory/PowerSeries/{Exp,Log}.lean`) — turning those *formal* series into
  honest *analytic* functions on a nonarchimedean field, and connecting to
  `IsUltrametricDist`, `Summable.tsum_comm`, `HasSum.mul_of_nonarchimedean`, and the
  `Padic`/`PadicInt` valuation API. Once present, mathlib's continuous-character /
  Iwasawa-theory developments (`AddChar`, `PadicInt`) gain a canonical `x^s` and the
  `1+pℤ_p ≅ ℤ_p`-via-`log` isometry for free.

Proposed mathlib location: `Mathlib/NumberTheory/Padics/Exponential.lean` (new file),
or alongside the analytic p-adic material in `Mathlib/NumberTheory/Padics/`.
Proposed PR title: `feat(NumberTheory/Padics): the p-adic exponential and logarithm`.
PR grouping (REQUIRED): **do NOT PR `padicExp_padicLog` alone.** It is meaningless
without the definitions and is one of a tight cluster that should ship together:
  - the defs `PadicLFunctions.padicExp`, `PadicLFunctions.padicLog`, `InExpBall`;
  - convergence/summability: `summable_padicExp_terms`, `summable_padicLog_terms`;
  - the isometry results `norm_padicExp_sub_padicExp`, `norm_padicExp_sub_one`,
    `norm_padicLog`;
  - the functional equations `padicExp_add`, `padicLog_mul`;
  - **both** inversions `padicExp_padicLog` *and* `padicLog_padicExp`;
  - the formal-series engine `exp_subst_log`, `log_subst_exp_sub_one`,
    `master_bridge` (the formal identities `exp(log(1+X))=1+X` / `log(1+(exp−1))=X`
    are *themselves* mathlib-worthy additions to `RingTheory/PowerSeries/Log.lean`
    and could be a **separate, earlier** PR that this analytic file then imports).

Pre-PR checklist before opening:
  - [ ] Split the formal-power-series identities (`exp_subst_log`,
        `log_subst_exp_sub_one`) into a prior `RingTheory/PowerSeries/Log.lean` PR —
        they generalise verbatim to any `[CommRing A] [Algebra ℚ A]` and are reusable
        beyond the p-adic setting.
  - [ ] `/generalise PadicLFunctions.padicExp_padicLog` — confirm no easy further
        weakening (expected: none; already maximal — but run it to be safe).
  - [ ] `/cleanup projects/PadicLFunctions/PadicLFunctions/PadicExp.lean
        PadicLFunctions.padicExp_padicLog` — full audit + diff gates on the whole
        cluster.
  - [ ] Pick a mathlib reviewer from recent `Mathlib/NumberTheory/Padics/` and
        `Mathlib/RingTheory/PowerSeries/` commits.

---

## Next step

PR-group this with the rest of the `padicExp`/`padicLog` API rather than alone. First
land the two formal-power-series identities (`exp_subst_log`,
`log_subst_exp_sub_one` — generalised to any `ℚ`-algebra) into
`Mathlib/RingTheory/PowerSeries/Log.lean`; then run
`/generalise PadicLFunctions.padicExp_padicLog` (expected: already maximal) and
`/cleanup` on the cluster; then open `feat(NumberTheory/Padics): the p-adic
exponential and logarithm` adding the defs, convergence, isometry, functional
equations, and both inversions (`padicExp_padicLog` + `padicLog_padicExp`) as one
coherent file.
