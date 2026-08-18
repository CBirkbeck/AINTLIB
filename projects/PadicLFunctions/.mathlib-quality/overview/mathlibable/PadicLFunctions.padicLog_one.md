# `/mathlibable` report — `PadicLFunctions.padicLog_one`

**Final verdict: `BORDERLINE-needs-human`** — the lemma is a standard, correct,
load-bearing companion (`log_p 1 = 0`) of the project-local `p`-adic logarithm.
Its mathlib-worthiness is entirely *derivative* of the host definition
`PadicLFunctions.padicLog`, which mathlib does **not** have; and the workspace
carries a **second, near-duplicate** `padicLog` / `padicLog_one` over `ℚ_[p]`
in a different project. Both facts are judgment calls the skill cannot settle
alone. See the numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               build **not re-run** (stale/slow per task note); reasoned from source.
- decl `PadicLFunctions.padicLog_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:388`
- kind:                      theorem (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "The `p`-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!`, `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n` on a complete ultrametric normed `ℚ_[p]`-algebra field; realises RJW Lemma 5.14 (Cassels §12, Washington *Cyclotomic Fields* §5.1).

Source (exact):

```lean
omit [IsUltrametricDist L] [CompleteSpace L] in
@[simp] theorem padicLog_one : padicLog p (1 : L) = 0 := by
  rw [padicLog]
  simp
```

Host definition (`PadicExp.lean:384`):

```lean
/-- E4: the `p`-adic logarithm `log(x) = ∑ (−1)^{n+1}(x−1)^n/n`, junk-total
(meaningful for `‖x − 1‖ < 1`). -/
noncomputable def padicLog (x : L) : L :=
  ∑' n : ℕ, (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1))
```

Ambient context (`PadicExp.lean:31–33`):

```lean
variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]
```

---

### Statement (Phase 1)

`PadicLFunctions.padicLog_one` is a theorem stating:

> For the `p`-adic (Iwasawa) logarithm `log_p` on a complete ultrametric normed
> `ℚ_[p]`-algebra field `L`, defined by the convergent power series
> `log_p(x) = ∑_{n≥0} (−1)ⁿ (n+1)⁻¹ (x−1)^{n+1} = ∑_{m≥1} (−1)^{m+1} (x−1)^m / m`,
> the value at the unit `x = 1` is `log_p(1) = 0`.

The proof is the immediate one: at `x = 1` every summand has the factor
`(x−1)^{n+1} = 0^{n+1} = 0` (since `n+1 ≥ 1`), so the whole `tsum` collapses to
`0`. (`rw [padicLog]; simp` — `simp` evaluates `(1−1)^{n+1} = 0` termwise and
sums to `0`; note the two side typeclasses `IsUltrametricDist`/`CompleteSpace`
are `omit`ted because the fact holds for the raw `tsum` with no convergence
input.)

Variables / typeclasses (Lean side):

- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L]` — a normed `ℚ_[p]`-algebra
  field (the value field of the logarithm).
- (`[IsUltrametricDist L] [CompleteSpace L]` are in the section `variable` block
  but **`omit`ted** from this lemma — not needed.)

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): `log_p(1) = 0`.

Conclusion (Lean): `padicLog p (1 : L) = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step "value at the base point" companion lemma of a logarithm
definition (analogue of `Real.log_one`); not itself a structure, a named
theorem, or a `## Main results` headline. (The *host* `padicLog` is the BIG
object; this lemma rides along with it.)

(Note: literature width was EXHAUSTIVE regardless — BIG/SMALL is framing only.)

### One-line check (Phase 2b)

Body line count: kind is **theorem**, not `def`/`abbrev`/`structure`.
One-liner verdict: **n/a — kind is theorem.**
The Phase-2b def-exemption table does not apply. (For the record the *proof*
body is two trivial tactic lines, `rw [padicLog]; simp`; this strengthens the
"trivial-companion" reading carried into Phase 7, but the one-line *definition*
gate is about defs, not lemmas.)

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic logarithm log_p(1)=0 definition Iwasawa power series" | yes | `−log_p(1−x)=∑_{n≥1} xⁿ/n`; `log_p(xy)=log_p x+log_p y`; **"x=0 ⇒ log 1 = 0"** | Wikipedia *p-adic exponential function*, MIT 18.785 PS10; Iwasawa-log extension sets `log_p(p)=0` |
| 2 | WebSearch (general form) | "p-adic logarithm definition nonarchimedean field log(1) equals zero properties" | yes | `log_p` on a complete nonarchimedean field; `\|log_p x\|=\|x−1\|` near `1` | PlanetMath, Leiden Ch.8, Michigan Appendix 2 — convergence on the unit ball is the only requirement |
| 3 | WebSearch (named-after / aliases) | "logarithm log 1 = 0 standard property real complex p-adic any field" | yes | `log_a 1 = 0` for **every** base; for char-0 fields with an ultrametric abs. value, defined by the same series, "converges at x=0 so log 1 = 0" | Confirms `log 1 = 0` is base-independent and holds for the formal-power-series / ultrametric definition |
| 4 | ChatGPT MCP | (intended: "standard def of the p-adic log, its generality, historical evolution") | **n/a** | — | No ChatGPT/Codex MCP is configured or authenticated on this machine (`mcp-needs-auth-cache.json` only; old plugin `.mcp.json` not wired). Recorded n/a; compensated with extra WebSearch + WebFetch + 5 in-repo named references (Washington, Iwasawa, Cassels, Keith Conrad, MIT/Dav). |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | **n/a** | — | Neither directory exists in this checkout (PDFs are local-only, per CLAUDE.md, and absent here). The module docstring names the sources directly: RJW Lem 5.14, Cassels §12, Washington §5.1. |
| 6 | nLab | WebSearch "nLab p-adic logarithm/exponential nonarchimedean" | partial | only inside *p-adic Hodge theory* | nLab has **no dedicated `p`-adic-logarithm page**; the concept appears only as machinery within p-adic Hodge theory. Not a categorical primitive. |
| 7 | nCatLab (categorical) | (same as #6) | **n/a** | — | Not a categorical concept — an analytic function on a normed field. No universal-property formulation in the literature. |
| 8 | Stacks Project | concept = "p-adic logarithm" | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; it is non-archimedean analysis. Stacks does not cover it. |
| 9 | MathOverflow / MSE | (covered transitively by #1–#3) | yes (transitive) | same series; same `log 1 = 0` | The standard form is unambiguous across ≥5 independent expository sources (Wikipedia, PlanetMath, Keith Conrad notes, MIT lecture notes, textbooks); no MO disagreement to resolve. |
| 10 | recent arXiv (≤5y) | surfaced under #1/#2 | yes | `log_p(1+x)=∑(−1)^{n+1}xⁿ/n` used verbatim | e.g. arXiv:2304.02789, 2107.00971, 2106.09315, 1502.04607 — all use the identical series; standard, not novel |

### Literature summary (Phase 3)

Concept identified as: **the `p`-adic logarithm** `log_p` (a.k.a. the **Iwasawa
logarithm** when extended to `ℂ_p^×`), `log_p(x) = ∑_{m≥1} (−1)^{m+1}(x−1)^m/m`.

Sources agree on the standard form: **yes**, unanimously (Wikipedia, PlanetMath,
Keith Conrad, MIT notes, Washington *Cyclotomic Fields* §5.1, Iwasawa). The
series and its domain `|x−1| < 1` are textbook-canonical.

Most general standard form: the series defines `log_p` on **any complete
non-archimedean (ultrametric) field of characteristic 0 over `ℚ_p`** on the open
unit ball `|x−1| < 1`; the literature usually *states* it over `ℚ_p` or `ℂ_p`
purely for concreteness, but only convergence on the unit ball is used.

Specifically for `log_p(1) = 0`: every source gives it as the immediate base
value — "x = 0 ⇒ log 1 = 0" (substitute `x = 1` into the series; all terms carry
`(x−1)^m`) — and it also follows from multiplicativity `log_p(1·1)=2log_p(1)`.
This is the `p`-adic instance of the base-independent identity `log 1 = 0`.

Generality dimensions where the literature varies:
- **Ambient field**: `ℚ_p` ⊂ `ℂ_p` ⊂ {complete non-archimedean char-0 field over `ℚ_p`}. The most general is the last; **the project's `L` already sits at this most-general level** (a complete ultrametric normed `ℚ_[p]`-algebra field).
- **Domain handling**: most texts state `log_p` only on `1 + 𝔪` (convergence ball); mathlib/the project use the *junk-total* `tsum` convention (`= 0` off the ball). `log_p(1) = 0` holds under **both** conventions and needs no convergence hypothesis.

Disagreement with the literature: **none.** The project's `padicLog` is exactly
the standard series (reindexed `m = n+1`), and `padicLog_one` is exactly the
standard base value.

---

## PHASE 4 — Generality analysis

### Generality status table — `PadicLFunctions.padicLog_one`

Literature-standard form (from Phase 3): `log_p(1) = 0`, where `log_p` is defined
by the series on any complete non-archimedean char-0 field over `ℚ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | value field `L` | `[NormedField L] [NormedAlgebra ℚ_[p] L]` (the two ultrametric/complete typeclasses are `omit`ted from *this* lemma) | complete non-archimedean char-0 field over `ℚ_p` | NO (already at/above the standard generality) | `padicLog_one` itself uses **no** completeness, ultrametricity, or even the algebra norm beyond making `(x−1)^{n+1}` and the `tsum` typecheck; the author already `omit`ted `IsUltrametricDist`/`CompleteSpace`. It is essentially as general as the *host definition* permits. |
| 2 | the base point | `x = 1` | `x = 1` | NO | This *is* the base-point lemma; weakening the point is a different theorem (`norm_padicLog`, the multiplicativity lemmas). |
| 3 | the prime `p` | `[Fact p.Prime]` | prime `p` | NO | Inherent to `ℚ_[p]`; cannot be dropped. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it is — a companion lemma of
`padicLog`; it is already as general as the host definition allows, and the
author has stripped the unused side-conditions).
Number of weakening opportunities found: **K = 0** (on the lemma itself).

Caveat that dominates the verdict: the lemma's generality is **bounded by the
host definition's generality**, not by the literature. The *real* generality
question is about `PadicLFunctions.padicLog` (the BIG object), which would be
assessed in its own `/mathlibable` run. `padicLog_one` cannot be "more mathlib
than" its host.

Cost of restatement: n/a (nothing to restate).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass/instance? | no | — | Already fully typeclass-driven (`NormedField`, `NormedAlgebra ℚ_[p]`). |
| 2 | sequences/metric → filters/nets? | no | — | The statement is a single equation `log_p 1 = 0`; no limit notion to filter-ise. (The *summability* lemmas next door already use `Tendsto … cofinite`.) |
| 3 | construct an object → universal property? | no | — | `log_p` is an explicit analytic series, not a universal-property object; the literature has no UP characterisation. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No subobject here. |
| 5 | vector-space/metric/field-specific → modules/(semi)ring? | no | — | The companion fact `log 1 = 0` does not specialise a richer algebraic statement; it is the value at a point. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The index `n : ℕ` is the summation index of a power series; not a generality axis for *this* lemma. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: `padicLog_one` is the value of an analytic logarithm at its base
point — a scalar equation with no preamble, no sequence/limit, no construction,
no subobject, and no concrete-index axis to modernise. The host `padicLog` is
already stated in the contemporary mathlib idiom (junk-total `tsum`, normed
`ℚ_[p]`-algebra typeclasses, ultrametric-distance class). There is no Bourbaki-2.0
move *for the lemma*.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** No definitional equality or
typeclass-search path is introduced. (Skipped per scope rule.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.padicLog_one`

```
[A] Lean-Finder       "p-adic logarithm at one is zero", "padic log_p 1 = 0"   n/a — no Lean-Finder MCP wired on this machine; substituted with [B]/[D]/[E] over the local mathlib tree.
[B] Loogle            (type-pattern, run as src grep) ⊢ _ = 0 for a tsum-log over a normed/nonarchimedean field; `padicLog _ = 0`   no hits — mathlib has no p-adic logarithm to state it about.
[C] LeanSearch        "p-adic logarithm of one equals zero"                     n/a — no LeanSearch MCP wired; covered by [D]+[E].
[D] Grep mathlib src  `padicLog`, `padic_log`, `pAdicLog`, `def .*[Ll]og.*tsum`, `tsum.*log`, `NormedField.*[Ll]og`   no hits for any p-adic / tsum-on-normed-field logarithm (the only `*log*` defs are `Real.log`, `Complex.log`, `PowerSeries.log`, `Nat.log`, `Int.log`, none of which is this object). The `NormedField` grep "hits" were unrelated `variable` lines.
[E] Name pattern      `padiclog` / `padic_log` / `p_adic_log` (case-insensitive) over `Mathlib/`   no hits — confirmed absent.
```

Searched for both:
- the user's current form `padicLog p (1 : L) = 0` — **absent** (no `padicLog`).
- the literature-standard form `log_p(1) = 0` over `ℚ_p`/`ℂ_p`/normed field — **absent** (no `p`-adic logarithm of any spelling).

What mathlib **does** have (the relevant near-misses, each read, not just named):

- `Mathlib/RingTheory/PowerSeries/Log.lean` — `PowerSeries.log : PowerSeries A`,
  `log(1+X) = X − X²/2 + …`, with `PowerSeries.constantCoeff_log : constantCoeff (log A) = 0`.
  This is the **formal** (algebraic) power series over a `ℚ`-algebra — *not* an
  analytic function `L → L`, has no convergence/`tsum`, and its
  `constantCoeff_log` is the *algebraic* shadow of `log 1 = 0`, not the analytic
  evaluation `padicLog 1 = 0`. (It is, however, the natural mathlib substrate a
  future analytic `padicLog` might be built on — the project's `ResidueZeta.lean`
  already bridges `padicLog` to `PowerSeries.log`/`formalLog`.)
- `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:106` —
  `@[simp, push] theorem Real.log_one : log 1 = 0`.
- `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:106` —
  `theorem Complex.log_one : log 1 = 0 := by simp [log]`.

  These two confirm the **API pattern**: every analytic logarithm mathlib defines
  ships a `log_one` companion. They are the precise analogues of `padicLog_one` —
  but for the real and complex logs, *not* the p-adic one. They prove the lemma's
  *shape* is exactly what mathlib wants when (and only when) the host log exists.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Mathlib has the *pattern* (`Real.log_one`,
`Complex.log_one`) and a *formal-series* cousin (`PowerSeries.constantCoeff_log`),
but **neither the analytic `p`-adic logarithm `padicLog` nor this lemma about it**.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.padicLog_one`

Internal use count (within PadicLFunctions, excluding the declaring file): **K = 4**
External-to-file callers: **2 files in this project** (`ExtLog.lean`, `ResidueZeta.lean`).
Plus the same-named lemma is referenced conceptually in a **different project**
(FltRegularBernoulli), which has its **own** independent `padicLog_one` (see below).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicLFunctions/ExtLog.lean:420` | `… extLog_eq_padicLog p (inExpBall_one_sub_one p), padicLog_one]` (empty-product base case of `extLog (∏) = ∑ extLog`) |
| `PadicLFunctions/ExtLog.lean:430` | `… (inExpBall_one_sub_one p), padicLog_one, smul_zero]` (roots of unity ⇒ `extLog = 0`) |
| `PadicLFunctions/ResidueZeta.lean:1510` | `… rw […, hu0, padicLog_one, add_zero]` (drop the `i = 0` term of a `Fin p` sum of logs) |
| `PadicLFunctions/ResidueZeta.lean:1576` | `rw [mul_inv_cancel₀ hpowne, padicLog_one] at hmul` (`log_p(x·x⁻¹)=log_p 1=0` step) |

Inline-derivation grep (was `padicLog p 1 = 0` re-derived elsewhere without the lemma?):
  - **(none)** — the only `padicLog (1 …` hit in the workspace
    (`Theorem518Resummation.lean:172`) is a *different* statement
    (`padicLog (1 − T) = …`) in the FltRegularBernoulli project, not a
    re-derivation of `padicLog 1 = 0`.

Signal (per the Phase-6 table): **K = 4 internal uses, no inline re-derivation
elsewhere → real, load-bearing API; consumers depend on it → leans YES.** This is
exactly the consumer profile mathlib's own `Real.log_one`/`Complex.log_one`
exhibit (used pervasively as a `@[simp]` rewrite).

### Composition check (Phase 6)

Can `padicLog p (1 : L) = 0` be derived from mathlib in ≤3 chained calls?

Attempt 1: `by rw [padicLog]; simp`
  - Mathlib decls used: `tsum_zero` / termwise `zero_pow` / `sub_self` via `simp`.
  - Result: **succeeds** — but this is composition **against the project's own
    `padicLog`**, not against a *mathlib* primitive. Mathlib has no `padicLog`, so
    there is nothing in mathlib to compose *from* to obtain "`padicLog 1 = 0`".
  - Notes: The 2-line proof is trivial **given** `padicLog`. That triviality does
    NOT make the lemma "composable from mathlib" in the Phase-6 sense — the object
    being unfolded (`padicLog`) is the project's, not mathlib's. The composability
    question is moot until `padicLog` itself is in mathlib.

Attempt 2: derive from a hypothetical mathlib `padicLog` + `Real.log_one`-style API
  - Not applicable: no mathlib `padicLog` exists to host the companion.

Conclusion: **NOT-COMPOSABLE-FROM-MATHLIB** (mathlib lacks the host object
`padicLog` entirely, so there is no mathlib building block to compose). The proof
is trivial *internally*, but that is a statement about the project, not mathlib.

---

## PHASE 7 — Verdict

## Verdict: `PadicLFunctions.padicLog_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): `log_p(1) = 0` is the universally-stated base value
  of the standard `p`-adic/Iwasawa logarithm (Wikipedia, PlanetMath, Keith Conrad,
  MIT notes, Washington §5.1) — but it is a *companion* of `log_p`, never an
  independently-named result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for a companion lemma (K = 0
  weakenings; the author already `omit`ted the unused `IsUltrametricDist`/
  `CompleteSpace`). Phase 4c: no modern-idiom move. **But** its generality is
  capped by the host `padicLog`'s, which is the BIG object the verdict really
  hinges on.
- Mathlib search (Phase 5): NOT in mathlib under any spelling; mathlib has the
  *pattern* (`Real.log_one`, `Complex.log_one`) and a *formal-series* cousin
  (`PowerSeries.constantCoeff_log`) but **no analytic `p`-adic logarithm**.
- Composition check (Phase 6): NOT-COMPOSABLE-FROM-MATHLIB (no host object in
  mathlib to compose from); K = 4 internal consumers, no inline re-derivation.

**Rationale (1–2 paragraphs):**

`padicLog_one` is correct, idiomatic, and genuinely used (K = 4): it is the exact
`p`-adic analogue of mathlib's `Real.log_one`/`Complex.log_one`, the canonical
`@[simp]` base-point fact of a logarithm. By the "Bourbaki 2.0" reading it is the
kind of API that ships *with* a logarithm definition — so it is not a
NO-mathlib-has-it (mathlib has no `padicLog`) nor a NO-composable (no mathlib
primitive to compose from). On a naive read those two facts push toward "YES, as
the companion of a YES-worthy `padicLog`."

The reason the verdict is **BORDERLINE rather than a YES** is that the decision is
*not the lemma's to make*, and two human-judgment blockers sit above it. **(a)
Derivativeness:** `padicLog_one` cannot enter mathlib on its own; it is a
one-equation companion whose fate is bound to the host definition
`PadicLFunctions.padicLog`. Whether mathlib should adopt an analytic `p`-adic
logarithm — and in *what* form: this project's normed-`ℚ_[p]`-algebra `tsum`, or
something built on the existing `PowerSeries.log` substrate, or only on `ℂ_p` per
the textbooks — is a substantial taste/architecture call for the mathlib
maintainers, exactly the BIG-object question that must be answered *first*. Per
the skill, "literature absence of an independently-named result" plus
"verdict-depends-on-a-judgment-the-skill-can't-ground" is the textbook BORDERLINE
trigger. **(b) Intra-workspace duplication:** the AINTLIB workspace already
contains a **second** `padicLog`/`padicLog_one` — `BernoulliRegular.FLT37.PadicL.padicLog`
over the concrete `ℚ_[p]`
(`projects/FltRegularBernoulli/BernoulliRegular/FLT37/PadicL/PadicLog.lean:52,69`),
with its own `@[simp] padicLog_one : padicLog (1 : ℚ_[p]) = 0`. Two definitions of
the same mathematical object in one library is precisely the "cardinal sin" the
project guards against; which one (if either) is the upstream candidate, and
whether they should first be unified, is a cross-project decision a human must
make before any mathlib PR. These are not uncertainties the search can resolve —
they are policy/taste questions, so the honest verdict is BORDERLINE with the
questions spelled out.

**Refactor-actionable bar — BORDERLINE-needs-human.**

Numbered questions (≤5):

1. **Host first.** Should the analytic `p`-adic logarithm `PadicLFunctions.padicLog`
   itself be proposed for mathlib? (Run `/mathlibable PadicLFunctions.padicLog`.)
   `padicLog_one` ships if and only if the host does — answer this before
   considering the companion.

2. **Which definition / which generality?** If yes to (1): upstream this project's
   form over a general complete ultrametric normed `ℚ_[p]`-algebra field `L`
   (more general than the textbooks), the concrete-`ℚ_[p]` FltRegularBernoulli
   form, or a reformulation built on mathlib's existing
   `PowerSeries.log` (formal series + a convergence/`HasSum` evaluation bridge)?
   The literature uses `ℚ_p`/`ℂ_p`; mathlib's iron rule prefers the general `L`.

3. **Deduplicate the workspace first?** There are two `padicLog`/`padicLog_one` in
   AINTLIB (`PadicLFunctions` over `L`; `BernoulliRegular.FLT37.PadicL` over
   `ℚ_[p]`). Should these be unified — e.g. the `ℚ_[p]` one re-expressed as the
   `L := ℚ_[p]` instance of the general one — before any mathlib submission, and
   if so which is the canonical home?

4. **Companion bundle / PR grain.** Assuming yes to (1): is `padicLog_one` to be
   PR'd as part of the `padicLog` *API bundle* (alongside `padicLog_eq_tsum`,
   `norm_padicLog`, the multiplicativity lemmas, `padicLog_summand` unfolding,
   etc.) — i.e. shipped in the same PR as the definition, never standalone?
   (Recommended; matches how `Real.log`/`Complex.log` ship their `log_one` with
   the definition.)

Next action: the user answers (1)–(4). Most likely resolution: **run
`/mathlibable PadicLFunctions.padicLog` (the host) first**; if that returns a YES,
`padicLog_one` inherits **YES-add-as-is, shipped inside the `padicLog` API bundle**
(it is the maximally-general, idiomatic, K=4-consumer analogue of `Real.log_one`,
which mathlib lacks only because the host object is missing); if the host returns
NO/BORDERLINE, this companion follows it. Either way, **deduplicate against
`BernoulliRegular.FLT37.PadicL.padicLog` before any PR.**

---

## Next step

Run `/mathlibable PadicLFunctions.padicLog` (the host definition) first — this
companion's verdict is bound to it. In parallel, resolve the intra-workspace
duplication with `BernoulliRegular.FLT37.PadicL.padicLog` /`.padicLog_one`. If the
host is accepted for mathlib, ship `padicLog_one` *inside the `padicLog` API
bundle* (the `Real.log_one`/`Complex.log_one` analogue), never as a standalone PR.
