# /mathlibable report — `PadicLFunctions.MeasureR.Ftilde`

**Final verdict: `NO-composable-from-mathlib`** — `Ftilde` is RJW §6.2's formal
antiderivative `F̃_θ` (the candidate for `∂⁻¹F_θ`), introduced *in-display* inside the
proof of Leopoldt's value formula `L_p(θ,1)` (arXiv:2309.15692, eq. before Lemma 6.4),
not as a separately-named standalone object. It is a `θ⁻¹`-weighted, `G(θ⁻¹)⁻¹`-cleared
finite sum over residues `c` of the per-root logarithmic series `logSeriesAt(ε^c) =
log((1+T)ε^c − 1)`; mathlib supplies the building block for the *non-constant* part of each
summand (`PowerSeries.log` / `PowerSeries.logOf`), while the constant terms (`extLog`, the
project-local Iwasawa-branch `log_p`) and the character/Gauss-sum weighting are
project-specific. Zero external call sites (44 in-file uses, 0 elsewhere). Keep it
project-local; do not PR. Mirrors the sibling verdicts on `FtildeA` and `rhoTheta`
(both `NO-composable-from-mathlib`).

---

### Baseline (Phase 0)
- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.MeasureR.Ftilde`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:53`
- kind:                      `def` (`noncomputable`)
- has sorry:                 **no** (`grep -nE '\bsorry\b|\badmit\b' ValuesAtOne.lean` → empty; the whole file is sorry-free)
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" —
  Leopoldt's formula `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)`
  proved by the distribution-free route: the explicit antiderivative `F̃_θ` (`Ftilde`),
  `∂F̃_θ = F_θ` formal, matched against the Mahler transform of the genuine measure `ρ_θ`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.Ftilde` is **a definition** of a formal power series over `K`.

For a modulus `N`, a Dirichlet character `θ : (ℤ/N)ˣ → K`, and a primitive `N`-th root of
unity `ε ∈ K`, `Ftilde p K θ hε` is **RJW's antiderivative** (arXiv:2309.15692, §6.2)

  F̃_θ(T) = −(1/G(θ⁻¹)) · Σ_{c∈(ℤ/N)×} θ⁻¹(c) · log( (1+T)·ε_N^c − 1 ),

the formal `∂⁻¹` of `F_θ(T) = −(1/G(θ⁻¹))·Σ_c θ⁻¹(c)/((1+T)ε_N^c − 1)` (RJW Lemma 5.12),
where `∂ = (1+T)·d/dT`. Plugging `T = 0` and using `L_p(θ,1) = (1−θ(p)p⁻¹)·∂⁻¹F_θ(0)` (RJW
eq. 6.3) yields the value formula. In the Lean realisation the per-root series is
`logSeriesAt p K (ε^c) = log((1+T)ε^c − 1)` (constant term `extLog p (ε^c−1)`, the
Iwasawa-branch p-adic log; higher coefficients `(−1)^{n−1}n⁻¹·(ε^c/(ε^c−1))ⁿ`), and the
docstring records that the `G(θ⁻¹)⁻¹` factor is **cleared** (stated G-cleared per the §5
clearing conventions, replan R6.5) — so the Lean body carries the `θ⁻¹`-weighted sum but
not the explicit `G⁻¹` (that scalar is reintroduced via `C G⁻¹ * Ftilde …` at the call
sites in `p_mul_constantCoeff_mahlerK_rhoTheta` / `LpFunction_one`).

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the prime (enters only through `extLog p` in the
  constant coefficients of `logSeriesAt`).
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]`
  `[CompleteSpace K] [CharZero K]` — the coefficient field (declared once for the section).
  The four analytic instances are **not used by the `Ftilde` def directly**, but its
  ingredient `logSeriesAt`'s constant term `extLog p (ε^c−1)` consumes them transitively.
- `{N : ℕ} [NeZero N]` — the conductor/modulus.
- `θ : DirichletCharacter K N` — the (non-trivial, primitive) character; only `θ⁻¹` is used.
- `{ε : K} (_hε : IsPrimitiveRoot ε N)` — a primitive `N`-th root of unity. **The hypothesis
  `_hε` is named with a leading underscore: it is a *phantom* argument, not used in the body**
  (the body refers only to `ε`, the value); it pins the intended semantics and is consumed by
  the lemmas *about* `Ftilde`.

Hypotheses (Lean side): none constrain the body (`_hε` is phantom); the real hypotheses
(`1 < N`, `θ ≠ 1`, `θ.IsPrimitive`, norm-one of `ε^c`, …) live on the theorems *about*
`Ftilde` (`one_add_mul_derivative_Ftilde`, `sum_seriesEval_Ftilde`, …).

Conclusion (math): the formal antiderivative power series `F̃_θ` of RJW §6.2.

Conclusion (Lean): `PowerSeries K` — n/a, it is a definition.

Body (1 substantive expression — a negated `Finset.range N` sum):
```lean
noncomputable def Ftilde {N : ℕ} [NeZero N] (θ : DirichletCharacter K N)
    {ε : K} (_hε : IsPrimitiveRoot ε N) : PowerSeries K :=
  -∑ c ∈ Finset.range N,
    PowerSeries.C (θ⁻¹ ((c : ZMod N))) * logSeriesAt p K (ε ^ c)
```
where (`ValuesAtOne.lean:46`)
```lean
noncomputable def logSeriesAt (u : K) : PowerSeries K :=
  PowerSeries.mk fun n =>
    if n = 0 then extLog p (u - 1)
    else (-1 : K) ^ (n - 1) * ((n : K))⁻¹ * (u / (u - 1)) ^ n
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a presentation-level bookkeeping power series internal to the §6.2 value
computation. It is *not* listed under `## Main results` (the file's headline result is
`LpFunction_one` — Leopoldt's value formula, RJW Thm 6.1(ii)); it introduces no new
mathematical *structure* (it returns an inhabitant of the existing type `PowerSeries K`);
and it carries no person/place name (`F̃_θ` is "θ-tilde", not a named theorem). It is an
intermediate antiderivative exactly analogous to its §7 sibling `FtildeA` (the residue
antiderivative `F̃_a`), which the sibling report classified SMALL.

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive expression** — a negated `∑_{c ∈ Finset.range N}` of
`C(θ⁻¹ c) * logSeriesAt(ε^c)`. This is a single `def` body but it is a *finite sum*, not a
sealed alias; treating it as the one-liner heuristic intends:

One-liner verdict: **ONE-LINER** (a single-expression `noncomputable def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | Every downstream proof *unfolds* `Ftilde` immediately via `rw [Ftilde, …]` (lines 235, 725, 1379, 1440, 1746) to expose the sum; it is used as a freely-unfolded abbreviation for the `θ⁻¹`-weighted log-sum, not as a sealed barrier. No proof depends on `Ftilde` *not* unfolding. |
| Avoid typeclass diamonds          | no       | Returns a bare `PowerSeries K`; introduces no instance, no typeclass-search target. |
| Mark semantic intent / API name   | partial  | It gives the recurring antiderivative `F̃_θ` a readable name used 44× *within* `ValuesAtOne.lean`. But the benefit is **intra-file only** — there is **no external consumer** (Phase 6: K = 0). It does not name an *external* consumer depending on a stable name (the Phase-2b bar). |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the "semantic name" benefit is intra-file
readability only; no external consumer relies on the name). Per Phase 2b / 6.0.2 this biases
Phase 7 toward a NO bucket — consistent with K = 0 external (Phase 6.0) and the
composition finding (Phase 6).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic L-function L_p(theta,1) Leopoldt formula Dirichlet character Gauss sum log_p(1−ε^c) explicit antiderivative power series` | **yes (target theorem)** | `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_{a} χ̄(a)·log_p(1−ζ^a)` (Leopoldt) | Surfaced RJW (arXiv:2309.15692 = Essential Number Theory 4(1) 2025), Zhao "Sum Expressions" (arXiv:2201.08870), Washington Ch. 5. These name the **value formula** (the theorem `LpFunction_one`), not the antiderivative `F̃_θ`. |
| 2 | WebSearch (general form) | `explicit antiderivative power series p-adic L-function value at s=1 sum theta inverse logarithm primitive root of unity formal derivative` | **yes (decisive on the value formula)** | "For an even nontrivial χ of conductor f and ζ a primitive f-th root of unity, **L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_{a=1}^{f} χ̄(a)·log_p(1−ζ^a)**". Also: p-adic log is the formal series `−log_p(1−x)=Σ x^n/n`; p-adic polylogs `Σ_{p∤k} x^k/k^r` are convergent power series. | Confirms the *value formula* is classical and the *components* (formal log, primitive roots) standard. No source names a `F̃_θ` antiderivative as a standalone object. |
| 3 | WebSearch (named-after / aliases) | `"Rodrigues Jacinto" Williams "introduction to p-adic L-functions" arXiv 2309.15692 Leopoldt L_p(theta,1)` | **yes — source identified** | RJW = **Joaquín Rodrigues Jacinto & Chris Williams**, *An introduction to p-adic L-functions*, arXiv:2309.15692v2 (19 Dec 2024), Essential Number Theory 4(1) 2025; three constructions (measure-theoretic / Coleman / Iwasawa). §6 = "the values at s = 1"; §6.2 = "the p-adic value at s = 1" (Leopoldt). | Pinned the source paper. The repo header cites "RJW §6.2"; the lecture-notes author C. Williams overlaps the repo owner (Chris Birkbeck's collaborator circle). |
| 4 | WebSearch (Coleman / log-derivative tradition) | `Coleman power series logarithmic derivative Dirichlet character twisted measure Mahler transform formal power series antiderivative` | partial | Coleman power series ↔ measures on ℤ_p; logarithmic-derivative operator `D(log ĝ) = ĝ′/ĝ`; "natural operations on measures give operators on power series via the Mellin/Mahler transform". | The *operation* (antiderivative of a measure-attached power series under `∂`, logarithmic derivative) is the named/standard concept; this particular `F̃_θ` is a specific instance of it, not separately named. |
| 5 | ChatGPT MCP | (intended: standard-form + generality + historical-evolution prompt) | **n/a** | — | **ChatGPT MCP not available in this environment.** The session's deferred-tool list exposes no `chatgpt`/`chatgpt-math` tool; `~/.claude/mcp-needs-auth-cache.json` lists `plugin:mathlib-quality:chatgpt-math` as needing auth (server present at `~/.claude/mcp-servers/chatgpt-math` but unauthenticated). Compensated with the extra WebSearch channels (#1–#4, #8) **and the primary source itself** (#10, `pdftotext` of the arXiv PDF), the authoritative channel here. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/` | **n/a** | — | `projects/PadicLFunctions/.mathlib-quality/references/` **does not exist**; there is no `refs/` directory/symlink in the checkout; no `*.tex`/`*.bib`/`*.pdf` source under the project. Recorded n/a (same as the sibling `FtildeA`/`rhoTheta`/`rhoA` reports). NB the **file header itself** cites the source as "RJW §6.2, Thm 6.1(ii)". |
| 7 | nLab | `formal logarithm power series` / `logarithmic derivative` / `p-adic L-function measure` | yes (components) | nLab/standard refs confirm the formal `log`/`exp` series, the Mahler transform `Φ_μ(T)=Σ(∫binom(x,n)dμ)Tⁿ` isomorphism `measures ≅ W[[T]]`, and the p-adic log `log_p(1+z)=Σ(−1)^{n+1}z^n/n` on `|z−1|<1`. **No** `F̃_θ`-specific entry. | Confirms the *components* (formal log, log-derivative, Mahler ≅ power series) are standard; the assembled `θ⁻¹`-weighted antiderivative is not an nLab concept. |
| 8 | recent arXiv (≤5 yr) / Math.SE — corroborating | `"sum expressions" Kubota-Leopoldt p-adic L-functions arXiv 2201.08870 power series operator (1+T)d/dT antiderivative` | **yes** | Zhao, *Sum Expressions for Kubota–Leopoldt p-adic L-functions* (Proc. Edinburgh Math. Soc. 65(2) 2022): writes K–L p-adic L-functions as infinite sums by **computing periods of appropriate measures**; reproves Ferrero–Greenberg `L_p′(0,χ)`; discusses convergence via elementary p-adic analysis. | An independent paper using the **same family of techniques** (measure periods → power-series sums) to reprove Leopoldt/Ferrero–Greenberg. Confirms the *method* is standard; still no separately-named `F̃_θ`. |
| 9 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept — a concrete formal power series tied to one p-adic L-value computation. No higher-categorical statement applies. |
| 10 | **Source paper (arXiv 2309.15692, §6.2) — decisive** | `pdftotext` of the PDF; read §6.2 body (text lines 3623–3760) | **yes — verbatim match** | §6.2 ("The p-adic value at s = 1"): after `L_p(θ,1) = A_{Res×}(x⁻¹μ_θ)(0) = (1−θ(p)p⁻¹)·∂⁻¹F_θ(0)` (eq. 6.3) and Lemma 5.12's `F_θ(T) = −G(θ⁻¹)⁻¹ Σ_c θ⁻¹(c)/((1+T)ε_N^c−1)`, the paper writes: *"if we define **F̃_θ(T) = −G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)×} θ⁻¹(c)·log((1+T)ε_N^c − 1)**, then formally ∂F̃_θ = F_θ … F̃_θ is a good candidate for ∂⁻¹F_θ."* **Lemma 6.4** then states `F̃_θ ∈ R⁺`; its proof expands `log((1+T)ε^c−1) = log_p(ε^c−1) + Σ_{n≥1} ((−1)^{n−1}/n)(ε^{cn}/(ε^c−1)ⁿ)Tⁿ` — **exactly the project's `logSeriesAt(ε^c)`**. | **Decisive.** `Ftilde` ≡ RJW's `F̃_θ` *verbatim*. It is introduced **in-display inside the value derivation** ("if we define …"), is the subject of Lemma 6.4 (`F̃_θ ∈ R⁺`) and Lemma 6.5 (`∂F̃_θ = F_θ`), but is **not a numbered `Definition`/standalone exported object** — it is the route device that proves the value formula. |
| 11 | MathOverflow / Math.SE | (folded into #1–#4, #8) | partial | `((1+T)^a − 1)`, logarithmic derivatives, and `x⁻¹·Res_{units}` measures are routine in Iwasawa-theory threads; `∂⁻¹` indeterminacy / `R⁺`-membership recur | No dedicated treatment of this particular antiderivative `F̃_θ` as a named object. |

### Literature summary (Phase 3)

Concept identified as: **RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692) §6.2's
antiderivative `F̃_θ`** — the formal `∂⁻¹` (under `∂ = (1+T)d/dT`) of the Mahler-transform
series `F_θ` of the twisted measure `μ_θ`, used to compute the value `L_p(θ,1)` (Leopoldt's
formula, RJW Thm 6.1(ii)). The Lean `Ftilde` matches the paper's display formula **verbatim**
(up to the documented `G(θ⁻¹)⁻¹` clearing). Its ingredients are all standard/named:
- the **value formula** `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ θ⁻¹(c)·log_p(1−ε_N^c)` (Leopoldt;
  Washington *Intro. to Cyclotomic Fields* Thm 5.18; Zhao arXiv:2201.08870; RJW Thm 6.1(ii));
- the per-root logarithmic series `log((1+T)u − 1)` (= project `logSeriesAt`), expanded in
  Lemma 6.4;
- the formal logarithm `log(1+X) = Σ(−1)^{n−1}n⁻¹Xⁿ` (Mercator; mathlib `PowerSeries.log`);
- the p-adic (Iwasawa-branch) logarithm `log_p` (= project `extLog`);
- the antiderivative / logarithmic-derivative operation (Coleman tradition).

But the **assembled object `F̃_θ` is not separately named** in the literature — RJW introduces
it in-display inside the proof of the value formula (it is the subject of Lemma 6.4/6.5, not a
numbered Definition).

Sources agree on the standard form: **yes** for the *value formula* (the theorem) and for
each *ingredient*; **no separately-named standard form** for the assembled antiderivative
`F̃_θ` (it is a route device inside one proof).

Most general standard form: there is none for `F̃_θ` qua named object. The closest standard
concepts are the **value formula** (a theorem, `LpFunction_one`, assessed separately), the
**formal log** (mathlib `PowerSeries.log`/`logOf`), and the **logarithmic-derivative /
antiderivative** operation.

Generality dimensions where the literature varies:
  - the formal-log component: over any ℚ-algebra (mathlib `PowerSeries.log`); here `K` is a
    complete ultrametric ℚ_p-Banach field — more than the *formal* construction needs, but the
    `extLog` constant terms genuinely require it.
  - the constant `log_p(ε^c−1)`: the p-adic log exists over any complete ℚ_p-algebra; the
    Iwasawa-branch normalisation (`log_p p = 0`) is one convention.
  - the modulus/character/root `(N, θ, ε)`: intrinsic to the value formula being proved; not a
    generalisation axis.

Disagreement with the literature: **none** — the Lean form matches RJW's display exactly
(modulo the documented `G⁻¹` clearing); the literature simply treats `F̃_θ` as a
proof-internal antiderivative, not an exported object.

---

### Generality analysis — `PadicLFunctions.MeasureR.Ftilde`

Literature-standard form (Phase 3): there is **no separately-named standard `F̃_θ`** to compare
against; the relevant standard objects are the value-formula *theorem*, the *formal log*
(mathlib, maximally general elsewhere), and the *p-adic log* (project `extLog`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` | normed field | (the *formal* sum needs only a ℚ-algebra; the `extLog` constant terms of `logSeriesAt` need a normed ℚ_p-algebra) | partial | The `θ⁻¹`-weighting and the non-constant `(−1)^{n−1}n⁻¹(u/(u−1))ⁿ` coefficients need only `[CommRing K][Algebra ℚ K]`; the **constant term `extLog p (ε^c−1)` genuinely needs the normed/ultrametric ℚ_p-Banach structure** (it is `padicLog`-based). So the def cannot be stated over a bare ℚ-algebra without dropping the constant terms. |
| 2 | `[NormedAlgebra ℚ_[p] K]` | ℚ_p-Banach algebra | needed by `extLog` | **NO** | `extLog p (ε^c−1)` is defined only over normed ℚ_p-algebras (via `padicLog`); load-bearing for `logSeriesAt`'s constant coefficient. |
| 3 | `[IsUltrametricDist K]` | ultrametric | needed by `extLog`/`padicLog` | **NO** | The p-adic-log domain (`InExpBall`, `ExtLogDomain`) is ultrametric-specific. |
| 4 | `[CompleteSpace K]` | complete | needed by `extLog` (convergence of `padicLog`) | **NO** | `padicLog` is a convergent series; completeness is essential. |
| 5 | `[CharZero K]` | char 0 | char 0 (inverses `n⁻¹`, `(ε^c−1)⁻¹`) | partial | Needed for the `n⁻¹`/`(u/(u−1))` coefficients; the natural home is char 0 anyway. |
| 6 | `θ : DirichletCharacter K N`, `{N}`, `ε` (`_hε` phantom) | character / modulus / primitive root | the data of Leopoldt's value formula (RJW §6.2) | **NO** | `θ⁻¹`, `N`, `ε^c` are intrinsic to `F̃_θ` (RJW's display); the construction is *about* a fixed character — there is no "more general `F̃_θ`" in the literature. (The phantom `_hε` is not even used in the body.) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what the assembled object is.** Like its sibling
`FtildeA` (and unlike `uA`, whose analytic instances were pure dead weight), `Ftilde`'s
constant terms `extLog p (ε^c−1)` **genuinely consume** the normed/ultrametric/complete
ℚ_p-algebra structure (rows 2–4 load-bearing, not removable). There is no clean weakening of
`Ftilde` as a whole, and **no literature-standard *more general* `F̃_θ`** to aim a
generalisation at (rows 1, 5 are cosmetic char-0/field framing).
Number of weakening opportunities found: **0 that keep the object intact.**
Proposed restatement: **none** — `Ftilde` is *not strictly narrower* than a literature
standard, because there is no separately-named literature standard for `F̃_θ`. (Contrast a
true YES-but-generalise case, where the literature has a strictly more general named form.)
Cost of restatement: n/a.

**This MAXIMALLY-GENERAL finding does NOT push toward `YES-add-as-is`**, because (Phases 5–6)
the object is a `θ⁻¹`-weighted, `G⁻¹`-cleared finite sum of `logSeriesAt(ε^c)` whose
non-constant part is mathlib `PowerSeries.log`/`logOf` and whose constant terms are the
project-local `extLog` — a thin construction-internal assembly with **zero external
consumers**, not a novel exported object. MAXIMALLY-GENERAL + (no more-general literature
form) + COMPOSABLE-substrate + K = 0-external → NO, not YES (verdicts reference: "MAXIMALLY
GENERAL is necessary but not sufficient; K = 0/1 internal-only ⇒ lean NO").

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclasses? | no | already typeclass-based | — |
| 2 | sequences/metric → filters/topology? | no | a *formal* (algebraic) power series; no topology in the def | — |
| 3 | construct object → universal-property class? | no | an explicit `θ⁻¹`-weighted finite sum, not a universal object | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | field-specific → weaken typeclasses? | partial | the non-constant part of each `logSeriesAt(ε^c)` is `PowerSeries.logOf (1 + C(ε^c/(ε^c−1))·X)` over `[CommRing K][Algebra ℚ K]`, but the `extLog` constant terms forbid weakening the *whole* object | the modern idiom says **delete `logSeriesAt`/`Ftilde`'s re-derivation and compose from mathlib `log`/`logOf` + project `extLog`**, not *generalise `Ftilde`* |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index → arbitrary monoid/group? | no | `θ`/`N`/`ε^c` are intrinsic to the value formula; `c ∈ Finset.range N` is the character sum, not an over-specialised index | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it does not yield a new object** — it yields the
instruction to **compose each summand's non-constant part from mathlib's `PowerSeries.logOf`**
(the project already uses mathlib's `PowerSeries.log` in `PadicExp.lean`). The contemporary
mathlib form of `log((1+T)u − 1)` is `C(extLog p (u−1)) + PowerSeries.logOf (1 +
C(u/(u−1))·X)` (factoring `(1+T)u−1 = (u−1)(1 + (u/(u−1))T)`); `Ftilde` is then the
`θ⁻¹`-weighted, `G⁻¹`-cleared sum of those. This reinforces NO-composable: the modern idiom
replaces the *log machinery* with mathlib calls rather than promoting `Ftilde` itself to
mathlib.
One-line reason this is *not* a "ship the modernised `Ftilde`" move: the constant terms
`extLog p (ε^c−1)` are **project-local** (the Iwasawa-branch `log_p`, with **no mathlib p-adic
logarithm**), and the `θ⁻¹`/`G(θ⁻¹)⁻¹` weighting is bespoke to Leopoldt's formula — so the
assembled object is inherently project-bound.

---

### Diamond / defeq risk — `PadicLFunctions.MeasureR.Ftilde`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Returns a bare `PowerSeries K`; introduces no instance, so nothing for typeclass search to disambiguate. |
| 2 | Reducibility leak | none | Plain `noncomputable def`, not `@[reducible]`/`abbrev`; the body (the `θ⁻¹`-weighted sum) is exposed only via explicit `rw [Ftilde, …]` (lines 235, 725, 1379, 1440, 1746). |
| 3 | Non-canonical unfolding | low | No `@[simp]`; `simp` will not unfold it; proofs unfold deliberately. No surprise. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `K : Type*`; `PowerSeries K` is monomorphic in `K`'s universe; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`; `PowerSeries.C`, the cast `(c : ZMod N)`, and `θ⁻¹` are ordinary. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW**
Top risks: none HIGH.
Recommended mitigations: none required. (Risk is moot for the final NO verdict anyway — NO
buckets do not add the def to mathlib.)

---

### Mathlib search-status: `PadicLFunctions.MeasureR.Ftilde`

[A] Lean-Finder       n/a: LSP/MCP Lean-Finder not available in this environment (recorded n/a
                      per `mathlib-search.md`); compensated by [D] grep over the mathlib source
                      tree at `.lake/packages/mathlib/Mathlib/`.
[B] Loogle            type-pattern `(DirichletCharacter _ _ → PowerSeries _)` /
                      `∑ _, PowerSeries.C _ * PowerSeries.log _` arising from a character-weighted
                      log-sum — n/a (LSP unavailable); emulated via [D] source grep. The relevant
                      mathlib decls (`PowerSeries.log`/`logOf`) were located directly.
[C] LeanSearch        "antiderivative power series p-adic L-function value at 1 Dirichlet
                      character sum logarithm primitive root" — n/a (LSP unavailable); covered by
                      the Phase-3 WebSearch channels #1–#4, #8 and the source paper #10.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib`:
                      • `PowerSeries.log` / `logOf` → **HIT**:
                        `Mathlib/RingTheory/PowerSeries/Log.lean:42` `log A = mk fun n => if n=0
                        then 0 else algebraMap ℚ A ((-1)^(n+1)/n)`; `:82` `logOf f = (log A).subst
                        (f − 1)` (`logOf_eq:85`, `logOf_one_add_X:96`). This is the building block
                        for the **non-constant** part of each `logSeriesAt(ε^c)` summand.
                      • `padicLog` / `Padics/*Log*` / `extLog` → **NO HIT**: mathlib has **no
                        p-adic logarithm** (no `NumberTheory/Padics/*Log*`). `logSeriesAt`'s
                        constant terms `extLog p (ε^c−1)` have no mathlib counterpart.
                      • `Kubota` / `Leopoldt` / `p-adic L-function` value/antiderivative object →
                        **NO HIT** (no Kubota–Leopoldt p-adic L-function in mathlib at all).
                      • `logSeriesAt` / `Ftilde` / `F_tilde` / character-weighted-log-sum →
                        **NO HIT** (no decl named or shaped like it).
[E] Name pattern      grep `Ftilde`/`logSeriesAt`/`Ftheta` in mathlib — no decl named anything
                      like it.

Searched for both:
  - the user's current form (the negated `θ⁻¹`-weighted `Finset.range N` sum of
    `logSeriesAt(ε^c)`) — **not in mathlib**;
  - the literature-standard form — there is no separately-named `F̃_θ`; its *ingredients*:
    `PowerSeries.log`/`logOf` are **in mathlib** (the Mercator log, the building block for the
    non-constant part of each summand); the p-adic `extLog` (constant terms) and the
    `θ⁻¹`/`G(θ⁻¹)⁻¹` character weighting are **not** in mathlib. The **value formula** (the
    theorem this serves) is also absent — mathlib has no Kubota–Leopoldt p-adic L-function.

Concluded: **found building blocks** —
`PowerSeries.log`/`PowerSeries.logOf` (`Mathlib/RingTheory/PowerSeries/Log.lean:42,82`) supply
the non-constant part of each per-root summand `logSeriesAt(ε^c)`. The constant terms
(`extLog p (ε^c−1)`, project-local Iwasawa-branch `log_p`, no mathlib p-adic log), the per-root
series `logSeriesAt` itself, and the `θ⁻¹`/`G⁻¹`-weighted assembly `Ftilde` are **not** mathlib
decls in any form.

---

### Call sites — `PadicLFunctions.MeasureR.Ftilde`

Internal use count (within project, **excluding** the declaring file `ValuesAtOne.lean`): **K = 0.**
External-to-file callers: **0 distinct files.**

A repo-wide word-boundary grep `\bFtilde\b` over `projects/**/*.lean` (excluding the sibling
`FtildeA`) returns matches **only** inside `ValuesAtOne.lean` — **44 in-file occurrences, 0
elsewhere**. No other file — in PadicLFunctions or any sibling project — references `Ftilde`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none outside `ValuesAtOne.lean`) | — |

In-file consumers (declaring file `ValuesAtOne.lean`, for completeness — all the §6.2 machinery):
| `ValuesAtOne.lean:223` | `one_add_mul_derivative_Ftilde` — `∂F̃_θ = F_θ` (the formal identity, RJW Lemma 6.5) |
| `ValuesAtOne.lean:710` (`summable_seriesEval_Ftilde`) | summability of `seriesEval (Ftilde …)` at `‖z‖<1` (the `R⁺`-membership, RJW Lemma 6.4) |
| `ValuesAtOne.lean:767` (`p_mul_constantCoeff_mahlerK_rhoTheta`) | uses `C G⁻¹ * Ftilde …` and `constantCoeff (Ftilde …)` |
| `ValuesAtOne.lean:1353` (`sum_seriesEval_Ftilde`) | `Σ_i seriesEval(F̃_θ)(ξ^i−1) = θ(p)·constantCoeff(F̃_θ)` (the `μ_p`-collapse) |
| `ValuesAtOne.lean:1594` (`LpFunction_one`) | the final value formula `L_p(θ,1) = …`, evaluated via `constantCoeff (Ftilde …)` |
| `ValuesAtOne.lean:235,725,1379,1440,1746` | `rw [Ftilde, …]` — the def is unfolded to its `θ⁻¹`-weighted sum |

Inline-derivation grep (was the equivalent re-derived elsewhere without `Ftilde`?): **none.**
The antiderivative appears only inside this one file, deliberately named once and unfolded as
needed; its `§7` cousin `FtildeA` is a *different* antiderivative (residue, not value).

What the pattern tells us: **K = 0 external uses, confined to a single declaring file, with its
entire lemma API also confined to that file, serving one proof (Leopoldt's value formula)** →
an *intra-file naming convenience* for a construction-internal antiderivative (Phase-6
heuristic: "K = 0 internal-to-other-files / used only in its own file ⇒ lean NO-composable").
Combined with ONE-LINER-WITHOUT-EXEMPTION (Phase 2b) and the composition finding (below), every
signal points to NO. Identical posture to the siblings `FtildeA` (K = 0; NO-composable) and
`rhoTheta`.

---

### Composition check (Phase 6)

Can `PadicLFunctions.MeasureR.Ftilde` be obtained in ≤3 chained calls from mathlib (plus the
already-existing project objects it is built from)?

**Attempt 1 — express each per-root summand `logSeriesAt(ε^c)` via mathlib `logOf` + project
`extLog`.** Factor `(1+T)u − 1 = (u−1)(1 + (u/(u−1))T)` (valid when `u−1` is a unit — exactly the
hypothesis carried by the lemmas about `Ftilde`). Then
`log((1+T)u − 1) = log(u−1) + log(1 + (u/(u−1))T)`, i.e.
```lean
-- per-root summand (u = ε^c):
logSeriesAt p K u
  =? PowerSeries.C (extLog p (u - 1))              -- project-local scalar (Iwasawa log_p)
   + PowerSeries.logOf (1 + PowerSeries.C (u / (u - 1)) * PowerSeries.X)  -- mathlib logOf
```
Mathlib decls used: `PowerSeries.logOf` (folding the `.subst` of `PowerSeries.log`). Result:
**succeeds as a definitional/coefficient identity** for the *single* per-root series (this is
precisely what the project's own `one_add_mul_derivative_logSeriesAt` lemma certifies, mirroring
mathlib's `one_add_mul_derivative_formalLog`). Remaining per summand: the constant `extLog p
(u−1)`, a `PowerSeries.C` of a **project-local** scalar.

**Attempt 2 — the full `Ftilde`.** `Ftilde` is not one such summand: it is the **negated,
`θ⁻¹`-weighted, `G(θ⁻¹)⁻¹`-cleared finite sum over `c ∈ Finset.range N`** of those summands:
```lean
Ftilde p K θ hε
  = -∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ (c : ZMod N)) * logSeriesAt p K (ε ^ c)
```
This is an N-term character-weighted sum, not a ≤3-call chain. Even after substituting Attempt 1
into each term, the result is a `Finset.sum` of `2N` pieces, half of which are `PowerSeries.C` of
the **project-local** `extLog p (ε^c−1)` and all weighted by the project's `θ⁻¹` and (at the call
sites) the Gauss-sum scalar `G(θ⁻¹)⁻¹`. There is **no ≤3-mathlib-call composition** that yields
`Ftilde`.

Conclusion: **NOT a ≤3-mathlib-call composition** for the *assembled* object — but in the
NO-composable sense relevant here: **mathlib supplies the building blocks for the only genuinely
reusable part** (the Mercator log of each summand, `PowerSeries.log`/`logOf`), while everything
specific to `Ftilde` (the per-root constant `extLog`, the `θ⁻¹`/`G⁻¹` character weighting, the
finite character sum) is **project-local bookkeeping**. No *new mathlib lemma* is warranted: the
reusable machinery is already `PowerSeries.log`/`logOf`, and the rest is a Leopoldt-formula-specific
assembly with zero external consumers.

(Heuristics check: this is mathlib `logOf` per summand + the project's own `extLog` + a
`θ⁻¹`-weighted `Finset.sum` — a construction-internal assembly, not a `by rw; ring_nf; aesop`
proof-in-disguise, and not a single-line nested-call composition either. It does not meet the bar
for a *new* mathlib lemma; it is a project-side antiderivative.)

---

## Verdict: `PadicLFunctions.MeasureR.Ftilde`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): identified — via `pdftotext` of the primary source — as
  **RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692) §6.2's antiderivative `F̃_θ`**, the
  candidate `∂⁻¹F_θ` used to prove Leopoldt's value formula `L_p(θ,1)` (Thm 6.1(ii)). The Lean
  `Ftilde` matches the paper's display formula **verbatim** (modulo the documented `G(θ⁻¹)⁻¹`
  clearing). RJW introduces it **in-display inside the proof** ("if we define …"), as the subject
  of Lemma 6.4 (`F̃_θ ∈ R⁺`) / Lemma 6.5 (`∂F̃_θ = F_θ`) — **not** a numbered Definition or
  exported object. The *value formula* itself is classical (Washington Thm 5.18; Zhao
  arXiv:2201.08870), but that is the theorem `LpFunction_one`, not this antiderivative. 4
  WebSearch channels + nLab + the source paper; ChatGPT MCP and local refs recorded n/a with
  reasons.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for the assembled object (the `extLog`
  constant terms genuinely consume the normed/ultrametric/complete ℚ_p-algebra structure;
  `θ`/`N`/`ε` are intrinsic) — but there is **no separately-named more-general literature `F̃_θ`**
  to aim at, and Phase 4c's modern idiom is "compose the log machinery from mathlib `log`/`logOf`",
  not "ship a generalised `Ftilde`". MAXIMALLY-GENERAL here does **not** imply YES.
- Mathlib search (Phase 5): **found building blocks** — `PowerSeries.log`/`PowerSeries.logOf`
  (`Mathlib/RingTheory/PowerSeries/Log.lean:42,82`) supply the non-constant part of each per-root
  summand; the constant terms (`extLog`/`padicLog`) have **no mathlib counterpart** (mathlib has no
  p-adic logarithm), and there is no Kubota–Leopoldt p-adic L-function in mathlib. The assembled
  `Ftilde`, the per-root `logSeriesAt`, and the value formula are **not** in mathlib in any form.
- Composition check (Phase 6): mathlib supplies the reusable log machinery (`logOf` per summand);
  `Ftilde` itself is the negated, `θ⁻¹`-weighted, `G⁻¹`-cleared **N-term character sum** of those
  summands plus the project-local `extLog` constants — **no new mathlib lemma is warranted**, and
  the object is project-side bookkeeping. K = 0 external callers.

**Rationale.**
`Ftilde` is RJW §6.2's transient antiderivative `F̃_θ` — the paper writes, *inside the proof of the
value formula*, "if we define `F̃_θ(T) = −G(θ⁻¹)⁻¹ Σ_c θ⁻¹(c)·log((1+T)ε_N^c − 1)`, then formally
`∂F̃_θ = F_θ` … `F̃_θ` is a good candidate for `∂⁻¹F_θ`", and the Lean `Ftilde` reproduces this
display verbatim (the `G⁻¹` factor cleared per §5 conventions). It exists solely to compute
`L_p(θ,1) = (1−θ(p)p⁻¹)·F̃_θ(0)`. It has **zero external call sites** (44 uses, all inside
`ValuesAtOne.lean`), its entire lemma API (`one_add_mul_derivative_Ftilde`,
`summable_seriesEval_Ftilde`, `sum_seriesEval_Ftilde`, `LpFunction_one`) lives in that one file,
and the source paper treats it as a route device rather than a named object. On the mathlib side,
the **only genuinely reusable ingredient** — the Mercator formal log of each summand's non-constant
part — is already `PowerSeries.log`/`PowerSeries.logOf` (which this very codebase uses in
`PadicExp.lean`); everything else about `Ftilde` (the per-root constant `extLog p (ε^c−1)`, the
`θ⁻¹`/Gauss-sum weighting, the finite character sum) is Leopoldt-formula-specific project material,
and mathlib has **no** p-adic logarithm and **no** Kubota–Leopoldt p-adic L-function to host it.
Every signal — verbatim-but-unnamed in the source, K = 0 external use, mathlib-supplied log
machinery, project-local constant terms and character weighting, MAXIMALLY-GENERAL-but-thin —
converges on NO-composable. This mirrors the sibling verdicts on the §7 cousin `FtildeA`
(NO-composable) and on `rhoTheta`/`rhoA` (NO-composable).

**WHY not (refactor-actionable):**
Mathlib has the building block for the reusable part (the Mercator log of each summand); the rest is
project-local. No new mathlib lemma is warranted, and `Ftilde` itself is not mathlib-bound.

Mathlib building blocks:
- `PowerSeries.logOf` — `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Log.lean:82`
  (`logOf_eq:85`, `logOf_one_add_X:96`): the non-constant part of each per-root summand,
  `log(1 + C(ε^c/(ε^c−1))·X) = PowerSeries.logOf (1 + C(ε^c/(ε^c−1))·X)` after factoring
  `(1+T)ε^c − 1 = (ε^c−1)(1 + (ε^c/(ε^c−1))T)`.
- `PowerSeries.log` — `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Log.lean:42`
  (the Mercator series; the project also calls it directly in `PadicExp.lean`, and re-defines an
  equivalent `formalLog` in `FormalPsi.lean`).
- `PowerSeries.C` (constant series) — standard.
Non-mathlib (project-local, *not* upstreamable here):
- `extLog p (ε^c−1)` — `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:286` (the Iwasawa-branch
  `log_p`; mathlib has **no** p-adic logarithm).
- `logSeriesAt` — `ValuesAtOne.lean:46` (the per-root series; itself project-local, built from
  `extLog` + the geometric coefficients).
- the `θ⁻¹` / Gauss-sum `G(θ⁻¹)⁻¹` weighting and the `Finset.range N` character sum — bespoke to
  Leopoldt's formula.

Composition sketch (per-root summand only; the *full* `Ftilde` is an N-term character sum, not a
≤3-call composition):
```lean
-- single per-root series logSeriesAt(u), u = ε^c, with (u-1) a unit:
example : logSeriesAt p K u
    = PowerSeries.C (extLog p (u - 1))                                  -- project-local Iwasawa log_p
      + PowerSeries.logOf (1 + PowerSeries.C (u / (u - 1)) * PowerSeries.X) := by  -- mathlib logOf
  -- factor (1+T)u−1 = (u−1)(1 + (u/(u−1))T); log of a product splits; constant term = extLog(u−1)
  sorry  -- coefficient identity; not a mathlib lemma worth shipping
-- Ftilde itself = -∑_{c<N} C(θ⁻¹ c) * logSeriesAt(ε^c)  — a project-side character sum, not composable
```

Call sites in our project (from Phase 6.0): **K = 0 external; 44 internal** to `ValuesAtOne.lean`.
Refactor plan: **mathlib action = none — do NOT submit `Ftilde` to mathlib.** It is a legitimate
*project-local* antiderivative used in exactly one proof (Leopoldt's value formula), with zero
external consumers, so no cross-file refactor is required. If desired purely for in-file hygiene,
each per-root `logSeriesAt(ε^c)` could be re-expressed against mathlib's `PowerSeries.logOf` (the
project already uses `PowerSeries.log` in `PadicExp.lean`), and the duplicate `formalLog` could be
retired in favour of `PowerSeries.log` — but this is optional file hygiene tied to `logSeriesAt`,
not a mathlib-quality obligation on `Ftilde`, and the constant terms (`extLog`) would remain
project-local regardless. The actionable mathlibability conclusion is: **not mathlib-bound** (the
reusable log machinery is composable from mathlib; the per-root constants and the character-weighted
assembly are project-specific).
Next action: keep `Ftilde` local to `ValuesAtOne.lean`; do **not** open a mathlib PR for it.
(Optional hygiene belongs to `logSeriesAt`, assessed separately — fold its non-constant part onto
mathlib `logOf`.)

**Note on the rejected alternatives.**
- *Not `BORDERLINE`.* One might ask "is the value-formula antiderivative a reusable object mathlib
  should have a canonical form for?" — but the genuinely-reusable content is the *formal log*
  (already mathlib `log`/`logOf`) and the *p-adic log* `extLog` (a **separate** mathlibability
  question — the project-specific Iwasawa logarithm, absent from mathlib), not this particular
  `θ⁻¹`-weighted assembly. `Ftilde` itself is unambiguously a construction-internal antiderivative
  with zero external use and a verbatim-but-unnamed origin in the source; no human judgment is needed
  to see it should not be a standalone mathlib def. (The real upstreaming question — "should mathlib
  gain a p-adic logarithm / Kubota–Leopoldt p-adic L-function?" — belongs to `extLog` and the value
  theorem, assessed individually.)
- *Not `YES-add-as-is`* despite Phase 4b = MAXIMALLY GENERAL: maximal generality is necessary but not
  sufficient; the verdicts reference and Phase-6 heuristics are explicit that a MAXIMALLY-GENERAL but
  composable-substrate, K = 0-external, one-liner-without-exemption assembly with no more-general
  literature form is NO, not YES.
- *Not `YES-but-generalise-first`*: there is **no separately-named, strictly-more-general literature
  `F̃_θ`** to restate toward (Phase 4b), and the modern idiom (Phase 4c) is "compose from mathlib
  log", not "generalise the assembly" — so the YES-but-generalise gate (which requires a concrete
  more-general restatement target from the literature/modern-idiom) is not met.
- *Not `NO-mathlib-has-it`*: Phase 5 found no mathlib decl for `Ftilde`, `logSeriesAt`, the p-adic
  log, or the value formula — so the NO-mathlib-has-it gate (which requires citing an existing
  mathlib decl from which our form follows in ≤1 line) does not apply. Mathlib has only a *building
  block* (`log`/`logOf`) for part of the construction, which is the NO-composable situation.

---

## Next step

Keep `PadicLFunctions.MeasureR.Ftilde` as a project-local `noncomputable def` in `ValuesAtOne.lean`;
**do not open a mathlib PR for it.** It is RJW §6.2's transient antiderivative `F̃_θ = −G(θ⁻¹)⁻¹ Σ_c
θ⁻¹(c)·log((1+T)ε_N^c − 1)` (arXiv:2309.15692), a route device for Leopoldt's value formula
`L_p(θ,1)`, with zero external call sites. Mathlib supplies the building block for the reusable part
— the Mercator log of each summand's non-constant component (`PowerSeries.log`/`PowerSeries.logOf`,
`Mathlib/RingTheory/PowerSeries/Log.lean`) — while the per-root constant terms (`extLog p (ε^c−1)`,
the Iwasawa-branch `log_p`, which mathlib does not have) and the `θ⁻¹`/Gauss-sum-weighted character
sum are project-specific. No mathlib-side refactor is required since `Ftilde` has zero external
consumers; optional in-file hygiene (folding each `logSeriesAt(ε^c)`'s non-constant part onto
mathlib's `logOf`, retiring the duplicate `formalLog`) belongs to `logSeriesAt` and is not a
mathlib-quality obligation on `Ftilde`. (Any genuine future upstreaming belongs to the p-adic
logarithm `extLog` and the value theorem `LpFunction_one`, assessed individually — not to this
construction-internal antiderivative.)
