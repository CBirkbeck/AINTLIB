# /mathlibable report — `PadicLFunctions.one_add_mul_derivative_FtildeA`

**Final verdict: `BORDERLINE-needs-human`** — this is Lemma 7.3 of one specific
expository paper (Rodrigues Jacinto & Williams, *An introduction to p-adic
L-functions*, arXiv:2309.15692), a single-use leaf step in that paper's residue
computation. It is true, non-trivial, and absent from mathlib, but its
mathlib-worthiness is entirely contingent on (a) whether the surrounding
Kubota–Leopoldt / Amice–Mahler-transform development is upstreamed at all, and
(b) naming/generality decisions about the project-specific objects `FtildeA`,
`Fa` it is stated in terms of. Those are human judgment calls, not facts the
search can settle. Numbered questions in Phase 7.

---

### Baseline (Phase 0)
- lake build:               **not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.one_add_mul_derivative_FtildeA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:529`
- kind:                      `theorem`
- has sorry:                 no (0 `sorry`/`admit` in `ResidueZeta.lean`)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" —
  the file proves continuity/simple-pole of the p-adic zeta branches at s = 1 and
  computes the residue `1 − p⁻¹` via the explicit antiderivative `F̃_a`.

---

### Statement (Phase 1)

`PadicLFunctions.one_add_mul_derivative_FtildeA` is **a theorem** stating the
following.

Let `p` be prime and `K` a complete ultrametric normed field that is a
`ℚ_p`-algebra of characteristic 0 (the working field `ℂ_p ⊇ ℚ_p(μ_p)` of §7).
For a natural number `a` with `p ∤ a` and `a ≠ 0`, the formal power series
`F̃_a ∈ K⟦T⟧` satisfies the differential identity

  (1 + T) · (d/dT) F̃_a(T)  =  F_a(T),

equivalently `∂F̃_a = F_a` for the derivation `∂ := (1+T) d/dT`, where:

- `F̃_a(T) := log( T/(1+T) · (1+T)^a/((1+T)^a − 1) )`, realised in the project as
  the legal formal composition `−log_p(a) − log(u_a) + (a−1)·log(1+T)`
  (`FtildeA`, `ResidueZeta.lean:469`); and
- `F_a(T) := 1/T − a/((1+T)^a − 1)`, the Mahler transform of the measure μ_a
  (`PadicMeasure.Fa`, `KubotaLeopoldt/MuA.lean:84`), here base-changed from
  `ℤ_p⟦T⟧` to `K⟦T⟧` along `(algebraMap ℚ_[p] K) ∘ PadicInt.Coe.ringHom`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]` — the coefficient field (declared once for the
  whole `section mass`; here only `CharZero K` and the `ℚ_p`-algebra structure are
  load-bearing — they make `formalLog` well-defined and `(1+T)∂(formalLog) = 1`
  hold; the analytic instances are inherited, not used by this theorem).
- `a : ℕ` — the exponent in `(1+T)^a`.

Hypotheses (Lean side):
- `ha : ¬ (p : ℕ) ∣ a` — needed because `Fa p a` is the junk value `0` when
  `p ∣ a` (`Ring.inverse` of a non-unit), while `∂F̃_a ≠ 0`. RJW carries `p ∤ a`
  throughout §4.1 onward.
- `ha0 : a ≠ 0` — needed because `uA 0 = 0` makes the formal substitution junk
  (`HasSubst` fails at constant coefficient `−1`).

Conclusion (math): the antiderivative identity `∂F̃_a = F_a` (RJW Lemma 7.3).

Conclusion (Lean): an equality of `PowerSeries K`:
`(1 + PowerSeries.X) * PowerSeries.derivativeFun (FtildeA p K a)
  = PowerSeries.map ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) (PadicMeasure.Fa p a)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent flag)
Reason: it is RJW's *named* Lemma 7.3, which leans toward BIG (theorem named by
its source). But it is named only *within* an expository paper, it is not a
result attributed to a person/place, it is not a `## Main results` headline of
the file (the headline is the residue/continuity of the zeta branches), and it
is stated entirely in terms of two project-internal bookkeeping power series
(`FtildeA`, `Fa`). On balance it is a **specialised helper lemma**, not a
standalone landmark. Literature width is EXHAUSTIVE regardless of this call.

### One-line check (Phase 2b)

Body line count: ~120 substantive lines. One-liner verdict: **n/a** — kind is
`theorem`, not `def`; the proof is a long multi-step formal-calculus argument.
(Skipped.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "formal power series derivative logarithmic antiderivative (1+T) d/dT identity p-adic L-function measure" | partial | the `(t d/dt)^m Φ_μ|_{t=1}` operator is standard (Iwasawa/Amice); the *specific* `∂F̃_a = F_a` is not a named general result | surfaced the standard measure↔power-series correspondence; the exact antiderivative is paper-specific |
|  2 | WebSearch (named source)         | "arXiv 2309.15692 p-adic L-functions residue zeta Lemma 7.3 antiderivative"                            | yes  | identifies RJW = Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions* | confirms the project formalises this exact paper |
|  3 | WebSearch (general form / aliases)| "Iwasawa power series measure ℤ_p '(1+T) d/dT' derivation Amice transform integral x^m antiderivative formal" | yes  | `∫ x^m dμ = (t d/dt)^m Φ_μ|_{t=1}`; Amice/Mahler transform `μ ↦ Φ_μ` iso to `ℚ_p ⊗ ℤ_p[[T]]` | the *derivation* `(1+T)d/dT` is standard; antiderivatives of specific transforms are computed ad hoc per application |
|  4 | ChatGPT MCP                      | (intended: "standard form / generality / history of the `∂F̃_a = F_a` antiderivative identity")        | n/a  | —                                | **MCP unavailable in this environment** (no `mcp__chatgpt__*` tool); recorded n/a per Phase-0 fallback. Compensated by the verbatim primary source (row 11) + 5 WebSearch queries. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/`                               | n/a  | (no references dir; no `refs/` store) | both absent on this checkout — recorded n/a |
|  6 | nLab                             | "formal logarithm power series derivation (1+T)d/dT logarithmic derivative formal group" (via WebSearch site results) | partial | nLab *formal group*: log_F is the unique series with `∂/∂X log_F(X) = p(X)`; logarithmic derivatives of formal series are standard | nLab has the *generic* formal-log / formal-group-log notion, not this measure-transform antiderivative |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | not a categorical concept — it is a concrete formal-power-series calculus identity |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (analytic NT / Iwasawa theory) |
|  9 | MathOverflow / Math.StackExchange| "p-adic zeta residue s=1 Kubota-Leopoldt explicit antiderivative power series 1/T − a/((1+T)^a−1)"      | no   | only general Kubota–Leopoldt pole/Laurent-expansion facts; no hit on the specific antiderivative | the residue `1 − p⁻¹` and pole-at-`s=1` are classical; the explicit `F̃_a` antiderivative device is RJW's exposition |
| 10 | recent arXiv (last 5 years)      | covered by rows 1–3 (arXiv-heavy result lists) — Eisenstein-measure / Γ-transform / Bernoulli-congruence papers | partial | many compute derivatives/Γ-transforms of measure power series; none state this `∂F̃_a = F_a` as a reusable lemma | the operation is a *technique*, applied ad hoc; not a packaged theorem |
| 11 | **Primary source (RJW PDF)**     | `pdftotext` of arXiv:2309.15692, §7, Lemma 7.3 (line 4219)                                              | yes  | **verbatim** (see summary)        | the decisive evidence — exact match to the Lean statement |

The protocol passed: WebSearch ran 5 distinct queries spanning the specific
form, the most-general form (the `(1+T)d/dT` measure derivation), and the
named-source/aliases; local refs, nLab, nCatLab, Stacks, MathOverflow, and
recent arXiv were each checked or recorded `n/a` with reason; and the **primary
source itself was read verbatim**. ChatGPT MCP is genuinely unavailable in this
environment (recorded `n/a`), and its role — pinning the standard form, its
generality, and its history — is fully discharged by the verbatim primary source
plus the 5 web queries.

### Literature summary (Phase 3)

Concept identified as: **RJW Lemma 7.3** — the formal antiderivative identity
`∂F̃_a = F_a` (with `∂ = (1+T) d/dT`) used to compute `∫_{ℤ_p^×} x⁻¹ μ_a` in the
residue calculation of the Kubota–Leopoldt p-adic zeta function at `s = 1`.
Source: Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions*,
arXiv:2309.15692, §7.

Verbatim from the source (pdftotext, §7):

> Recall that `F_a(T) = 1/T − a/((1+T)^a − 1)` is the Mahler transform of `μ_a`;
> we find a power series `F̃_a(T)` such that `∂F̃_a(T) = F_a(T)`, where
> `∂ = (1 + T) d/dT`. …
> To this end, let `F̃_a(T) := log( T/(1+T) · (1+T)^a/((1+T)^a − 1) )`.
>
> **Lemma 7.3.** — Formally, we have `∂F̃_a(T) = F_a(T)`.

Lean ↔ source match: the Lean theorem is **exactly** Lemma 7.3, written in the
unfolded multiplicative form `(1+T)·∂F̃_a = F_a` (the project uses
`derivativeFun` = `d/dT` and multiplies by `(1+T)` rather than naming `∂`). The
Lean `FtildeA` is RJW's `F̃_a` (same docstring, same `−log_p(a) − log(u_a) +
(a−1)log(1+T)` factorisation), and the Lean `Fa` is RJW's `F_a = 1/T −
a/((1+T)^a−1)`. The two junk-value hypotheses (`p ∤ a`, `a ≠ 0`) are
formalisation guards RJW does not need to spell out (he carries `p ∤ a` from
§4.1 informally).

Sources agree on the standard form: **yes** — there is exactly one source for
the *specific* identity (the paper being formalised), and it matches the Lean
form. The *general* ingredient (the `(1+T)d/dT` derivation and the
measure↔power-series Amice/Mahler correspondence) is standard across Iwasawa
theory (Iwasawa, Amice, Schneider–Teitelbaum, de Shalit's *Mahler bases*).

Most general standard form: the identity itself is **not** a general theorem —
it is the antiderivative of one specific transform `F_a`. There is no broader
"standard form" to weaken toward; the generality lives in the *coefficient ring*
and the *derivation API*, not in the statement.

Generality dimensions where the literature varies:
  - Coefficient field: RJW works over `ℂ_p`; the project works over an abstract
    `K` (any complete ultrametric `CharZero` `ℚ_p`-algebra). The project is
    already *more* general than the paper on this axis.
  - The derivation `∂ = (1+T)d/dT`: a fixed, standard operator — no variation.

Disagreement with the literature: **none**. The Lean statement is RJW's Lemma
7.3 verbatim (modulo the formalisation guards and the abstract `K`).

---

### Generality analysis — `PadicLFunctions.one_add_mul_derivative_FtildeA`

Literature-standard form (from Phase 3): `∂F̃_a = F_a` over `ℂ_p`, `p ∤ a`.

| # | Parameter / hypothesis      | Current Lean form                                  | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|----------------------------------------------------|---------------------------------------|---------------------|----------------------------------|
| 1 | `K` (coefficient field)     | abstract complete ultrametric `CharZero` `ℚ_p`-alg | concrete `ℂ_p`                        | already MORE general | the project already abstracts RJW's `ℂ_p` to any such `K`. The proof only needs `CharZero` (for `formalLog` and `(1+T)∂log = 1`) and the `ℚ_p`-algebra map (to base-change `F_a` from `ℤ_p`). The four analytic instances on `K` are inherited from `section mass`, not used here. |
| 2 | `ha : ¬ p ∣ a`              | `p ∤ a`                                            | `p ∤ a` (RJW §4.1)                    | NO                  | `Fa p a` is junk (`0`) when `p ∣ a` while `∂F̃_a ≠ 0`; the identity is *false* without it. This is a genuine mathematical hypothesis, not over-constraint. |
| 3 | `ha0 : a ≠ 0`               | `a ≠ 0`                                            | implicit (`a ≥ 1`)                    | NO                  | `uA 0 = 0` breaks the formal substitution (`HasSubst` fails); `F̃_0` is junk. Genuine guard. |
| 4 | the derivation `(1+T)d/dT`  | `(1+X)*derivativeFun`                              | `∂ = (1+T)d/dT`                       | NO                  | fixed standard operator; nothing to weaken. |

This is the rare case where the *project's* form is already more general than the
literature's (abstract `K` vs concrete `ℂ_p`); the two hypotheses are
mathematically necessary, not artifacts.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for this specific identity — it is
already abstracted over the coefficient field beyond RJW's `ℂ_p`, and the two
hypotheses are essential).
Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

One latent over-binding worth noting (does not change the verdict): the theorem
sits inside `section mass` and so silently carries `[IsUltrametricDist K]
[CompleteSpace K]` instances it does not use (only `CharZero` + the algebra map
matter). If this were ever upstreamed it should drop those (the project already
uses `omit` for exactly this on neighbouring lemmas, e.g. `constantCoeff_FtildeA`).
That is a `/cleanup`-grade tidy, not a generality flip.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                           | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                 | no       | — | already fully typeclass-driven (`NormedField`, `NormedAlgebra ℚ_[p] K`, `CharZero`); nothing bundled to unbundle |
|  2 | sequences/metric → filters/topological?                                                            | no       | — | this is a *formal* (algebraic) power-series identity; no convergence, no topology in the statement |
|  3 | construct an object → universal-property class?                                                    | no       | — | it is a stated equation between two given series, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | — | no substructure here |
|  5 | vector-space/metric/field-specific → weaker typeclass (module/(semi)ring)?                          | partial  | the *generic shape* `(1+X)∂(antiderivative) = transform` could in principle live over a `CharZero` `ℚ`-algebra — but the *content* (`F_a`, `F̃_a`, μ_a) is irreducibly p-adic | no real downstream — see honesty bar below |
|  6 | 1-categorical → higher/∞-categorical?                                                               | no       | — | not categorical |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                    | no       | — | `a : ℕ` is the binomial exponent; `(1+T)^a` with `a ∈ ℕ` is exactly right |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the statement is already in mathlib's contemporary formal-power-
series-derivation idiom (`PowerSeries.derivativeFun`, `HasSubst`,
`PowerSeries.map`); the only "abstraction" on offer (row 5) would strip the
identity of the very p-adic content (`F_a` = Mahler transform of μ_a) that gives
it meaning — that is abstraction for its own sake, which the honesty bar rejects.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; skipped per the skill's scope rule.

---

### Mathlib search-status: `PadicLFunctions.one_add_mul_derivative_FtildeA`

[A] Lean-Finder       n/a — tool not available in this environment (recorded n/a)
[B] Loogle            type-pattern `(1 + PowerSeries.X) * PowerSeries.derivativeFun _ = _`  — n/a (no Loogle tool here); reasoned from the grep below
[C] LeanSearch        "(1+T) times derivative of antiderivative equals Mahler transform of p-adic measure" — n/a (no tool); reasoned from grep
[D] Grep mathlib src  `FtildeA`, `one_add_mul_derivative`, `Amice`, `mahlerTransform`, `kubota`, `leopoldt`, `p-adic L-function`, `\(1 \+ X\) \* .*derivative`  — **no hits** in `.lake/packages/mathlib/Mathlib/`
[E] Name pattern      grep `derivativeFun`, `derivative_subst`, `derivative_pow` — **hits, but only the generic API** (`Mathlib/RingTheory/PowerSeries/Derivative.lean`); none about `F̃_a`/`F_a`

Searched for both:
  - the user's current form (`(1+X)∂F̃_a = M(F_a)`) — absent.
  - the literature-standard form (`∂F̃_a = F_a`, the antiderivative of the Mahler
    transform) — absent, and so is the entire surrounding development.

What mathlib *does* have (the building blocks the proof uses, all generic):
  - `PowerSeries.derivativeFun`, `PowerSeries.derivative_X`,
    `PowerSeries.derivative_pow`, `PowerSeries.derivativeFun_mul`,
    `PowerSeries.derivativeFun_smul`, `PowerSeries.derivativeFun_add`,
    `PowerSeries.derivativeFun_C`, `PowerSeries.derivative_subst`
    (`Mathlib/RingTheory/PowerSeries/Derivative.lean`).
  - `PowerSeries.map`, `HasSubst`, `substAlgHom` (substitution/base-change API).
  - **Not** present: any Kubota–Leopoldt p-adic L-function, any Amice/Mahler
    transform of measures, any `Fa`/`FtildeA`/`uA`/`geomSum`, any p-adic
    formal-log antiderivative device. Grep for `kubota|leopoldt|p-adic
    L-function|padicLFunction` over the whole mathlib tree returned **nothing**.

Concluded: **not in mathlib** (the specific identity and its entire surrounding
machinery are absent; only the generic power-series-derivative API exists, and
that is what the proof consumes).

---

### Call sites — `PadicLFunctions.one_add_mul_derivative_FtildeA`

Internal use count: **1** (within the project, not counting the declaring stmt)
External-to-file callers: **0 distinct files** (the one use is in the same file)

| Caller file:line                | Usage pattern (one-line excerpt)                                                |
|---------------------------------|---------------------------------------------------------------------------------|
| ResidueZeta.lean:927            | `rw [one_add_mul_derivative_FtildeA p K ha ha0, mahlerK_baseChange_muA]`         |

That single site is inside `p_mul_constantCoeff_mahlerK_rhoA`
(`ResidueZeta.lean:913`), where it supplies the bridge
`(1+X)·∂F̃_a = mahlerK(baseChange μ_a)` toward the mass identity
`∫_{ℤ_p^×} x⁻¹ μ_a = −(1−p⁻¹)·log_p(a)` — i.e. it is one rewrite step in the
larger residue computation.

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?):
  - (none) — no other proof re-derives `(1+X)∂F̃_a = …` inline.

Composability signal (per the Phase-6.0 table): **K = 1 internal use only, no
external callers, no inline re-derivation.** This is the "possibly the wrong
abstraction / could be inlined" pattern — *except* that the proof body is ~120
lines, so inlining is not actually viable (see Phase 6). The signal therefore
reads as: a genuine, non-trivial helper lemma that currently has exactly one
consumer because it is the unique step in one computation. It is real
(not dead code, not a bypassed wrapper), but its audience is a single proof in a
single paper-formalisation.

---

### Composition check (Phase 6)

Can `one_add_mul_derivative_FtildeA` be derived from mathlib in ≤3 chained calls?

Attempt 1: chain the generic derivative lemmas (`derivative_subst`,
`derivative_pow`, `derivativeFun_mul`, `derivativeFun_smul`) directly.
  - Mathlib decls used: the `PowerSeries.derivative*` family.
  - Result: **fails.** These give the *Leibniz/chain rules*, but assembling them
    into `∂F̃_a = F_a` requires: (i) Step A — `a·u_a = base-change of geomSum`;
    (ii) Step B — `u_a·(∂log)(u_a−1) = 1` (substituting `u_a−1` into
    `(1+X)∂log = 1`); (iii) differentiating `α·(u_a·X) = (1+X)^a − 1` and
    multiplying by `(1+X)`; (iv) the RHS computation
    `M(F_a)·((1+X)^a−1) = S − a` via `one_add_X_pow_sub_one_mul_Fa`;
    (v) `G = (1+X)^a − 1 ≠ 0` and a `mul_right_cancel₀`; (vi) a final
    `linear_combination`. This is genuine multi-step formal calculus, not a
    composition.
  - Notes: the proof body is ~120 lines and depends on four project lemmas
    (`natCast_smul_uA_eq_map_geomSum`, `uA_mul_subst_derivative_formalLog`,
    `one_add_mul_derivative_formalLog`, `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`)
    that are themselves project-specific.

Attempt 2: derive from a more general mathlib antiderivative theorem.
  - Result: **fails** — no such theorem exists (Phase 5); mathlib has no Mahler
    transform and no `F_a`/`F̃_a`.

Conclusion: **NOT-COMPOSABLE** (far more than 3 mathlib calls; it is a real proof
resting on irreducibly project-specific objects).

---

## Verdict: `PadicLFunctions.one_add_mul_derivative_FtildeA`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified **exactly** as RJW Lemma 7.3
  (arXiv:2309.15692 §7), matched verbatim against the primary source; the
  underlying `(1+T)d/dT` derivation is standard, the specific antiderivative is
  paper-internal.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for this identity (already
  abstracted over `K` beyond RJW's `ℂ_p`; both hypotheses essential); Phase 4c
  found **no** real modern-idiom improvement.
- Mathlib search (Phase 5): **not in mathlib** — neither the identity nor the
  entire Kubota–Leopoldt / Amice–Mahler-transform development is present; only
  the generic `PowerSeries.derivative*` API the proof consumes.
- Composition check (Phase 6): **NOT-COMPOSABLE** (~120-line proof on
  project-specific objects; K = 1 internal use, 0 external).

**Rationale.**

This is not a "is it true and useful" question — it plainly is both — but a "is
this the right *unit* for mathlib, and is now the right time" question, and that
turns on facts the search cannot supply. The result is genuinely novel for
mathlib and non-trivial (so it is neither `NO-mathlib-has-it` nor
`NO-composable-from-mathlib`), and it is maximally general for what it states
(so the generality gate does not force `YES-but-generalise-first`). The reason it
is **not** a clean `YES-add-as-is` is that the theorem is *constitutively* about
two objects — `FtildeA` (`F̃_a`) and `Fa` (`F_a`) — that exist only as
bookkeeping inside this one paper-formalisation. A prior `/mathlibable` run put
the sibling ingredient `uA` at `NO-composable-from-mathlib`; `Fa` and `FtildeA`
have never been individually assessed and are not in mathlib. A theorem can only
be upstreamed once the *definitions it mentions* have a home and a name. So the
mathlib-worthiness of this lemma is downstream of, and inseparable from, the
upstreaming decision for the whole p-adic-L-function tower (Kubota–Leopoldt zeta,
the Amice/Mahler transform `μ ↦ Φ_μ`, `F_a` as the transform of `μ_a`,
`F̃_a` as its antiderivative). If that tower goes to mathlib, this lemma ships
*with* it (as `YES-add-as-is`, after the `omit`-the-unused-instances tidy noted
in Phase 4b); if the tower stays project-local, this lemma stays with it. The
single internal call site and zero external consumers reinforce that it is, today,
a private step in one computation. That packaging-and-timing call belongs to the
maintainer, not the search.

**Numbered questions (≤5):**

1. Is the **p-adic L-function development as a whole** (Kubota–Leopoldt ζ_p, the
   Amice/Mahler transform of measures on ℤ_p, `F_a`, `F̃_a`, μ_a) intended for
   upstreaming to mathlib, or is it a standalone project formalising
   arXiv:2309.15692 that will live in AINTLIB? (If standalone → drop from mathlib
   consideration; the lemma is correctly project-local.)
2. If yes to (1): should the **base objects** `Fa` / `FtildeA` / `uA` be
   upstreamed first under mathlib-canonical names (e.g. a `PadicLFunction.`
   namespace), at which point this lemma ships *with* them as `YES-add-as-is`?
3. Is the abstract coefficient field `K` (any complete ultrametric `CharZero`
   `ℚ_p`-algebra) the form mathlib should carry, or should the upstreamed version
   be pinned to `ℂ_p` to match RJW and the rest of any future p-adic-L API?
4. For an upstreamed version, do you want the statement kept in the
   `(1+T)·derivativeFun` form, or repackaged behind a *named* `∂ = (1+T)d/dT`
   derivation (RJW's `∂`) so the API reads `∂F̃_a = F_a`? (A named `∂` would be a
   small but real piece of reusable formal-NT infrastructure.)
5. Acceptable to ship the lemma *with the unused* `[IsUltrametricDist K]
   [CompleteSpace K]` instances dropped (via `omit`, as neighbouring lemmas
   already do), since the proof needs only `CharZero K` + the `ℚ_p`-algebra map?

**Next action:** user answers the questions; re-run
`/mathlibable PadicLFunctions.one_add_mul_derivative_FtildeA` to resolve the
verdict. Likely outcomes based on the answers:
  - **(1) standalone / project-local** → drop from mathlib consideration; keep as
    the project lemma it is (RJW Lemma 7.3), no rename needed.
  - **(1) yes-upstream + (2) base objects first** → flips to **`YES-add-as-is`**,
    shipped in the same PR series as `Fa`/`FtildeA` under a mathlib namespace,
    after dropping the unused instances (q5) and optionally introducing the named
    `∂` derivation (q4). Proposed home if so:
    `Mathlib/NumberTheory/Padics/LFunction/...` (a directory that does not yet
    exist — itself confirming the whole area is the real gap).

---

## Next step

User answers the five Phase-7 questions; re-run
`/mathlibable PadicLFunctions.one_add_mul_derivative_FtildeA`. The pivotal
question is (1): whether the surrounding Kubota–Leopoldt / Amice–Mahler-transform
development is bound for mathlib at all. A "no" keeps this correctly project-local;
a "yes (with the base defs first)" flips it to `YES-add-as-is`, shipped alongside
`Fa`/`FtildeA` in a new `Mathlib/NumberTheory/Padics/LFunction/` area.
