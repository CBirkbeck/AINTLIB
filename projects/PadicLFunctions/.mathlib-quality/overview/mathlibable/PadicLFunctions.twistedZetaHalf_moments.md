# `/mathlibable` report — `PadicLFunctions.twistedZetaHalf_moments`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-19. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> The *mathematics* this theorem encodes is **canonical**: it is the moments form of the
> Kubota–Leopoldt interpolation property — *"the p-adic zeta function (here twisted and halved
> into the Eisenstein constant coefficient `A₀ = x·ζ_p/2`) interpolates `(1−p^{k−1})ζ(1−k)/2`,
> the constant Fourier coefficient of the p-stabilised Eisenstein series `E_k^{(p)}`"* (RJW
> arXiv:2309.15692 Thm 4.1 / Prop 4.11, and §8 Def 8.1 + Thm 8.2; Serre 1973). But the Lean
> statement lives **entirely on a substrate mathlib does not have** — the linear-functional p-adic
> measures `PadicMeasure`, the Iwasawa algebra `Λ(ℤ_p^×)` and its total fraction ring
> `Q(ℤ_p^×) = QuotientField`, the pseudo-measure formalism, `padicZeta`, the x-twist, and the
> twisted-pseudo-measure *witness encoding* (erratum #11) in which the moment is stated. Mathlib
> has the *rational* value `(1−p^{k−1})ζ(1−k)` ingredient (`riemannZeta_neg_nat_eq_bernoulli` =
> the project's `zetaNeg`) but **not** the p-adic interpolation theorem nor any of its carrier
> objects. The theorem has **0 call sites outside its defining file** (used once, inside
> `eisensteinFamily_interpolation`). So it cannot be a standalone mathlib lemma; whether the whole
> RJW measure / p-adic-zeta layer is destined for mathlib, and in what form the interpolation
> theorem should be stated there, is exactly the project-policy / mathematical-taste judgment the
> skill routes to a human. (This matches the verdicts already recorded for the sibling
> declarations in the same file — `twistedZetaHalf`, `divisorMeasure_moment`, `unitsTwist`.)

---

### Baseline (Phase 0)

- lake build:                **build not re-run; reasoned from source** (per the task BUILD NOTE — `lake build` is stale/slow in this checkout; `.lake/build` artifacts predate today, mathlib present at `.lake/packages/mathlib`). The declaration and its full dependency chain were read directly from source.
- decl `PadicLFunctions.twistedZetaHalf_moments`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:259`
- kind:                       **theorem**
- has sorry:                  **no** — `grep -c sorry` is `0` for the target file *and* for the whole dependency chain (`KubotaLeopoldt/ZetaP.lean`, `KubotaLeopoldt/ZetaValues.lean`, `Measure/PseudoMeasure.lean`). The proof and every lemma it invokes are complete.
- module docstring summary:   "The p-adic family of Eisenstein series (RJW §8)" — the Kubota–Leopoldt pseudo-measure interpolates the constant coefficients of the p-stabilised Eisenstein series; the non-constant coefficients are interpolated by divisor-sums of Dirac measures. The constant coefficient `A₀ = x·ζ_p/2` is `twistedZetaHalf`; *this* theorem computes its moments.

---

### Statement (Phase 1)

`PadicLFunctions.twistedZetaHalf_moments` is **a theorem** stating the following.

Let `p` be an odd prime, `b ∈ ℤ_p^×` a unit, and `k ≥ 4`. Let `A₀ = twistedZetaHalf = x·ζ_p/2`
be the constant coefficient of the Λ-adic Eisenstein family (the x-twist of the Kubota–Leopoldt
p-adic zeta pseudo-measure, halved). Because `A₀` is **not** itself a pseudo-measure (the pole of
`x·ζ_p` sits at the character `x⁻¹`, not the trivial character — the project's **erratum #11**),
its moments are recorded through a *witness*: any `ν ∈ Λ(ℤ_p^×)` with

  `((b·δ_b) − 1)·A₀ = ν`   in `Q(ℤ_p^×)`

(i.e. `ν` witnesses that the **twisted** denominator `(b·[b] − [1])` clears `A₀` into the Iwasawa
algebra) satisfies the moment identity

  `∫_{ℤ_p^×} x^{k−1} · ν  =  (b^k − 1) · (1 − p^{k−1}) · ζ(1−k) / 2`   (as an element of `ℚ_p`).

The right-hand side is exactly **`(b^k − 1)` times the constant Fourier coefficient
`(1 − p^{k−1})ζ(1−k)/2` of the p-stabilised Eisenstein series `E_k^{(p)}`** (RJW Def 8.1); the
factor `(b^k − 1)` is the moment of the twisted denominator `(b·[b] − [1])`, the analogue of the
`(b^k − 1)` factor in the Kubota–Leopoldt interpolation (RJW Prop 4.11). In short: *`A₀` p-adically
interpolates the constant term of `E_k^{(p)}`*, in the corrected twisted-witness encoding.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `hp2 : p ≠ 2` — odd prime (needed for the `/2`: `2` is a unit of `ℤ_p`).
- `b : ℤ_[p]ˣ` — the auxiliary unit whose twisted denominator `(b·[b] − [1])` clears `A₀`.
- `{k : ℕ}` with `hk : 4 ≤ k` — the weight; `k − 1` is the moment exponent.
- `ν : PadicMeasure p ℤ_[p]ˣ` — the Iwasawa-algebra witness.

Hypotheses (Lean side):
- `hν : algebraMap _ (QuotientField p) ((b : ℤ_[p]) • dirac p b − 1) * twistedZetaHalf p hp2 = algebraMap _ _ ν` — `ν` witnesses `(b·[b] − [1])·A₀ ∈ Λ(ℤ_p^×)`.

Conclusion (math): the `(k−1)`-th moment of the witness `ν` equals `(b^k−1)(1−p^{k−1})ζ(1−k)/2` —
`(b^k−1)` × the constant coefficient of `E_k^{(p)}`.

Conclusion (Lean):
`((ν (PadicMeasure.unitsPowCM p (k − 1)) : ℤ_[p]) : ℚ_[p]) = ((b : ℚ_[p])^k − 1) * (1 − (p : ℚ_[p])^(k−1)) * ((zetaNeg (k−1) : ℚ) : ℚ_[p]) / 2`.

**Objects this statement is built from (all project-local except where noted):**
- `PadicMeasure p X` — an `abbrev` for `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the *linear-functional*
  notion of a p-adic measure (RJW Def 3.6; `Measure/Basic.lean:52`). **Not** mathlib's
  `MeasureTheory.Measure`. **Not in mathlib.**
- `PadicMeasure.QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` — the total fraction ring
  `Q(ℤ_p^×)` of the Iwasawa algebra `Λ(ℤ_p^×)` (RJW Def 3.34; `Measure/PseudoMeasure.lean:804`).
  **Not in mathlib.**
- `PadicMeasure.dirac`, `PadicMeasure.unitsPowCM p k` (`u ↦ u^k`), the convolution `CommRing`
  structure, `unitsTwist`/`quotientTwist` (x-twist), `padicZeta`, `twistedZetaHalf` — all
  project-local. **None in mathlib.**
- `zetaNeg k := (−1)^k · bernoulli(k+1)/(k+1)` (`KubotaLeopoldt/ZetaValues.lean:17`) — the *rational*
  value `ζ(−k)`. Mathlib **does** have this value as `riemannZeta_neg_nat_eq_bernoulli`
  (`= (−1)^k bernoulli(k+1)/(k+1)`); the project keeps a rational copy to avoid importing complex
  analysis into the main chain.

Proof body (≈12 lines, all over project objects): extract a witness `νb` for `(b·[b]−[1])·ζ_p`
from `padicZeta_isPseudoMeasure`; show `ν = c · unitsTwist νb` (`c = (2⁻¹ : ℤ_[p])`) by
`IsFractionRing.injective` + the helper `twistedZetaHalf_witness_eq`; convert the moment of `ν`
into `c · (νb at exponent k)` via `unitsTwist_moment` (the twist shifts the exponent `k−1 ↦ k`);
then substitute the Kubota–Leopoldt moment `padicZeta_moments` (`∫x^k·νb = (b^k−1)(1−p^{k−1})ζ(1−k)`)
and `coe_inv_two` (`c = (2:ℚ_p)⁻¹`); close with `field_simp`.

So this theorem is the **Eisenstein-constant-term corollary of `padicZeta_moments`**: the
Kubota–Leopoldt interpolation formula, twisted by `x` (exponent shift `k−1 ↦ k`) and halved.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG/SMALL — recorded BIG for framing).
Reason: although it is mechanically a *corollary* of `padicZeta_moments`, it is the **p-adic half of
RJW's §8 Eisenstein-family Theorem 8.2(b)** — a named, headline result of Part I's closer (it is the
constant-coefficient leg of `eisensteinFamily_interpolation`, the file's main theorem). The
mathematical content (p-adic zeta interpolates the Eisenstein constant term) is a theorem "named
after" the Serre/Kubota–Leopoldt construction, which per the skill's BIG criteria is "basically
guaranteed to be in or near the literature in some form" — and it is.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for the report's
framing.)

### One-line check (Phase 2b)

Body line count: ≈12 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.** (The one-line def exemption analysis does
not apply to a proof; the section is skipped.)

---

### Literature search table — EXHAUSTIVE protocol

The mathematical concept is **the interpolation / moment property of the Kubota–Leopoldt p-adic zeta
function** — `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)` — specialised to its appearance as the
**constant Fourier coefficient `(1−p^{k−1})ζ(1−k)/2` of the p-stabilised Eisenstein series**, in the
twisted-witness (`A₀ = x·ζ_p/2`) encoding. The project's substrate objects are searched as context.

| #  | Channel                          | Query                                                                                                                              | Hit? | Standard form found                                                                                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Kubota-Leopoldt p-adic zeta interpolation formula values negative integers (1−p^{k−1}) zeta(1−k) Bernoulli"                        | yes  | `ζ_p(n) = lim (1−p^{−s})ζ(s)`; values at negative integers `= (1−p^{k−1})ζ(1−k)` up to an Euler factor               | Mazur-construction notes (Guitart), Koblitz, HandWiki "p-adic L-function", LTCC notes (= RJW). The Euler factor `(1−p^{k−1})` and the Bernoulli identity `ζ(−k)=(−1)^k B_{k+1}/(k+1)` are textbook-standard. |
|  2 | WebSearch (general form / Eisenstein constant term) | "p-stabilised Eisenstein series constant term coefficient (1−p^{k−1}) zeta(1−k)/2 Fourier expansion"                                 | yes  | `E_k^{(p)} = (1−p^{k−1})ζ(1−k)/2 + Σ σ^p_{k−1}(n) qⁿ`                                                                | The constant Fourier coefficient of the p-stabilised Eisenstein series is exactly `(1−p^{k−1})ζ(1−k)/2` — the RHS of our theorem (modulo the `b^k−1` twisted-denominator factor). Standard modular-forms exercise (DS05 Ch.1). |
|  3 | WebSearch (named-after / mechanism) | "Mazur measure p-adic zeta Eisenstein series constant coefficient interpolation Serre bootstrap moments pseudo-measure negative integers" | yes  | "Mazur's measure μ_c on ℤ_p^× produces special values **ζ(1−k)(1−p^{k−1})**; the constant term of the p-adic Eisenstein family = the p-adic zeta" | **Near-verbatim match.** Springer (Koblitz Ch.2), arXiv:1204.3878 (Analytic constructions of p-adic L-functions and Eisenstein series), and **arXiv:2309.15692 (the exact source, RJW)** all surfaced. Confirms the moment formula and the Serre bootstrap: interpolating non-constant coefficients forces interpolation of the constant term = the p-adic zeta. |
|  4 | ChatGPT MCP                      | (intended: "standard form of the Kubota–Leopoldt interpolation/moment formula, its generality, and historical evolution")          | n/a  | —                                                                                                                    | **n/a — ChatGPT MCP not configured in this environment** (`~/.claude` has no chatgpt MCP entry; only OAuth-gated unrelated MCPs are listed; consistent with every sibling report in this project). Compensated with the extra WebSearch passes (#1–#3) **and a direct read of the source PDF** (rows 5/10), which answer the standard-form + historical-evolution question authoritatively. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                                            | n/a  | (directories absent)                                                                                                 | **n/a — neither directory exists.** Compensated by fetching the source paper directly (arXiv:2309.15692) and **reading the relevant pages (26–29, 43–45) with the PDF reader** — see rows 3 and 10. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/p-adic+L-function`                                                                                  | no   | (page returned HTTP 404)                                                                                             | The nLab `p-adic+L-function` page is absent/404. nLab has scattered Iwasawa-theory material but no isolated page stating "`∫x^k ζ_p = (1−p^{k−1})ζ(1−k)`" as a named formula. Recorded so the channel is not silently skipped. |
|  7 | nCatLab (if categorical)         | (the interpolation/moment formula is an analytic identity, not a categorical universal construction)                               | n/a  | —                                                                                                                    | n/a — not a categorical concept; it is a special-value interpolation identity. Covered by #1–#3. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                                                  | n/a  | —                                                                                                                    | n/a — not an algebraic-geometry / scheme-theoretic concept (p-adic L-function special values). |
|  9 | MathOverflow / Math.StackExchange| "p-adic L-function interpolation property moment measure Iwasawa algebra x^{k−1} Eisenstein family constant coefficient" (and survey hits) | yes  | "p-adic L-functions interpolating L-values are elements of the Iwasawa algebra; the value of the Kubota–Leopoldt zeta = the constant in the Fourier expansion; the constant term of the p-adic Eisenstein family ∈ Λ" | ahilado expository post + Iwasawa-Main-Conjecture survey PDFs. Confirms the "constant term of the Eisenstein family = p-adic zeta = Iwasawa-algebra element" framing the project formalises. |
| 10 | recent arXiv (last 5 years) + **direct source read** | arXiv:2309.15692 (RJW) — **read pages 26–29 (§4) and 43–45 (§8) directly from the downloaded PDF**                                  | yes  | **Thm 4.1 / Prop 4.11**: `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)` for `k>0`. **Def 8.1**: `E_k^{(p)} = (1−p^{k−1})ζ(1−k)/2 + Σ σ^p_{k−1}(n)qⁿ`. **Thm 8.2**: family `E = Σ A_n qⁿ`, `A₀ = xζ_p/2`, "`A₀` interpolates the constant term of the Eisenstein series." | This is the **exact source** of the declaration. RJW state the moment formula (Prop 4.11) and the §8 family verbatim; the project's `twistedZetaHalf_moments` is the Lean realisation of "`A₀` interpolates the constant term", in the *corrected* (erratum #11) twisted-witness encoding with the extra `(b^k−1)` factor. |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (the specific
interpolation formula; the general Eisenstein-constant-term form; the named-after / Serre–Mazur
mechanism); the ChatGPT-MCP row is honestly recorded n/a (tool genuinely unavailable) with the
compensating WebSearch + **authoritative source-PDF read** noted; local refs checked (absent → n/a,
compensated by fetching the source); nLab checked (404, recorded); nCatLab/Stacks recorded n/a with
reasons; MathOverflow/SE perspective captured; recent arXiv located **and the source paper was read
directly** (rows 3, 10).

### Literature summary (Phase 3)

Concept identified as: **the interpolation (moment) property of the Kubota–Leopoldt p-adic zeta
function** — `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)` (RJW Thm 4.1 / Prop 4.11) — in its incarnation
as the **constant Fourier coefficient `(1−p^{k−1})ζ(1−k)/2` of the p-stabilised Eisenstein series
`E_k^{(p)}`** (RJW Def 8.1), realised by the family's constant coefficient `A₀ = x·ζ_p/2` (RJW
Thm 8.2). The whole construction is **Serre's 1973 bootstrap** (Ser73, Corollaire 2): interpolating
the non-constant coefficients of the Eisenstein family forces interpolation of the constant term,
which is the p-adic zeta function.

Sources agree on the standard form: **yes** — uniformly across the literature (Koblitz, Mazur,
Serre, Kubota–Leopoldt, and the RJW source notes). The moment/interpolation formula
`∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` and the Eisenstein constant term `(1−p^{k−1})ζ(1−k)/2` are textbook
canonical; `ζ(−k) = (−1)^k B_{k+1}/(k+1)` is the standard Bernoulli identity (mathlib's
`riemannZeta_neg_nat_eq_bernoulli`).

Most general standard form: for a topological generator `a` (or any auxiliary `b`) of `ℤ_p^×`, the
unique pseudo-measure `ζ_p` on `ℤ_p^×` with `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` for all `k>0`; equivalently
(RJW §5, Thm 5.1) `∫ χ(x)x^k ζ_p = L(χ,1−k)` for Dirichlet `χ` of p-power conductor — the
**Dirichlet-twisted generalisation**. The Eisenstein-family constant term `A₀ = x·ζ_p/2` is the §8
specialisation; *our theorem* is its moment computation in the twisted-witness encoding.

Generality dimensions where the literature varies:
- **The L-value interpolated.** Most general: `L(χ,1−k)` for any Dirichlet `χ` of p-power conductor
  (RJW Thm 5.1). Here: the trivial-character value `(1−p^{k−1})ζ(1−k)`, halved, with the `(b^k−1)`
  twist factor. The project formalises the trivial-character / Eisenstein case (`χ` twists are the
  separate `Interpolation/` development).
- **The carrier / encoding of "moment".** Classical / mathlib: `MeasureTheory.integral` against a
  σ-additive measure. RJW / Iwasawa theory (this project): a *measure is a bounded `ℤ_[p]`-linear
  functional* on `C(ℤ_p^×, ℤ_[p])`; the "integral `∫x^k·μ`" is function application `μ(unitsPowCM k)`.
  Under the linear-functional definition, the moment is `μ` applied to a monomial.
- **The pseudo-measure witness.** Because `A₀` is not a pseudo-measure (erratum #11), the moment is
  stated through the witness `ν` of `(b·[b]−[1])·A₀ ∈ Λ`, introducing the `(b^k−1)` factor — the same
  device RJW use for `ζ_p` itself (Prop 4.11's `∫x^k·([b]−[1])ζ_p` form).

Disagreement with the literature: **none**. The Lean statement is a faithful, correct realisation of
RJW Thm 8.2(b)/Def 8.1 (the constant-coefficient interpolation), with the project's documented
correction (erratum #11: the witness is twisted because `A₀` is not literally a pseudo-measure).

---

### Generality analysis — `PadicLFunctions.twistedZetaHalf_moments`

Literature-standard form (from Phase 3): the Kubota–Leopoldt interpolation
`∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)` (and its Dirichlet generalisation `∫χ(x)x^k ζ_p = L(χ,1−k)`),
specialised to the Eisenstein-family constant term `A₀ = x·ζ_p/2` with `∫x^{k−1}·A₀` = the constant
coefficient of `E_k^{(p)}`.

| # | Parameter / hypothesis            | Current Lean form                                            | Literature-standard form                                       | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------------------------------------------|----------------------------------------------------------------|---------------------|---------------------------------|
| 1 | `hp2 : p ≠ 2`                     | odd prime                                                    | the `/2` in the Eisenstein constant term needs `2` invertible  | NO (essential)      | `A₀ = x·ζ_p/2`; `2` must be a unit of `ℤ_p`, i.e. `p ≠ 2`. Intrinsic to the *halved* Eisenstein constant term, not an artificial restriction. |
| 2 | `hk : 4 ≤ k`                      | weight `k ≥ 4`                                              | RJW §8 states the family interpolation for even `k ≥ 4`        | partial             | The *p-adic* moment identity here actually only uses `0 < k` (the proof passes `by omega : 0 < k` to `padicZeta_moments`); `4 ≤ k` is carried to match `eisensteinFamily_interpolation`'s hypothesis (evenness/`k≥4` enter only in the *complex* identification of the constant term with `E_k^{(p)}`, in `EisensteinComplex.lean`). A `0 < k` version is mechanically available — but it is a *project-internal* weakening of a project lemma, not a step toward a mathlib form. |
| 3 | the value `(1−p^{k−1})ζ(1−k)`     | trivial-character zeta value, halved                        | `L(χ,1−k)` for any Dirichlet `χ` of p-power conductor (RJW §5) | yes (large)         | The Dirichlet-twisted generalisation is the literature's fuller form — but it is a *different, larger development* (the project's `Interpolation/` files), not a signature weakening of *this* lemma. |
| 4 | carrier `PadicMeasure p ℤ_[p]ˣ` / `QuotientField p` | `ℤ_[p]`-linear-functional measures, their fraction ring | the source's `𝒪_L`-valued measures (RJW §5)                 | yes (deferred)      | The project explicitly defers the general-`𝒪_L` coefficient case to a later pass (`Measure/Basic.lean` docstring). Not available now without that infrastructure. |

**The decisive fact, not a row above:** the literature object *and all of its narrower/general forms*
live on a substrate **mathlib does not have** — there is no Iwasawa-algebra-of-measures, no
`QuotientField`, no `padicZeta`, no pseudo-measure formalism in mathlib (Phase 5). So the generality
question is moot for a *direct* mathlib contribution: one cannot restate `twistedZetaHalf_moments` in
*any* mathlib-shippable form without first upstreaming the entire RJW §3–§4 + §8 measure / zeta /
family layer.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (trivial-character value vs. the Dirichlet
`L(χ,1−k)`; `4 ≤ k` vs. the `0 < k` the p-adic proof actually needs; `ℤ_[p]` vs. general `𝒪_L`).
Number of weakening opportunities found: 1 cheap project-internal one (`4 ≤ k` → `0 < k`), 2 large
ones (Dirichlet twist; general `𝒪_L`) that are *separate developments*, not regeneralisations of this
lemma.
Proposed restatement (if one pursued the cheap one *within the project*): drop `hk : 4 ≤ k` to
`0 < k` (or `1 ≤ k`), since the proof only feeds `0 < k` into `padicZeta_moments` and
`Nat.sub_add_cancel`. But this changes a *project* lemma to be marginally more general; it does **not**
produce a mathlib-shippable statement, because the carrier objects remain absent from mathlib.
Cost of restatement: **CHEAP** (mechanical) for the `k` weakening *within the project*;
**EXPENSIVE / not-applicable** as a mathlib contribution (substrate must be upstreamed first).

Because the form is STRICTLY NARROWER, a naive reading might push toward `YES-but-generalise-first` —
**but the verdict gate forbids that here**: Phase 5 shows the general form (and the carrier algebra
itself) are *also* absent from mathlib, so the move is "upstream an entire theory", not "generalise
this lemma". That is a project-policy judgment → Phase 7 = BORDERLINE.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                     | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                          | no       | —                                                                                      | Hypotheses are already minimal (`Fact p.Prime`, `p ≠ 2`, `4 ≤ k`); nothing to class-ify. |
|  2 | sequences/metric → filters/topological?                                                                      | no       | —                                                                                      | No limit/convergence content; it is an algebraic moment identity over `Q(ℤ_p^×)`. (The genuine "interpolation as a p-adic limit" content lives in `noMeasure_interpolates_pPow` / the Mahler-transform layer, not here.) |
|  3 | construct an object where a universal-property class would characterise it?                                  | no       | —                                                                                      | This is a *property* of an already-constructed object (`twistedZetaHalf`), not a construction. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                                       | no       | —                                                                                      | No substructure involved. |
|  5 | vector-space/metric/field-specific → weaken to modules/(semi)ring?                                           | partial  | the `𝒪_L`-valued generalisation (row 4a #4) and the Dirichlet-twist (#3)              | These are *separate larger RJW developments* stated over the *same non-mathlib substrate*; there is no mathlib downstream to compose with, so this is not a Phase-4c modernisation of *this* lemma. |
|  6 | 1-categorical → higher/∞-categorical?                                                                         | no       | —                                                                                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structures?                                              | no       | —                                                                                      | The exponent `k` and the rational value `ζ(1−k)` are intrinsically arithmetic; generalising removes the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a mathlib contribution).
Reason: the only "modernisations" on offer (Dirichlet twist; general `𝒪_L`; the cheap `k`-weakening)
are stated over the project's `PadicMeasure`/`QuotientField` substrate, which is itself not in
mathlib. There is no contemporary mathlib idiom that turns *this* theorem into a better *mathlib*
theorem; the abstractions presuppose first upstreaming the whole "p-adic measure = continuous dual +
Iwasawa algebra + pseudo-measure" framework — a separate, much larger question (see Phase 7).

---

### Diamond / defeq risk — `PadicLFunctions.twistedZetaHalf_moments`

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search paths are
introduced by a proof; Phase 4.5 is skipped per the skill's scope rule.)

### Risk verdict (Phase 4.5)

Overall risk: **n/a (theorem)**.

---

### Mathlib search-status: `PadicLFunctions.twistedZetaHalf_moments`

[A] Lean-Finder       "Kubota Leopoldt p-adic zeta interpolation moment measure"   **n/a** — no Lean MCP / Lean-Finder server configured this session (confirmed: `ToolSearch` for `lean_loogle`/`lean_leansearch`/`lean_local_search` returns "No matching deferred tools"). Substituted by authoritative direct grep over the *local pinned* mathlib [D] + name-pattern [E] + the literature search.
[B] Loogle           `(FractionRing _) → ℤ_[p]`, `_ →ₗ[ℤ_[p]] ℤ_[p]` moment patterns   **n/a** — server unavailable this session. The structural search is covered by [D]/[E]: mathlib has no "measure = `C(X,ℤ_[p]) →ₗ ℤ_[p]` functional" and no fraction ring of such an algebra.
[C] LeanSearch       "p-adic zeta function interpolates zeta values at negative integers; constant term of p-stabilised Eisenstein series"   **n/a** — server unavailable this session; question fully covered by [D] + the Phase-3 web/source search.
[D] Grep mathlib src  terms tried: `kubota`, `leopoldt`, `p-adic zeta`, `padic.*zeta`, `pseudoMeasure`/`pseudo-measure`/`isPseudoMeasure`, `Iwasawa`, `EisensteinFamily`/`eisensteinFamily`/`Eisenstein measure`, `padicLFunction`, `interpolat`, `riemannZeta_neg_nat`   **see below**
[E] Name pattern      `twistedZetaHalf`, `twistedZetaHalf_moments`, `padicZeta`, `QuotientField`, `unitsPowCM`, `PadicMeasure`, `zetaNeg`   exist **only** in this project; zero mathlib hits.

Searched for both:
- the user's current form (the twisted-witness moment of `A₀`) — **no mathlib hit** (the objects are
  project-local).
- the literature-standard form (Kubota–Leopoldt interpolation `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)`; the
  Eisenstein constant term; the p-adic zeta as a pseudo-measure) — **also no mathlib hit**:
  - `grep -rniE "kubota|leopoldt|p-adic zeta|pseudomeasure|pseudo-measure|isPseudoMeasure"` over all of
    `Mathlib/` returns **nothing**. Mathlib has **no** Kubota–Leopoldt / p-adic zeta / pseudo-measure.
  - `grep "Iwasawa"` finds only `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` (the **Iwasawa
    decomposition** simplicity criterion — unrelated) and `MulAction.IwasawaStructure`. No Iwasawa
    *algebra* / algebra of measures.
  - `grep "interpolat"` over `Mathlib/NumberTheory/` returns nothing relevant — mathlib has no special-
    value p-adic interpolation theorem.
  - **What mathlib DOES have (the RHS ingredient only):** `riemannZeta_neg_nat_eq_bernoulli`
    (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`): `riemannZeta (−k) = (−1)^k
    bernoulli(k+1)/(k+1)` — which equals the project's `zetaNeg k` **exactly**. But this is the
    *complex/rational value* `ζ(−k)`, **not** the p-adic *interpolation* of that value by a measure on
    `ℤ_p^×`, and certainly not the moment/witness identity over `PadicMeasure`.
  - Classical complex Eisenstein series exist (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/*`,
    with `riemannZeta`-factor q-expansions) — but no p-adic side, no p-stabilisation, no family, no
    interpolation.
  - The generic plumbing the proof uses (`IsFractionRing.injective`, `algebraMap`, `LinearMap.smul_apply`,
    `field_simp`) **is** in mathlib — but it is generic, not this statement.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form).
Mathlib has the *rational value* `ζ(−k)` (`riemannZeta_neg_nat_eq_bernoulli` = `zetaNeg`) but **neither**
the Kubota–Leopoldt p-adic zeta, **nor** the pseudo-measure formalism, **nor** the `PadicMeasure`/
`QuotientField` carrier, **nor** the interpolation/moment identity over them, **nor** any p-adic
Eisenstein family.

---

### Call sites — `PadicLFunctions.twistedZetaHalf_moments`

Internal use count: **K = 1** (within the project, NOT counting the declaring file's own statement).
The single use is at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:395`, inside the
file's **main result `eisensteinFamily_interpolation`** (the constant-coefficient leg).
External-to-file callers: **0 distinct files** (a repo-wide `grep -rn twistedZetaHalf_moments
projects/ --include="*.lean"` returns only the declaration at line 259 and the single call at line 395).

| Caller file:line               | Usage pattern (one-line excerpt)                                                            |
|--------------------------------|----------------------------------------------------------------------------------------------|
| EisensteinFamily.lean:395      | `rw [twistedZetaHalf_moments p hp2 b hk ν hν, stabilisedCoeff, if_pos rfl]`                   |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`twistedZetaHalf_moments`?): **(none)** — no other site computes a moment of `twistedZetaHalf` /
`A₀` by hand. (The structurally analogous moment for the *other* coefficients, `divisorMeasure_moment`,
is a separate lemma; the underlying Kubota–Leopoldt moment `padicZeta_moments` is the engine this
lemma wraps, used once here.)

What this tells us: `K = 1` internal use, same file, **0 external consumers**, no inline
re-derivation. This is a *single-use corollary extracted from one proof* (the constant-coefficient leg
of `eisensteinFamily_interpolation`) — a classic "could-be-inlined" signal that leans away from a
standalone mathlib contribution. It is not dead code (it feeds the file's main theorem) and not a
widely-used API (no `K ≥ 3`, no downstream library). It mirrors the call-site pattern of its sibling
`divisorMeasure_moment` (also `K = 1`, also feeding line 395).

### Composition check (Phase 6)

Can `twistedZetaHalf_moments` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: assemble from a hypothetical mathlib p-adic-zeta interpolation lemma + the Bernoulli value.
  - Mathlib decls used: `riemannZeta_neg_nat_eq_bernoulli` (for the value `ζ(−k)`), and a *would-be*
    `padicZeta_moments`-analogue.
  - Result: **fails** — mathlib has the rational value `ζ(−k)` but **no** p-adic interpolation lemma to
    chain it onto; the `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` engine (`padicZeta_moments`) is project-local, and
    so are `twistedZetaHalf`, `QuotientField`, `unitsTwist`, `unitsPowCM`. The statement is not even
    *expressible* via mathlib decls (its LHS `ν (unitsPowCM (k−1))` is application of a `ℤ_[p]`-linear
    functional, with no mathlib counterpart).

Attempt 2: derive it as a corollary of the project's own `padicZeta_moments` + `unitsTwist_moment` +
`twistedZetaHalf_witness_eq` (the actual ≈12-line proof).
  - Mathlib decls used: only generic plumbing (`IsFractionRing.injective`, `algebraMap`,
    `LinearMap.smul_apply`, `field_simp`).
  - Result: **partial / not a mathlib composition.** This *is* the real proof, but every substantive
    step is a **project** lemma (`padicZeta_moments`, `padicZeta_isPseudoMeasure`, `unitsTwist_moment`,
    `coe_inv_two`, `twistedZetaHalf_witness_eq`) over project objects. Stripped of the project objects
    there is no statement left. This is "our form is a short proof *over project objects* using project
    lemmas + generic plumbing", **not** "compose mathlib primitives to get our form".

Conclusion: **NOT-COMPOSABLE from mathlib** (in the sense relevant to a mathlib verdict). Mathlib does
not contain the objects the statement names, nor the interpolation engine it wraps; the proof's mathlib
content is generic fraction-ring / `field_simp` plumbing only. This cannot be inlined into mathlib at
all, because the call site lives in a project-specific construction over a project-specific substrate.

---

## Verdict: `PadicLFunctions.twistedZetaHalf_moments`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the result is the moments form of the **canonical** Kubota–Leopoldt
  interpolation `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` (RJW Thm 4.1/Prop 4.11), in its appearance as the
  **constant Fourier coefficient `(1−p^{k−1})ζ(1−k)/2` of the p-stabilised Eisenstein series**
  (RJW Def 8.1, Thm 8.2; Serre 1973 bootstrap) — confirmed verbatim by **direct read of the source
  PDF (arXiv:2309.15692, pages 26–29 and 43–45)** and three independent web channels. No
  universally-named *standalone* theorem corresponds to this exact (twisted-witness, halved) Lean
  statement; it is RJW's §8 bookkeeping in the project's corrected (erratum #11) encoding.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — trivial-character value vs.
  Dirichlet `L(χ,1−k)`, `4 ≤ k` vs. the `0 < k` the proof needs, `ℤ_[p]` vs. general `𝒪_L`. But the
  general forms are *separate larger developments over the same non-mathlib substrate*. Modern-idiom:
  none for a mathlib contribution.
- Mathlib search (Phase 5): **not in mathlib** under either the user's form or the literature-standard
  form. Mathlib has the *rational value* `ζ(−k)` (`riemannZeta_neg_nat_eq_bernoulli` = `zetaNeg`) but
  **no** Kubota–Leopoldt p-adic zeta, **no** pseudo-measure formalism, **no** `PadicMeasure`/
  `QuotientField` carrier, **no** interpolation/moment identity over them.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the statement names objects mathlib
  lacks and wraps a project-local interpolation engine; its mathlib content is generic plumbing only.
  **K = 1** internal call site (the file's main theorem), **0 external consumers**, no inline
  re-derivation.

**Rationale (why BORDERLINE, not a clean bucket):**

`twistedZetaHalf_moments` formalises a genuinely **canonical** piece of mathematics — the
Kubota–Leopoldt interpolation property *"the p-adic zeta function interpolates `(1−p^{k−1})ζ(1−k)`,
which is the constant Fourier coefficient of the p-stabilised Eisenstein series `E_k^{(p)}`"* — read
verbatim from the source (RJW Thm 4.1/Prop 4.11 + Def 8.1 + Thm 8.2). Yet the four mechanical buckets
all fail their gates, for the same reason that governed the sibling declarations in this file
(`twistedZetaHalf`, `divisorMeasure_moment`, `unitsTwist`): the Lean statement lives **entirely on a
substrate mathlib does not have** — the linear-functional p-adic measures `PadicMeasure`, the Iwasawa
algebra `Λ(ℤ_p^×)` and its total fraction ring `Q(ℤ_p^×)`, the pseudo-measure predicate, `padicZeta`,
the x-twist, and the *twisted-pseudo-measure witness* encoding (erratum #11) in which the moment is
phrased. **NO-mathlib-has-it** is wrong: Phase 5 found mathlib has the *rational value* `ζ(−k)` but
none of the carrier objects nor the interpolation engine, so there is no ≤1-line specialisation.
**NO-composable-from-mathlib** is wrong: Phase 6 is NOT-COMPOSABLE — the statement is not expressible
over mathlib, and the proof's substance is project lemmas over project objects. **YES-add-as-is** is
wrong: Phase 4 is STRICTLY NARROWER (Dirichlet twist / general `𝒪_L` / the `0<k` weakening are
available), and — decisively — the theorem sits atop the entire RJW §3–§4 + §8 prerequisite tower,
which would have to be upstreamed first; a leaf corollary cannot be "added as-is" ahead of its whole
foundation. **YES-but-generalise-first** is wrong as the headline verdict: Phase 5 shows the more
general forms (and the carrier algebra itself) are *also* absent from mathlib, so the move is "upstream
an entire theory and then state the interpolation theorem in its general Dirichlet/`𝒪_L` form", not a
mechanical generalise-first of this lemma — and the verdicts reference explicitly flags that
whole-development, EXPENSIVE situation as a BORDERLINE "is the bigger thing worth it / in what form?"
call, not a self-resolving downgrade. The decisive question — *should the underlying RJW p-adic
measure / Kubota–Leopoldt / Eisenstein-family layer go to mathlib at all, and how should the
interpolation theorem be packaged there (which object is the headline: `padicZeta`, the family
`eisensteinFamily`, or this constant-coefficient corollary; with or without the twisted-witness
encoding; for the trivial character or the full Dirichlet generalisation)?* — is exactly the
mathematical-taste / project-policy judgment the skill must not make alone. The call-sites signal
(`K = 1`, single-file, 0 external consumers, no inline re-derivation) compounds this: *this particular
corollary* is a single-use leg of one proof, which on its own leans toward "keep project-local / inline
into `eisensteinFamily_interpolation`", not "upstream".

**Numbered questions (≤5):**

1. **Foundation-first.** `twistedZetaHalf_moments` cannot reach mathlib before its whole tower
   (`PadicMeasure` on `ℤ_p^×`, the Iwasawa algebra `Λ(ℤ_p^×)` + total fraction ring `Q(ℤ_p^×)`, the
   pseudo-measure formalism, `padicZeta` and its interpolation `padicZeta_moments`, the x-twist). Is
   upstreaming that **foundation** to mathlib a goal? If **no**, this corollary stays project-local and
   the assessment ends as "keep" — there is nothing to PR. If **yes**, proceed to Q2–Q5. (This is the
   same gating question raised by the sibling reports; answering it once resolves the whole §8 file.)
2. **Which object is the real mathlib target?** Is the mathlib-worthy headline the **p-adic zeta and
   its interpolation** (`padicZeta` + `padicZeta_moments`, the engine), the **family**
   `eisensteinFamily` + its interpolation theorem (with this moment as an internal step), or the
   **twisted constant-coefficient corollary** in isolation? The skill reads the first two as the
   natural headlines and *this* lemma as their corollary, not a standalone target.
3. **Trivial character vs. Dirichlet generality.** RJW §5 (Thm 5.1) gives the strictly more general
   `∫χ(x)x^k ζ_p = L(χ,1−k)`. Should any mathlib contribution state the interpolation in that fuller
   Dirichlet-twisted form (the project's `Interpolation/` development) rather than the trivial-character
   Eisenstein case formalised here?
4. **Witness encoding & `½`/twist packaging.** The moment is stated through the twisted witness `ν` of
   `(b·[b]−[1])·A₀ ∈ Λ` (erratum #11, because `A₀` is not a pseudo-measure), with the `(b^k−1)` factor.
   Would mathlib want this family-specific twisted-witness statement, or the cleaner un-twisted engine
   `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` (over the genuine pseudo-measure `ζ_p`), with the half/twist applied
   at the family-assembly site?
5. **`4 ≤ k` vs. `0 < k`, and `zetaNeg` vs. mathlib.** Independently of mathlib: (a) the p-adic proof
   only needs `0 < k` — do you want the hypothesis weakened from `4 ≤ k` to `0 < k` in the project
   (CHEAP)? (b) mathlib's `riemannZeta_neg_nat_eq_bernoulli` equals `zetaNeg`; should any upstreamed
   statement use mathlib's `riemannZeta`/`bernoulli` value directly (and is the project's separate
   rational `zetaNeg`, kept to avoid importing complex analysis, the right interface)?

**Next action:** user answers Q1 first. If Q1 = no → close as project-local (no mathlib action;
optionally inline this single-use corollary into `eisensteinFamily_interpolation`). If Q1 = yes → the
mathlib target is the engine/family (Q2), likely in the Dirichlet-general form (Q3), with the
twisted-witness/`½` packaging revisited (Q4) — and *this* corollary ships, if at all, only as an
internal step of that much larger upstreaming, after the foundation lands. Re-run
`/mathlibable PadicLFunctions.twistedZetaHalf_moments` once Q1–Q4 are decided. Q5 (the `k`-weakening
and `zetaNeg` interface) can be actioned regardless.

---

## Next step

User answers the numbered questions (Q1 is the gate: is the RJW measure / Kubota–Leopoldt / Eisenstein
layer mathlib-bound?). If no, `twistedZetaHalf_moments` stays project-local (a single-use corollary of
the file's main theorem). If yes, treat upstreaming the `PadicMeasure` + `padicZeta` layer as a
separate large effort, decide which object is the headline (Q2) and at what generality (Q3–Q4), and
ship this moment computation only as an internal step of that effort; re-run `/mathlibable` thereafter.

---

### Sources (Phase 3)
- https://arxiv.org/pdf/2309.15692 — Rodrigues Jacinto & Williams, *An Introduction to p-adic L-functions* (THE source; Thm 4.1/Prop 4.11 §4, Def 8.1 + Thm 8.2 §8 — read directly from the PDF, pages 26–29 and 43–45)
- https://www.ub.edu/nt/guitart/notes_files/KubotaLeopoldt.pdf — Guitart, *Mazur's construction of the Kubota–Leopoldt p-adic L-function*
- https://perso.univ-rennes1.fr/serge.cantat/Documents/Koblitz_ENS_2020.pdf — Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions* (Mazur measure, interpolation at negative integers)
- https://link.springer.com/chapter/10.1007/978-1-4684-0047-2_2 — *p-adic interpolation of the Riemann zeta-function* (Springer; `ζ(1−k)(1−p^{k−1})`)
- https://arxiv.org/pdf/1204.3878 — *Analytic constructions of p-adic L-functions and Eisenstein series*
- https://handwiki.org/wiki/P-adic_L-function — overview of the Kubota–Leopoldt interpolation property
- https://ahilado.wordpress.com/2020/11/30/iwasawa-theory-p-adic-l-functions-and-p-adic-modular-forms/ — constant term of the p-adic Eisenstein family = the p-adic zeta = an Iwasawa-algebra element
- Mathlib: `riemannZeta_neg_nat_eq_bernoulli` (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`) — the *rational value* `ζ(−k) = (−1)^k bernoulli(k+1)/(k+1)`, equal to the project's `zetaNeg`; the only mathlib piece of the formula's RHS, and the full extent of mathlib's overlap.
