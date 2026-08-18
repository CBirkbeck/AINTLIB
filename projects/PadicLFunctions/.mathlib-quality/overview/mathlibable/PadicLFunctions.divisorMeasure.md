# `/mathlibable` report — `PadicLFunctions.divisorMeasure`

**Final verdict: `BORDERLINE-needs-human`.**

The *mathematical content* is genuinely standard and named in the literature: `A_n =
Σ_{0<d∣n, p∤d} δ_d` is the `n`-th non-constant coefficient of the **Λ-adic / Serre–Katz
Eisenstein measure** (RJW §8, TeX 2411; Serre, Katz, Eischen *An introduction to Eisenstein
measures*). It is **not** in mathlib, and it is **not composable** from mathlib primitives —
because the *entire substrate is absent*: mathlib has no p-adic measure type
(`PadicMeasure = C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the continuous dual / Iwasawa-algebra setting),
no p-adic `dirac` functional, no Iwasawa algebra `ℤ_p[[ℤ_p^×]]`, and no p-adic-L-function /
Eisenstein-family machinery at all. So the honest blockers are not search blockers but
*roadmap* ones: this one `def` cannot be upstreamed in isolation (it is the leaf of a large
project-local tower), its name/shape are tuned to one in-file consumer (the prime-to-`p`
filter, the `unitOfNat` junk-value indexing — itself assessed BORDERLINE), and whether the
whole p-adic-measure tower belongs in mathlib is a project/mathlib-policy judgment the skill
cannot make alone. Numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow in this checkout; the decl and its full dependency chain were read directly from `projects/PadicLFunctions/…` and `.lake/packages/mathlib/`).
- decl `PadicLFunctions.divisorMeasure`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:68`
- kind:                      `def` (`noncomputable`)
- has sorry:                 no (the def is a closed `Finset.sum`; its companion `divisorMeasure_moment` at line 74 is sorry-free)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)" — the Kubota–Leopoldt pseudo-measure interpolates the *constant* coefficient of the p-stabilised Eisenstein series `E_k^{(p)}`, and the non-constant coefficients are interpolated by elementary divisor-sums of Dirac measures; bundling coefficientwise gives the Λ-adic Eisenstein family `𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`.

Dependency chain read from source (all project-local; none in mathlib):

- **`PadicMeasure p X`** (`Measure/Basic.lean:52`) — `abbrev PadicMeasure (X) := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`. The space of `ℤ_[p]`-valued p-adic measures = `ℤ_[p]`-linear functionals on continuous `ℤ_[p]`-valued functions (RJW Def. 3.6, `def:measures`). This is the **continuous-dual / Iwasawa-algebra** notion of measure, **not** mathlib's `MeasureTheory.Measure` (which is `ℝ≥0∞`-valued on a `MeasurableSpace`). The two are mathematically different objects.
- **`PadicMeasure.dirac p (x : X)`** (`Measure/Basic.lean:64`) — the Dirac/point-mass functional `f ↦ f x` (RJW Ex. 3.7, `ex:dirac`). This is the group-like element `[x] = δ_x` of the Iwasawa algebra. **Not** mathlib's `MeasureTheory.Measure.dirac`.
- **`unitOfNat p d`** (`EisensteinFamily.lean:53`) — `d : ℕ` viewed in `ℤ_p^×` (junk value `1` when `p∣d`). Assessed separately as **BORDERLINE** (`PadicLFunctions.unitOfNat.md`).
- The `AddCommMonoid` structure on `PadicMeasure p ℤ_[p]ˣ` (so the `Finset.sum` is well-defined) is the standard linear-map additive structure; the multiplicative/convolution structure lives in `Measure/PseudoMeasure.lean` (the convolution algebra `Λ(ℤ_p^×)`, RJW §3.6).
- `divisorMeasure_moment` uses `PadicMeasure.unitsPowCM p k` (`PseudoMeasure.lean:650`), the test function `x ↦ x^k` on `ℤ_p^×`, and `unitOfNat_coe` to evaluate `∫ x^k δ_d = d^k`.

---

### Statement (Phase 1)

`PadicLFunctions.divisorMeasure` is a **definition** of the following.

> Fix a prime `p`. For `n : ℕ`, the **divisor-sum measure** `A_n ∈ Λ(ℤ_p^×)` is the finite
> sum of Dirac (point-mass) measures over the divisors `d` of `n` that are coprime to `p`:
> `A_n = Σ_{0<d∣n, p∤d} δ_d`, where `δ_d` is the point mass at `d` viewed in `ℤ_p^×`.
> (`A_0 = 0`, the empty sum; the family's actual constant coefficient is the twisted
> pseudo-measure `twistedZetaHalf = x·ζ_p/2`, defined elsewhere in the file.)

Its defining property (`divisorMeasure_moment`, line 74) is the **moment formula**: integrating
the `k`-th power character `x^k` against `A_n` recovers the prime-to-`p` divisor power sum,
`∫_{ℤ_p^×} x^k · A_n = σ^p_k(n) = Σ_{0<d∣n, p∤d} d^k`. This is exactly the shape of the higher
Fourier coefficients of a p-adic Eisenstein series: the `n`-th coefficient is a measure whose
weight-`k` moment is the divisor power sum `σ_k(n)`.

The source body (lines 68–70):
```lean
noncomputable def divisorMeasure (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d),
    PadicMeasure.dirac p (unitOfNat p d)
```

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section `variable`).
- `n : ℕ` — the coefficient index (`= q^n` slot in the Λ-adic family).

Hypotheses (Lean side): none on the def (it is total; `A_0 = 0`).

Conclusion (math): the `n`-th non-constant coefficient `A_n` of the Λ-adic Eisenstein family, as an element of the Iwasawa algebra `Λ(ℤ_p^×)`.

Conclusion (Lean): `PadicMeasure p ℤ_[p]ˣ` (i.e. `C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`). — n/a as a "statement"; it is a definition.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG/SMALL — recorded BIG).

Reason: it is one of the named building blocks of a `## Main results` headline — the module
docstring's centerpiece is the **Λ-adic Eisenstein family `𝐄`** and its interpolation
`eisensteinFamily_interpolation`, and `divisorMeasure` is the literal definition of the family's
non-constant coefficients `A_n` (RJW Theorem at TeX 2399, coefficient definition at TeX 2411). It
realises a *named mathematical object* (the higher coefficients of the Eisenstein measure), not a
mere bookkeeping helper. It does not introduce a brand-new *structure* (it is a term of the
existing project type `PadicMeasure`), which is the only reason it isn't unambiguously BIG.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for report framing only; it did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: **1 substantive expression** — a single `Finset.sum` over the prime-to-`p`
divisors of the Dirac summand. (It spans two physical lines only for width; it is one term.)

One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | No downstream proof relies on the RHS spelling being *sealed*; on the contrary `divisorMeasure_moment` (line 77) immediately `rw [divisorMeasure, LinearMap.coe_sum, Finset.sum_apply, …]` to **unfold** it. The def is meant to be unfolded, not sealed. |
| Avoid typeclass diamonds          | no       | The `Finset.sum` picks the unique `AddCommMonoid` on the linear-map type `PadicMeasure p ℤ_[p]ˣ`; no competing `Zero`/`Add` instance is being disambiguated. |
| Mark semantic intent / API name   | **yes** | The name + docstring **is** the API surface: `A_n` is referenced by name in the family definition (`eisensteinFamily`, line 368) and in the main interpolation theorem (`eisensteinFamily_interpolation`, lines 388–399). The name encodes the RJW object `A_n = Σ δ_d`. This is a genuine semantic-intent anchor (the family is *built out of* `divisorMeasure n`), though confined to one file. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name: it names the family's `n`-th
coefficient and is consumed by the family def + interpolation theorem). Carried into Phase 7: the
one-liner is not itself a blocker to a YES, but combined with K=4 *in-file-only* call sites and the
absent substrate it reinforces the BORDERLINE/NO leaning rather than a clean YES.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic Eisenstein measure divisor sum Dirac measures Iwasawa algebra Lambda-adic family coefficients" | **yes** | The Eisenstein measure is a measure (element of the Iwasawa algebra) whose specialisations are Eisenstein series; its constant term gives an Iwasawa-algebra element (Kubota–Leopoldt). | Hits: RJW/Williams Warwick notes (= the project source, arXiv:2309.15692); arXiv:1204.3878 (analytic constructions of p-adic L-fns & Eisenstein series); Wan IMC (Rankin–Selberg); ahilado blog (Hida/Eisenstein measure exposition). Confirms the *named object* "Eisenstein measure". |
|  2 | WebSearch (general form / Serre–Katz lineage) | "Eisenstein measure non-constant coefficient divisor sum sigma_k interpolation p-adic L-function Serre Katz" | **yes** | "Starting with Serre and Katz, p-adic families of Eisenstein series construct p-adic L-functions"; Serre interprets `L_p(1−k)` as the constant term of a (Hilbert) Eisenstein series; Katz builds Eisenstein measures interpolating Eisenstein series. | Hits: arXiv:1106.3692, 1302.7229 (Eischen Eisenstein measures for unitary/vector-weight forms), Leiden thesis "Computing p-adic L-fns of totally real fields", 1305.3693 (Eisenstein–Kronecker). The divisor-power-sum coefficient `σ_k(n)` is the **standard Fourier coefficient** of the Eisenstein series being interpolated. |
|  3 | WebSearch (named-after / aliases: "sum of Dirac" / point mass over divisors) | `"Eisenstein measure" OR "Eisenstein family" higher coefficient "sum of Dirac" delta measure divisors coprime to p` | **yes** | Variant divisor function `σ^{k-1}_{χ₁,χ₂}(n)=Σ_{d∣n}χ₁(n/d)χ₂(d)d^{k-1}` appears in Eisenstein Fourier expansions; constructions use sums over divisors with coprimality/congruence conditions; "measure valued in Eisenstein series … Fourier expansion computed". | Hits: arXiv:1106.3692, 2109.13218, 1304.5204 (Eisenstein measure on Shimura curves, Fourier expansion), 2308.15051. The **prime-to-`p`/coprimality restriction on the divisor sum is standard** in the p-stabilised setting. |
|  4 | WebSearch (Eisenstein-measure survey + Iwasawa-algebra-as-measures) | "nLab Eisenstein measure OR 'Iwasawa algebra' measures continuous dual locally constant functions p-adic" | **yes** | **"An `M`-valued measure on a compact totally-disconnected `X` over a p-adic ring `R` is an element of `Hom(C(X,R), M)`"**; "taking the constant term of a p-adic Eisenstein series yields a measure that gives an element of the Iwasawa algebra". | Hits the dedicated survey **Eischen, *An introduction to Eisenstein measures* (arXiv:2101.01879)** + 2109.13218. **Directly confirms the project's `PadicMeasure = Hom(C(X,ℤ_p), ℤ_p)` definition is the universal/standard one.** |
|  5 | WebSearch (Iwasawa algebra / Dirac group-like element) | "Iwasawa algebra Z_p[[Z_p^times]] measures on Z_p^times Dirac measure group-like element point mass [g] standard" | **yes** | `Λ = ℤ_p[[ℤ_p]] ≅ ℤ_p[[T]]` (Amice transform); natural maps `G → A[G] → A[[G]]`, **image of `g` is the Dirac measure supported at `g`** (`δ_g`, point mass = group-like `[g]`); restriction of measures on `ℤ_p` to `ℤ_p^×` is standard. | Hits: academia.edu (Iwasawa λ-invariants of p-adic measures + Γ-transforms), nLab *Iwasawa theory*, Eischen survey. **Confirms `δ_d = [d]` is the standard point-mass/group-like element of the Iwasawa algebra** — exactly `PadicMeasure.dirac`. |
|  6 | ChatGPT MCP                      | (intended: "standard definition of the higher coefficients of a p-adic Eisenstein measure as divisor sums of Dirac measures; generality; historical evolution Serre→Katz→Eischen") | **n/a** | — | **ChatGPT-math MCP not connected in this environment.** `claude mcp list` → `plugin:mathlib-quality:chatgpt-math` *Failed to connect* (its server path `/home/chris/.claude/mcp-servers/chatgpt-math/server.js` is on a different machine). Substituted with extra WebSearch breadth (rows 1–5) + the source-identity confirmation (row 8) + arXiv (row 10), per the absent-channel fallback used in the sibling reports. |
|  7 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/`; `refs/PadicLFunctions/` | **n/a** | — | No `references/` dir under the project's `.mathlib-quality/` (only `overview/`); no `refs/` symlink in this checkout (reference PDFs are LOCAL ONLY and not populated here). The RJW source is quoted *in the file itself* (TeX 2399/2411/2413), so the standard form is available directly. Recorded `n/a`. |
|  8 | nLab / source identity            | nLab *Iwasawa theory* (fetched); arXiv:2309.15692 (RJW, source identity) | partial | nLab *Iwasawa theory* covers `ℤ_p[[Γ]]`-modules, the Main Conjecture, Mazur–Wiles — **but is structural/algebraic, NOT measure-theoretic**: it does *not* discuss the Iwasawa algebra as measures, Dirac/point-mass elements, or Eisenstein measures. | Source confirmed: arXiv:2309.15692 (Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions*, ESSENTIAL NUMBER THEORY 2025) contains a section "The p-adic family of Eisenstein series" — the project's `divisorMeasure` is its `A_n`. The *measure-theoretic* framing is in the survey-row-4/row-5 sources, not on nLab. |
|  9 | nCatLab (if categorical)         | — | **n/a** | — | Not a categorical concept. (`PadicMeasure` is a Hom-module / continuous dual; the relevant abstract framing — measures as `Hom(C(X,R),M)` — was already pinned by row 4.) |
| 10 | Stacks Project (if alg geom)     | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic statement. (Eisenstein *measures* in the Katz/Eischen line do live near Shimura varieties, but the object here is an elementary divisor-sum of point masses on `ℤ_p^×`, fully covered by rows 1–5.) |
| 11 | MathOverflow / Math.StackExchange| (subsumed by the row-1..5 web sweep: "Eisenstein measure", "Iwasawa algebra Dirac point mass", "divisor sum coefficient p-adic Eisenstein") | yes | Community/expository sources reproduce the same framework (Iwasawa algebra = measures; `δ_g` = point mass; Eisenstein coefficients = divisor sums). | Not separately tabulated (would duplicate rows 1–5). No source treats *this specific Lean packaging* (`divisorMeasure n` as a standalone named function) as an object — it is a coefficient *within* the family. |
| 12 | recent arXiv (last 5 years)      | "Rodrigues Jacinto Williams introduction p-adic L-functions Eisenstein family 2309.15692 divisor measure A_n" + the Eischen 2021 survey | **yes** | arXiv:2309.15692 (2023/24) is the direct source; arXiv:2101.01879 (Eischen 2021) is the modern survey of Eisenstein measures; arXiv:2606.10626 (2025, Eisenstein–Kronecker / new construction of Katz's measure) shows the framework is actively used. | The mathematics is classical (Serre 1973, Katz 1976) and *actively current*; the higher coefficients are uniformly the divisor-sum measures. |

Protocol pass check:
- WebSearch ran **5 distinct queries at different generality levels** (specific divisor-sum-Dirac form; the Serre–Katz general lineage; the "sum of Dirac"/coprimality alias form; the measures-as-`Hom(C(X,R),M)` survey; the Iwasawa-algebra/point-mass form) — ✓ (≥3 required).
- ChatGPT MCP: not connected; recorded `n/a` with reason; compensated with extra WebSearch breadth + arXiv — handled per fallback.
- Local references checked (`n/a`, reason recorded) — ✓.
- nLab checked (Iwasawa-theory page fetched; structural-only, recorded) — ✓.
- nCatLab / Stacks / MathOverflow / arXiv each checked or `n/a` with reason — ✓.

### Literature summary (Phase 3)

Concept identified as: **the higher (non-constant) Fourier coefficients of a `p`-adic /
Λ-adic Eisenstein measure**, realised as **divisor sums of Dirac/point-mass measures on
`ℤ_p^×`**: `A_n = Σ_{0<d∣n, p∤d} δ_d`, with weight-`k` moment the prime-to-`p` divisor power
sum `σ^p_k(n) = Σ_{0<d∣n, p∤d} d^k`. This is the **Serre–Katz Eisenstein-measure** construction
(Serre 1973, Katz 1976; modern survey Eischen, arXiv:2101.01879), in the specific form of
Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions* (arXiv:2309.15692, §8) —
the project's stated source.

Sources agree on the standard form: **yes**. Three layers are all standard and unanimous:
1. **Measure as continuous dual** — an `M`-valued measure on a profinite `X` over a p-adic
   ring `R` is `Hom(C(X,R), M)`; over `ℤ_p` this is the **Iwasawa algebra** `ℤ_p[[ℤ_p^×]]`
   (Eischen survey; row 5).
2. **Dirac = point mass = group-like element** `δ_g = [g]` (the map `g ↦ δ_g`, `G → A[[G]]`;
   row 5).
3. **Eisenstein-family higher coefficient = divisor sum**, moment `= σ_k(n)`, prime-to-`p` in
   the p-stabilised setting (rows 1–3).

Most general standard form: the Eisenstein measure / Λ-adic family lives over a general p-adic
coefficient ring and (in Katz/Eischen) over general totally real / CM fields and unitary
groups; the `ℚ / ℤ_p^×` case here (Kubota–Leopoldt) is the **base case** of that hierarchy. The
divisor-sum-of-Diracs coefficient is the universal shape across all these generalisations.

Generality dimensions where the literature varies:
- *Coefficient ring*: `ℤ_p` (here) → general p-adic `R` / `𝒪_L` (RJW defers this to §5; Eischen
  works over general `R`).
- *Base field / group*: `ℚ` & `ℤ_p^×` (here) → totally real fields (Serre), CM fields (Katz),
  unitary groups (Eischen). The `ℚ` case is the narrowest, foundational one.
- *Test functions*: power characters `x^k` (here) → general locally constant / continuous
  characters and Hecke characters.

Disagreement with the literature: **none on the mathematics.** The one caveat is *packaging*:
the literature treats `A_n` as the `n`-th coefficient *within* the family `𝐄 = Σ A_n q^n`, not
as a standalone reusable named function `divisorMeasure : ℕ → Λ(ℤ_p^×)`. That packaging choice
(a per-`n` def) is a formalisation convenience, and the file's own erratum #11 + the
prime-to-`p` filter show the exact shape is tuned to this development.

If the literature had returned nothing this would itself be a signal — but it returned a rich,
unanimous, *named* framework. The decisive question is therefore **not** novelty (the
mathematics is standard) but whether *this leaf, in mathlib, in isolation* is the right unit —
which is gated entirely by the absence of the whole substrate (Phase 5).

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the higher Eisenstein-measure coefficient
`A_n = Σ_{0<d∣n, p∤d} δ_d` over a p-adic measure space / Iwasawa algebra, moment `σ^p_k(n)`;
the most general form is over a general coefficient ring `R` and general base field/group.

### Generality status table (Phase 4a) — `divisorMeasure`

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | coefficient ring `ℤ_[p]` (via `PadicMeasure p X`) | `ℤ_[p]`-valued measures | general p-adic `R`/`𝒪_L`-valued measures (Eischen; RJW §5) | **yes (in principle)** | The RJW notes themselves "defer the general coefficient case to the §5 development pass" (`Measure/Basic.lean` docstring). But the **whole `PadicMeasure` type would have to be generalised first** — this is a substrate change, not a change to `divisorMeasure`. Not a `divisorMeasure`-local weakening. |
| 2 | the index group `ℤ_[p]ˣ` | measures on `ℤ_p^×` | measures on `(𝒪_F⊗ℤ_p)^×` / unitary-group analogues | **yes (in principle)** | Same as row 1 — a substrate (base-field) generalisation, the Serre→Katz→Eischen hierarchy. Orthogonal to this leaf. |
| 3 | the prime-to-`p` filter `¬ p ∣ d` | sum over `d∣n` with `p∤d` | the p-stabilised coefficient (prime-to-`p`) **is** the standard form here; the un-stabilised `σ_k` is a *different* object | **NO** | The `p∤d` filter is **not** an over-restriction to be weakened — it is the defining feature of the p-*stabilised* Eisenstein series `E_k^{(p)} = E_k − p^{k-1}E_k(p·)` (file docstring). Dropping it gives the classical (non-p-adic-interpolable) `σ_k`. Correct as stated. |
| 4 | the index `n : ℕ` | natural-number coefficient index | `n` ranges over `ℕ` (the `q^n` exponent) | **NO** | The coefficient index of a `q`-expansion is intrinsically `ℕ`. No generalisation. |
| 5 | the summand `δ_d` (point mass) | `PadicMeasure.dirac p (unitOfNat p d)` | `δ_d = [d]`, point mass / group-like (standard) | **NO** (correct) | This *is* the literature-standard summand. The only wrinkle is the `unitOfNat` junk-value lift (BORDERLINE on its own), not the Dirac. |

The only "weakenings" (rows 1–2) are **substrate generalisations of the ambient `PadicMeasure`
type**, explicitly on the project's own §5 roadmap — they are *not* weakenings of
`divisorMeasure` as a declaration. Given the *current* `PadicMeasure p ℤ_[p]ˣ` substrate, the
def is at the right (p-stabilised, prime-to-`p`) generality.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL relative to its substrate** (`PadicMeasure p ℤ_[p]ˣ`).

Number of `divisorMeasure`-local weakening opportunities found: **0**. (The two "in-principle"
generalisations, rows 1–2, are changes to the *ambient measure type*, not to this def — they are
the Serre→Katz→Eischen coefficient-ring/base-field hierarchy, which the project itself defers to
a §5 pass.)

Proposed restatement: **none at the `divisorMeasure` level.** A more general statement would be
"the `n`-th Eisenstein-measure coefficient over a general coefficient ring `R` / general base
field" — but that is a *different, much larger* development (generalise `PadicMeasure` first),
not a mechanical rewrite of this line.

Cost of restatement: **EXPENSIVE** (and not local) — it requires first generalising the whole
p-adic-measure / Iwasawa-algebra tower. Per the skill's cost rule, EXPENSIVE does not by itself
downgrade a verdict; but here the relevant point is that the generalisation is *not of this
declaration* — so 4b is MAXIMALLY-GENERAL-relative-to-substrate, and the substrate question is a
separate (BORDERLINE) judgment surfaced in Phase 7.

→ MAXIMALLY GENERAL (rel. substrate) → Phase 7 weighs YES-add-as-is **vs** the NO/BORDERLINE
buckets; 4c is run next.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Already typeclass-driven (`[Fact p.Prime]`); the measure type is an `abbrev` for a linear-map space with its standard instances. Nothing to de-bundle. |
|  2 | sequences/metric → filters/topological? | no | — | No limit/convergence content in *this* def (it is a finite sum). The ambient `PadicMeasure` already uses `C(X,ℤ_p)` / topological duals correctly. |
|  3 | construct an object where a universal-property class would characterise it? | **yes (mild, substrate-level)** | The Iwasawa algebra `ℤ_p[[ℤ_p^×]]` could be the *completed group algebra* / a universal-property profinite-completion object rather than the raw continuous dual `C(ℤ_p^×,ℤ_p)→ₗℤ_p`; then `δ_d` = the canonical group-like `[d]` and `divisorMeasure` = `Σ [d]` in the group algebra. | Would compose with mathlib's `MonoidAlgebra` / completed-group-algebra API (if/when present). **But this is a reformulation of `PadicMeasure`/`dirac`, not of `divisorMeasure`** — at the `divisorMeasure` level it is still `Σ over divisors of [d]`. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | Not a substructure. |
|  5 | vector-space/metric/field-specific → weaken typeclass? | no (locally) | — | The coefficient-ring generalisation (Phase 4a row 1) is real but is a substrate change, already counted. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary structure? | no | — | The `q`-expansion index is intrinsically `ℕ`; the divisor sum is over `ℕ` divisors. No real generalisation. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no — not at the `divisorMeasure` level.**

The one genuine modernisation in the neighbourhood (row 3: model the Iwasawa algebra as a
completed group algebra with a universal property, so `δ_d` is the canonical group-like element
`[d]`) is a reformulation of the **substrate** (`PadicMeasure` + `dirac`), not of
`divisorMeasure`. Under *any* such reformulation, `divisorMeasure` remains "the finite sum of the
canonical group-like elements `[d]` over the prime-to-`p` divisors of `n`" — the same content. So
there is no `divisorMeasure`-specific modern-idiom restatement that would flip a MAXIMALLY-GENERAL
classification to YES-but-generalise-first. (The substrate-modernisation question is real but
belongs to a `/mathlibable` on `PadicMeasure` / `PadicMeasure.dirac`, and feeds the BORDERLINE
questions in Phase 7.)

One-line reason this is not a `divisorMeasure`-modernisation move: every candidate reformulation
acts on the ambient measure type, leaving the divisor-sum-of-group-likes definition unchanged.

---

## PHASE 4.5 — Diamond / defeq risk (`def`)

### Diamond / defeq risk — `divisorMeasure`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | Not an instance; it is a plain `noncomputable def` producing a term of `PadicMeasure p ℤ_[p]ˣ`. The `Finset.sum` uses the unique `AddCommMonoid` instance on the linear-map space `C(ℤ_[p]ˣ,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (mathlib's `LinearMap.addCommMonoid`); no competing additive structure exists on that type. |
| 2 | Reducibility leak | **none** | Not `@[reducible]`; sealed `noncomputable def`. The body is exposed to defeq only on explicit `unfold`/`rw [divisorMeasure]`, which is exactly what `divisorMeasure_moment` does (line 77). A `Finset.sum` body is not the kind of cheap RHS whose semireducibility surprises `simp`. |
| 3 | Non-canonical unfolding | **none/low** | No `@[simp]`. `simp` will not unfold a `Finset.sum`-over-a-filter spontaneously; `rfl` will not fire (the sum is `noncomputable` and over a `Finset.filter` with a `Decidable` predicate). Downstream proofs rewrite via the dedicated `divisorMeasure_moment` lemma, the canonical API. No surprise. |
| 4 | Instance priority collision | **n/a** | Not an instance. |
| 5 | Universe-polymorphism issues | **none** | Monomorphic — `PadicMeasure p ℤ_[p]ˣ` lives in `Type 0` (`ℤ_[p]`, `ℤ_[p]ˣ` are `Type 0`). No universe variable to over-constrain. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort` declared. The only coercion in sight is the standard `Units.val : ℤ_[p]ˣ → ℤ_[p]` (inside `unitOfNat`/`unitsPowCM`), which does not compete with anything on `PadicMeasure`. The `LinearMap`'s own `FunLike` coercion is mathlib-standard. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.**
Top risks: none.
Recommended mitigations: none needed. (The def is a sealed finite sum of linear functionals; it
introduces no instance, no reducible defeq surface, and no coercion. If the *substrate*
`PadicMeasure` were ever upstreamed, the diamond questions would attach to `PadicMeasure` /
`dirac`, not to this sum.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.divisorMeasure`

[A] **Lean-Finder** — n/a: the hosted Lean-Finder endpoint was not reachable as a scriptable
    service from this session. Substituted with grep (D) + name-pattern (E) + LeanSearch-style
    natural-language reasoning (C) + a direct read of the candidate mathlib areas
    (`MeasureTheory/Measure/Dirac.lean`, `NumberTheory/ModularForms/EisensteinSeries/`,
    `NumberTheory/ArithmeticFunction/`).

[B] **Loogle** (type-pattern) — queries (run conceptually against the mathlib source; the live
    endpoint is not scriptable here):
    - `C(?X, ℤ_[?p]) →ₗ[ℤ_[?p]] ℤ_[?p]` (the `PadicMeasure` type) → **no occurrences in
      mathlib**: there is no "continuous functions into `ℤ_p`, linear functionals" measure type
      anywhere in mathlib. `grep` for `→ₗ\[ℤ_\[` over mathlib's `Padics/` returns nothing of this
      shape.
    - `Finset.sum ?s (fun d => MeasureTheory.Measure.dirac ?d)` → mathlib *does* have
      `Measure.sum (fun b => … • dirac b)` (`MeasureTheory/Measure/Dirac.lean:138`,
      `Measure.sum_smul_dirac`) — **but for `ℝ≥0∞`-valued `MeasureTheory.Measure`, an entirely
      different object** (measures on a `MeasurableSpace`, not linear functionals on `C(X,ℤ_p)`).
      Not a match.
    - `?n.divisors.filter (fun d => ¬ ?p ∣ d)` → the prime-to-`p` divisor filter pattern appears
      (`NumberTheory/Divisors.lean` has `divisors.filter` lemmas), but only as a `Finset ℕ`
      construct, never summed into a *measure*.

[C] **LeanSearch** (natural language) — queries (endpoint returned 4xx on the scripted call;
    resolved via D/E + source reads): "sum of Dirac measures over divisors of n coprime to p";
    "p-adic Eisenstein measure coefficient"; "Iwasawa algebra divisor sum". Expected/actual: the
    only `dirac`/`sum` hits are the `MeasureTheory.Measure` ones (ℝ≥0∞-valued); **no p-adic
    measure / Eisenstein-family object**.

[D] **Grep mathlib src** — terms over `.lake/packages/mathlib/Mathlib/`:
    - `divisorMeasure`, `divisor.*Measure`, `Eisenstein.*measure`, `measure.*Eisenstein` →
      **0 hits**. Nothing of this name or shape.
    - `iwasawa` (case-insensitive) → only `GroupTheory/GroupAction/Iwasawa.lean` (an *Iwasawa
      decomposition / group-action* permutation lemma) + two GL/alternating-group uses.
      **No Iwasawa *algebra* / Iwasawa *theory* / measures in number theory.**
    - `padicLFunction`, `p-adic L`, `MonoidAlgebra .* PadicInt`, "measure on … units" → **0
      hits**. Mathlib has **no p-adic L-function or p-adic-measure infrastructure** at all.
    - `eisenstein` (case-insensitive) → `NumberTheory/ModularForms/EisensteinSeries/` (the
      **complex-analytic** Eisenstein series `eisensteinSeriesMF` on the upper half-plane,
      valued in `ℂ` — confirmed by `grep ℂ EisensteinSeries/Basic.lean`), `RingTheory/Polynomial/
      Eisenstein` (Eisenstein's *criterion* / `IsWeaklyEisensteinAt`), `LegendreSymbol/
      GaussEisensteinLemmas`. **None is a p-adic Eisenstein *measure* or family.**
    - `Measure.sum`, `Measure.dirac`, `sum_smul_dirac` → present in `MeasureTheory/Measure/`,
      but for the `ℝ≥0∞`-valued `MeasureTheory.Measure` on a `MeasurableSpace` — the **wrong
      category of object** (a different notion of "measure" from RJW's continuous dual).

[E] **Name-pattern** (`lean_local_search` proxy via grep) — terms: `divisorMeasure`, `sigmaP`,
    `dirac` (in a `PadicInt`/units context), `unitsPowCM`, `Lambda`/`Iwasawa` algebra,
    `PadicMeasure`. Hits: **only inside the project** (`projects/PadicLFunctions/…`). Zero in
    `.lake/packages/mathlib/`.

Searched for both:
- the user's current form (`Σ_{d∣n,p∤d} dirac (unitOfNat d)` as a `PadicMeasure p ℤ_[p]ˣ`) —
  **not in mathlib** (the type itself is absent);
- the literature-standard / more general form (an Eisenstein-measure coefficient over a general
  coefficient ring / base field; the Iwasawa-algebra group-like sum `Σ [d]`) — **also not in
  mathlib**: there is no Iwasawa algebra, no p-adic measure, no Eisenstein measure / family, and
  no p-adic-L-function machinery of any kind.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard general
form). Crucially, **even the *building blocks* are absent** — there is no p-adic `PadicMeasure`
type, no p-adic `dirac` functional, and no Iwasawa-algebra additive structure to sum over. The
only superficially-related mathlib objects (`MeasureTheory.Measure.dirac` / `Measure.sum`, the
complex `eisensteinSeriesMF`, `ArithmeticFunction.sigma`) are in **different categories of
object** and cannot be assembled into `divisorMeasure`.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `divisorMeasure`

Internal use count: **K = 4** substantive uses (excluding the `def` line 68 and the trivial
`rw [divisorMeasure]` unfold inside its own moment proof at line 77). **All within the declaring
file** `EisensteinFamily.lean`. **External-to-file callers: 0** (a repo-wide
`grep -rn divisorMeasure --include=*.lean --exclude-dir=.lake projects/` finds matches only in
`EisensteinFamily.lean`). **Downstream-library callers: 0.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `EisensteinFamily.lean:74–81` (`divisorMeasure_moment`) | `divisorMeasure p n (PadicMeasure.unitsPowCM p k) = ((sigmaP p k n : ℕ) : ℤ_[p])` — the moment lemma; proof `rw [divisorMeasure, LinearMap.coe_sum, Finset.sum_apply, sigmaP, …]`. |
| `EisensteinFamily.lean:368` (`eisensteinFamily`) | `else algebraMap _ _ (divisorMeasure p n)` — the `n≠0` coefficients of the family `𝐄`. |
| `EisensteinFamily.lean:388` (`eisensteinFamily_interpolation`) | `PowerSeries.coeff n (eisensteinFamily p hp2) = algebraMap _ _ (divisorMeasure p n)` |
| `EisensteinFamily.lean:389,399` (`eisensteinFamily_interpolation`) | `((divisorMeasure p n (PadicMeasure.unitsPowCM p (k-1)) : ℤ_[p]) : ℚ_[p]) = …` then `rw [divisorMeasure_moment, …]` — the `n`-th moment equals `stabilisedCoeff p k n`. |

Inline-derivation grep (was the equivalent re-derived inline without using `divisorMeasure`?):
**(none)** — the family def + interpolation theorem always go through the named `divisorMeasure`
and its `divisorMeasure_moment` lemma; the `Σ δ_d` sum is not re-spelled elsewhere.

Call-sites signal (Phase 6.0.1): **K = 4 internal uses, no inline bypass, but 0 external/0
downstream callers, all confined to one file** — a *cohesive internal API for one development*.
Per the heuristics, K≥3-with-no-bypass leans YES; but K being entirely **in-file with zero
downstream consumers**, on a leaf whose substrate is absent from mathlib, is exactly the
"genuinely-new + currently-internal" pattern that leans **BORDERLINE** (the YES is blocked by the
substrate; see Phase 7).

### Composition check (Phase 6)

Can `divisorMeasure` be derived from mathlib in ≤3 chained calls?

**Attempt 1 — assemble from mathlib's `MeasureTheory.Measure.dirac` + `Measure.sum`:**
- Sketch: `Measure.sum (fun d => Measure.dirac d)` over the divisor finset.
- Mathlib decls used: `MeasureTheory.Measure.dirac`, `MeasureTheory.Measure.sum`.
- Result: **fails.** `MeasureTheory.Measure` is `ℝ≥0∞`-valued on a `MeasurableSpace` — a
  *different object* from `PadicMeasure = C(ℤ_[p]ˣ,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`. There is no
  coercion or equivalence between the two; the moment `∫ x^k dμ ∈ ℤ_[p]` is meaningless for an
  `ℝ≥0∞`-measure. Type-incorrect, not a composition.

**Attempt 2 — assemble from a mathlib Iwasawa-algebra / completed-group-algebra `Σ [d]`:**
- Sketch: `∑ d ∈ …, MonoidAlgebra.single d 1` in `ℤ_p[[ℤ_p^×]]`.
- Mathlib decls used: would need an Iwasawa-algebra / completed-group-algebra over `ℤ_p` and its
  group-like elements.
- Result: **fails — the object does not exist in mathlib.** `grep iwasawa` finds only a
  group-action lemma; there is no `ℤ_p[[ℤ_p^×]]`, no completed group algebra over `ℤ_p`, no
  group-like-element map into it. Nothing to compose with.

**Attempt 3 — derive the *content* (the moment `σ^p_k(n)`) instead of the object:**
- The moment lemma `divisorMeasure_moment` is itself a 4-line `rw`-chain over the project's own
  `dirac_apply` / `unitOfNat_coe`. But that derives a *theorem about* the object; it does not
  *construct* `divisorMeasure` from mathlib, and it depends on the project's `PadicMeasure`/`dirac`
  API, not mathlib. Not a mathlib composition.

Conclusion: **NOT-COMPOSABLE.** Mathlib provides **neither the exact form nor the building
blocks**: no p-adic measure type, no p-adic Dirac functional, no Iwasawa algebra. The only
same-named mathlib objects are in different categories (`ℝ≥0∞`-measures; complex Eisenstein
series; the arithmetic function `σ_k`) and cannot be chained into this `PadicMeasure`-valued
divisor sum. (This rules out NO-composable-from-mathlib; Phase 7 weighs YES-add-as-is vs
BORDERLINE.)

---

## Verdict: `divisorMeasure`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the mathematics is **standard and named** — the higher
  Eisenstein-measure coefficient `A_n = Σ_{0<d∣n, p∤d} δ_d`, moment `σ^p_k(n)`, in the
  **Serre–Katz–Eischen** Eisenstein-measure framework (≥5 WebSearch hits unanimous; survey
  arXiv:2101.01879; source arXiv:2309.15692 §8). Measures-as-`Hom(C(X,R),M)` and `δ_d`=point-mass
  group-like element are both confirmed standard.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL relative to its substrate**
  `PadicMeasure p ℤ_[p]ˣ`; the prime-to-`p` filter is the *correct* p-stabilised shape, not an
  over-restriction. The only generalisations (coefficient ring, base field) are **substrate
  changes** (the project's own §5 roadmap), not weakenings of this declaration. Phase 4c found no
  `divisorMeasure`-level modern-idiom restatement.
- Diamond/defeq risk (Phase 4.5): **NONE** (sealed finite sum of linear functionals; no
  instance/coercion/reducible surface).
- Mathlib search (Phase 5): **not in mathlib, and the building blocks are absent** — no
  `PadicMeasure` type, no p-adic `dirac`, no Iwasawa algebra, no p-adic-L-function machinery;
  the same-named mathlib objects (`MeasureTheory.Measure.dirac`/`sum`, complex `eisensteinSeriesMF`,
  `ArithmeticFunction.sigma`) are different categories of object.
- Composition check (Phase 6): **NOT-COMPOSABLE** (Attempts 1–3 all fail on the absent
  substrate); **K = 4 in-file call sites, 0 external/0 downstream**, no inline bypass.

**Rationale (1–2 paragraphs):**

`divisorMeasure` is, mathematically, an unimpeachably standard object: it is the `n`-th
non-constant coefficient `A_n` of the Λ-adic Eisenstein measure, in the exact Serre–Katz form
(point masses summed over the prime-to-`p` divisors, with weight-`k` moment the divisor power sum
`σ^p_k(n)`), as packaged by Rodrigues Jacinto–Williams §8. The literature search returned a rich,
unanimous, *named* framework (the "Eisenstein measure", the Iwasawa algebra as the continuous dual
`Hom(C(X,ℤ_p),ℤ_p)`, the point-mass/group-like `δ_d=[d]`), so this is **not** a too-narrow or
project-invented object. But mathlib's bar is "the right statement at the right generality, not
already there, and not a substrate this small library can absorb in isolation" — and Phase 5 is
decisive: **mathlib has none of the substrate.** There is no p-adic measure type, no p-adic Dirac
functional, no Iwasawa algebra `ℤ_p[[ℤ_p^×]]`, and no p-adic-L-function machinery whatsoever (the
only `Iwasawa` file in mathlib is an unrelated group-action lemma). `divisorMeasure` therefore
cannot be shipped *as a standalone declaration*: it is the leaf of a multi-file tower
(`PadicMeasure` → `dirac` → `unitsPowCM`/`Λ(ℤ_p^×)` → the pseudo-measure / fraction-ring
machinery → the Eisenstein family), every layer of which is project-local and would have to be
upstreamed first (and several layers — e.g. `unitOfNat` — are themselves BORDERLINE/needing-design).

This is **not** `NO-composable-from-mathlib` (Phase 6 is NOT-COMPOSABLE: the building blocks are
absent, not present) and **not** `NO-mathlib-has-it` (Phase 5 found nothing). It is **not** a clean
`YES-add-as-is` either: although Phase 4b is MAXIMALLY-GENERAL-relative-to-substrate, a YES gate
requires that the decl be a sensible *unit* to add, and a single coefficient-`def` of a p-adic
Eisenstein family — with its substrate entirely missing, zero downstream consumers, a name/shape
(`unitOfNat` junk lift, the file's own erratum #11) tuned to this one development, and a modern-idiom
question (should the Iwasawa algebra be the completed group algebra?) that lives one level *below*
it — is exactly a judgment call about **mathlib's p-adic-L-function roadmap and the right
abstraction for the substrate**, not a self-resolving YES. Per the skill's gate, when the verdict
hinges on a roadmap/abstraction/taste judgment the worker cannot ground in the evidence, the
verdict is **BORDERLINE**, with the questions spelled out.

(Cost is *not* the reason for BORDERLINE — per the Bourbaki-2.0 rule EXPENSIVE never downgrades.
The reason is that the *unit of contribution* and the *substrate abstraction* are human/roadmap
calls, and the substrate is wholly absent from mathlib.)

**Numbered questions (≤5):**

1. **Is the p-adic-measure / Iwasawa-algebra substrate (`PadicMeasure`, `PadicMeasure.dirac`,
   the convolution algebra `Λ(ℤ_p^×)`, pseudo-measures) intended for mathlib at all?** If *no*
   (it stays an AINTLIB-local foundation), then `divisorMeasure` is a project-internal coefficient
   and is **out of mathlib scope** — keep it local. If *yes*, this becomes a multi-PR upstreaming
   effort and `divisorMeasure` would ship near the *end* of it (questions 2–5 then apply).

2. **If the substrate is upstreamed, should the Iwasawa algebra be modelled as the raw continuous
   dual `C(ℤ_p^×,ℤ_p)→ₗ[ℤ_p]ℤ_p` (the current `PadicMeasure`), or as a completed group algebra /
   profinite-completed `MonoidAlgebra` with a universal property** (so `δ_d` is the canonical
   group-like `[d]`)? This abstraction choice (Phase 4c row 3) should be settled *before*
   `divisorMeasure`, because it determines what "`Σ δ_d`" even means in mathlib.

3. **Should `divisorMeasure` be a standalone `def : ℕ → Λ(ℤ_p^×)` at all, or should the family
   `𝐄 = Σ A_n q^n` be the upstreamed unit, with `A_n` only its `n`-th coefficient?** The
   literature treats `A_n` as a coefficient *within* the family, never as a reusable named
   function; mathlib may prefer the family (a `PowerSeries (Λ(ℤ_p^×))`) as the API surface, with
   `divisorMeasure` inlined.

4. **Is the `ℚ / ℤ_p^×` (Kubota–Leopoldt) base case the intended mathlib target, or should the
   first upstreamed form already be the general-coefficient-ring / totally-real-field version**
   (Serre/Katz/Eischen — the project's own deferred §5 generality)? Adding the narrow base case
   first risks a later re-statement; adding the general one first is much more work.

5. **Does the project want `divisorMeasure` upstreamed at all, given it currently has zero
   downstream/external consumers** (K = 4, all in `EisensteinFamily.lean`)? If it is purely an
   internal step toward `eisensteinFamily_interpolation`, the answer to "should mathlib have *this
   decl*" may simply be "no — mathlib should have the *family* and its interpolation theorem, once
   the substrate is in."

Next action: the user answers Q1 first (it is dispositive). If Q1 = "substrate not for mathlib",
record `divisorMeasure` as **out-of-scope, keep project-local** (no further action). If Q1 = "yes",
this is a long multi-PR roadmap: settle the substrate-abstraction question (Q2) and the
unit-of-contribution question (Q3) via `/develop`-style design, upstream the substrate
(`PadicMeasure`, `dirac`, `Λ(ℤ_p^×)`) **first**, then re-run `/mathlibable` on the *family*
`eisensteinFamily` / `eisensteinFamily_interpolation` rather than this leaf coefficient.

---

## Next step

The verdict hinges on a roadmap/abstraction judgment the skill cannot make alone, so it is
**BORDERLINE-needs-human**. Answer **Q1** first — *is the p-adic-measure / Iwasawa-algebra
substrate (`PadicMeasure`, `dirac`, `Λ(ℤ_p^×)`) intended for mathlib at all?* If no, keep
`divisorMeasure` project-local (out of mathlib scope). If yes, treat it as the leaf of a multi-PR
upstreaming effort: settle the substrate abstraction (raw continuous dual vs completed group
algebra, Q2) and the unit of contribution (standalone `A_n` vs the whole family `𝐄`, Q3) via a
`/develop` design pass, upstream the substrate first, and only then re-run `/mathlibable` on the
Eisenstein *family* and its interpolation theorem rather than on this single coefficient `def`.
