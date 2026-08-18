# `/mathlibable` report — `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA`

**Final verdict: `BORDERLINE-needs-human`** (full reasoning in Phase 7).

This is the formalised **"T705 / Lemma 6.3 pattern"** step of the project's
residue-of-ζ_p computation: it is a single-use leaf *application* of RJW's
**general** Amice/Mahler-transform intertwining `A_{xμ} = ∂A_μ`
(arXiv:2309.15692, **Lemma 3.29**, `∂ = (1+T)d/dT`) to one bespoke base-changed
measure `ρ_a`. It is true, non-trivial, and absent from mathlib — but its
mathlib-worthiness is entirely contingent on whether the surrounding p-adic-measure /
Amice-transform / Kubota–Leopoldt apparatus (all project-defined, none in mathlib)
is upstreamed, and on naming/generality calls for the project objects `mahlerK`,
`rhoA`, `MeasureR.res`, `MeasureR.baseChange`, `PadicMeasure.muA`. Those are human
judgment calls the search cannot settle. Numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task instruction — build stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:703`
- kind:                      `theorem`
- has sorry:                 **no** (0 `sorry`/`admit` in `ResidueZeta.lean`)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — the file proves continuity / simple-pole / residue `1 − p⁻¹` of the Kubota–Leopoldt p-adic zeta branches at `s = 1`.

The declaration head (with the active ambient context):

```lean
omit [CharZero K] in
/-- R7.5c: multiplication by `x` recovers `Res_{ℤ_p^×}(μ_a)` —
`∂𝓐(ρ_a) = 𝓐(Res_{units}(μ_a))` over `K` (Lemma 6.3's pattern, T614). -/
theorem one_add_mul_derivative_mahlerK_rhoA (a : ℕ) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoA p K a))
      = mahlerK p K (MeasureR.res p K
          (PadicMeasure.isClopen_units p)
          (MeasureR.baseChange p K (PadicMeasure.muA p a))) := by
  -- base-change the ℤ_p-level multiplication-by-x identity to K, then transport
  -- through mahlerK via 𝓐_{xμ} = ∂𝓐_μ and map-commutation with ∂.
  ...
```

Ambient context (`section mass`, `ResidueZeta.lean:432`):
`variable (p : ℕ) [hp : Fact p.Prime]` and
`variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
— with `CharZero K` `omit`-ted for this theorem (the proof is a purely
algebraic/formal-power-series identity; the analytic instances are inherited,
not used).

---

### Statement (Phase 1)

`PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA` is **a theorem** stating the
following.

> Let `p` be prime and `K` a complete ultrametric normed field that is a
> `ℚ_p`-algebra, with ring of integers `R = integerRing K`. For each natural
> number `a`, applying the operator `∂ := (1+T) d/dT` to the Mahler/Amice
> transform `𝓐(ρ_a) ∈ K⟦T⟧` of the numerator measure `ρ_a` recovers the Mahler
> transform of the units-restriction of the base-changed Kubota–Leopoldt measure:
>
>   `∂ 𝓐(ρ_a)  =  𝓐( Res_{ℤ_p^×}( μ_a ⊗ K ) ).`
>
> Mathematically this is the instance `∂𝓐(ρ_a) = 𝓐(x·ρ_a)` of the general
> intertwining `A_{xμ} = ∂A_μ`, specialised to `ρ_a`, where multiplying `ρ_a`
> by `x` cancels the `x⁻¹` inside `zetaNum a` and exposes `Res_{ℤ_p^×}(μ_a)`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` — a complete ultrametric `ℚ_p`-field (in the project's residue argument, eventually `ℂ_p ⊇ ℚ_p(μ_p)`). `[CharZero K]` is in the section but `omit`-ted here (unused).
- `a : ℕ` — the auxiliary integer of the Kubota–Leopoldt construction (the `(1−a)`-twist parameter). The statement holds for **all** `a` (no coprimality hypothesis is needed for this identity; the `p ∤ a` constraint enters only later, in the mass computation that consumes it).

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): the multiplication-by-`x` ↔ `∂` bridge applied to `ρ_a`
(RJW §6 "Lemma 6.3 pattern", the formalised version of `A_{Res_×(x·μ)}`).

Conclusion (Lean): an equality of `PowerSeries K`:
`(1 + PowerSeries.X) * PowerSeries.derivativeFun (mahlerK p K (rhoA p K a)) = mahlerK p K (MeasureR.res p K (PadicMeasure.isClopen_units p) (MeasureR.baseChange p K (PadicMeasure.muA p a)))`.

Underlying objects (all project-defined, in `PadicLFunctions/MeasureR/*` and `PadicLFunctions/Measure/*`):
- `MeasureR K X := C(X, integerRing K) →ₗ[integerRing K] integerRing K` (`MeasureR/Basic.lean:50`) — an `R`-valued measure as an `R`-linear functional (RJW Def 3.6); an Iwasawa-algebra element in functional disguise.
- `mahlerK` (`MeasureR/FormalPsi.lean:749`) — the `K`-mapped Mahler/Amice transform `𝓐_μ ∈ K⟦T⟧` (`PowerSeries.map (integerRing K).subtype (MeasureR.mahlerTransform p K μ)`); `MeasureR.mahlerTransform` (`MeasureR/MahlerTransform.lean:67`) is RJW Def 3.15 over `R`, `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ`.
- `rhoA` (`ResidueZeta.lean:651`) — the §4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)`, defined as `baseChange(ι(zetaNum a))`.
- `MeasureR.res` / `IsSupportedOn` (`MeasureR/Toolbox.lean:133`, `:137`) — restriction of a measure to a clopen by multiplication by its characteristic function (RJW §3.5.3).
- `MeasureR.baseChange` (`MeasureR/BaseChange.lean:39`) — the ring map `PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p]` extending coefficients from `ℤ_p` to `R`.
- `PadicMeasure.muA` (`KubotaLeopoldt/MuA.lean:101`) — RJW Def 4.5, the classical Kubota–Leopoldt measure on `ℤ_p` whose Mahler transform is `F_a = 1/T − a/((1+T)^a−1)`.
- `PowerSeries.derivativeFun` (**mathlib**, `Mathlib/RingTheory/PowerSeries/Derivative.lean:44`) — the formal derivative `d/dT`. The combination `(1+X)·derivativeFun` is the project's operator `∂` (`MeasureR.del`, `MeasureR/Toolbox.lean:50`, "RJW Lem 3.24").

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step corollary lemma (docstring tag "R7.5c"), the units/`∂`-bridge for the *specific* numerator measure `ρ_a`. It is not a `def`/`class`/`structure`, not named after a person/place, and not a `## Main results` headline (the §7 headline is the analyticity/pole/residue of the zeta branches). Its proof is a short `rw`/`simp` chain (one `have hbase` from the `ℤ_p`-level identity, base-changed to `K`, then transported through `mahlerK`) that applies the *general* project lemmas (`mahlerTransform_cmul_X`, `baseChange_cmul`, `baseChange_res`, `mahlerTransform_cmul_X`) to the concrete `ρ_a`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: ~14 substantive lines (a `have hbase` block plus a `rw … simp … rw` transport). One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`. (For the record the body is a small multi-step formal-calculus argument; this reinforces the "thin corollary" reading, but the one-liner *def* gate does not apply to theorems.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Amice transform p-adic measure multiplication by x corresponds to (1+T) d/dT operator Mahler power series Iwasawa" | yes | `∫ x^m dμ = (t d/dt)^m Φ_μ\|_{t=1}`; `A(δ_{αv}) = (1+T)^α` | the multiplication-by-x ↔ `(1+T)d/dT` intertwining is the **standard** Amice/Mahler fact (de Shalit *Mahler bases*; Γ-transform literature) |
|  2 | WebSearch (named source)         | "arXiv 2309.15692 p-adic L-functions Mahler transform Lemma 3.24 multiplication by x derivative power series" | yes | identifies RJW = Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions*, §3.4 "p-adic analysis and Mahler transforms" | confirms the project formalises this exact paper; the relevant lemma is in §3.4 |
|  3 | WebSearch (general / abstract form)| "Iwasawa Amice transform measure '(1+T) d/dT' 'x mu' power series restriction units Z_p residue zeta" | yes | `A_μ(t) = ∫(1+t)^y dμ`; distributions on `ℤ_p` ≅ `ℤ_p[[T]]`; restriction to `ℤ_p^×` is standard | the whole measure↔power-series + restriction-to-units dictionary is textbook (Colmez, Amice, Iwasawa) |
|  4 | WebSearch (residue / units-restriction)| "p-adic measure restriction units Amice transform Res derivative operator residue Kubota-Leopoldt x inverse indeterminacy" | yes | `A_{Res_×(x^{k-1}μ)}(0)`; unique pseudo-measure `ζ_p` on `ℤ_p^×`; Amice = isometry measures ≅ bounded power series | confirms the §6 `A_{Res_×(x·μ)}` shape and the `x⁻¹` indeterminacy that this lemma's parent computation must handle |
|  5 | ChatGPT MCP                      | (intended: "standard form / generality / history of the `A_{xμ} = ∂A_μ` intertwining and its `Res_×` application") | n/a | — | **ChatGPT MCP server not installed in this environment** (only auth stubs for Asana/Atlassian/… in the deferred-tools list; no `mcp__chatgpt__*`/`mcp__openai__*`). Compensated by the verbatim primary source (row 11) + 4 WebSearch queries at 4 generality levels + 2 nLab fetches. |
|  6 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` symlink                          | n/a | (directory absent)               | No `.mathlib-quality/references/` dir and no `refs/` store on this checkout — recorded `n/a`. |
|  7 | nLab                             | WebFetch `ncatlab.org/nlab/show/Iwasawa+algebra`                                                        | yes | "the Iwasawa algebra, classically, is the completed group ring `ℤ_p[[Γ]]` … `≅ ℤ_p[[T]]`" | **stub** — defines the Iwasawa algebra only; **no** measures, **no** Amice/Mahler transform, **no** `x·μ ↔ ∂` operator. |
|  8 | nCatLab (categorical)            | WebFetch `ncatlab.org/nlab/show/Amice+transform`                                                        | n/a | (HTTP 404)                       | Page does not exist; this is not a categorical concept anyway (analytic NT / Iwasawa theory). |
|  9 | Stacks Project (alg geom)        | —                                                                                                      | n/a | —                                | Not an algebraic-geometry concept — p-adic measures / Amice transform / Iwasawa theory are out of Stacks' scope. |
| 10 | MathOverflow / Math.StackExchange| (folded into #1, #3, #4 — the analytic-NT queries surfaced MO/MSE-style sources)                        | partial | only general Amice/Kubota–Leopoldt facts; no named "`∂𝓐(ρ_a)=𝓐(Res_×μ_a)`" result | the general intertwining is well-covered; the specific `ρ_a` instance is paper-internal bookkeeping. |
| 11 | **Primary source (RJW PDF)**     | `pdftotext` of arXiv:2309.15692 v2, §3.4 (Lemma 3.29 / Cor 3.30) and §6 (Eq. 6.2/6.3)                  | yes  | **verbatim** (see summary)        | the decisive evidence — exact match of the *general* lemma and the *application shape*. |

The protocol passed: WebSearch ran **4** distinct queries spanning the specific
form (`A_{xμ}=∂A_μ`), the most-general form (the measure↔power-series Amice
dictionary), the named source (arXiv:2309.15692), and the units-restriction/residue
shape; local refs, nLab, nCatLab, Stacks, and MathOverflow were each checked or
recorded `n/a` with reason; and the **primary source was read verbatim** (the
authoritative compensation for the genuinely-unavailable ChatGPT MCP, whose role —
pinning the standard form, generality, and history — is fully discharged by RJW §3.4
+ §6 plus the 4 web queries).

**Verbatim from the source** (pdftotext of arXiv:2309.15692 v2):

> *(§3.4, around the measure `xμ` defined by `∫ f(x)·xμ = ∫ x f(x)·μ`)*
>
> **Lemma 3.29.** — We have `A_{xμ} = ∂A_μ`, where `∂` denotes the differential
> operator `(1 + T) d/dT`.
>
> **Corollary 3.30.** — For `μ ∈ Λ(ℤ_p)`, we have `∫_{ℤ_p} x^k · μ = ∂^k A_μ(0)`.

> *(§6, the residue computation, Eq. 6.2–6.3)*
>
> … if `k > 0`, we showed above that
> `∫_{ℤ_p^×} χ(x) x^{k−1} · μ_η = A_{Res_×(x^{k−1} μ_θ)}(0) = (1 − θ(p)p^{k−1}) ∂^{k−1} F_θ(0).`
> We want to compute this for `k = 0`. Identically we could try to argue that
> `L_p(θ, 1) = A_{Res_×(x^{−1} μ_θ)}(0) = (1 − θ(p)p^{−1}) ∂^{−1} F_θ(0).`  (6.3)
> … In order to make this reasoning rigorous, one needs to deal with the fact
> that `x^{−1}` is not a well-defined operation on measures on `ℤ_p`, rendering
> `x^{−1} μ_θ` ill-defined. On power series, this is captured by the indeterminacy
> in defining `∂^{−1}`. …

Lean ↔ source match: the Lean theorem is the **formalised, rigorous version of the
`k = 0` step** of RJW §6/§7. RJW writes `A_{Res_×(x^{-1} μ_θ)}(0)` and flags that
`x^{-1}μ_θ` is ill-defined; the project resolves the indeterminacy by *first*
defining the unit-supported numerator measure `ρ_a = baseChange(ι(zetaNum a))`
(with `zetaNum a = x⁻¹·Res_×(μ_a)` living already on the units, so `x⁻¹` is
applied where it *is* defined) and *then* proving `∂𝓐(ρ_a) = 𝓐(x·ρ_a) =
𝓐(Res_×(μ_a))` — i.e. multiplying back by `x` cancels the `x⁻¹` and lands on the
units-restriction. The operator `∂ = (1+T)d/dT` is the project's `MeasureR.del`
(`MeasureR/Toolbox.lean:50`, docstring "RJW Lem 3.24"), here written unfolded as
`(1+X)*derivativeFun`. The *engine* of the proof is the general `A_{xμ}=∂A_μ`,
which the project formalises as `MeasureR.mahlerTransform_cmul_X`
(`MeasureR/Toolbox.lean:74`, docstring "RJW Lem 3.24, TeX 1066–1075"). Note the
project's internal numbering ("Lem 3.24"/"Lemma 6.3") tracks a TeX draft; the
arXiv v2 numbers the same general lemma **3.29** and the units-restriction step
sits at **(6.2)/(6.3)**.

### Literature summary (Phase 3)

Concept identified as: the **Amice/Mahler-transform intertwining** "multiplication
by `x` on a measure ↔ the operator `∂ = (1+T)d/dT` on its transform"
(RJW **Lemma 3.29** / **Cor 3.30**; `∫ x^k dμ = ∂^k A_μ(0)`), and specifically its
**units-restriction application** in the residue/value computation (RJW §6,
Eq. 6.2/6.3, `A_{Res_×(x^{k-1}μ)}(0)`). The target `one_add_mul_derivative_mahlerK_rhoA`
is the *application* of the general intertwining to the single base-changed
numerator measure `ρ_a`, packaged so the §7 residue mass `∫_{ℤ_p^×} x⁻¹ μ_a =
−(1−p⁻¹)log_p(a)` can be read off.

Sources agree on the standard form: **yes**. The intertwining `A_{xμ}=∂A_μ` with
`∂ = (1+T)d/dT` (equivalently `t d/dt` under `t = 1+T`) is uniform across de Shalit
*Mahler bases and elementary p-adic analysis*, Colmez *Fontaine's rings and p-adic
L-functions*, Amice's original work, and the Γ-transform / Iwasawa-λ-invariant
literature; the measure↔`ℤ_p[[T]]` correspondence and restriction-to-`ℤ_p^×` are
textbook (Washington Ch. 12, Lang *Cyclotomic Fields*).

Most general standard form: the **general** theorem `A_{xμ} = ∂A_μ` (and
`x^k μ = ∂^k A_μ(0)`) for an *arbitrary* measure `μ` — a structural fact about the
Amice transform with no reference to `ζ_p`, `μ_a`, or `ρ_a`. The literature states
this once and then derives unit-restriction value-formulas (the residue, special
values `L_p(θ,1−k)`) as applications; it does **not** name an
"`∂𝓐(ρ_a)=𝓐(Res_×μ_a)`"-shaped result.

Generality dimensions where the literature varies:
  - **Coefficient ring:** `ℤ_p`/`ℂ_p` (classical / RJW) → any complete
    nonarchimedean `ℚ_p`-algebra `R = integerRing K` (the project's `MeasureR`
    layer, the §5 widening). The project already takes the more general `R`.
  - **The object the intertwining is applied to:** the literature states the
    *general* `A_{xμ}=∂A_μ`, then derives unit-restriction value formulas as
    one-line corollaries — it does not single out the `ρ_a` instance.

Disagreement with the literature: **none on content**. The mismatch is one of
*granularity*: this theorem is a specialisation of the general (literature-standard)
intertwining to one bespoke measure `ρ_a`, which the literature treats as an
immediate application rather than a named result. The literature search returned
**not nothing** — it returned the **general** lemma (`A_{xμ}=∂A_μ`) and the
**general** units-restriction value-computation framework — but not a
`one_add_mul_derivative_mahlerK_rhoA`-shaped statement. That is the central tension
for the verdict.

---

### Generality analysis — `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA` (Phase 4)

Literature-standard form (from Phase 3): the structural intertwining
`A_{xμ} = ∂A_μ` (with `∂ = (1+T)d/dT`) for an *arbitrary* measure `μ` over an
arbitrary complete nonarchimedean coefficient ring — the project's
`MeasureR.mahlerTransform_cmul_X` (`MeasureR/Toolbox.lean:74`).

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | the measure `rhoA p K a`              | one *specific* measure `baseChange(ι(zetaNum a))` | an *arbitrary* measure `μ` | **yes** | The identity `∂𝓐(μ) = 𝓐(xμ)` holds for *every* `μ`; this theorem fixes `μ = ρ_a` and additionally identifies `x·ρ_a = Res_×(baseChange μ_a)` (a project fact, `cmul_mahler_one_iota_zetaNum`). The genuinely-general statement is `mahlerTransform_cmul_X` (RJW Lemma 3.29), already in the project. |
| 2 | the RHS `Res_×(baseChange μ_a)`       | the units-restriction of one specific base-changed measure | (no general analogue — this is `x·ρ_a` for this `ρ_a`) | n/a | The RHS is not an independent parameter; it is `x·ρ_a` computed for this `ρ_a`. Generalising the measure (row 1) subsumes it. |
| 3 | `[NormedAlgebra ℚ_[p] K]`, `[IsUltrametricDist K]`, `[CompleteSpace K]`, `[CharZero K]` | complete ultrametric `ℚ_p`-field | nonarchimedean field with integer ring | borderline (already general; some instances unused) | The general lemma `mahlerTransform_cmul_X` is proved with `omit [CompleteSpace K]`; this theorem `omit`s `[CharZero K]` and does not use the analytic instances. The *abstract* fact is more general than this section's typeclasses — but that generality already lives in the general lemma, not here. (A `/cleanup`-grade `omit` of the unused `[IsUltrametricDist K] [CompleteSpace K]` would tidy this leaf; it is not a generality flip.) |
| 4 | `a : ℕ`                               | unconstrained natural        | the construction parameter   | NO (already maximal) | The identity holds for **all** `a` (no `p ∤ a` needed here — that constraint enters only in the downstream mass computation). The narrowness is not in `a`; it is in fixing the *whole measure* to be `ρ_a`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in a *degenerate* way
(identical in kind to the sibling `psi_rhoA`). The narrowing is not "a hypothesis
that should be weakened by one typeclass"; it is that the statement is an *instance*
(the measure is the fixed concrete object `ρ_a`, and the RHS is its
`x`-multiplication) of a *general structural theorem* the project already proves
separately — `MeasureR.mahlerTransform_cmul_X` (= RJW Lemma 3.29). The "more general
form" is **not** a re-typeclassed `one_add_mul_derivative_mahlerK_rhoA`; it is the
already-existing general lemma `A_{xμ}=∂A_μ`, of which this theorem is a short
application (combined with the project's `cmul_mahler_one_iota_zetaNum` /
`baseChange_*` lemmas that compute `x·ρ_a = Res_×(baseChange μ_a)`).

Number of weakening opportunities found: **1 substantive** — generalise the *object*
`ρ_a` to "an arbitrary measure `μ`", which is precisely the content of the
already-present `mahlerTransform_cmul_X` (i.e. there is nothing new to prove; the
general result already exists in the project). Plus 1 cosmetic (`omit` the unused
analytic instances on this leaf).

Proposed restatement: not applicable as a *new* statement — the maximally-general
form is the **already-present** `MeasureR.mahlerTransform_cmul_X`
(`MeasureR/Toolbox.lean:74`) together with the base-change transport
`MeasureR.baseChange_cmul` (`MeasureR/BaseChange.lean:155`),
`MeasureR.baseChange_res` (`:175`), and `MeasureR.algCM_mahler` (`:74`). This
theorem adds no generality over those.

Cost of restatement: CHEAP (the proof is already the short application body) — but
this does not produce a *new* mathlib-worthy statement; it points back at the
general lemma.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | The hypotheses are already typeclasses (`NormedAlgebra`, `IsUltrametricDist`, …); nothing bundled to unbundle. | — |
|  2 | sequences/metric → filters/topological? | no | No limit/convergence content; this is a *formal* (algebraic) power-series identity. The operator `∂` and `derivativeFun` are purely algebraic. | — |
|  3 | construct an object → universal-property class? | partial (already done by the project) | The "mult-by-x ↔ ∂" intertwining is the structural characterisation; the project already has it as the general `mahlerTransform_cmul_X`. This theorem is a *consumer* of that characterisation, not a place to introduce a new one. | the project already gets the intertwining; this lemma just applies it to `ρ_a` |
|  4 | set-with-closure-predicate → bundled substructure? | no | `MeasureR.res`/`IsSupportedOn` are already the project's restriction API; no lattice-of-supports is in play for this corollary. | — |
|  5 | vector-space/field-specific → weaken typeclasses? | no (already general in `R`) | The `MeasureR` layer is already the `R`-coefficient generalisation of the `ℤ_p`-only `PadicMeasure` layer; `mahlerK`/`del` are stated over `integerRing K`. | — |
|  6 | 1-categorical → higher-categorical? | no | Not a categorical statement (concrete formal-power-series / functional-analytic identity). | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | `a : ℕ` is the construction's parameter, not an index to abstract; the intertwining is already uniform in `a` and the operator `∂` is fixed/standard. | — |

Modern idiom available: **no** (for this theorem itself). One-line reason: the
modern, structural form of this mathematics — "multiplication by `x` on a measure ↔
`∂ = (1+T)d/dT` on its Amice transform" — already exists in the project as the
*general* `MeasureR.mahlerTransform_cmul_X` (using mathlib's contemporary
`PowerSeries.derivativeFun` / `PowerSeries.map` idiom); this theorem is a downstream
application of it to `ρ_a`, not a candidate modernisation in its own right.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; skipped per the skill's scope rule.

---

### Mathlib search-status: `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA` (Phase 5)

Five-method search (read `references/mathlib-search.md`; mathlib source tree present
at `.lake/packages/mathlib/Mathlib`, so methods D/E were run directly against
source — the authoritative signal for "does the decl/infrastructure exist"):

[A] Lean-Finder       (web service; not reachable from this sandboxed worker) — n/a: relied on the local mathlib grep (D/E), authoritative for the existence question.
[B] Loogle            type-pattern `(1 + PowerSeries.X) * PowerSeries.derivativeFun _ = _`, and `_ →ₗ[_] _` "measure as functional" → transform — n/a (no network from worker); D/E cover existence directly.
[C] LeanSearch        NL: "(1+T) times derivative of Amice transform equals transform of units-restricted p-adic measure"; "multiplication by x on p-adic measure corresponds to (1+T)d/dT" — n/a (no network); D/E cover it.
[D] Grep mathlib src  `Amice`, `mahlerTransform`, `measure.*power series`, `(1 \+ X).*derivativeFun` / `derivativeFun.*(1 \+ X)`, `Iwasawa`, `kubota`/`leopoldt`/`padicLFunction`/`p-adic L-function`/`p-adic zeta`, `PadicMeasure`/`MeasureR`, `IsSupportedOn`/`res_units`/`restrict.*clopen` — **no relevant hits**.
[E] Name pattern      grep `rhoA`, `zetaNum`, `mahlerK`, `one_add_mul_derivative`, `mahlerTransform_cmul_X`, `del` (as the `∂` operator) across `Mathlib/` — **no hits**.

What the grep found, and why each is irrelevant:
- `Mathlib/RingTheory/PowerSeries/Derivative.lean` — the **generic** `PowerSeries.derivativeFun` / `derivative` / `derivativeFun_mul` API the proof *consumes*; it has no `(1+X)·∂` operator, no Amice transform, no measures.
- `μa`/`μb` in `Dynamics/Ergodic/MeasurePreserving.lean`, `Conservative.lean` — bound *variable names* for abstract measures in ergodic theory; not the Kubota–Leopoldt `μ_a`.
- `measureRestrict` / `restrict` (`MeasureTheory/Measure/Restrict.lean`, `Trim.lean`, `Conservative.lean`) — restriction of a *Bochner/Lebesgue measure to a measurable set*, not multiplication of a `C(X,R)→ₗR` functional by a clopen characteristic function.
- `one_add_…` hits (`LSeries/Nonvanishing.lean`, `RadonNikodym.lean`) — an L-series derivative bound and a Radon–Nikodym `1 + …` algebra step; unrelated to `(1+T)d/dT` on power series.
- `Iwasawa` (`GroupTheory/GroupAction/Iwasawa.lean`) — the **Iwasawa decomposition / lemma on group actions** (group simplicity), *not* the Iwasawa algebra of measures.
- `Mahler` (`MahlerMeasure.lean`, `MahlerBasis.lean`, `Padics/AddChar.lean`) — the **Mahler measure (height) of a polynomial** and the **Mahler basis of `C(ℤ_p, ℚ_p)`**; neither is the project's `mahlerTransform` of a p-adic measure.

Searched for both:
  - the user's current form (`∂𝓐(ρ_a) = 𝓐(Res_×(baseChange μ_a))`): **absent** — `ρ_a`, `zetaNum`, `mahlerK`, `μ_a` and the entire Kubota–Leopoldt apparatus are not in mathlib.
  - the literature-standard general form (`A_{xμ} = ∂A_μ`, the Amice intertwining for arbitrary `μ`): **also absent** — mathlib has *neither* an Amice/Mahler transform of measures, *nor* the `(1+T)d/dT` operator on it, *nor* `MeasureR`/`PadicMeasure`, *nor* a notion of a measure being "restricted to a clopen" in this functional-analytic sense.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
general form). Mathlib does **not** even contain the *building blocks* (`MeasureR`,
the Amice/Mahler transform `mahlerK`/`mahlerTransform`, the `∂` operator `del`,
`MeasureR.res`, `baseChange`, `zetaNum`, `μ_a`) from which this identity could be
composed — every ingredient is project-defined. Mathlib's p-adic analysis presently
stops at `PadicInt`, the Mahler *basis* of `C(ℤ_p, ℚ_p)`, p-adic add-characters, and
`ℂ_p`; it has no theory of p-adic measures / the Amice transform of measures / the
Iwasawa algebra of measures / p-adic L-functions. The only mathlib decl the proof
uses is the **generic** `PowerSeries.derivativeFun` (and `PowerSeries.map`).

---

### Call sites — `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA` (Phase 6.0)

Internal use count: **K = 1** (within the project; one use, and it is in the
*declaring file*).
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                            |
|--------------------------------|------------------------------------------------------------------------------|
| ResidueZeta.lean:934           | `rw [one_add_mul_derivative_mahlerK_rhoA, MeasureR.res_units_eq, mahlerK_sub, mahlerK_phi]` |

That single site is inside `p_mul_constantCoeff_mahlerK_rhoA` (`ResidueZeta.lean:913`),
the **Step 1 of the c₀-pin** in the §7 residue computation: it supplies the bridge
`(1+X)·∂(𝓐_ρ) = mahlerK(baseChange μ_a) − φ B` (using `Res_× = 1 − φψ`, RJW Eq 3.10),
which combines with the `M`-bridge (`mahlerK_baseChange_muA`) and the antiderivative
identity (`one_add_mul_derivative_FtildeA`, the sibling Lemma 7.3) to compute the
mass `∫_{ℤ_p^×} x⁻¹ μ_a = −(1−p⁻¹)·log_p(a)`. It is one rewrite step in the larger
residue argument.

Inline-derivation grep (was `∂𝓐(ρ_a) = 𝓐(Res_×(baseChange μ_a))` re-derived elsewhere
without this lemma?): **(none)** — no other proof re-derives it inline; the one
consumer uses the lemma.

What the pattern tells us (per the Phase-6.0 signal table): **K = 1, in-file only, no
external callers, no inline re-derivation.** This is the "possibly the wrong
abstraction / could be inlined" pattern — *but* the proof depends on the general
`mahlerTransform_cmul_X` plus base-change transport and a local `have hbase`, so it
is a genuine, non-trivial helper, not dead code or a bypassed wrapper. Its audience
is, today, a single proof in a single paper-formalisation.

### Composition check (Phase 6)

The relevant composition question for `/mathlibable` is "can **mathlib's** primitives
compose to give this in ≤3 calls?" — and the answer is decisively **no**, because
mathlib has none of the primitives (`MeasureR`, the Amice transform, the `∂`
operator, `MeasureR.res`, `baseChange`, `zetaNum`/`ρ_a`). So there is no mathlib
composition to inline.

For completeness, the *project-internal* composition (which is essentially what the
proof body is) is:

Attempt 1: `have hbase : cmul(mahlerCM 1) ρ_a = Res_×(baseChange μ_a)` (from
`congrArg (baseChange) cmul_mahler_one_iota_zetaNum`, then `baseChange_cmul`,
`algCM_mahler`, `baseChange_res`); then `rw [← hbase]; simp only [mahlerK];
rw [mahlerTransform_cmul_X, …, map_one_add_mul_derivativeFun']`.
  - Project decls used: `cmul_mahler_one_iota_zetaNum`, `MeasureR.baseChange_cmul`,
    `MeasureR.algCM_mahler`, `MeasureR.baseChange_res`, `MeasureR.mahlerTransform_cmul_X`,
    and the private local `map_one_add_mul_derivativeFun'`.
  - Mathlib decls used: only the generic `PowerSeries.derivativeFun` / `PowerSeries.map`.
  - Result: succeeds (the ~14-line proof in the source).
  - Notes: this is a clean application of *project* lemmas — the same shape
    `/mathlibable` flags as NO-composable *when the building blocks are in mathlib*.
    Here the building blocks are in the **project**, not mathlib — so the corollary
    is composable-from-the-project, and the mathlib-worthiness question shifts
    entirely onto whether the *general framework* (the Amice transform + the
    `A_{xμ}=∂A_μ` intertwining), not this leaf, should be upstreamed.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks every primitive).
Composable from *project* lemmas — which is the decisive observation for the verdict.

---

## Verdict: `PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Literature search (Phase 3):** the multiplication-by-`x` ↔ `∂ = (1+T)d/dT`
  intertwining of the Amice/Mahler transform is firmly classical (de Shalit, Colmez,
  Amice, Iwasawa) and is **RJW Lemma 3.29** (`A_{xμ}=∂A_μ`) / **Cor 3.30**
  (`x^k μ = ∂^k A_μ(0)`) — matched verbatim against the primary source
  (arXiv:2309.15692 v2 §3.4). The *units-restriction application* this theorem
  formalises is RJW §6 Eq. (6.2)/(6.3), `A_{Res_×(x^{k-1}μ)}(0)` — also verbatim. But
  the literature states the **general** intertwining and derives unit-restriction
  value formulas as applications; it gives **no** named "`∂𝓐(ρ_a)=𝓐(Res_×μ_a)`"
  result.
- **Generality analysis (Phase 4):** **STRICTLY NARROWER THAN STANDARD**, degenerately
  — this is an *instance* (fixed concrete measure `ρ_a`, RHS = `x·ρ_a`) of the
  project's own general theorem `MeasureR.mahlerTransform_cmul_X` (= RJW Lemma 3.29).
  Phase 4c found no modern-idiom improvement *for the corollary itself*; the
  structural form already exists as the general lemma.
- **Mathlib search (Phase 5):** **not in mathlib, and not composable from mathlib** —
  mathlib has *no* Amice/Mahler transform of measures, *no* `(1+T)d/dT` operator on
  it, *no* `MeasureR`/`PadicMeasure`/`mahlerK`/`del`/`res`/`baseChange`/`zetaNum`/`μ_a`,
  *no* Kubota–Leopoldt p-adic L-function. Every ingredient is project-defined; the
  sole mathlib dependency is the generic `PowerSeries.derivativeFun`/`map`. The
  `Iwasawa.lean`, `Mahler*`, `Restrict.lean`, `μa`/`μb` hits are unrelated namesakes.
- **Composition check (Phase 6):** **NOT-COMPOSABLE from mathlib**; composable from
  *project* lemmas (`mahlerTransform_cmul_X` + base-change transport + a local
  `map`-commutation helper). Call sites: **K = 1**, in the declaring file only, no
  external consumers, no inline re-derivations.

**Rationale (synthesis).**

This declaration sits at the same intersection as its siblings `psi_rhoA` and
`one_add_mul_derivative_FtildeA`, and is BORDERLINE for the same structural reason —
not because the worker is unsure, but because the genuine question is one the search
*cannot* settle from evidence alone.

On one hand, `one_add_mul_derivative_mahlerK_rhoA` is *not itself* a clean mathlib
candidate: it is a `SMALL`, ~14-line application that specialises a *general*
structural theorem (`mahlerTransform_cmul_X`, RJW Lemma 3.29, `A_{xμ}=∂A_μ`) to one
bespoke base-changed measure `ρ_a`, has a single in-file consumer, and is strictly
narrower than the literature-standard form (the general intertwining for arbitrary
`μ`). By every local signal — granularity, call-site count, "application of a general
lemma" shape — it is the kind of thing that, *if the general framework were in
mathlib*, would be NO-composable-from-mathlib (just apply the general lemma plus the
units-restriction identity at the one call site).

On the other hand, the standard NO buckets are unavailable on their own terms, and
that is decisive. **`NO-mathlib-has-it` fails the verdict gate:** Phase 5's conclusion
is "not in mathlib", not "found in mathlib as X" — there is no mathlib decl to cite,
because mathlib has neither this identity nor the general `A_{xμ}=∂A_μ` nor any of the
objects it mentions. **`NO-composable-from-mathlib` also fails its gate:** Phase 6
concluded NOT-COMPOSABLE *from mathlib* (mathlib lacks the Amice transform, the `∂`
operator, `MeasureR`, `res`, `baseChange` entirely), so there is no ≤3-line *mathlib*
composition to inline; the composition that exists is from *project* lemmas, which is
not what that bucket means. And **`YES-*` is wrong** too: this specific application is
strictly narrower than the literature standard (so not `YES-add-as-is`), yet the "more
general form" is not a re-typeclassed `one_add_mul_derivative_mahlerK_rhoA` to hand to
`/generalise` — it is the project's *already-existing* general lemma
`mahlerTransform_cmul_X`, so there is no new statement to propose (so not
`YES-but-generalise-first` in the usual sense either).

The genuine question is therefore one the skill cannot resolve from evidence alone:
**the entire surrounding framework — `PadicMeasure` / `MeasureR`, the Amice/Mahler
transform `mahlerTransform`/`mahlerK`, the operator `∂ = (1+T)d/dT` (`del`), the
intertwining `A_{xμ}=∂A_μ` (RJW Lemma 3.29), `MeasureR.res`, `baseChange`, and the
Kubota–Leopoldt zeta apparatus (`μ_a`, `zetaNum`, `ρ_a`) — is absent from mathlib,
and whether any of it (and at what grain) should be upstreamed is a large
project-policy and mathematical-taste call.** This theorem itself is a leaf
application that should never be upstreamed in isolation; but it is a leaf of a tree
whose *trunk* — the general `mahlerTransform_cmul_X` intertwining and the
`MeasureR`/Amice-transform infrastructure beneath it — is exactly the sort of
foundational p-adic-measure theory mathlib currently lacks and might want. That is a
decision for the maintainer, not the search. (Cost is **not** a factor in this
verdict; per the skill's Bourbaki-2.0 rule, an expensive upstreaming of the framework
would be worth doing — the open question is *policy and grain*, not effort.)

**Refactor-actionable detail / numbered questions (≤5):**

1. **Framework scope.** Is the AINTLIB plan to eventually upstream the
   p-adic-measure / Amice-transform infrastructure (`MeasureR`, the Mahler/Amice
   transform `mahlerTransform`/`mahlerK`, the operator `∂ = (1+T)d/dT` = `del`, the
   intertwining `mahlerTransform_cmul_X`, `MeasureR.res`, `baseChange`, and the
   Kubota–Leopoldt `μ_a`) to mathlib, or to keep it project-local as scaffolding for
   the residue / L-function results? (If project-local → this theorem is correctly an
   in-file leaf and drops out of mathlib consideration entirely.)

2. **Right grain for the trunk.** If yes to (1): the mathlib-worthy statement is the
   **general** intertwining `MeasureR.mahlerTransform_cmul_X` (= RJW Lemma 3.29,
   `A_{xμ}=∂A_μ`), together with `MeasureR.apply_powCM` (= RJW Cor 3.30,
   `x^k μ = ∂^k A_μ(0)`) and the `mahlerTransform`/`mahlerK` definitions — **not**
   this `ρ_a` application. Should the next `/mathlibable` runs target those general
   lemmas (and the Amice-transform def itself)? (This theorem then becomes a one-line
   downstream application: `mahlerTransform_cmul_X` + the units-restriction identity.)

3. **Coefficient generality.** The general intertwining is proved over
   `R = integerRing K` with `omit [CompleteSpace K]` — i.e. it holds over an arbitrary
   complete nonarchimedean `ℚ_p`-field. For an eventual mathlib statement, is the
   intended generality "arbitrary complete nonarchimedean `ℚ_p`-algebra" (the
   `MeasureR` layer) or the `ℤ_p`-only `PadicMeasure` layer, or both linked by
   `baseChange`? (Mathlib would want the most general — the `MeasureR` layer.)

4. **Named operator `∂`.** Would an upstreamed framework want the operator kept as the
   unfolded `(1+T)·derivativeFun`, or repackaged behind a *named* derivation
   `∂ = (1+T)d/dT` (RJW's `∂`, the project's `MeasureR.del`) so the API reads
   `A_{xμ} = ∂A_μ`? (A named `∂` is a small but real piece of reusable formal-NT
   infrastructure — and would make this leaf, and its siblings `one_add_mul_derivative_FtildeA`,
   read more cleanly.)

5. **Inline the leaf.** Independent of (1)–(4): this theorem has exactly one consumer
   (`ResidueZeta.lean:934`) and a short proof. Keep it as a named in-file lemma
   (current state — fine for a dev branch), or inline the `have hbase … ; rw […]`
   composition at that one call site? Also acceptable, if kept, to `omit` the unused
   `[IsUltrametricDist K] [CompleteSpace K]` instances (as neighbouring lemmas already
   do)? (No mathlib bearing either way; purely project hygiene.)

**Next action:** the maintainer answers (1)–(3) to fix the upstreaming policy; the
practical conclusion for **`one_add_mul_derivative_mahlerK_rhoA` specifically is "do
not upstream this application"** under any answer — it is a leaf application of the
general intertwining. If the framework *is* slated for mathlib, re-run `/mathlibable`
on `MeasureR.mahlerTransform_cmul_X` (RJW Lemma 3.29), `MeasureR.apply_powCM`
(RJW Cor 3.30), and the `MeasureR.mahlerTransform` / `mahlerK` definitions (the
trunk) — those are the genuine candidates. Proposed home for the framework if so:
`Mathlib/NumberTheory/Padics/LFunction/...` (a directory that does not yet exist —
itself confirming the whole area is the real gap).

---

## Next step

Maintainer answers questions 1–3 to set the p-adic-measure / Amice-transform
upstreaming policy. Regardless of the answer, `one_add_mul_derivative_mahlerK_rhoA`
itself stays project-local (a one-step, single-consumer application of the general
`A_{xμ}=∂A_μ` intertwining to the bespoke measure `ρ_a`); it is not upstreamed in
isolation. If the framework is destined for mathlib, the real `/mathlibable` targets
are the *general* lemmas `MeasureR.mahlerTransform_cmul_X` (RJW Lemma 3.29) and
`MeasureR.apply_powCM` (RJW Cor 3.30) and the Amice-transform definition — not this
application. Optionally (question 5), inline the proof at its single call site
(`ResidueZeta.lean:934`) and/or `omit` the unused analytic instances.
