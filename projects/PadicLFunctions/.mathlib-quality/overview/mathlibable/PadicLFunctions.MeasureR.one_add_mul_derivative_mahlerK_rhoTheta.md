# `/mathlibable` report — `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta`

**Final verdict: `BORDERLINE-needs-human`** (full reasoning in Phase 7).

This is the **Dirichlet-character-twisted** sibling of
`PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA`: a single-use leaf
*application* of RJW's **general** Amice/Mahler-transform intertwining
`A_{xμ} = ∂A_μ` (arXiv:2309.15692 v2, **Lemma 3.29**, `∂ = (1+T)d/dT`) to one
bespoke measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` (RJW's **Definition 5.13 `ζ_η`**,
the §6.2 object). It is true, non-trivial, and absent from mathlib — but its
mathlib-worthiness is entirely contingent on whether the surrounding
p-adic-measure / Amice-transform / Kubota–Leopoldt apparatus (all
project-defined, none in mathlib) is upstreamed, and on naming/generality calls
for the project objects `mahlerK`, `rhoTheta`, `MeasureR.res`, `twist`,
`muEtaCleared`, `del` (the operator `∂`). Those are human judgment calls the
search cannot settle. Numbered questions in Phase 7. (This conclusion matches
the established sibling verdict for `one_add_mul_derivative_mahlerK_rhoA`.)

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow here; Phase 0 fallback used, reading the declaration and its dependencies directly).
- decl `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:335`.
- kind:                      `theorem`
- has sorry:                 **no** (target body sorry-free; `ValuesAtOne.lean` total `sorry`/`admit` count = 0; the dependencies `rhoTheta`, `mahlerK`, `del`, `mahlerTransform_cmul_X`, `map_one_add_mul_derivativeFun` are all sorry-free).
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — Leopoldt's formula `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_c θ⁻¹(c)·log_p(1−ε_N^c)` via the distribution-free antiderivative route, for `θ = χη` non-trivial.

The declaration head (with the active ambient context):

```lean
omit [CharZero K] in
/-- P6-p5 (continued): `∂𝓐(ρ_θ) = (1−φψ)F_θ` over `K` — multiplication by
`x` recovers `Res_{ℤ_p^×}(μ_θ)` and `Res = 1 − φ∘ψ`
(Lem 6.3's second half in the formal route; the right-hand side is `p3`'s
explicit series). -/
theorem one_add_mul_derivative_mahlerK_rhoTheta {D : ℕ} [NeZero D]
    (_hD1 : 1 < D) {η : DirichletCharacter (integerRing K) D}
    (_hη : η.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    (1 + PowerSeries.X) * PowerSeries.derivativeFun
        (mahlerK p K (rhoTheta p K η hζ hD χ))
      = mahlerK p K (res p K (PadicMeasure.isClopen_units p)
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))) := by …
```

Ambient context (`namespace PadicLFunctions; namespace MeasureR`, `ValuesAtOne.lean:35–41`):
`variable (p : ℕ) [hp : Fact p.Prime]` and
`variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
— with `[CharZero K]` `omit`-ted for this theorem (the proof is a purely
algebraic/formal-power-series identity; the analytic instances are inherited
from the section, not used here).

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta` is **a
theorem** stating the following.

> Let `p` be prime and `K` a complete ultrametric normed field that is a
> `ℚ_p`-algebra, with ring of integers `R = integerRing K`. Let `η` be a
> *primitive* Dirichlet character of tame conductor `D > 1` prime to `p`, valued
> in `R`, and let `χ` be a Dirichlet character of conductor `pⁿ` valued in `R`;
> let `ζ` be a primitive `D`-th root of unity in `R`. Form the genuine measure
> `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` on `ℤ_p` (the χ-twisted, η-cleared object
> `rhoTheta`; RJW's `ζ_η = x⁻¹ Res_{ℤ_p^×}(...)`, Definition 5.13). Then applying
> the operator `∂ := (1+T) d/dT` to the `K`-Mahler/Amice transform `𝓐(ρ_θ) ∈ K⟦T⟧`
> recovers the Mahler transform of the units-restriction of the χ-twisted measure:
>
>   `∂ 𝓐(ρ_θ)  =  𝓐( Res_{ℤ_p^×}( twist_χ μ̃_η ) ).`
>
> Mathematically this is the instance `∂𝓐(ρ_θ) = 𝓐(x·ρ_θ)` of the general
> intertwining `A_{xμ} = ∂A_μ` (RJW Lemma 3.29), specialised to `ρ_θ`: multiplying
> `ρ_θ` by `x` cancels the `x⁻¹` inside `ρ_θ` and exposes `Res_{ℤ_p^×}(μ_θ)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` — a complete ultrametric `ℚ_p`-field (eventually `ℂ_p ⊇ ℚ_p(μ_p)`). `[CharZero K]` is in the section but `omit`-ted here (unused).
- `D : ℕ`, `[NeZero D]` — the tame conductor; `η : DirichletCharacter (integerRing K) D`.
- `ζ : integerRing K`, `hζ : IsPrimitiveRoot ζ D`; `hD : ¬ (p:ℕ) ∣ D` — tame data, prime to `p`.
- `n : ℕ`, `χ : DirichletCharacter (integerRing K) (p ^ n)` — the wild (`p`-power) character.

Hypotheses (Lean side):
- `_hD1 : 1 < D` — tame conductor `> 1` (named with a leading underscore: *not used in this proof*; carried for the downstream `L_p(θ,1)` assembly where the `D > 1` regime matters).
- `_hη : η.IsPrimitive` — `η` primitive (also leading-underscore: *unused in this proof*; needed by the consumer).
- `hζ`, `hD`, `χ` — used only to *name* `ρ_θ` (they are constructor arguments of `rhoTheta`, `muEtaCleared`, `twist`); the identity's content does not depend on them.

Conclusion (math): the multiplication-by-`x` ↔ `∂` bridge applied to `ρ_θ` (RJW §6.2, the χ-twisted/Dirichlet-character version of the "Lemma 6.3 pattern").

Conclusion (Lean): an equality of `PowerSeries K`:
`(1 + PowerSeries.X) * PowerSeries.derivativeFun (mahlerK p K (rhoTheta p K η hζ hD χ)) = mahlerK p K (res p K (PadicMeasure.isClopen_units p) (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)))`.

Underlying objects (all project-defined, in `PadicLFunctions/MeasureR/*`, `PadicLFunctions/Interpolation/*`, and `ValuesAtOne.lean`):
- `MeasureR K X := C(X, integerRing K) →ₗ[integerRing K] integerRing K` (`MeasureR/Basic.lean`) — an `R`-valued measure as an `R`-linear functional (RJW Def 3.6); an Iwasawa-algebra element in functional disguise.
- `mahlerK` (`MeasureR/FormalPsi.lean:749`) — the `K`-mapped Mahler/Amice transform `𝓐_μ ∈ K⟦T⟧`, `PowerSeries.map (integerRing K).subtype (MeasureR.mahlerTransform p K μ)`. `MeasureR.mahlerTransform` (`MeasureR/MahlerTransform.lean:67`) is RJW Def 3.15 over `R`: `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ`.
- `rhoTheta` (`ValuesAtOne.lean:290`) — the §6 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_θ)`, defined as `iota(twist χ̃ μ̃_η ∘ extendByZero ∘ mulLeft invU)`; the χ-twisted analogue of RJW's `ζ_η` (Def 5.13).
- `MeasureR.res` (`MeasureR/Toolbox.lean:133`) — restriction of a measure to a clopen by multiplication by its characteristic function (RJW §3.5.3); `PadicMeasure.isClopen_units p` is the clopen `ℤ_p^×`.
- `twist` (`Interpolation/Twist.lean:38`) — `g(x)·μ`, twist of a measure by `g ∈ C(ℤ_p, R)` (RJW §3.5.2); `χ.toContinuousMapZp` is the continuous lift of `χ`.
- `muEtaCleared` — the η-cleared base measure `μ̃_η` (the §5 clearing conventions; `Interpolation/LpFunction.lean` neighbourhood).
- `del` (`MeasureR/Toolbox.lean:50`) — the operator `∂ = (1+T)·derivativeFun` (RJW Lem 3.24/3.29); appears here unfolded as `(1 + PowerSeries.X) * PowerSeries.derivativeFun`.
- `PowerSeries.derivativeFun` (**mathlib**, `Mathlib/RingTheory/PowerSeries/Derivative.lean:44`) and `PowerSeries.map` (**mathlib**) — the only mathlib dependencies of the statement/proof.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step corollary (docstring tag "P6-p5 (continued)"), the units/`∂`-bridge for the *specific* twisted numerator measure `ρ_θ`. It is not a `def`/`class`/`structure`, not named after a person/place, and not a `## Main results` headline (the §6.2 headline is Leopoldt's `L_p(θ,1)` formula, RJW Thm 6.1(ii); this lemma is one bridge in its proof). Its proof is a short `have hmeas … ; rw [← hmeas]; simp; rw […]` chain (≈26 lines) that applies the *general* project lemmas (`mahlerTransform_cmul_X`, `map_one_add_mul_derivativeFun`) plus a measure-level `cmul`-identity to the concrete `ρ_θ`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for the report's framing.)

### One-line check (Phase 2b)

Body line count: ≈26 substantive lines (a `have hmeas : cmul(mahlerCM 1) ρ_θ = Res_×(twist …)` block proved by `LinearMap.ext` + `ContinuousMap.ext`, then a transport `rw [← hmeas]; simp only [mahlerK]; rw [mahlerTransform_cmul_X, …, map_one_add_mul_derivativeFun]`).
One-liner verdict: **n/a — kind is `theorem`**, not `def`/`abbrev`/`structure` (the def-one-liner exemption table does not apply to theorems). Noted for framing: the body is a genuine multi-step formal-calculus argument, reinforcing the "thin corollary of a general lemma" reading without being a one-liner.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Amice transform p-adic measure multiplication by x corresponds to (1+T) d/dT operator Mahler power series Iwasawa" | yes (general) | `A_μ(t) = ∫(1+t)^y dμ`; `A_{δ_a} = (1+T)^a`; measures `≅ ℤ_p[[T]]` (Iwasawa algebra) | de Shalit *Mahler bases and elementary p-adic analysis*; Γ-transform / Iwasawa-λ-invariant literature. The measure↔power-series dictionary is textbook; the exact `mult-by-x ↔ (1+T)d/dT` line is in the specialised source (row 11). |
|  2 | WebSearch (named source)         | "arXiv 2309.15692 p-adic L-functions Mahler transform Lemma 3.29 multiplication by x derivative power series A_{xμ}=∂A_μ" | yes | identifies the source: Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions* (arXiv:2309.15692 v2), §3.4 "p-adic analysis and Mahler transforms" | confirms the project formalises this exact paper; the relevant general lemma is §3.4. |
|  3 | WebSearch (Dirichlet-twist / residue / value form)| "p-adic L-function Dirichlet character twist measure restriction units residue Kubota-Leopoldt x inverse antiderivative power series" | yes | `L_p(s,χ)` interpolates `L(χ,1−k)`; for `η` of conductor prime to `p`, a measure on `ℤ_p` interpolates `L(χη,−k)`; trivial-character pole residue `1−p⁻¹` | arXiv:2309.15692; Cambridge EMS "Sum expressions for Kubota–Leopoldt p-adic L-functions" (arXiv:2201.08870); Williams Warwick/LTCC notes. Confirms the χη-twist + units-restriction value-computation framework is standard. |
|  4 | ChatGPT MCP                      | (intended: "standard form / generality / history of the `A_{xμ}=∂A_μ` intertwining and its `Res_×` application to a Dirichlet-twisted measure") | **n/a** | — | **ChatGPT/codex MCP server not installed in this environment** (ToolSearch surfaced only auth stubs for Asana/Atlassian/Box/Canva/Figma/…; no `mcp__chatgpt__*`/`mcp__openai__*`). Per the skill's documented fallback, compensated by the **verbatim primary source** (row 11, extracted by `pdftotext` myself) + 3 WebSearch queries at 3 generality levels + the nLab fetch. |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                  | **n/a** | (directories absent)             | No `.mathlib-quality/references/` dir (only `overview/` exists) and no `refs/` store on this checkout. The docstrings cite "RJW" with TeX line numbers; the source is arXiv:2309.15692, fetched directly in row 11. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/Iwasawa+algebra`                                                        | no  | only "completed group ring `ℤ_p[[Γ]] ≅ ℤ_p[[T]]`" | **stub** — defines the Iwasawa algebra only; the page has **no** measures, **no** Amice/Mahler transform, **no** `(1+T)d/dT` operator, **no** `x·μ`, **no** `Res_×`, **no** character-twist (confirmed verbatim by the fetch). |
|  7 | nCatLab (categorical)            | concept scan (`Amice transform` / `p-adic measure` as a categorical object)                            | **n/a** | —                                | Not a categorical concept — a concrete statement about one functional on `C(ℤ_p, R)` and its image power series. No higher-categorical formulation applies. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | **n/a** | —                                | Not an algebraic-geometry / scheme-theoretic concept — p-adic measures / Amice transform / Iwasawa theory are out of Stacks' scope. |
|  9 | MathOverflow / Math.StackExchange| (folded into #1, #3 — the analytic-NT queries surfaced MO/MSE-style sources)                           | partial | only the general Amice/Kubota–Leopoldt dictionary; no named "`∂𝓐(ρ_θ)=𝓐(Res_×μ_θ)`" result | the general intertwining + units-restriction value framework is well-covered; the specific `ρ_θ` instance is paper-internal bookkeeping (RJW §6.2). |
| 10 | recent arXiv (≤5 years)          | "p-adic L-function Lean formalization Iwasawa algebra measure Dirichlet character" (transitively, via #2/#3) | yes | arXiv:2309.15692 (2023/24); arXiv:2201.08870 (sum expressions); Narayanan arXiv:2302.14491 (Lean 3 p-adic L, bespoke measure layer, not upstreamed) | even formalised p-adic-L work keeps a *bespoke* measure layer; no mathlib measure-on-`ℤ_p` exists. |
| 11 | **Primary source (RJW PDF)**     | `pdftotext` of arXiv:2309.15692 v2: §3.4 (Lemma 3.29 / Cor 3.30, lines ~1490–1535), §3.5.3/3.5.4 (Res, lines ~1558–1759), §5.2 Def 5.13 (`ζ_η`, line 3208), §6 (Thm 6.1(ii) / §6.2, lines 3202–3623) | **yes** | **verbatim** (see below) | the decisive evidence — exact match of the *general* lemma, the units-restriction operation, RJW's `ζ_η` object that `rhoTheta` formalises, and the §6.2 `L_p(θ,1)` setting. |

The protocol passed: WebSearch ran **3** distinct queries spanning the specific
form (`A_{xμ}=∂A_μ`), the named source (arXiv:2309.15692), and the
Dirichlet-twist / units-restriction / residue value framework; local refs,
nLab, nCatLab, Stacks, MathOverflow, and recent arXiv were each checked or
recorded `n/a` with reason; the **primary source was extracted verbatim by
`pdftotext`** (the authoritative compensation for the genuinely-unavailable
ChatGPT MCP, whose role — pinning the standard form, generality, and history —
is fully discharged by RJW §3.4/§5.2/§6 plus the 3 web queries + nLab fetch).

**Verbatim from the source** (`pdftotext` of arXiv:2309.15692 v2; line numbers from the extraction):

> *(§3.4, lines 1490–1495)*
> "We can ask what the operation `µ ↦ xµ` does on Mahler transforms; we find:
> **Lemma 3.29.** — We have `A_{xµ} = ∂A_µ`, where `∂` denotes the differential
> operator `(1 + T) d/dT`."

> *(§3.4, lines 1522–1527)*
> "**Corollary 3.30.** — For `µ ∈ Λ(Z_p)`, we have `∫_{Z_p} x^k · µ = ∂^k A_µ(0)`."

> *(§3.5.4, line 1618)*  "`A_{Res_{Z_p^×}(µ)}(T) = A_µ(T) − …`" (the units-restriction on the transform).

> *(§5.2, line 3208 — the object `rhoTheta` formalises)*
> "**Definition 5.13.** — Define `ζ_η ..= x^{−1} Res_{Z_p^×}(…)`."
> *(line 3223)*  "`∫ χ(x) x^k · ζ_η = (1 − θ(p)p^{k−1}) L(θ, 1 − k)`."

> *(§6, Theorem 6.1(ii), line 3424; §6.2 header, line 3623)*
> "`L_p(θ, 1) = −(1 − θ(p)p^{−1}) …`"  /  "**6.2. The p-adic value at `s = 1`.** — We now compute …"
> *(Remark 6.2, line 3433)*  "Part (ii) of Theorem 6.1 is due to Leopoldt."

**Lean ↔ source match.** The Lean theorem is the formalised, rigorous version of
the **`k = 0` (`s = 1`) step** of RJW §6.2. The *engine* is the general
`A_{xµ} = ∂A_µ` (**Lemma 3.29**), which the project formalises as
`MeasureR.mahlerTransform_cmul_X` (`MeasureR/Toolbox.lean:74`, docstring "RJW
Lem 3.24, TeX 1066–1075" — the project's TeX-draft numbering of the same lemma
arXiv v2 numbers **3.29**). The operator `∂ = (1+T)d/dT` is the project's
`MeasureR.del` (`Toolbox.lean:50`), here written unfolded as
`(1+X)*derivativeFun`. The measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` is the
χ-twisted/η-cleared formalisation of RJW's **`ζ_η`** (Def 5.13); multiplying it
back by `x` cancels the `x⁻¹` (the `invUnitsCM` factor inside `rhoTheta`) and
lands on `Res_{ℤ_p^×}(twist_χ μ̃_η)`, exactly RJW's `A_{Res_×(x·ζ_η)} =
A_{Res_×(μ_θ)}` shape. So this theorem is **strictly more specific** than
Lemma 3.29: it fixes `µ = ρ_θ`. (It is the §6.2/`s=1` twin of the §7 residue
sibling `one_add_mul_derivative_mahlerK_rhoA`, which fixes `µ = ρ_a`.)

### Literature summary (Phase 3)

Concept identified as: the **Amice/Mahler-transform intertwining** "multiplication
by `x` on a measure ↔ the operator `∂ = (1+T)d/dT` on its transform"
(RJW **Lemma 3.29** / **Cor 3.30**, `∫ x^k dμ = ∂^k A_μ(0)`), and specifically
its **units-restriction application** to the Dirichlet-twisted measure
`ζ_η = x⁻¹ Res_{ℤ_p^×}(…)` (RJW Def 5.13) in the `s = 1` value computation (§6.2,
Thm 6.1(ii), Leopoldt's `L_p(θ,1)` formula). The target
`one_add_mul_derivative_mahlerK_rhoTheta` is the *application* of the general
intertwining to the single twisted measure `ρ_θ`, packaged so the
`L_p(θ,1)` value can be read off.

Sources agree on the standard form: **yes**. The intertwining `A_{xµ}=∂A_µ` with
`∂ = (1+T)d/dT` (equivalently `t d/dt` under `t = 1+T`) is uniform across de Shalit
*Mahler bases*, Colmez, Amice's original work, and the Γ-transform / Iwasawa-λ
literature; the measure↔`ℤ_p[[T]]` correspondence, the restriction-to-`ℤ_p^×`, and
the χη-twist value-interpolation are textbook (Washington Ch. 12, Lang *Cyclotomic
Fields*, the Williams/LTCC notes).

Most general standard form: the **general** theorem `A_{xµ} = ∂A_µ` (and
`x^k µ = ∂^k A_µ(0)`) for an *arbitrary* measure `µ` — a structural fact about
the Amice transform with no reference to `ζ_η`, `μ_θ`, or `ρ_θ`. The literature
states this once (Lemma 3.29 / Cor 3.30) and then derives unit-restriction value
formulas (Def 5.13 + the special-value identities) as applications; it does
**not** name an "`∂𝓐(ρ_θ)=𝓐(Res_×μ_θ)`"-shaped result.

Generality dimensions where the literature varies:
  - **Coefficient ring:** `ℤ_p`/`ℂ_p`/`O_L` (classical / RJW) → any complete
    nonarchimedean `ℚ_p`-algebra `R = integerRing K` (the project's `MeasureR`
    layer). The project already takes the more general `R`.
  - **The object the intertwining is applied to:** the literature states the
    *general* `A_{xµ}=∂A_µ`, then derives unit-restriction value formulas (for
    `ζ_η`) as corollaries — it does not single out an `∂𝓐(ρ_θ)` named result.

Disagreement with the literature: **none on content**. The mismatch is one of
*granularity*: this theorem is a specialisation of the general
(literature-standard) intertwining `A_{xµ}=∂A_µ` to one bespoke measure `ρ_θ`,
which the literature treats as an immediate application (via `ζ_η`) rather than a
named result. The literature search returned **not nothing** — it returned the
**general** lemma (Lemma 3.29) and the **general** units-restriction
value-computation framework (Def 5.13, §6.2) — but not a
`one_add_mul_derivative_mahlerK_rhoTheta`-shaped statement. That is the central
tension for the verdict.

---

### Generality analysis — `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta` (Phase 4)

Literature-standard form (from Phase 3): the structural intertwining
`A_{xµ} = ∂A_µ` (with `∂ = (1+T)d/dT`) for an *arbitrary* measure `µ` over an
arbitrary complete nonarchimedean coefficient ring — the project's
`MeasureR.mahlerTransform_cmul_X` (`MeasureR/Toolbox.lean:74`, = RJW Lemma 3.29).

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | the measure `rhoTheta p K η hζ hD χ`  | one *specific* measure `iota(twist χ̃ μ̃_η ∘ extendByZero ∘ mulLeft invU)` | an *arbitrary* measure `µ` | **yes** | The identity `∂𝓐(µ) = 𝓐(xµ)` holds for *every* `µ`; this theorem fixes `µ = ρ_θ` and additionally identifies `x·ρ_θ = Res_{ℤ_p^×}(twist_χ μ̃_η)` (the local `have hmeas`, a project computation). The genuinely-general statement is `mahlerTransform_cmul_X` (RJW Lemma 3.29), already in the project. |
| 2 | the RHS `Res_×(twist χ̃ μ̃_η)`         | units-restriction of one specific twisted measure | (no general analogue — this is `x·ρ_θ` for this `ρ_θ`) | n/a | The RHS is not an independent parameter; it is `x·ρ_θ` computed for this `ρ_θ`. Generalising the measure (row 1) subsumes it. |
| 3 | `[NormedAlgebra ℚ_[p] K]`, `[IsUltrametricDist K]`, `[CompleteSpace K]`, `[CharZero K]` | complete ultrametric `ℚ_p`-field | nonarch. field with integer ring | borderline (already general; some instances unused) | The general lemma `mahlerTransform_cmul_X` is proved with `omit [CompleteSpace K]`; this theorem `omit`s `[CharZero K]` and does not use the analytic instances. The *abstract* fact is more general than this section's typeclasses — but that generality already lives in the general lemma. (A `/cleanup`-grade `omit` of unused instances would tidy this leaf; not a generality flip.) |
| 4 | `_hD1 : 1 < D`, `_hη : η.IsPrimitive` | tame conductor `> 1` + primitive | (downstream constraints) | **yes — both are unused dead weight for *this* identity** | The leading underscores in the source mark them: neither `1 < D` nor `η.IsPrimitive` is used in the proof of *this* equation. They are carried because the *consumer* (`L_p(θ,1)`) needs them. The identity itself holds without them — narrower-than-needed *hypotheses*, but the genuine narrowness is fixing the whole measure to `ρ_θ`. |
| 5 | `hζ`, `hD`, `χ`                       | tame root + `p∤D` + wild char | the construction parameters  | NO (intrinsic) | Used only to *name* `ρ_θ`/`muEtaCleared`/`twist`; the narrowness is not in these data — it is in fixing the *whole measure* to be `ρ_θ`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in a *degenerate*
way (identical in kind to the sibling `one_add_mul_derivative_mahlerK_rhoA` and to
`psi_rhoTheta`). The narrowing is not "a hypothesis to weaken by one typeclass";
it is that the statement is an *instance* (the measure is the fixed concrete object
`ρ_θ`, and the RHS is its `x`-multiplication) of a *general structural theorem the
project already proves separately* — `MeasureR.mahlerTransform_cmul_X` (= RJW
Lemma 3.29). The "more general form" is **not** a re-typeclassed
`one_add_mul_derivative_mahlerK_rhoTheta`; it is the already-existing general lemma
`A_{xµ}=∂A_µ`, of which this theorem is a short application (combined with the local
`hmeas` that computes `x·ρ_θ = Res_×(twist χ̃ μ̃_η)`).

Number of weakening opportunities found: **1 substantive** — generalise the *object*
`ρ_θ` to "an arbitrary measure `µ`", which is precisely the content of the
already-present `mahlerTransform_cmul_X` (i.e. there is nothing new to prove; the
general result already exists in the project). Plus 2 cosmetic (drop the unused
`_hD1`/`_hη`; `omit` the unused analytic instances on this leaf).

Proposed restatement: not applicable as a *new* statement — the maximally-general
form is the **already-present** `MeasureR.mahlerTransform_cmul_X`
(`MeasureR/Toolbox.lean:74`), together with the measure-level identity
`x·ρ_θ = Res_×(twist χ̃ μ̃_η)` (the local `hmeas`) and the `map`-commutation helper
`map_one_add_mul_derivativeFun` (`ValuesAtOne.lean:324`). This theorem adds no
generality over those.

Cost of restatement: CHEAP (the proof is already the short application body) — but
this does not produce a *new* mathlib-worthy statement; it points back at the
general lemma. (Per the skill's Bourbaki-2.0 rule, cost is **not** a verdict factor.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | The hypotheses are already typeclasses (`NormedAlgebra`, `IsUltrametricDist`, …) plus character/root *data*; nothing bundled to unbundle (the unused `_hD1`/`_hη` are a hygiene issue, not a bundling one). | — |
|  2 | sequences/metric → filters/topological? | no | No limit/convergence content; this is a *formal* (algebraic) power-series identity. `∂` and `derivativeFun` are purely algebraic. | — |
|  3 | construct an object → universal-property class? | partial (already done by the project) | The "mult-by-x ↔ ∂" intertwining is the structural characterisation; the project already has it as the general `mahlerTransform_cmul_X`. This theorem is a *consumer* of that characterisation, not a place to introduce a new one. | the project already gets the intertwining; this lemma just applies it to `ρ_θ`. |
|  4 | set-with-closure-predicate → bundled substructure? | no | `MeasureR.res`/`IsSupportedOn` are already the project's restriction API; no lattice-of-supports is in play for this corollary. | — |
|  5 | vector-space/field-specific → weaken typeclasses? | no (already general in `R`) | The `MeasureR` layer is already the `R`-coefficient generalisation of the `ℤ_p`-only `PadicMeasure` layer; `mahlerK`/`del` are stated over `integerRing K`. | — |
|  6 | 1-categorical → higher-categorical? | no | Not a categorical statement (concrete formal-power-series / functional-analytic identity). | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no | `D`, `pⁿ`, `n` are intrinsic to the Dirichlet-character setup; not indices to abstract. The intertwining is already uniform and `∂` is fixed/standard. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this theorem itself). One-line reason: the
modern, structural form of this mathematics — "multiplication by `x` on a measure ↔
`∂ = (1+T)d/dT` on its Amice transform" — already exists in the project as the
*general* `MeasureR.mahlerTransform_cmul_X` (using mathlib's contemporary
`PowerSeries.derivativeFun` / `PowerSeries.map` idiom); this theorem is a downstream
*application* of it to `ρ_θ`, not a candidate modernisation in its own right.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; skipped per the skill's scope rule.

---

### Mathlib search-status: `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta` (Phase 5)

Five-method search (`references/mathlib-search.md` read). The mathlib source tree is
present at `.lake/packages/mathlib/Mathlib`, so methods [D]/[E] were run directly
against source — the authoritative signal for "does the decl/infrastructure exist".

```
[A] Lean-Finder       (web service; not reachable from this sandboxed worker)        — n/a: relied on the local mathlib grep [D]/[E], authoritative for existence.
[B] Loogle            type-pattern `(1 + PowerSeries.X) * PowerSeries.derivativeFun _ = _`; `_ →ₗ[_] _` ("measure as functional") → transform — n/a (no network from worker); [D]/[E] cover existence directly.
[C] LeanSearch        NL: "(1+T) times derivative of Amice transform equals transform of units-restricted twisted p-adic measure"; "multiplication by x on p-adic measure ↔ (1+T)d/dT" — n/a (no network); [D]/[E] cover it.
[D] Grep mathlib src  `Amice`, `mahlerTransform`, `MeasureR`, `PadicMeasure`, `(1 + X).*derivativeFun` / `derivativeFun.*(1 + X)`, `Kubota`/`Leopoldt`/`padicLFunction`/`p-adic L-function` — **no relevant hits**.
[E] Name pattern      grep `rhoTheta`, `mahlerK`, `one_add_mul_derivative`, `mahlerTransform_cmul`, `muEtaCleared`, `twist` (as a measure op), `del` (the `∂` operator) across `Mathlib/` — **no hits**.
```

What the grep found, and why each is irrelevant:
- `Mathlib/RingTheory/PowerSeries/Derivative.lean:44` — the **generic**
  `PowerSeries.derivativeFun` / `coeff_derivativeFun` API the proof *consumes*; no
  `(1+X)·∂` operator, no Amice transform, no measures.
- `Mathlib/NumberTheory/BernoulliPolynomials.lean` (`.comp (1 + X)`) and
  `Mathlib/RingTheory/PowerSeries/Binomial.lean` (`binomialSeries`, `(1 + X) ^ r`) —
  the only `(1 + X)`-on-power-series hits; **composition with `1+X`** and the
  **binomial series**, *not* the operator `(1+T)·d/dT`. Unrelated.
- `Kubota`/`Leopoldt`/`padicLFunction`/`p-adic L-function` — **zero hits** in mathlib.
- No `PadicMeasure`, no `MeasureR`, no `Amice`, no `mahlerTransform` — **zero hits**:
  mathlib has no p-adic-measure type as a `C(X,R) →ₗ R` functional and no Amice/Mahler
  transform of measures. (Mathlib's p-adic analysis stops at `PadicInt`, the Mahler
  *basis* of `C(ℤ_p, ℚ_p)`, p-adic add-characters, and `ℂ_p`.)

Searched for both:
  - the user's current form (`∂𝓐(ρ_θ) = 𝓐(Res_×(twist χ̃ μ̃_η))`): **absent** —
    `rhoTheta`, `mahlerK`, `muEtaCleared`, `twist`, and the entire Kubota–Leopoldt /
    Dirichlet-L apparatus are not in mathlib.
  - the literature-standard general form (`A_{xµ} = ∂A_µ`, the Amice intertwining for
    arbitrary `µ`): **also absent** — mathlib has *neither* an Amice/Mahler transform
    of measures, *nor* the `(1+T)d/dT` operator on it, *nor* `MeasureR`/`PadicMeasure`,
    *nor* a notion of a measure "restricted to a clopen" in this functional-analytic
    sense, *nor* a "twist of a measure by a character".

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
general form). Mathlib does **not** even contain the *building blocks* (`MeasureR`,
the transform `mahlerK`/`mahlerTransform`, the operator `del`, `MeasureR.res`,
`twist`, `muEtaCleared`, `rhoTheta`) from which this identity could be composed —
every ingredient is project-defined. The only mathlib decls the proof uses are the
**generic** `PowerSeries.derivativeFun` and `PowerSeries.map`. (Cross-check: the
formalised p-adic-L work that exists — Narayanan, Lean 3, arXiv:2302.14491 — is a
separate, non-upstreamed project with its own measure layer. `NO-mathlib-has-it` is
therefore impossible: mathlib has neither the statement nor any general form of it.)

---

### Call sites — `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta` (Phase 6.0)

Internal use count: **K = 1** (within the project; one use, and it is in the
*declaring file* `ValuesAtOne.lean`).
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                            |
|--------------------------------|------------------------------------------------------------------------------|
| `…/ValuesAtOne.lean:822`       | `rw [one_add_mul_derivative_mahlerK_rhoTheta hD1 hη hζ hD χ, res_units_eq, mahlerK_sub, mahlerK_phi]` |

That single site is inside a `have hAder : (1+X)·∂(𝓐_ρ) = mahlerK(twist …) − φ B`
block (`ValuesAtOne.lean:819–824`) within the `L_p(θ,1)`-value assembly: it supplies
the bridge `(1+X)·∂(𝓐_ρ) = mahlerK(twist χ̃ μ̃_η) − φ ψ(…)` (using `Res_× = 1 − φψ`,
RJW Eq 3.10 / `res_units_eq`), which combines with the `W`-equation
(`hWder`, the antiderivative identity `one_add_mul_derivative_Ftilde`) to pin the
constant and compute Leopoldt's `L_p(θ,1)`. It is one rewrite step in the larger §6.2
argument — exactly the §6.2/`s=1` analogue of how the §7 sibling
`one_add_mul_derivative_mahlerK_rhoA` is used at `ResidueZeta.lean:934`.

Inline-derivation grep (was `∂𝓐(ρ_θ) = 𝓐(Res_×(twist χ̃ μ̃_η))` re-derived elsewhere
without this lemma?): **(none)** — no other proof re-derives it inline; the one
consumer uses the lemma. (The sibling `one_add_mul_derivative_mahlerK_rhoA` proves the
*analogous* identity for the *different* measure `ρ_a` — i.e. the same pattern is
written once per measure, confirming this is a per-measure application of the general
intertwining, not a reusable API.)

What the pattern tells us (per the Phase-6.0 signal table): **K = 1, in-file only, no
external callers, no inline re-derivation.** This is the "possibly the wrong
abstraction / could be inlined" pattern — *but* the proof depends on the general
`mahlerTransform_cmul_X` plus the local measure-level `hmeas` and the `map`-commutation
helper, so it is a genuine, non-trivial helper, not dead code or a bypassed wrapper.
Its audience is, today, a single proof in a single paper-formalisation.

### Composition check (Phase 6)

The relevant composition question for `/mathlibable` is "can **mathlib's** primitives
compose to give this in ≤3 calls?" — and the answer is decisively **no**, because
mathlib has none of the primitives (`MeasureR`, the Amice transform, the `∂` operator
`del`, `MeasureR.res`, `twist`, `muEtaCleared`, `rhoTheta`). So there is no mathlib
composition to inline.

For completeness, the *project-internal* composition (essentially the proof body) is:

Attempt 1: `have hmeas : cmul(mahlerCM 1) ρ_θ = Res_×(twist χ̃ μ̃_η)` (proved by
`LinearMap.ext` + unfolding `rhoTheta`/`iota`/`pushforward` and the unit-cancellation
`invCM u · u = 1`); then `rw [← hmeas]; simp only [mahlerK]; rw [mahlerTransform_cmul_X,
(show del K (mahlerTransform p K ρ_θ) = (1+X)·derivativeFun (mahlerTransform p K ρ_θ)
from rfl), map_one_add_mul_derivativeFun]`.
  - Project decls used: `MeasureR.mahlerTransform_cmul_X` (RJW Lemma 3.29), the private
    `map_one_add_mul_derivativeFun`, and the local `hmeas` (≈18 lines: `cmul_apply`,
    `rhoTheta`/`iota`/`pushforward_apply`, `extendByZero_comp_unitsVal`,
    `invUnitsCM`/`mahlerCM`/`unitsValCM` simp, `inv_mul_cancel`).
  - Mathlib decls used: only the generic `PowerSeries.derivativeFun` / `PowerSeries.map`.
  - Result: succeeds (the ≈26-line proof in the source).
  - Notes: this is an application of *project* lemmas — the shape `/mathlibable` flags
    as NO-composable *when the building blocks are in mathlib*. Here they are in the
    **project**, not mathlib — so the corollary is composable-from-the-project, and the
    mathlib-worthiness question shifts entirely onto whether the *general framework*
    (the Amice transform + the `A_{xµ}=∂A_µ` intertwining), not this leaf, is upstreamed.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks every primitive).
Composable from *project* lemmas — the decisive observation for the verdict.

---

## Verdict: `PadicLFunctions.MeasureR.one_add_mul_derivative_mahlerK_rhoTheta`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Literature search (Phase 3):** the multiplication-by-`x` ↔ `∂ = (1+T)d/dT`
  intertwining of the Amice/Mahler transform is firmly classical (de Shalit, Colmez,
  Amice, Iwasawa) and is **RJW Lemma 3.29** (`A_{xµ}=∂A_µ`) / **Cor 3.30**
  (`x^k µ = ∂^k A_µ(0)`) — matched **verbatim** against the primary source
  (arXiv:2309.15692 v2 §3.4, extracted by `pdftotext`). The measure this theorem fixes,
  `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)`, is RJW's **`ζ_η`** (Def 5.13, line 3208), and the
  setting is §6.2 / Thm 6.1(ii), Leopoldt's `L_p(θ,1)`. But the literature states the
  **general** intertwining and derives value formulas as applications; it gives **no**
  named "`∂𝓐(ρ_θ)=𝓐(Res_×μ_θ)`" result.
- **Generality analysis (Phase 4):** **STRICTLY NARROWER THAN STANDARD**, degenerately
  — this is an *instance* (fixed concrete measure `ρ_θ`, RHS = `x·ρ_θ`) of the
  project's own general theorem `MeasureR.mahlerTransform_cmul_X` (= RJW Lemma 3.29).
  Two unused hypotheses (`_hD1`, `_hη`) confirm the leaf is shaped for its consumer, not
  for generality. Phase 4c found no modern-idiom improvement *for the corollary itself*;
  the structural form already exists as the general lemma.
- **Mathlib search (Phase 5):** **not in mathlib, and not composable from mathlib** —
  mathlib has *no* Amice/Mahler transform of measures, *no* `(1+T)d/dT` operator on it,
  *no* `MeasureR`/`PadicMeasure`/`mahlerK`/`del`/`res`/`twist`/`muEtaCleared`/`rhoTheta`,
  *no* Kubota–Leopoldt p-adic L-function. Every ingredient is project-defined; the sole
  mathlib dependency is the generic `PowerSeries.derivativeFun`/`map`. The `(1+X)` hits
  (`BernoulliPolynomials`, `binomialSeries`) are unrelated.
- **Composition check (Phase 6):** **NOT-COMPOSABLE from mathlib**; composable from
  *project* lemmas (`mahlerTransform_cmul_X` + a local measure-level `hmeas` + a
  `map`-commutation helper). Call sites: **K = 1**, in the declaring file only, no
  external consumers, no inline re-derivations.

**Rationale (synthesis).**

This declaration sits at exactly the same intersection as its established sibling
`one_add_mul_derivative_mahlerK_rhoA` (verdict on record: `BORDERLINE-needs-human`)
and the related `psi_rhoTheta` — it is the **Dirichlet-character-twisted, `s = 1`**
twin of the `rhoA` residue lemma. It is BORDERLINE for the same structural reason: not
because the worker is unsure, but because the genuine question is one the search
*cannot* settle from evidence alone.

On one hand, `one_add_mul_derivative_mahlerK_rhoTheta` is *not itself* a clean mathlib
candidate: it is a `SMALL`, ≈26-line application that specialises a *general*
structural theorem (`mahlerTransform_cmul_X`, RJW Lemma 3.29, `A_{xµ}=∂A_µ`) to one
bespoke twisted measure `ρ_θ` (= RJW's `ζ_η`), has a single in-file consumer, carries
two unused hypotheses, and is strictly narrower than the literature-standard form (the
general intertwining for arbitrary `µ`). By every local signal — granularity,
call-site count, two dead hypotheses, "application of a general lemma" shape — it is the
kind of thing that, *if the general framework were in mathlib*, would be
NO-composable-from-mathlib (apply the general lemma plus the measure-level identity at
the one call site).

On the other hand, the standard NO buckets are unavailable on their own terms, and that
is decisive. **`NO-mathlib-has-it` fails the verdict gate:** Phase 5's conclusion is
"not in mathlib", not "found in mathlib as X" — there is no mathlib decl to cite,
because mathlib has neither this identity, nor the general `A_{xµ}=∂A_µ`, nor any of the
objects it mentions. **`NO-composable-from-mathlib` also fails its gate:** Phase 6
concluded NOT-COMPOSABLE *from mathlib* (mathlib lacks the Amice transform, the `∂`
operator, `MeasureR`, `res`, `twist` entirely), so there is no ≤3-line *mathlib*
composition to inline; the composition that exists is from *project* lemmas, which is
not what that bucket means. And **`YES-*` is wrong** too: this specific application is
strictly narrower than the literature standard (so not `YES-add-as-is`), yet the "more
general form" is not a re-typeclassed `one_add_mul_derivative_mahlerK_rhoTheta` to hand
to `/generalise` — it is the project's *already-existing* general lemma
`mahlerTransform_cmul_X`, so there is no new statement to propose (so not
`YES-but-generalise-first` in the usual sense either).

The genuine question is therefore one the skill cannot resolve from evidence alone:
**the entire surrounding framework — `PadicMeasure` / `MeasureR`, the Amice/Mahler
transform `mahlerTransform`/`mahlerK`, the operator `∂ = (1+T)d/dT` (`del`), the
intertwining `A_{xµ}=∂A_µ` (RJW Lemma 3.29), `MeasureR.res`, `twist`, and the
Kubota–Leopoldt / Dirichlet-L apparatus (`muEtaCleared`, `rhoTheta` = `ζ_η`) — is
absent from mathlib, and whether any of it (and at what grain) should be upstreamed is
a large project-policy and mathematical-taste call.** This theorem itself is a leaf
application that should never be upstreamed in isolation; but it is a leaf of a tree
whose *trunk* — the general `mahlerTransform_cmul_X` intertwining and the
`MeasureR`/Amice-transform infrastructure beneath it — is exactly the sort of
foundational p-adic-measure theory mathlib currently lacks and might want. That is a
decision for the maintainer, not the search. (Cost is **not** a factor in this verdict;
per the skill's Bourbaki-2.0 rule, an expensive upstreaming of the framework would be
worth doing — the open question is *policy and grain*, not effort.)

**Refactor-actionable detail / numbered questions (≤5):**

1. **Framework scope.** Is the AINTLIB plan to eventually upstream the
   p-adic-measure / Amice-transform infrastructure (`MeasureR`, the Mahler/Amice
   transform `mahlerTransform`/`mahlerK`, the operator `∂ = (1+T)d/dT` = `del`, the
   intertwining `mahlerTransform_cmul_X`, `MeasureR.res`, `twist`, and the
   Kubota–Leopoldt/Dirichlet-L measures `muEtaCleared`/`rhoTheta`) to mathlib, or to
   keep it project-local as scaffolding for the `L_p(θ,1)` / residue results? (If
   project-local → this theorem is correctly an in-file leaf and drops out of mathlib
   consideration entirely.)

2. **Right grain for the trunk.** If yes to (1): the mathlib-worthy statement is the
   **general** intertwining `MeasureR.mahlerTransform_cmul_X` (= RJW Lemma 3.29,
   `A_{xµ}=∂A_µ`), together with `MeasureR.apply_powCM` (= RJW Cor 3.30,
   `x^k µ = ∂^k A_µ(0)`) and the `mahlerTransform`/`mahlerK` definitions — **not** this
   `ρ_θ` application. Should the next `/mathlibable` runs target those general lemmas
   (and the Amice-transform def itself)? (This theorem then becomes a one-line
   downstream application: `mahlerTransform_cmul_X` + the measure-level identity + the
   units-restriction `res_units_eq`.) Note: the trunk lemmas do **not** yet have their
   own mathlibable reports — only the `ρ_a`/`ρ_θ` *applications* and `rhoTheta`/`Ftilde`
   have been assessed.

3. **Coefficient generality.** The general intertwining is proved over
   `R = integerRing K` with `omit [CompleteSpace K]` — i.e. it holds over an arbitrary
   complete nonarchimedean `ℚ_p`-field. For an eventual mathlib statement, is the
   intended generality "arbitrary complete nonarchimedean `ℚ_p`-algebra" (the `MeasureR`
   layer) or the `ℤ_p`-only `PadicMeasure` layer, or both linked by `baseChange`?
   (Mathlib would want the most general — the `MeasureR` layer.)

4. **Named operator `∂`.** Would an upstreamed framework want the operator kept as the
   unfolded `(1+T)·derivativeFun`, or repackaged behind the *named* `MeasureR.del`
   (`∂ = (1+T)d/dT`, RJW's `∂`) so the API reads `A_{xµ} = ∂A_µ`? A named `∂` is a small
   but real piece of reusable formal-NT infrastructure — and would make this leaf, its
   `rhoA` sibling, and `one_add_mul_derivative_Ftilde` read more cleanly. (Currently the
   theorem statement spells `∂` out inline as `(1 + PowerSeries.X) * derivativeFun`.)

5. **Inline the leaf + hygiene.** Independent of (1)–(4): this theorem has exactly one
   consumer (`ValuesAtOne.lean:822`) and a short proof. Keep it as a named in-file lemma
   (current state — fine for a dev branch), or inline the `have hmeas … ; rw […]`
   composition at that one call site? Also: drop the **unused** hypotheses `_hD1 : 1 < D`
   and `_hη : η.IsPrimitive` (the leading underscores already mark them dead in this
   proof), and `omit` the unused `[IsUltrametricDist K] [CompleteSpace K]` instances?
   (No mathlib bearing either way; purely project hygiene — a `/cleanup` action, not a
   `/mathlibable` one.)

**Next action:** the maintainer answers (1)–(3) to fix the upstreaming policy; the
practical conclusion for **`one_add_mul_derivative_mahlerK_rhoTheta` specifically is "do
not upstream this application"** under any answer — it is a leaf application of the
general intertwining to RJW's `ζ_η` measure. If the framework *is* slated for mathlib,
re-run `/mathlibable` on `MeasureR.mahlerTransform_cmul_X` (RJW Lemma 3.29),
`MeasureR.apply_powCM` (RJW Cor 3.30), and the `MeasureR.mahlerTransform` / `mahlerK`
definitions (the trunk) — those are the genuine candidates. Proposed home for the
framework if so: `Mathlib/NumberTheory/Padics/LFunction/...` (a directory that does not
yet exist — itself confirming the whole area is the real gap).

---

## Next step

Maintainer answers questions 1–3 to set the p-adic-measure / Amice-transform
upstreaming policy. Regardless of the answer, `one_add_mul_derivative_mahlerK_rhoTheta`
itself stays project-local (a one-step, single-consumer application of the general
`A_{xµ}=∂A_µ` intertwining to the bespoke twisted measure `ρ_θ` = RJW's `ζ_η`); it is
not upstreamed in isolation. If the framework is destined for mathlib, the real
`/mathlibable` targets are the *general* lemmas `MeasureR.mahlerTransform_cmul_X` (RJW
Lemma 3.29) and `MeasureR.apply_powCM` (RJW Cor 3.30) and the Amice-transform
definition — not this application. Optionally (question 5), inline the proof at its
single call site (`ValuesAtOne.lean:822`), drop the unused `_hD1`/`_hη` hypotheses,
and/or `omit` the unused analytic instances — all project hygiene with no mathlib
bearing.
