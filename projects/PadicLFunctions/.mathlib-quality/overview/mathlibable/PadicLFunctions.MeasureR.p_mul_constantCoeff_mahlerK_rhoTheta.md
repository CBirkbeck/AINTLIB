# `/mathlibable` report — `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`

**Final verdict: `BORDERLINE-needs-human`.** This is the "P6-p6' constant pin"
(RJW T615) — a ~170-line *construction-internal* identity that is **STEP 1** in
the project's proof of **Leopoldt's formula** for the p-adic L-value `L_p(θ,1)`
(RJW §6.2, Thm 6.1(ii)). It is stated **entirely** in project-local objects
mathlib does not have (`mahlerK` = the Amice/Mahler transform, `rhoTheta`,
`Ftilde`, `seriesEval`, `phiSeries`, `twist`, `muEtaCleared`, the whole
`MeasureR` p-adic-measure substrate). It is therefore neither "in mathlib"
(Phase 5: nothing), nor a ≤3-call mathlib composition (Phase 6: the proof is
long and its building blocks are themselves project decls), nor upstreamable
as-stated (it cannot be phrased in mathlib's vocabulary). The verdict turns on
a judgment the skill cannot make alone: whether the project intends to upstream
the whole RJW §3–§6 measure / Amice–Mahler / `seriesEval` substrate — the only
world in which this specific Gauss-sum-cleared `ρ_θ`/`F̃_θ` specialisation
becomes meaningful — and, if so, whether the right upstream object is the
*general* trace lemma `sum_seriesEval_mahlerK` (which this specialises) rather
than this single-use pin. Numbered questions in Phase 7.

This decl is the exact §6.2 Dirichlet-character analog of the already-assessed
§7 sibling `PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA`
(`BORDERLINE-needs-human`): same operator-kernel proof architecture
(`W := C·F̃ − 𝓐_ρ`, `(1+T)∂`, trace over the `p`-torsion roots `ξ^i−1`,
`sum_seriesEval_mahlerK` + the `ψ`-vanishing lemma), here additionally carrying
Dirichlet characters `η, χ, θK` and the **Gauss-sum clearing** factor `G`.

---

### Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task note) — **reasoned from source** (Phase-0 fallback)
- decl `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:767`
- kind:                     `theorem`
- has sorry:                **no** — the proof body (lines 767–936) contains 0 `sorry`/`admit`; the proof is complete.
- module docstring summary: "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" — RJW Theorem 6.1(ii) (Leopoldt): `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)` for `θ = χη` non-trivial, `η` primitive of tame conductor `D > 1` prime to `p`, `χ` of conductor `p^n`. Route is distribution-free via the explicit antiderivative `F̃_θ` and the §6 c₀-design.

(Namespace note: the decl sits in `namespace PadicLFunctions` → `namespace MeasureR`, so the fully-qualified name is `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`. The task handle and the sibling reports drop the `MeasureR.` segment in places; both resolve to the same theorem at `ValuesAtOne.lean:767`.)

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta` is **a theorem**
stating the following "cleared constant-coefficient pin" (RJW's c₀-design, the
project's T615 pattern, made distribution-free per replan R6.6).

Let `p` be prime and `K` a complete characteristic-zero ultrametric normed
`ℚ_p`-algebra (in the intended application `K = ℂ_p ⊇ ℚ_p(μ_N)`). Fix:

- a primitive Dirichlet character `η` of tame conductor `D > 1` with `p ∤ D`
  (valued in the ring of integers `𝓞 = integerRing K`), and a primitive root
  `ζ` of order `D`;
- a primitive Dirichlet character `χ` of conductor `p^n`;
- the combined character `θ = θK = ηχ` over `K`, of conductor `N := D·p^n`,
  non-trivial, with `N > 1`;
- a primitive `N`-th root of unity `ε ∈ K`, and a primitive `p`-th root `ξ ∈ K`;
- a Gauss-clearing unit `G ∈ K`;
- (coprime-guarded norm hypothesis) `‖ε^c − 1‖ = 1` for every unit residue
  `c ∈ (ℤ/N)ˣ` — RJW's cyclotomic-product fact, only the unit `c` contribute
  because `θ⁻¹(c) = 0` otherwise;
- (the cleared-twist hypothesis `hGtwist`) the Amice transform of the
  `χ`-twisted measure `μ̃_η` equals `C G⁻¹` times an explicit rational sum of
  `Ring.inverse((1+T)·C(ε^c) − 1)` terms.

Then

  p · 𝓐(ρ_θ)(0)  =  G⁻¹ · ( p · F̃_θ(0)  −  Σ_{i ∈ Fin p} F̃_θ(ξ^i − 1) ).

Here:
- `𝓐(ρ_θ) = mahlerK p K (rhoTheta p K η hζ hD χ)` is the **Mahler/Amice
  transform** power series (in `K⟦T⟧`) of the genuine measure
  `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` (RJW §6's clearing pattern applied to the
  `χ`-twisted `μ̃_η`, pushed forward along the unit inclusion `iota`);
- `F̃_θ = Ftilde p K θK hε` is RJW's explicit `K`-coefficient antiderivative
  (TeX ~2070; `extLog`-constant terms + the per-root log series `logSeriesAt`);
- `(·)(0) = PowerSeries.constantCoeff (·)` is the constant coefficient;
- `F̃_θ(ξ^i − 1) = seriesEval (Ftilde …) (ξ^i − 1)` is the **analytic**
  evaluation `Σ_n coeff_n(F̃_θ)·(ξ^i−1)ⁿ` (a `tsum`, convergent because
  `‖ξ^i−1‖ < 1`; summability is `summable_seriesEval_Ftilde`).

Mathematically this is the **mass / c₀-extraction step** of Leopoldt's
formula. The proof forms `W := C G⁻¹·F̃_θ − 𝓐(ρ_θ)`; shows `(1+T)·∂W = φ(B)`
for the bounded `B = G⁻¹-cleared 𝓐(ψ-part)` (matching three operator
identities for `∂F̃_θ`, `∂𝓐(ρ_θ)`, `∂(φC₁)`); deduces `W = φC₁ + C c₀` because
the operator `(1+T)d/dT` has a one-dimensional kernel of constants; then
evaluates `W` at the `p`-torsion shifts `ξ^i−1` (where the `φ`-images collapse
to `0` and the `𝓐(ρ_θ)`-trace `Σ_i 𝓐(ρ_θ)(ξ^i−1) = p·𝓐_{ψρ}(0) = 0` by
`sum_seriesEval_mahlerK` + `psi_rhoTheta`) and at `0`, pinning `c₀` and
assembling the displayed identity by `linear_combination`. After STEP 1, the
caller `LpFunction_one` turns this into `L_p(θ,1) = G_η⁻¹·𝓐_ρ(0)` and then into
the closed Leopoldt formula.

Variables / typeclasses involved (Lean side; file-level `variable` block,
`ValuesAtOne.lean:31–34`):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime / residue characteristic.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]` — the coefficient field (the ℂ_p stand-in).
  All five are genuinely used: `seriesEval`'s `tsum` needs the norm +
  completeness; `mahlerK`/`MeasureR K ℤ_[p]`/base-change need the
  complete-ultrametric-Banach structure (the Mahler `RingEquiv` only exists over
  such `K`); `CharZero` for the rational scalars in `logSeriesAt`/`F̃_θ`. (None
  is `omit`-ted in this theorem.)
- `{D : ℕ} [NeZero D]`, `(hD1 : 1 < D)` — the tame conductor.
- `{η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)` — the tame
  character.
- `{ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)`, `(hD : ¬ p ∣ D)`.
- `{n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (_hχ : χ.IsPrimitive)`
  — the wild part.
- `{θK : DirichletCharacter K (D * p ^ n)}`, `(hN : 1 < D * p ^ n)`,
  `(hθ1 : θK ≠ 1)`, `(_hθK : θK = toFieldChar (η-changeLevel * χ-changeLevel))`.
- `{ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n))`, `{ξ : K} (hξ : IsPrimitiveRoot ξ p)`.
- `{G : K} (_hG : IsUnit G)`.

Hypotheses (Lean side, math role):
- `hnorm : ∀ c ∈ range N, IsUnit (c : ZMod N) → ‖ε^c − 1‖ = 1` — RJW's
  cyclotomic-product fact, coprime-guarded (the original `¬N∣c`-guard is FALSE
  for `c = D·j`; see the docstring's statement-fix note, replan R6.6).
- `hGtwist : mahlerK …(twist χ μ̃_η)… = C G⁻¹ · (−Σ_c C(θK⁻¹ c)·Ring.inverse(…))`
  — the cleared-twist identity supplying the explicit transform shape.

Conclusion (math): the `p`-scaled constant coefficient of `𝓐(ρ_θ)` equals `G⁻¹`
times (`p`-scaled `F̃_θ(0)` minus the trace-sum of `F̃_θ` over the `p`-torsion
shifts) — RJW's Gauss-cleared c₀-pin (STEP 1 of Leopoldt's formula).

Conclusion (Lean):
`(p : K) * PowerSeries.constantCoeff (mahlerK p K (rhoTheta p K η hζ hD χ))
  = G⁻¹ * ((p : K) * PowerSeries.constantCoeff (Ftilde p K θK hε)
    - ∑ i : Fin p, seriesEval (Ftilde p K θK hε) (ξ ^ (i : ℕ) - 1))`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (a sub-result, not the headline).
Reason: it is the "P6-p6'" *step* of the project's decomposition — the cleared
mass / c₀-pin feeding the §6.2 value computation — not a new mathematical
structure, not the file's headline result (that is `LpFunction_one`,
`ValuesAtOne.lean:1594`, RJW Thm 6.1(ii) / Leopoldt's formula), and not named
after a person/place. The docstring tag "P6-p6' (the constant pin, c₀-design)"
marks it as an internal step. It is, however, a *substantive* lemma (a ~170-line
proof, lines 767–936), not a one-liner — which matters for Phase 6 (it is **not**
a 3-call composition).

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~170 substantive lines (lines 767–936: a long sequence of
`have`s assembling the operator-kernel argument).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** The
one-liner/exemption machinery applies to `def`/`abbrev`/`structure`. Skipped.
(Note for Phase 6/7: this is emphatically a multi-step proof, so the
"inline-the-one-liner" reasoning does **not** apply — the composition route is
closed here for a different reason: the building blocks are project decls and
the assembly is real reasoning.)

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `Kubota-Leopoldt p-adic L-function value at s=1 Leopoldt formula Dirichlet character Gauss sum logarithm L_p(theta,1)` | **yes** | "p-adic L-function has explicit values at `s=1`, obtaining **Leopoldt's formula** in the p-adic case" — the value `L_p(θ,1)` is given by a Gauss sum `G(θ⁻¹)⁻¹` times `Σ_c θ⁻¹(c)·log_p(1−ε^c)`. | Top hits: Iwasawa, *Lectures on p-adic L-functions* (AM-74); **RJW arXiv:2309.15692** (the project's source); Washington, *Cyclotomic Fields* (the p-adic L-function chapter explicitly "obtains Leopoldt's formula"). The **value at `s=1` is named after Leopoldt** (announced 1964, this form). |
| 2 | WebSearch (general / framework) | `p-adic L-function L_p(1,chi) explicit formula Gauss sum tau(chi) sum chi-inverse log(1 - zeta_N^c) Iwasawa` | **yes** | The value at `s=1` is the p-adic logarithm of cyclotomic/principal units assembled against the inverse Gauss sum; classical Iwasawa-theory form. | Annals (Hecke L-function Iwasawa invariant), Williams Warwick notes, "Local Factorization of p-adic Gamma Sums" (Iwasawa log + Gauss sums). The **closed value formula is standard**; the *route* (explicit antiderivative `F̃_θ`, c₀-pin) is RJW's, not separately named. |
| 3 | WebSearch (named-after / aliases — RJW) | `Rodrigues Jacinto Williams introduction p-adic L-functions arXiv 2309.15692 theorem 6.1 value s=1 Dirichlet character` | **yes** | Confirms the source: **RJW = Rodrigues Jacinto–Williams, "An introduction to p-adic L-functions"** (arXiv:2309.15692; Essential Number Theory 4(1), 2025; MSP `ent-v4-n1-p03`). §6 treats the value at `s=1`. | The document is the project's authoritative reference. `F̃_θ`, the c₀-design, and the trace-over-roots step are presented as **internal computational steps** in the value-at-`s=1` derivation, not standalone named theorems. (PDF text-extraction blocked by stream compression on direct fetch; identification rests on the search snippets + the project's own in-file citations.) |
| 4 | WebSearch (Leopoldt / Washington) | `Leopoldt formula p-adic L-function value at 1 Washington cyclotomic fields theorem chi odd Gauss sum log_p(1 - zeta)` | **yes** | "The p-adic L-function has explicit values at `s = 1`, thereby obtaining **Leopoldt's formula** in the p-adic case, analogous to … the complex case." | Springer (Washington, *Cyclotomic Fields I & II*, the p-adic L-function chapter); the BDP formula is described as "a direct generalisation of the formulae of **Leopoldt** and Katz". Confirms **the value at `s=1` is the classical, named "Leopoldt's formula"** — exactly the project's `LpFunction_one`. |
| 5 | ChatGPT MCP | (intended) "standard form + generality + historical evolution of the c₀-pin identity that, summing an Amice transform over `p`-torsion shifts, extracts `p`×the constant of the cleared difference `C·F̃_θ − 𝓐(ρ_θ)`" | **n/a** | — | **n/a — no ChatGPT/OpenAI MCP server is available/authenticated in this environment** (`ls ~/.claude` shows no chatgpt config; consistent with the sibling reports `rhoA.md`, `p_mul_constantCoeff_mahlerK_rhoA.md`, which record the same). Compensated by 4 WebSearch queries (#1–#4) at three generality levels + the project's authoritative RJW citation + mathlib-source grep (Phase 5). |
| 6 | Local references | `ls/grep projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/` | **n/a** | (directory absent) | `projects/PadicLFunctions/.mathlib-quality/references/` does **not** exist; no `refs/` symlink in this checkout (PDFs are local-only, never committed). Same as the sibling reports. The in-file RJW citations (header lines 12–30; "RJW §6.2, Thm 6.1(ii)"; "TeX 2076–2080, ~2070") give the source form directly. |
| 7 | nLab | `Iwasawa theory`, `Iwasawa algebra`, `Amice transform`, `p-adic L-function` | **partial** | nLab "Iwasawa theory": `Λ(ℤ_p) ≅ ℤ_p⟦T⟧` = measures = dual of `C(ℤ_p,ℤ_p)`; the **Amice transform** is "a generalization of the Iwasawa–Mahler transform"; p-adic L-functions realised as measures inside the Iwasawa algebra. | Confirms the **ambient framework** (Iwasawa algebra = measures = power series via Amice/Mahler) is classical and standard. No nLab entry for this specific Gauss-cleared c₀-pin identity. |
| 8 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept: a concrete `tsum`/constant-coefficient identity in a concrete coefficient field. No 1-/∞-categorical content to abstract. |
| 9 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry concept (no schemes/sites/cohomology). Stacks has no p-adic-measure / Amice-transform / p-adic-L-function material. |
| 10 | MathOverflow / Math.SE | (folded into #1–#4, #7: Leopoldt-formula / Iwasawa-algebra / Amice-transform / Coleman-map threads) | **partial** | Same as #2/#7: the value `L_p(θ,1)` via inverse Gauss sum and `Σ θ⁻¹(c) log_p(1−ε^c)`, and `D⁰(ℤ_p) ≅ ℤ_p⟦T⟧`, are routine in Iwasawa-theory discussion. | No dedicated thread isolating this exact cleared `C·F̃_θ − 𝓐(ρ_θ)` pin; construction-internal. |
| 11 | recent arXiv (last 5 years) | de Shalit, *Mahler bases & elementary p-adic analysis* (JTNB jtnb.955); arXiv:2201.08870 (*Sum expressions for Kubota–Leopoldt p-adic L-functions*); RJW arXiv:2309.15692 | **yes** | de Shalit: the Amice/Mahler transform and evaluation-at-roots are textbook elementary p-adic analysis. arXiv:2201.08870: sum expressions for the Kubota–Leopoldt L-function (the value/special-value circle). | Confirms the **frameworks** (Amice transform, evaluation, sum-over-roots trace) are classical and actively used; the **specific cleared c₀-pin** assembling them on `ρ_θ`/`F̃_θ` is RJW-internal bookkeeping, not a standalone named theorem. |

**Protocol pass check.** WebSearch ran 4 distinct queries at three generality
levels (specific value/Leopoldt form #1, #4; general framework form #2; named-
after/source #3). ChatGPT MCP genuinely unavailable (recorded `n/a` +
compensating channels). Local references checked (`n/a`, absent). nLab checked
(partial hit — confirms the framework). nCatLab / Stacks / MO–MSE / arXiv each
checked or `n/a` with a one-line reason. ✓

### Literature summary (Phase 3)

Concept identified as: an **internal computational step** ("the cleared c₀-pin",
P6-p6', RJW T615) **inside the derivation of Leopoldt's formula** for the p-adic
L-value `L_p(θ,1)` — **RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692) §6.2,
Theorem 6.1(ii)**. The *headline* result it feeds (the value `L_p(θ,1) =
−(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_c θ⁻¹(c)·log_p(1−ε^c)`) is **classical and named after
Leopoldt** (1964; Iwasawa's *Lectures*; Washington's *Cyclotomic Fields*). The
pin itself rests on three standard, classical *frameworks* — (a) the
**Amice/Mahler transform** `D⁰(ℤ_p) ≅ ℤ_p⟦T⟧` (the project's `mahlerK`), (b)
**analytic evaluation** of a unit-norm power series at `‖z‖<1` (the project's
`seriesEval`), and (c) the **trace/Coleman** identity that summing over the
`p`-torsion shifts `ξ^i−1` isolates `p`×(constant/`ψ`-part). All three are
textbook in Coleman/Iwasawa theory; the *specific cleared identity* (with the
Gauss factor `G` and the `ρ_θ`/`F̃_θ` pair) is RJW-internal bookkeeping.

Sources agree on the standard form: **yes** for the closed value (Leopoldt's
formula — the consumer `LpFunction_one`) and for the three frameworks (Amice
transform, evaluation, sum-over-roots trace). **No independent literature life**
for this specific `p·𝓐(ρ_θ)(0) = G⁻¹·(p·F̃_θ(0) − Σ F̃_θ(ξ^i−1))` pin — it is one
step inside one proof.

Most general standard form: there is no "more general standard cleared c₀-pin"
to aim at. The generality lives in the *primitives* (the Amice transform of any
measure; evaluation of any unit-norm series; the trace over any cyclotomic
extension). The project already factors that generality out: the trace half is
the **general** lemma `sum_seriesEval_mahlerK` (over an *arbitrary*
`μ : MeasureR K ℤ_[p]`, `FormalPsi.lean:1072`); the target is its
**specialisation** to the difference `C G⁻¹·F̃_θ − 𝓐(ρ_θ)` plus the
operator-kernel argument.

Generality dimensions where the literature varies:
  - measure `μ`: general `MeasureR K ℤ_[p]` (as in `sum_seriesEval_mahlerK`) vs.
    the specific `ρ_θ`/`F̃_θ` Gauss-cleared pair here — the target is at the
    *specific* end.
  - coefficient ring: any p-adic coefficient ring containing `μ_N`; here a
    complete ultrametric `ℚ_p`-Banach field of char 0 (ℂ_p). Standard.
  - These are dimensions of the *primitives*, not of this composite identity.

Disagreement with the literature: **none** — the literature does not isolate
this cleared pin as an object; it is a step (treating "the source doesn't name
it" as a signal: construction-internal, not a standalone standard result; cf.
the verdicts-reference anti-pattern "treating literature absence as YES").

---

## PHASE 4 — Generality analysis

### Generality analysis — `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`

Literature-standard form (Phase 3): there is **no separately-named standard
form** of this cleared c₀-pin. The relevant generality lives in (i) the three
primitive frameworks (Amice transform / evaluation / sum-over-roots trace) and
(ii) the project's own *general* trace lemma `sum_seriesEval_mahlerK`. So the
"compare to the literature-standard form" exercise reduces to: *is each input
applied at the right generality, and is the composite the right thing to
state?* — and the honest answer is that the composite is a deliberate
**specialisation** of an already-general project lemma, tied to project objects
plus a Gauss-clearing convention.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` + 4 analytic instances | char-zero complete ultrametric normed `ℚ_p`-algebra (ℂ_p stand-in) | the coefficient field of an Amice-transform / `seriesEval` computation over `ℚ_p(μ_N)` | **NO** | All genuinely used (none `omit`-ted in this theorem): `seriesEval`'s `tsum` needs norm+completeness; `mahlerK`/`MeasureR`/base-change need the complete-ultrametric-Banach structure (the Mahler `RingEquiv`); `CharZero` for `logSeriesAt`/`F̃_θ`'s rational scalars. |
| 2 | `(hD1 : 1 < D)`, `(hD : ¬ p ∣ D)`, `(hη : η.IsPrimitive)` | tame conductor `D > 1`, prime to `p`, `η` primitive | RJW §5.2 standing hypotheses for `θ = χη` | **NO** | These are RJW's exact tame-part hypotheses (the `D = 1` pure-`p`-power case is deferred per the header). `hD1`/`hD` force the cyclotomic-product norm fact; primitivity is the conductor condition. |
| 3 | `(hθ1 : θK ≠ 1)`, `(hN : 1 < D·p^n)` | combined char non-trivial, conductor `> 1` | RJW §6.2 ("`θ` non-trivial") | **NO** | non-triviality is essential (the value formula and the `MulChar.sum_eq_zero` collapses fail for `θ = 1`); matches RJW. |
| 4 | `hε : IsPrimitiveRoot ε (D·p^n)`, `hξ : IsPrimitiveRoot ξ p` | primitive `N`-th and `p`-th roots | the cyclotomic data + the trace/torsion variable (Coleman/Amice) | **NO** | `ε` is the conductor-`N` root in the value formula; the sum-over-`p`-torsion-shifts trace mechanism requires a primitive `p`-th root `ξ`. Both natural; `ξ` matches `sum_seriesEval_mahlerK`. |
| 5 | `hnorm` (coprime-guarded norm), `hGtwist` (cleared twist), `_hG : IsUnit G` | RJW's cyclotomic-product fact + the Gauss-cleared transform shape + unit Gauss factor | RJW §6.2 clearing conventions | **NO** | `hnorm` is exactly RJW's `‖ε^c−1‖=1` for unit `c` (coprime-guarded per replan R6.6; the original `¬N∣c`-guard is FALSE — see docstring). `hGtwist`/`_hG` carry the Gauss-clearing `G`; this is the §6.2 cleared route, not a removable convenience. |
| 6 | the objects `mahlerK`, `rhoTheta`, `Ftilde`, `seriesEval`, `twist`, `muEtaCleared` | project-specific Amice transform / genuine measure / antiderivative / evaluation / twist / cleared base measure | no literature-standard form (RJW-internal) | **NO** | project objects; mathlib has no counterpart toward which to generalise (Phase 5). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL within an intrinsically project-local
scope.** Every hypothesis is tight and genuinely used (none `omit`-ted), the
tame-part / non-triviality / primitive-root / Gauss-clearing hypotheses are all
RJW's exact §5.2–§6.2 standing conditions, and the *statement itself* is bound
to project objects (`mahlerK`/`rhoTheta`/`Ftilde`/`seriesEval`) plus the Gauss
factor `G`, so there is **no "more general literature form of this theorem"** to
aim at.

Number of weakening opportunities found: **0** for the theorem as stated.

Important nuance feeding Phase 7: the *one* real generalisation in the
neighbourhood is **not** a weakening of *this* theorem but the recognition that
its trace half is already the **general** project lemma
`sum_seriesEval_mahlerK` (arbitrary `μ`). This theorem is the deliberate
*specialisation* (to `ρ_θ`/`F̃_θ`, with Gauss-clearing) plus the operator-kernel
`c₀` argument. That is an argument for the specialisation being
**single-purpose** (→ BORDERLINE / NO), not for restating it more generally.

Proposed restatement (if STRICTLY NARROWER): n/a — not strictly narrower than a
*literature* standard (there is none); the more-general sibling is a different
(already-existing) project lemma, not a restatement of this one.

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | already fully typeclass-based (`[NormedField K]`, `[NormedAlgebra ℚ_[p] K]`, `[IsUltrametricDist K]`, …); the characters are `DirichletCharacter` bundles | — |
|  2 | sequences/metric → filters/topology? | no | the only limit is the `tsum` inside `seriesEval`, already the idiomatic `Summable`/`tsum` framework | — |
|  3 | construct an object → universal-property class? | no | this is a value identity, not a construction | — |
|  4 | set+closure-predicate → bundled substructure? | no | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses? | no | the field/Banach/char-0 hypotheses are all genuinely required (Phase 4b row 1); nothing to weaken | — |
|  6 | 1-categorical → higher-categorical? | no | no categorical content | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | partial | the trace sum is over `Fin p` (the `p`-torsion) — already the natural index for a primitive-`p`-th-root trace; the conductors `D, p^n` are the natural Dirichlet-character moduli | — (no genuine generalisation axis) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The statement is already a contemporary,
typeclass-based, `tsum`/`Summable`-idiomatic identity at the right generality,
using mathlib's `DirichletCharacter` and `IsPrimitiveRoot` bundles. The only
"modernisation" that would matter — formalising the whole RJW §3–§6
**Amice/Mahler-transform + p-adic-measure + `seriesEval`** layer idiomatically —
is *upstream* of this theorem (it is exactly the work the project is doing), not
a reformulation of this one identity. There is no
filter-ise/categorify/weaken-typeclass move that improves *this* statement.
One-line reason: this is a construction-internal value identity in
already-idiomatic project primitives; nothing about the identity itself is to be
modernised.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities and no typeclass-search paths; the six-row risk table is skipped.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`

[A] **Lean-Finder**  — natural-language + type queries — **n/a: no Lean-Finder MCP tool surfaced** in this environment. Compensated by [D] direct grep over the pinned mathlib clone (`./.lake/packages/mathlib/Mathlib`, confirmed present), which is authoritative.
[B] **Loogle**       — type-pattern `(p : K) * constantCoeff _ = _ * ((p:K) * constantCoeff _ - ∑ _, seriesEval _ _)` / `∑ _ : Fin p, (tsum _) = _` — **n/a as MCP** (no `lean_loogle`); emulated via [D]. **No hit**: mathlib has no `seriesEval` (analytic `tsum coeff·zⁿ`) and no Amice-transform constant-coefficient identity.
[C] **LeanSearch**   — "p-adic L-function value at s=1 Leopoldt formula Gauss sum"; "sum of a p-adic power series over primitive p-th-root shifts equals p times constant coefficient" — **n/a as MCP** (no `lean_leansearch`); covered by the WebSearch literature channels (#1–#4) + [D].
[D] **Grep mathlib src** — over `./.lake/packages/mathlib/Mathlib/`:
  - `mahlerK`, `rhoTheta`, `Ftilde`, `muEtaCleared`, `seriesEval`, `phiSeries`, `extLog`, `toFieldChar`, `MeasureR`, `mahlerTransform`, `amiceTransform` → **0 files each** (all project-only objects).
  - **p-adic L-function**: `padicLFunction` / `kubota` / `leopoldt` / `LFunctionPadic` → **0 hits**. Mathlib has **no p-adic L-function at all** (no Kubota–Leopoldt construction, no value at `s=1`, no Leopoldt formula). It *does* have complex `LFunction`/`DirichletCharacter` L-series, but nothing p-adic.
  - **p-adic measure / Amice–Mahler transform / Iwasawa-algebra-as-dual** (`D⁰(ℤ_p) ≅ ℤ_p⟦T⟧`) → **0 hits**. Mathlib's only p-adic-functional-analysis content is one layer down: `Mathlib/NumberTheory/Padics/MahlerBasis.lean` (Mahler's theorem / orthonormal basis of `C(ℤ_p, E)`) and the binomial-ring structure on `ℤ_[p]` — **not** a measure (dual) theory, and **no Amice transform**.
  - `PowerSeries` evaluation: mathlib has **formal** substitution/evaluation (`PowerSeries.eval₂`, `HasEval`, `subst`; `RingTheory/PowerSeries/{Evaluation,Substitution}.lean`) — but **not** the analytic `seriesEval` (`∑' n, coeff_n F · zⁿ` as a `tsum` in a normed field), the project's `FormalPsi.lean:577` definition.
  - **Gauss sums**: mathlib *has* `gaussSum` (`NumberTheory/GaussSum.lean:72`) and `DirichletCharacter/GaussSum.lean` (e.g. `gaussSum_mul_gaussSum_eq_card`). These are the **complex/finite-field** Gauss sums used in the consumer's clearing, but mathlib has **no p-adic L-value formula** assembling them — so this is a *building block of the eventual statement*, not the theorem.
  - roots-of-unity: mathlib has `IsPrimitiveRoot` + `RootsOfUnity/*` (incl. cyclotomic units, `pow_eq_one_iff_dvd`, `pow_of_coprime` — both used in the proof) but **no** "sum over primitive-root shifts extracts the constant/`ψ`-part of a measure's transform" lemma — that lemma is the project's `sum_seriesEval_mahlerK` (`FormalPsi.lean:1072`).
[E] **Name pattern** — grep mathlib for `*_mul_constantCoeff_*`, `*constantCoeff*rho*`, `sum_seriesEval*`, `*mahlerK*`, `*rhoTheta*` → **0 hits**. Nothing named like a p-adic-measure constant-coefficient trace pin.

Searched for both:
  - the **user's current form** (`p·𝓐(ρ_θ)(0) = G⁻¹·(p·F̃_θ(0) − Σ F̃_θ(ξ^i−1))`,
    with `𝓐 = mahlerK`, `seriesEval`, `Ftilde`, `rhoTheta`): **not in mathlib** —
    every object in the statement is project-only.
  - the **literature/framework form** (Leopoldt's value `L_p(θ,1)`; the Amice
    transform of a measure; analytic evaluation at `‖z‖<1`;
    sum-over-`p`-torsion-shifts trace = `p`·(`ψ`-part)): the **value formula is
    absent** (mathlib has no p-adic L-function) and the **frameworks themselves
    are absent** — mathlib has Mahler's theorem on `C(ℤ_p)`, `gaussSum`, and
    `IsPrimitiveRoot`, but no p-adic-measure / Amice-transform theory, no
    analytic `seriesEval`, and hence no such trace identity.

Concluded: **not in mathlib (all methods exhausted, both the composite form and
every framework component, including the headline Leopoldt value it feeds).**
Moreover the building blocks of the *proof* are themselves **project decls**
(`summable_seriesEval_Ftilde`, `one_add_mul_derivative_Ftilde`,
`one_add_mul_derivative_mahlerK_rhoTheta`, `res_units_eq`, `mahlerK_sub`,
`mahlerK_phi`, `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`,
`exists_antideriv_bounded`, `one_add_mul_derivative_phiSeries`,
`phiSeries_C_mul`, `seriesEval_phi_at_root_of_summable`, `seriesEval_*`,
`sum_seriesEval_mahlerK`, `psi_rhoTheta`), not mathlib decls — so there is no
mathlib composition to inline (this closes the `NO-composable` route; see
Phase 6). The only mathlib lemmas in the proof are generic glue (`map_sub`,
`map_sum`, `mul_sub`, `ring`, `linear_combination`, `IsPrimitiveRoot.pow_eq_one`,
`IsPrimitiveRoot.pow_of_coprime`, `isUnit_iff_ne_zero`,
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`).

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`

Internal use count (within the project, **excluding** the declaring line): **K = 1.**
External-to-file callers: **0 distinct files.**

A repo-wide word-boundary grep `\bp_mul_constantCoeff_mahlerK_rhoTheta\b` over
`projects/**/*.lean` returns exactly two lines: the declaration
(`ValuesAtOne.lean:767`) and one use (`ValuesAtOne.lean:1738`). No other file —
in PadicLFunctions or any sibling project — references it.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ValuesAtOne.lean:1738` | `have hT615 := p_mul_constantCoeff_mahlerK_rhoTheta hD1 hη hζ hD hχ hN hθ1 hθK hε hξ hnorm hGχKne.isUnit hGtwist` (inside `LpFunction_one`, line 1594 — **RJW Thm 6.1(ii) / Leopoldt's formula**, "STEP 1: the cleared mass identity") |

Inline-derivation grep (was the equivalent re-derived elsewhere without this
lemma?): **(none).** The cleared `p·constantCoeff(𝓐 ρ_θ)` pin is computed in
exactly one place — this theorem — and consumed in exactly one place — its
immediate caller `LpFunction_one`, which combines it with `sum_seriesEval_Ftilde`
(STEP 2) and the constant-coefficient computation to obtain `L_p(θ,1) =
G_η⁻¹·𝓐_ρ(0)` and then the closed Leopoldt formula.

What the call-sites pattern tells you: **K = 1 internal use, 0 external, no
inline re-derivation.** Per the Phase-6 / verdicts-reference table this is the
"single-consumer corollary — possibly the wrong *standalone* abstraction; leans
toward a NO/BORDERLINE bucket" signal. It is a "feeds-exactly-one-theorem" step
in the §6.2 value chain, not reusable cross-project API. (It is *not* dead code:
the one consumer is the file's headline theorem; but it is not API anyone else
uses.) Identical signal to the §7 twin `p_mul_constantCoeff_mahlerK_rhoA`
(K = 1, also feeding its file's mass lemma).

### Composition check (Phase 6)

Can `p_mul_constantCoeff_mahlerK_rhoTheta` be derived from **mathlib** in ≤3
chained calls? **No.**

**Attempt 1 — direct mathlib composition.** There is none: every object in the
statement (`mahlerK`, `rhoTheta`, `seriesEval`, `Ftilde`) is project-only and
absent from mathlib (Phase 5). Mathlib cannot even express the statement, let
alone discharge it in ≤3 calls. **Fails** (no mathlib vocabulary).

**Attempt 2 — composition from the *project's* building blocks.** The actual
proof (lines 767–936, ~170 lines) is a genuine multi-step argument:
  1. derive `hunit` (`ε^c−1` a unit for `¬N∣c`) from `IsPrimitiveRoot.pow_eq_one_iff_dvd`;
  2. obtain a bounded antiderivative `C₁` of the `ψ`-part (`exists_antideriv_bounded`);
  3. three operator identities `(1+X)·∂(·)` for `C G⁻¹·F̃_θ`, `𝓐(ρ_θ)`, and `φ C₁`
     (`one_add_mul_derivative_Ftilde` + `hGtwist`,
     `one_add_mul_derivative_mahlerK_rhoTheta` + `res_units_eq` + `mahlerK_sub`/`mahlerK_phi`,
     `one_add_mul_derivative_phiSeries` + `phiSeries_C_mul`);
  4. deduce `(1+X)·∂(W − φC₁) = 0` for `W = C G⁻¹·F̃_θ − 𝓐(ρ_θ)`, hence
     `W − φC₁ = C c₀` (`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`);
  5. five summability facts at the torsion shifts `ξ^j−1`
     (`summable_seriesEval_Ftilde`, `summable_seriesEval_of_norm_coeff_le_one/le_linear`, …);
  6. evaluate `W = φC₁ + C c₀` at each `ξ^j−1` via `seriesEval_phi_at_root_of_summable`
     (φ-part → 0) and `seriesEval_C` (constant → c₀), summing to `p·c₀`;
  7. the `𝓐(ρ_θ)`-trace vanishes via `sum_seriesEval_mahlerK` + `psi_rhoTheta`;
  8. expand `c₀` at `0`, `rw`/`ring`, and `linear_combination` to assemble.

This is **a proof**, not a composition: ~170 lines, a dozen `have`-steps with
non-trivial operator-theoretic reasoning, `rw`/`ring`/`linear_combination` glue,
and — most decisively — **every** non-trivial input is a *project* lemma, not a
mathlib lemma. Per the Phase-6 heuristics table this is firmly in the "multiple
`have`s with reasoning between ⇒ NO, this is a proof" / "anything requiring
`rw`/`ring`/`linear_combination` glue ⇒ NO, real proof" rows.

**Conclusion: NOT-COMPOSABLE** (neither from mathlib — no vocabulary, no
building blocks — nor as a ≤3-call assembly of *project* primitives; it is a
substantive ~170-line proof).

This closes **both** NO buckets: `NO-mathlib-has-it` (Phase 5: nothing) and
`NO-composable-from-mathlib` (Phase 6: NOT-COMPOSABLE, and the gate's required
≤3-line mathlib sketch cannot be honestly produced — the substrate is
project-only). It also rules out the YES buckets (the statement is unphrasable
in mathlib). What remains is a synthesis judgment → Phase 7.

---

## Verdict: `PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified as an **internal computational step**
  (the cleared "c₀-pin", P6-p6', RJW T615) **inside the derivation of Leopoldt's
  formula** for the p-adic L-value `L_p(θ,1)` (RJW arXiv:2309.15692 §6.2, Thm
  6.1(ii)). The headline value it feeds is classical and **named after
  Leopoldt**; the pin rests on three classical *frameworks* (Amice/Mahler
  transform; analytic evaluation; sum-over-`p`-torsion trace) but is **not a
  separately-named standard result**; the project already factors the trace
  generality into `sum_seriesEval_mahlerK`, and this theorem is its
  specialisation to `ρ_θ`/`F̃_θ` with Gauss-clearing.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL within an intrinsically
  project-local scope** (0 weakenings; all hypotheses forced/used; none
  `omit`-ted; the tame-part/non-triviality/primitive-root/Gauss-clearing
  hypotheses are RJW's exact §5.2–§6.2 standing conditions); modern-idiom
  **none** (already idiomatic; the only modernisation is upstreaming the whole
  RJW measure/Amice layer, which is *upstream* of this theorem).
- Mathlib search (Phase 5): **not in mathlib** under the composite form, every
  framework component, **and the headline Leopoldt value it feeds** (mathlib has
  no p-adic L-function at all). Mathlib's p-adic content stops at Mahler's
  theorem on `C(ℤ_p)` + `gaussSum` + `IsPrimitiveRoot`, with **no** p-adic-measure
  / Amice-transform theory, **no** analytic `seriesEval`, and hence no such
  trace identity.
- Composition check (Phase 6): **NOT-COMPOSABLE** — no mathlib vocabulary or
  building blocks (so no `NO-composable` ≤3-line sketch is honestly possible);
  the actual proof is a substantive ~170-line operator-kernel argument whose
  every non-trivial input is a *project* lemma. K = 1 internal caller
  (`LpFunction_one`), 0 external, no inline re-derivation.

**Rationale.**
`p_mul_constantCoeff_mahlerK_rhoTheta` is the project's "T615 cleared c₀-pin":
the identity `p·𝓐(ρ_θ)(0) = G⁻¹·(p·F̃_θ(0) − Σ_{i<p} F̃_θ(ξ^i−1))` that is
**STEP 1** in `LpFunction_one`'s proof of **Leopoldt's formula**
`L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_c θ⁻¹(c)·log_p(1−ε^c)` (RJW §6.2, Thm
6.1(ii)). Its content is genuinely classical Coleman/Iwasawa mathematics
(summing an Amice transform over `p`-torsion shifts extracts `p`×the
constant/`ψ`-part; the operator `(1+T)d/dT` has a one-dimensional kernel of
constants), plus a Gauss-sum clearing convention. But **as a Lean object it is
irreducibly project-local**: its *statement* names `mahlerK` (the Amice
transform), `rhoTheta` (the genuine measure), `seriesEval` (the analytic `tsum`),
and `Ftilde` (RJW's explicit antiderivative) — and **none of these exists in
mathlib**, which has no p-adic-measure/Amice-transform layer and no p-adic
L-function at all. So mathlib cannot contain this theorem as stated, it is not a
≤3-call composition (the proof is ~170 lines and every building block is a
project lemma), and there is no mathlib decl to cite for `NO-mathlib-has-it`.

Three of the five buckets are therefore mechanically excluded (YES-*: unphrasable
in mathlib; NO-mathlib-has-it: nothing to cite; NO-composable: no mathlib sketch
honestly producible — and this is a *substantive theorem*, not a one-liner, so
the elastic `NO-composable` reading the *def* siblings used does not apply). The
remaining honest choice — between recording it as "not-mathlib-bound" and
`BORDERLINE` — turns on a **judgment the skill cannot make alone**: whether the
project intends to upstream the **whole** RJW §3–§6 Amice-transform /
p-adic-measure / `seriesEval` layer (the only world in which the theorem becomes
meaningful), and, if so, whether the right upstream object is the **general**
trace lemma `sum_seriesEval_mahlerK` (which this specialises) rather than this
single-use Gauss-cleared `ρ_θ`/`F̃_θ` pin. That is a project-policy +
mathematical-taste call — exactly what `BORDERLINE-needs-human` is for, and the
verdict the structurally-identical §7 sibling `p_mul_constantCoeff_mahlerK_rhoA`
also received. (Per the verdicts reference, "audience-narrow result / project
policy / generality-vs-packaging tradeoff" are textbook BORDERLINE triggers, and
"treating literature absence as YES" / forcing a NO with an un-producible sketch
are the anti-patterns to avoid.)

**Numbered questions (≤5):**

  1. **Upstreaming intent.** Do you intend to upstream the RJW §3–§6
     **p-adic-measure + Amice/Mahler-transform + analytic `seriesEval`** layer
     (`MeasureR`, `mahlerK`/`mahlerTransform`, `seriesEval`, `phiSeries`) — and
     ultimately a **p-adic L-function** `L_p` (which mathlib entirely lacks) — to
     mathlib at all? If **no**, this theorem is settled as *project-local, not
     mathlib-bound* (keep it where it is) and no further action is needed. If
     **yes**, proceed to Q2–Q5.
  2. **Right grain for the trace.** Given that the *general* trace identity is
     already the project lemma `sum_seriesEval_mahlerK` (over an arbitrary
     `μ : MeasureR K ℤ_[p]`, `FormalPsi.lean:1072`), is **that** general lemma
     (plus `seriesEval_phi_at_root`) the intended mathlib contribution, with the
     present Gauss-cleared `ρ_θ`/`F̃_θ` pin staying project-internal as a
     specialisation? (Yes ⇒ this specific theorem is *not* a mathlib target; the
     upstream work moves to `sum_seriesEval_mahlerK`, assessed separately.)
  3. **`seriesEval` vs mathlib evaluation.** For any upstreaming, should the
     analytic evaluation be the project's bespoke `seriesEval`
     (`∑' n, coeff_n F · zⁿ`), or reformulated against mathlib's existing
     `PowerSeries.eval₂`/`HasEval` evaluation framework
     (`RingTheory/PowerSeries/Evaluation.lean`) where applicable? (This decides
     whether the contribution is "new `seriesEval` API" or a `HasEval`-based
     restatement.)
  4. **Statement packaging.** If a value/mass-extraction identity is upstreamed,
     is the Gauss-cleared `p·(·) = G⁻¹·(p·(·) − Σ(·))` packaging (with
     `rhoTheta`/`Ftilde`/`G` baked in) the right form, or should it be the
     abstract operator-kernel statement ("the constant of `W` with
     `(1+T)∂W = φB` is recovered as `p⁻¹·Σ W(ξ^i−1)`") decoupled from the
     specific `ρ_θ`/`F̃_θ`/Gauss instances? (The latter would coincide with the
     §7 sibling's abstract pin — one shared lemma, not two specialisations.)
  5. **Naming + dedup with the §7 twin.** The name
     `p_mul_constantCoeff_mahlerK_rhoTheta` encodes project-specific objects
     (`mahlerK`, `rhoTheta`) and is the §6.2 analog of the §7
     `p_mul_constantCoeff_mahlerK_rhoA`. If anything graduates, what is the
     intended mathlib-namespaced name, and should the two be **unified** into one
     abstract operator-kernel lemma (per Q4) rather than upstreamed as two
     near-duplicate pins?

**Refactor-actionable detail (interim, until the questions are answered).**
Treat the theorem as **project-local glue** in `ValuesAtOne.lean`, next to its
single consumer `LpFunction_one` (line 1594) — do **not** open a mathlib PR, and
do **not** inline it (its ~170-line proof at the one call site would only
obscure the value-formula theorem). The likely resolution, given the sibling
assessments (the §7 twin `p_mul_constantCoeff_mahlerK_rhoA` → BORDERLINE; the
`*_rhoA` def/coeff siblings → NO-composable; `sum_seriesEval_FtildeA`,
`one_add_mul_derivative_mahlerK_rhoA` → BORDERLINE) and the answers to Q1–Q2:
**not mathlib-bound** (the substrate is project-only; the general trace lemma
`sum_seriesEval_mahlerK`, not this specialisation, is the only plausible upstream
candidate, and only after the whole measure/Amice/p-adic-L layer is upstreamed).
A strong secondary action (Q4–Q5): **deduplicate against the §7 twin** by
extracting one abstract operator-kernel pin lemma that both §6.2 and §7
specialise — but that is a project-internal refactor decision, not a mathlib
move.

**Note on the rejected alternatives.**
- *Not `YES-add-as-is` / `YES-but-generalise-first`:* the statement cannot be
  phrased in mathlib (every object is project-only; mathlib has no p-adic
  L-function), and Phase 4b found 0 weakenings + no literature-standard target;
  the only "generalisation" nearby is a *different, already-existing* project
  lemma (`sum_seriesEval_mahlerK`), not a restatement of this one. (Verdicts-
  reference: do not treat literature absence as YES.)
- *Not `NO-mathlib-has-it`:* Phase 5 found nothing in mathlib to cite — the gate
  requires an existing mathlib decl, which does not exist (not even the headline
  Leopoldt value, let alone this pin).
- *Not `NO-composable-from-mathlib`:* this is a substantive ~170-line theorem;
  Phase 6 is NOT-COMPOSABLE, and the `NO-composable` gate's required ≤3-line
  mathlib composition sketch **cannot be honestly produced** (no mathlib
  vocabulary, no mathlib building blocks). Forcing this theorem into
  `NO-composable` would violate that gate; the honest bucket for "not
  mathlib-bound, but the call is a project-policy/grain judgment on a real
  theorem" is `BORDERLINE-needs-human` (exactly as for the §7 twin).

---

## Next step

Answer the five questions in Phase 7 (the gating one is Q1: do you intend to
upstream the RJW p-adic-measure / Amice-transform / `seriesEval` / p-adic-L
layer at all?), then re-run
`/mathlibable PadicLFunctions.MeasureR.p_mul_constantCoeff_mahlerK_rhoTheta` to
resolve. Expected resolution: **not mathlib-bound** — keep
`p_mul_constantCoeff_mahlerK_rhoTheta` project-local in `ValuesAtOne.lean` next
to its sole consumer `LpFunction_one`; if any upstreaming happens, the target is
the **general** trace lemma `sum_seriesEval_mahlerK` (assessed separately) — and,
per Q4–Q5, ideally a single abstract operator-kernel pin that **both** this §6.2
theorem and the §7 twin `p_mul_constantCoeff_mahlerK_rhoA` specialise — not this
Gauss-cleared `ρ_θ`/`F̃_θ` specialisation, and only after the underlying
p-adic-measure / Amice-transform substrate is itself upstreamed. No mathlib PR
and no call-site refactor in the interim.
