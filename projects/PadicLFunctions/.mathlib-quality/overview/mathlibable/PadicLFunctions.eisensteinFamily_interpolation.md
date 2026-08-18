# `/mathlibable` report — `PadicLFunctions.eisensteinFamily_interpolation`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-20. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> This is the **headline theorem of the file** (RJW §8, the Part-I closer): the coefficientwise
> interpolation `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` of the Λ-adic Eisenstein family by the
> p-stabilised Eisenstein series, for `k ≥ 4`. The *mathematics is canonical and central* —
> the Λ-adic Eisenstein family (Serre 1973, Hida, Wiles, Katz) whose **constant term is
> interpolated by the Kubota–Leopoldt p-adic L-function** and whose higher coefficients
> interpolate prime-to-`p` divisor sums is one of the foundational objects of Iwasawa theory.
> Yet every mechanical bucket fails its gate for the same reason that governed all of this
> file's siblings (`eisensteinFamily`, `twistedZetaHalf_moments`, `divisorMeasure_moment`,
> `unitsTwist`, …): the Lean statement lives **entirely on a substrate mathlib does not have**
> — the linear-functional p-adic measures `PadicMeasure := C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the
> Iwasawa algebra `Λ(ℤ_p^×)` and its total fraction ring `Q(ℤ_p^×) = QuotientField`, the
> pseudo-measure formalism, the Kubota–Leopoldt `padicZeta`, the x-twist, the divisor-sum
> measures, **and** the twisted-pseudo-measure *witness* encoding (erratum #11) in which the
> constant-coefficient leg is phrased. Mathlib has only the **rational value** `ζ(−k)`
> (`riemannZeta_neg_nat_eq_bernoulli` = the project's `zetaNeg`) and the generic `PowerSeries`/
> `FractionRing` plumbing. The theorem has **0 call sites anywhere** — it is the terminal
> result of the file. So it cannot be a ≤1-line specialisation of anything (NO-mathlib-has-it
> fails), it is not expressible — let alone composable — from mathlib primitives (NO-composable
> fails), it is STRICTLY NARROWER than the literature-standard Dirichlet/`𝒪_L` form (YES-add-as-is
> fails), and the "more general form" is *also* absent from mathlib so the move is "upstream an
> entire theory and then state the interpolation theorem", not a mechanical generalise-first
> (YES-but-generalise-first fails as the headline verdict). The decisive question — *should the
> whole RJW p-adic-measure / Kubota–Leopoldt / Eisenstein-family layer go to mathlib, and is the
> right headline this interpolation theorem, the family `eisensteinFamily`, or `padicZeta`
> itself; in the trivial-character or full Dirichlet generality; with or without the
> twisted-witness `½` encoding* — is exactly the project-policy / mathematical-taste judgment the
> skill routes to a human. The sibling reports name *this very theorem* as one of the candidate
> mathlib targets (`eisensteinFamily.md` Q2); deciding which is the headline is the human call.

---

### Baseline (Phase 0)

- lake build:                **build not re-run; reasoned from source** (per the task BUILD NOTE — `lake build` is stale/slow in this checkout; `.lake/build` artifacts predate today, mathlib is present at `.lake/packages/mathlib`). The declaration and its full dependency chain were read directly from source.
- decl `PadicLFunctions.eisensteinFamily_interpolation`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:378`
- kind:                       **theorem**
- has sorry:                  **no** — `grep -c sorry` is `0` for the target file *and* for its key dependency chain (`KubotaLeopoldt/ZetaP.lean`, `Measure/PseudoMeasure.lean`, `Measure/Basic.lean`). The proof and every lemma it invokes are complete (fleet-eligible work).
- module docstring summary:   "The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)" — the Kubota–Leopoldt pseudo-measure interpolates the *constant* coefficients of the p-stabilised Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`; the non-constant coefficients are interpolated by divisor-sums of Dirac measures; bundling coefficientwise gives the Λ-adic Eisenstein family `𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧` with `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}`. *This* theorem is that interpolation property (p-adic half).

---

### Statement (Phase 1)

`PadicLFunctions.eisensteinFamily_interpolation` is **a theorem** stating the following.

Let `p` be an odd prime and `k ≥ 4`. Let `𝐄 = eisensteinFamily = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`
be the Λ-adic Eisenstein family, with constant coefficient `A₀ = twistedZetaHalf = x·ζ_p/2`
(the x-twist of the Kubota–Leopoldt p-adic zeta pseudo-measure, halved) and higher coefficients
`A_n = divisorMeasure p n = Σ_{0<d∣n, p∤d} δ_d` (prime-to-`p` divisor-sum Dirac measures, embedded
into `Q(ℤ_p^×)` by `algebraMap`). The theorem asserts that applying the `(k−1)`-th moment functional
`∫_{ℤ_p^×} x^{k−1}·(−)` coefficientwise recovers the p-stabilised Eisenstein coefficient sequence
`stabilisedCoeff p k`, i.e. **`∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}`** (RJW Thm 8.2(b)/Def 8.1). It is
stated as a **conjunction of two legs**:

* **Constant-coefficient leg (`n = 0`)** — in the twisted-pseudo-measure *witness* encoding (because
  `A₀` is not literally a pseudo-measure — erratum #11): for every auxiliary unit `b ∈ ℤ_p^×` and
  every witness `ν ∈ Λ(ℤ_p^×)` of `(b·δ_b − 1)·A₀ ∈ Λ` (i.e. the twisted denominator `(b·[b]−[1])`
  clears `A₀` into the Iwasawa algebra), the `(k−1)`-th moment of `ν` equals
  `(b^k − 1) · stabilisedCoeff p k 0 = (b^k − 1)·(1 − p^{k−1})·ζ(1−k)/2` in `ℚ_p`. The factor
  `(b^k − 1)` is the moment of the twisted denominator.

* **Higher-coefficient leg (`n ≠ 0`)** — for every `n ≥ 1`, the `n`-th `PowerSeries` coefficient of
  `𝐄` is `algebraMap _ _ (divisorMeasure p n)`, *and* its `(k−1)`-th moment equals
  `stabilisedCoeff p k n = σ^p_{k−1}(n) = Σ_{0<d∣n, p∤d} d^{k−1}` in `ℚ_p`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic (section variable).
- `hp2 : p ≠ 2` — odd prime (needed for the `/2` in `A₀`: `2` is a unit of `ℤ_p` iff `p` is odd).
- `{k : ℕ}` with `hk : 4 ≤ k` — the weight; `k − 1` is the moment exponent.
- (universally quantified in the body) `b : ℤ_[p]ˣ`, `ν : PadicMeasure p ℤ_[p]ˣ`, `n : ℕ`.

Hypotheses (Lean side): `hp2 : p ≠ 2`, `hk : 4 ≤ k`, plus per-leg local hypotheses (the witness
equation `hν` and `hn : n ≠ 0`).

Conclusion (math): the coefficientwise p-adic interpolation `∫x^{k−1}·𝐄 = E_k^{(p)}` (RJW Thm 8.2(b)),
split into the constant-term leg (witness-encoded) and the higher-coefficient leg.

Conclusion (Lean): a conjunction
```
(∀ b ν, algebraMap _ (QuotientField p) ((b:ℤ_[p]) • dirac p b − 1) * constantCoeff (eisensteinFamily p hp2) = algebraMap _ _ ν →
   ((ν (unitsPowCM p (k−1)) : ℤ_[p]) : ℚ_[p]) = ((b:ℚ_[p])^k − 1) * ((stabilisedCoeff p k 0 : ℚ) : ℚ_[p]))
∧ ∀ n, n ≠ 0 →
   coeff n (eisensteinFamily p hp2) = algebraMap _ _ (divisorMeasure p n)
   ∧ ((divisorMeasure p n (unitsPowCM p (k−1)) : ℤ_[p]) : ℚ_[p]) = ((stabilisedCoeff p k n : ℚ) : ℚ_[p]).
```

**Objects this statement is built from (all project-local except where noted):**
- `PadicMeasure p X` — an `abbrev` for `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the *linear-functional* notion
  of a p-adic measure (RJW Def 3.6; `Measure/Basic.lean:52`). **Not** mathlib's `MeasureTheory.Measure`.
  **Not in mathlib.**
- `PadicMeasure.QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` — the total fraction ring
  `Q(ℤ_p^×)` of the Iwasawa algebra `Λ(ℤ_p^×)` (RJW Def 3.34; `Measure/PseudoMeasure.lean:804`).
  **Not in mathlib.**
- `PadicMeasure.dirac`, `PadicMeasure.unitsPowCM p k` (the continuous map `u ↦ u^k`, the moment
  test function), the convolution `CommRing` structure on `PadicMeasure p ℤ_[p]ˣ`, the pseudo-measure
  predicate `IsPseudoMeasure`, `padicZeta`, the x-twist `unitsTwist`/`quotientTwist`,
  `twistedZetaHalf`, `divisorMeasure`, `sigmaP`, `eisensteinFamily`, `stabilisedCoeff` — **all
  project-local. None in mathlib.**
- `zetaNeg k := (−1)^k · bernoulli(k+1)/(k+1)` (`KubotaLeopoldt/ZetaValues.lean:17`) — the *rational*
  value `ζ(−k)`. Mathlib **does** have this value as `riemannZeta_neg_nat_eq_bernoulli`
  (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`); the project keeps a rational copy to
  avoid importing complex analysis into the main chain.
- `PowerSeries.mk` / `PowerSeries.coeff` / `PowerSeries.constantCoeff` / `algebraMap` /
  `IsFractionRing.injective` — **generic mathlib infrastructure** (used in the proof, but generic).

Proof body (≈10 lines): `refine ⟨fun b ν hν => ?_, fun n hn => ⟨?_, ?_⟩⟩` — then the constant-term
leg unfolds `constantCoeff (eisensteinFamily …) = twistedZetaHalf` (by `rfl`), rewrites by the sibling
lemma `twistedZetaHalf_moments` and `stabilisedCoeff` at `n=0` (`push_cast; ring`); the
higher-coefficient legs rewrite `eisensteinFamily`/`PowerSeries.coeff_mk` (the `coeff` claim, `if_neg`)
and `divisorMeasure_moment`/`stabilisedCoeff` at `n≠0` (the moment claim, `push_cast; rfl`). So the
theorem is the **bundling of two already-assessed legs** — `twistedZetaHalf_moments` (BORDERLINE) and
`divisorMeasure_moment` (BORDERLINE) — over the `eisensteinFamily` def (BORDERLINE), with the bridge
sequence `stabilisedCoeff` (YES-but-generalise-first as a *standalone rational sequence*).

---

### Size classification (Phase 2a)

Verdict: **BIG**.
Reason: this is **the main result of the file** — the module docstring's headline ("`∫_{ℤ_p^×}
x^{k−1}·𝐄 = E_k^{(p)}` for even `k ≥ 4`", "RJW Theorem at TeX 2399") *is* this theorem; its docstring
opens "**RJW §8 Theorem (TeX 2399–2407), p-adic half**". It is a named, headline result of the
project's Part-I closer, formalising a theorem named after the Serre/Kubota–Leopoldt/Hida–Wiles
construction — per the skill's BIG criteria, "basically guaranteed to be in or near the literature in
some form" (and it is — see Phase 3).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for the report's framing.)

### One-line check (Phase 2b)

Body line count: ≈10 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.** (The one-line def exemption analysis does
not apply to a proof; the section is skipped.)

---

### Literature search table — EXHAUSTIVE protocol

The mathematical concept is **the Λ-adic / p-adic Eisenstein family and its coefficientwise
interpolation property**: the family of measures `𝐄 = Σ A_n qⁿ` on `ℤ_p^×` whose `(k−1)`-th moments
recover the q-expansion of the p-stabilised Eisenstein series `E_k^{(p)}`, with **constant term
interpolated by the Kubota–Leopoldt p-adic zeta function** and higher coefficients interpolating
prime-to-`p` divisor power sums `σ^p_{k−1}`. This is Serre's 1973 bootstrap, made into a Λ-adic family
by Hida and Wiles (GL(2)/ℚ) and Katz. The project's substrate objects are searched as context.

| #  | Channel                          | Query                                                                                                                              | Hit? | Standard form found                                                                                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Lambda-adic Eisenstein family p-stabilised Eisenstein series interpolation moment integral x^{k−1} constant term Kubota-Leopoldt p-adic zeta" | yes  | The Λ-adic Eisenstein family; **its constant term is interpolated by the p-adic L-function of Kubota–Leopoldt / Deligne–Ribet**; "natural generalisation of the ordinary Λ-adic Eisenstein series constructed by **Hida and Wiles for GL(2)/ℚ**"; the p-stabilisation `E* = E − χ(p)p^{k−1}E(pz)` has prime-to-`p` divisor-sum Fourier coefficients. | Kawamura (arXiv:1207.0198/2302.13009), Rockwood (Warwick slides), Dasgupta ("evil Eisenstein"). The interpolation `∫x^{k−1}·family = E_k^{(p)}` is the defining property; the constant term = the Kubota–Leopoldt zeta is textbook. |
|  2 | WebSearch (general form / mechanism) | "p-adic Eisenstein measure family coefficientwise interpolation E_k^{(p)} integral measure on Z_p^times Serre 1973 bootstrap constant term p-adic zeta" | yes  | "Eisenstein measure … interpolates p-adically the Fourier expansion of Eisenstein series"; "families of measures on **ℤ_p^×**"; "these measures specialise … to **p-adic L-functions interpolating L-values**". | Eischen (arXiv:1302.7229), Bannai–Kobayashi (Eisenstein–Kronecker, 1912.03657/2412.11332), Darmon–Rotger. Confirms the general mechanism: an Eisenstein *measure* whose moments recover Fourier coefficients and whose constant term is the p-adic L-function. |
|  3 | WebSearch (named-after / the exact source) | "Rodrigues Jacinto Williams introduction p-adic L-functions Eisenstein family theorem constant coefficient x times zeta_p divisor measures section 8" | yes  | **The exact source**: RJW *An introduction to p-adic L-functions*, **§8 "The p-adic family of Eisenstein series"**, published in *Essential Number Theory* 4(1), 2025 (and arXiv:2309.15692v2, 19 Dec 2024). | The notes are built on Kubota–Leopoldt's measure-theoretic p-adic interpolation; §8 is the Eisenstein-family closer. **This is the declaration's exact source** (the file cites "RJW §8, TeX 2361–2446"). |
|  4 | ChatGPT MCP                      | (intended: "standard form of the Λ-adic Eisenstein family interpolation theorem, its generality, and historical evolution")        | n/a  | —                                                                                                                    | **n/a — ChatGPT MCP not callable in this harness** (`ToolSearch` for `chatgpt`/`chatgpt-math__ask` returns no callable tool; only OAuth-gated unrelated MCPs are exposed; consistent with every sibling report in this project). Over-compensated with extra WebSearch passes (#1–#3) and the authoritative source identification (RJW §8) + the standard secondary literature (Hida, Wiles, Serre, Katz, Eischen). |
|  5 | Local references                 | `ls`/grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                                       | n/a  | (directories absent)                                                                                                 | **n/a — neither directory exists on this checkout** (confirmed by `ls`). The canonical source is nonetheless pinned: **RJW, arXiv:2309.15692 §8**, cited by TeX line throughout the module docstring. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/p-adic+modular+form`                                                                                | partial | nLab has **p-adic modular form** (Serre: a power-series limit of modular forms; Katz: sections on the ordinary locus) — the ambient concept — but **no** named "Eisenstein-family interpolation theorem", no measures on `ℤ_p^×`, no Kubota–Leopoldt constant-term statement. | The family concept's *ambient setting* is on nLab; the specific interpolation theorem is not isolated there. Recorded so the channel is not silently skipped. |
|  7 | nCatLab (if categorical)         | (the interpolation property is an analytic/measure-theoretic identity, not a categorical universal construction)                    | n/a  | —                                                                                                                    | n/a — not a categorical concept; it is a coefficientwise special-value interpolation identity. Covered by #1–#3. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                                                  | n/a  | —                                                                                                                    | n/a — not an algebraic-geometry / scheme-theoretic concept (p-adic L-function / Eisenstein-measure special values). |
|  9 | MathOverflow / Math.StackExchange| "p-stabilization Eisenstein series q-expansion coefficients prime to p"; "constant term p-adic Eisenstein family = p-adic zeta"     | yes (via arXiv/expository) | Same shape: divisors `d∣n` with `gcd(d,p)=1` give p-adically convergent `d^{k−1}`; the constant term of the p-adic Eisenstein family ∈ Λ equals the Kubota–Leopoldt zeta; the moments recover the Fourier coefficients. | Dasgupta's "evil Eisenstein" notes, the Eigenbook (Bellaïche), ahilado expository post. Confirms the "constant term of the Eisenstein family = p-adic zeta = Iwasawa-algebra element" framing the project formalises. |
| 10 | recent arXiv (last 5 years)      | arXiv:2309.15692 (RJW, the source) + 1207.0198/2302.13009 (Kawamura, p-stabilised Siegel Eisenstein + interpolation) + 1302.7229 (Eischen, p-adic Eisenstein measure) + 2412.11332 (Eisenstein–Kronecker p-adic interpolation, 2024) | yes  | RJW §8: `E_k^{(p)} = (1−p^{k−1})ζ(1−k)/2 + Σ σ^p_{k−1}(n)qⁿ`; the family `𝐄 = Σ A_n qⁿ`, `A₀ = xζ_p/2`, `∫x^{k−1}·𝐄 = E_k^{(p)}`. Kawamura/Eischen: the higher-rank and measure-valued generalisations. | The exact source (RJW §8) plus the active modern research line (Eischen, Kawamura, Bannai–Kobayashi) confirming this is a live, central, generalisable object — not a dead corner. |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (the specific Λ-adic
family interpolation form; the general Eisenstein-measure / Serre-bootstrap mechanism; the named-after /
exact-source RJW §8); the ChatGPT-MCP row is honestly recorded n/a (tool genuinely uncallable in this
harness) with compensating WebSearch + authoritative source identification noted; local refs checked
(absent → n/a, source pinned); nLab checked (ambient concept present, specific theorem absent —
recorded); nCatLab/Stacks recorded n/a with reasons; MathOverflow/SE perspective captured; recent arXiv
located the source paper and the active generalisation literature.

### Literature summary (Phase 3)

Concept identified as: **the (Λ-adic / p-adic) Eisenstein family and its coefficientwise interpolation
property** — the family of measures `𝐄 = Σ_{n≥0} A_n qⁿ` on `ℤ_p^×` whose `(k−1)`-th moments recover the
q-expansion of the p-stabilised Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`, with **constant
term `A₀ = x·ζ_p/2` interpolated by the Kubota–Leopoldt p-adic zeta** and higher coefficients `A_n` the
prime-to-`p` divisor-sum measures interpolating `σ^p_{k−1}(n)`. This is **Serre's 1973 bootstrap**
(interpolating the non-constant coefficients forces interpolation of the constant term = the p-adic
zeta), made into a Λ-adic family by **Hida and Wiles** for GL(2)/ℚ and **Katz**; the project's exact
source is **RJW §8** (arXiv:2309.15692, Essential Number Theory 2025), Def 8.1 + Thm 8.2.

Sources agree on the standard form: **yes** — uniformly across the literature (Serre, Kubota–Leopoldt,
Hida, Wiles, Katz, Eischen, Kawamura, and the RJW source notes). The interpolation
`∫x^{k−1}·𝐄 = E_k^{(p)}`, the constant term `(1−p^{k−1})ζ(1−k)/2`, and the prime-to-`p` divisor-sum
higher coefficients are textbook canonical; `ζ(−k) = (−1)^k B_{k+1}/(k+1)` is the standard Bernoulli
identity (mathlib's `riemannZeta_neg_nat_eq_bernoulli`).

Most general standard form: the family interpolation over **arbitrary Dirichlet nebentypus `χ` of
p-power conductor** (RJW §5/§8; Hida–Wiles; Kawamura: "various nebentypus characters"), with
coefficients valued in a general coefficient ring `𝒪_L` and over higher-rank groups (Eischen, Kawamura:
Siegel Eisenstein for `Sp_{2n}`). The trivial-character GL(2)/ℚ case formalised here is the base case.

Generality dimensions where the literature varies:
- **The nebentypus character.** Most general: arbitrary Dirichlet `χ` of p-power conductor (the
  family interpolates `L(χ, 1−k)` in the constant term). Here: the trivial character (Eisenstein /
  `ζ`). The project's Dirichlet-twist development is the separate `Interpolation/` files.
- **The group / rank.** Most general: Siegel Eisenstein for `Sp_{2n}` / unitary groups (Kawamura,
  Eischen). Here: GL(2)/ℚ (classical elliptic Eisenstein series).
- **The carrier / encoding of "measure" and "moment".** Classical / mathlib: a σ-additive
  `MeasureTheory.Measure` and `∫ x^{k−1} dμ`. RJW / Iwasawa theory (this project): a *measure is a
  bounded `ℤ_[p]`-linear functional* `C(ℤ_p^×, ℤ_[p]) →ₗ ℤ_[p]`, the moment is `μ(unitsPowCM (k−1))`,
  and the family lives in `Q(ℤ_p^×)⟦q⟧`.
- **The constant-term encoding.** Because `A₀ = x·ζ_p/2` is not literally a pseudo-measure (erratum
  #11), the constant-term leg is phrased through the *twisted witness* `ν` of `(b·[b]−[1])·A₀ ∈ Λ`,
  introducing the `(b^k−1)` factor — the same device RJW use for `ζ_p` itself.

Disagreement with the literature: **none**. The Lean statement is a faithful, correct realisation of
RJW Thm 8.2(b)/Def 8.1 (the coefficientwise interpolation, p-adic half), with the project's documented
correction (erratum #11: the constant-term witness is twisted because `A₀` is not literally a
pseudo-measure). The evenness/`k ≥ 4` restriction is carried for the *complex* identification of
`stabilisedCoeff` with the q-expansion of `E_k^{(p)}` (`EisensteinComplex.lean`); the p-adic legs here
need only `0 < k`.

---

### Generality analysis — `PadicLFunctions.eisensteinFamily_interpolation`

Literature-standard form (from Phase 3): the Λ-adic Eisenstein-family interpolation
`∫x^{k−1}·𝐄_χ = E_{k,χ}^{(p)}` over arbitrary Dirichlet `χ` of p-power conductor (and over higher-rank
groups / general coefficient rings `𝒪_L`), with constant term the Kubota–Leopoldt / Deligne–Ribet
p-adic L-function `L_p(χ)`. The trivial-character, GL(2)/ℚ, `ℤ_[p]`-coefficient case formalised here is
the base case.

| # | Parameter / hypothesis                | Current Lean form                                  | Literature-standard form                                  | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------------------------------|-----------------------------------------------------------|---------------------|---------------------------------|
| 1 | `hp2 : p ≠ 2`                        | odd prime                                          | the `/2` in the Eisenstein constant term needs `2` invertible | NO (essential)      | `A₀ = x·ζ_p/2`; `2` must be a unit of `ℤ_p`, i.e. `p ≠ 2`. Intrinsic to the *halved* Eisenstein constant term, not artificial. |
| 2 | `hk : 4 ≤ k`                         | weight `k ≥ 4`                                     | RJW §8 states the family for even `k ≥ 4`                  | partial             | The **p-adic legs here only use `0 < k`** (the proof feeds `0 < k` into `twistedZetaHalf_moments`/`divisorMeasure_moment`; `4 ≤ k` is carried only to match the complex identification). A `0 < k` version is mechanically available — but it is a *project-internal* weakening of a project theorem, not a step toward a mathlib form. |
| 3 | the value (trivial-character `ζ`)    | `(1−p^{k−1})ζ(1−k)` / `σ^p_{k−1}`                  | arbitrary Dirichlet `χ`: `L(χ,1−k)` / `σ^p_{k−1,χ}` (RJW §5) | yes (large)         | The Dirichlet-twisted family is the literature's fuller form — but it is a *different, larger development* (the project's `Interpolation/` files), not a signature weakening of *this* theorem. |
| 4 | carrier `PadicMeasure`/`QuotientField`, GL(2)/ℚ | `ℤ_[p]`-linear-functional measures, classical elliptic Eisenstein | `𝒪_L`-valued measures; Siegel/unitary Eisenstein (`Sp_{2n}`) | yes (deferred / large) | The general-`𝒪_L` and higher-rank cases are separate large developments (Kawamura, Eischen); the project defers general `𝒪_L` (`Measure/Basic.lean` docstring). Not available now. |

**The decisive fact, not a row above:** the literature object *and all of its narrower/general forms*
live on a substrate **mathlib does not have** — there is no Iwasawa-algebra-of-measures, no
`QuotientField`, no `padicZeta`, no pseudo-measure formalism, no p-adic Eisenstein family in mathlib
(Phase 5). So the generality question is moot for a *direct* mathlib contribution: one cannot restate
`eisensteinFamily_interpolation` in *any* mathlib-shippable form without first upstreaming the entire
RJW §3–§4 + §8 measure / zeta / family tower.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (trivial character vs. Dirichlet `L(χ,1−k)`;
`4 ≤ k` vs. the `0 < k` the p-adic proof actually needs; `ℤ_[p]`/GL(2)/ℚ vs. general `𝒪_L`/Siegel).
Number of weakening opportunities found: 1 cheap project-internal one (`4 ≤ k` → `0 < k`); 3 large ones
(Dirichlet twist; general `𝒪_L`; higher rank) that are *separate developments*, not regeneralisations
of this theorem.
Proposed restatement (if one pursued the cheap one *within the project*): drop `hk : 4 ≤ k` to `0 < k`,
since both legs only feed `0 < k` to the moment lemmas. But this changes a *project* theorem to be
marginally more general; it does **not** produce a mathlib-shippable statement, because the carrier
objects remain absent from mathlib.
Cost of restatement: **CHEAP** (mechanical) for the `k` weakening *within the project*; **EXPENSIVE /
not-applicable** as a mathlib contribution (substrate must be upstreamed first; the Dirichlet/`𝒪_L`/
higher-rank generalisations are large independent developments).

Because the form is STRICTLY NARROWER, a naive reading might push toward `YES-but-generalise-first` —
**but the verdict gate forbids that here**: Phase 5 shows the general form (and the carrier algebra
itself) are *also* absent from mathlib, so the move is "upstream an entire theory", not "generalise this
theorem". That is a project-policy judgment → Phase 7 = BORDERLINE.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                     | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                          | no       | —                                                                                      | Hypotheses are already minimal (`Fact p.Prime`, `p ≠ 2`, `4 ≤ k`); nothing to class-ify. |
|  2 | sequences/metric → filters/topological?                                                                      | no       | —                                                                                      | No limit/convergence content in *this* statement; it is an algebraic coefficientwise moment identity over `Q(ℤ_p^×)⟦q⟧`. (The genuine "interpolation as a p-adic limit / no-measure-interpolates-p^k" content lives in `noMeasure_interpolates_pPow`, not here.) |
|  3 | construct an object where a universal-property class would characterise it?                                  | partial  | the p-adic L-function / Eisenstein measure is often *characterised* by its interpolation property (a universal/defining property) rather than constructed | This is the one genuinely interesting modern-idiom angle: mathlib might want a "p-adic measure characterised by its moments" abstraction. **But** this presupposes the entire `PadicMeasure`/Iwasawa-algebra substrate exists in mathlib first; there is no mathlib downstream to compose with today. So it is a *future* organisational question for the upstreamed theory, not a Phase-4c modernisation of *this* theorem in isolation. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                                       | no       | —                                                                                      | No substructure involved. |
|  5 | vector-space/metric/field-specific → weaken to modules/(semi)ring?                                           | partial  | the `𝒪_L`-valued / Dirichlet / higher-rank generalisations (rows 4a #3,#4)             | These are *separate larger developments* over the *same non-mathlib substrate*; there is no mathlib downstream to compose with, so this is not a Phase-4c modernisation of *this* theorem. |
|  6 | 1-categorical → higher/∞-categorical?                                                                         | no       | —                                                                                      | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structures?                                              | no       | —                                                                                      | The weight `k` and the rational value `ζ(1−k)` are intrinsically arithmetic; generalising removes the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a mathlib contribution today).
Reason: the only genuine modernisation angle (row 3: characterise the measure/L-function by its
interpolation property, à la a universal property) — and the larger generalisations (Dirichlet,
`𝒪_L`, higher rank) — are all stated over the project's `PadicMeasure`/`QuotientField` substrate, which
is itself not in mathlib. There is no contemporary mathlib idiom that turns *this* theorem into a
better *mathlib* theorem without first upstreaming the whole "p-adic measure = continuous dual + Iwasawa
algebra + pseudo-measure" framework — a separate, much larger question (see Phase 7). This rules out the
"YES-but-generalise-first via MODERN-IDIOM" path: there is no concrete mathlib downstream to point at.

---

### Diamond / defeq risk — `PadicLFunctions.eisensteinFamily_interpolation`

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search paths are
introduced by a proof; Phase 4.5 is skipped per the skill's scope rule.)

### Risk verdict (Phase 4.5)

Overall risk: **n/a (theorem)**.

---

### Mathlib search-status: `PadicLFunctions.eisensteinFamily_interpolation`

[A] Lean-Finder       "Lambda-adic Eisenstein family interpolation p-adic zeta constant term measure moments"   **n/a** — no Lean MCP / Lean-Finder server callable this session (confirmed: `ToolSearch` for `lean_loogle`/`lean_leansearch`/`lean_local_search`/`lean-finder` returns no callable deferred tool; only `WebSearch`/`WebFetch` plus unrelated OAuth MCPs are exposed). Substituted by authoritative direct grep over the *local pinned* mathlib [D] + name-pattern [E] + the Phase-3 literature search.
[B] Loogle           `(FractionRing _)⟦X⟧`, `PowerSeries (FractionRing _)`, `_ →ₗ[ℤ_[p]] ℤ_[p]` moment patterns   **n/a** — server uncallable this session. The structural search is covered by [D]/[E]: mathlib has no "measure = `C(X,ℤ_[p]) →ₗ ℤ_[p]` functional", no fraction ring of such an algebra, no power series of such, and no p-adic Eisenstein family.
[C] LeanSearch       "p-adic Eisenstein family interpolates p-stabilised Eisenstein series; constant term is the Kubota–Leopoldt p-adic zeta"   **n/a** — server uncallable this session; question fully covered by [D] + the Phase-3 web/source search.
[D] Grep mathlib src  terms tried: `kubota`, `leopoldt`, `p-adic zeta`, `padic.*zeta`, `pseudoMeasure`/`pseudo-measure`/`isPseudoMeasure`, `Iwasawa`, `EisensteinFamily`/`eisensteinFamily`/`Eisenstein measure`, `padicLFunction`/`p-adic L-function`, `interpolat`, `stabilis`/`stabiliz`, `riemannZeta_neg_nat`, `divisorMeasure`, `unitsPowCM`   **see below**
[E] Name pattern      `eisensteinFamily`, `eisensteinFamily_interpolation`, `twistedZetaHalf`, `divisorMeasure`, `padicZeta`, `QuotientField`, `unitsPowCM`, `PadicMeasure`, `stabilisedCoeff`, `sigmaP`, `zetaNeg`   exist **only** in this project; zero mathlib hits.

Searched for both:
- the user's current form (the coefficientwise interpolation of `eisensteinFamily` in the twisted-witness
  encoding) — **no mathlib hit** (every object is project-local).
- the literature-standard form (the Λ-adic Eisenstein family; its interpolation; the constant term as the
  Kubota–Leopoldt p-adic zeta; the Dirichlet/higher-rank generalisations) — **also no mathlib hit**:
  - `grep -rniE "kubota|leopoldt|p-adic zeta|pseudomeasure|pseudo-measure|isPseudoMeasure"` over all of
    `Mathlib/` returns **nothing**. Mathlib has **no** Kubota–Leopoldt / p-adic zeta / pseudo-measure.
  - `grep "Iwasawa"` finds only `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` (the **Iwasawa
    decomposition** simplicity criterion — unrelated) and `MulAction.IwasawaStructure`. No Iwasawa
    *algebra* / algebra of measures.
  - `grep -riE "eisenstein.*(famil|measure|p-adic|stabilis)|interpolat"` over `Mathlib/NumberTheory/`
    returns nothing relevant — mathlib has classical complex Eisenstein series
    (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/*`, with `riemannZeta`-factor q-expansions)
    but **no** p-adic side, **no** p-stabilisation, **no** family, **no** interpolation.
  - **What mathlib DOES have (the RHS ingredient only):** `riemannZeta_neg_nat_eq_bernoulli`
    (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`): `riemannZeta (−k) = (−1)^k
    bernoulli(k+1)/(k+1)` — equal to the project's `zetaNeg k` **exactly**. But this is the
    *complex/rational value* `ζ(−k)`, **not** the p-adic *interpolation* of that value by a family of
    measures on `ℤ_p^×`, and certainly not the coefficientwise interpolation theorem over `PadicMeasure`.
  - The generic plumbing the proof uses (`PowerSeries.mk`, `PowerSeries.coeff_mk`,
    `PowerSeries.constantCoeff`, `algebraMap`, `IsFractionRing.injective`, `push_cast`, `ring`) **is** in
    mathlib — but it is generic, not this statement.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form).
Mathlib has the *rational value* `ζ(−k)` (`riemannZeta_neg_nat_eq_bernoulli` = `zetaNeg`) but **neither**
the Kubota–Leopoldt p-adic zeta, **nor** the pseudo-measure formalism, **nor** the `PadicMeasure`/
`QuotientField` carrier, **nor** any p-adic / Λ-adic Eisenstein family, **nor** the coefficientwise
interpolation identity over them.

---

### Call sites — `PadicLFunctions.eisensteinFamily_interpolation`

Internal use count: **K = 0** (within the project, NOT counting the declaring file). A repo-wide
`grep -rn "eisensteinFamily_interpolation" projects/ --include="*.lean"` returns only the declaration
at `EisensteinFamily.lean:378` and one *prose mention* in a docstring at `EisensteinFamily.lean:355`
(`stabilisedCoeff`'s docstring naming it as the pivot's p-adic consumer). There are **no call sites
anywhere** — it is the **terminal main theorem** of the file.
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                                            |
|--------------------------------|----------------------------------------------------------------------------------------------|
| (none)                         | terminal result — no consumers                                                               |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`eisensteinFamily_interpolation`?): **(none)** — no other site re-derives the coefficientwise
interpolation. (Its two legs are the separate lemmas `twistedZetaHalf_moments` / `divisorMeasure_moment`,
each used once *inside this theorem*; the complex companion `hasSum_stabilisedEisenstein` in
`EisensteinComplex.lean` is the *other* half of the pivot, not a re-derivation of this one.)

What this tells us: `K = 0` is the expected signature of a **headline / terminal theorem** — it is the
*output* of the project's Part-I closer, not an API lemma that downstream code calls. This is the
"genuinely-new, terminal main result" case from the call-sites table (NOT the "dead code" case: it is the
documented headline of the file, the realisation of RJW Thm 8.2(b)). For a *mathlib* verdict, `K = 0`
plus terminal-headline status means: this is a candidate *public-facing theorem to upstream*, not an
inline-able wrapper — but only as part of upstreaming its whole foundation. It does not lean toward
NO-composable on the call-site signal; it leans toward "the value, if any, is the theorem itself, pending
the foundation decision".

### Composition check (Phase 6)

Can `eisensteinFamily_interpolation` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: assemble from a hypothetical mathlib p-adic-Eisenstein-family interpolation lemma + the
Bernoulli value.
  - Mathlib decls used: `riemannZeta_neg_nat_eq_bernoulli` (for `ζ(−k)`), and *would-be*
    family/moment lemmas.
  - Result: **fails** — mathlib has the rational value `ζ(−k)` but **no** p-adic interpolation lemma, **no**
    `eisensteinFamily`, **no** `twistedZetaHalf_moments`/`divisorMeasure_moment` engine, **no**
    `QuotientField`/`unitsPowCM`/`PadicMeasure` carrier. The statement is not even *expressible* via
    mathlib decls (its LHS is application of a `ℤ_[p]`-linear functional to a moment test function, in the
    twisted-witness encoding, with no mathlib counterpart).

Attempt 2: derive it as the bundling of the project's own `twistedZetaHalf_moments` +
`divisorMeasure_moment` + `eisensteinFamily`/`stabilisedCoeff` unfolds (the actual ≈10-line proof).
  - Mathlib decls used: only generic plumbing (`PowerSeries.coeff_mk`, `PowerSeries.constantCoeff`,
    `algebraMap`, `push_cast`, `ring`, `rfl`).
  - Result: **partial / not a mathlib composition.** This *is* the real proof, but every substantive step
    is a **project** lemma (`twistedZetaHalf_moments`, `divisorMeasure_moment`) over project objects
    (`eisensteinFamily`, `twistedZetaHalf`, `divisorMeasure`, `stabilisedCoeff`, `QuotientField`,
    `unitsPowCM`, `PadicMeasure`). Stripped of the project objects there is no statement left. This is
    "our form is a short proof *over project objects* bundling two project lemmas + generic plumbing",
    **not** "compose mathlib primitives to get our form". And it is ≥4 substantive moves (two legs ×
    rewrite-by-moment-lemma + the `coeff`/`constantCoeff` unfolds + `push_cast`/`ring`), exceeding the
    3-call composition bar even setting aside the project-object problem.

Conclusion: **NOT-COMPOSABLE from mathlib** (in the sense relevant to a mathlib verdict). Mathlib does
not contain the objects the statement names, nor the moment lemmas it bundles; the proof's mathlib
content is generic power-series / fraction-ring / `ring` plumbing only. This cannot be inlined into
mathlib at all, because the statement and its call site live in a project-specific construction over a
project-specific substrate.

---

## Verdict: `PadicLFunctions.eisensteinFamily_interpolation`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the result is the **canonical** coefficientwise interpolation property of
  the Λ-adic / p-adic Eisenstein family — `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}`, with constant term
  interpolated by the Kubota–Leopoldt p-adic zeta and higher coefficients interpolating prime-to-`p`
  divisor sums (Serre 1973 bootstrap; Hida–Wiles for GL(2)/ℚ; Katz; RJW §8 Def 8.1 + Thm 8.2). Confirmed
  by three independent web channels, the authoritative source identification (RJW arXiv:2309.15692,
  Essential Number Theory 2025), nLab (ambient p-adic-modular-form concept), and the active modern
  generalisation literature (Eischen, Kawamura). No universally-named *standalone* theorem corresponds to
  this exact (twisted-witness, halved, trivial-character, GL(2)/ℚ) Lean statement; it is RJW's §8 closer
  in the project's corrected (erratum #11) encoding.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — trivial character vs. Dirichlet
  `L(χ,1−k)`; `4 ≤ k` vs. the `0 < k` the p-adic legs actually need; `ℤ_[p]`/GL(2)/ℚ vs. general `𝒪_L`/
  Siegel. But the general forms are *separate larger developments over the same non-mathlib substrate*.
  Modern-idiom (4c): none for a mathlib contribution today (the one interesting angle — characterise the
  measure by its moments — presupposes the substrate exists in mathlib).
- Mathlib search (Phase 5): **not in mathlib** under either the user's form or the literature-standard
  form. Mathlib has the *rational value* `ζ(−k)` (`riemannZeta_neg_nat_eq_bernoulli` = `zetaNeg`) but
  **no** Kubota–Leopoldt p-adic zeta, **no** pseudo-measure formalism, **no** `PadicMeasure`/
  `QuotientField` carrier, **no** p-adic Eisenstein family, **no** interpolation identity over them.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the statement names objects mathlib
  lacks and bundles two project-local moment lemmas; its mathlib content is generic plumbing only.
  **K = 0** call sites (terminal main theorem of the file), 0 external consumers, no inline re-derivation.

**Rationale (why BORDERLINE, not a clean bucket):**

`eisensteinFamily_interpolation` formalises a genuinely **canonical and central** theorem — the
coefficientwise interpolation of the Λ-adic Eisenstein family, *"the p-adic family of measures whose
moments recover the p-stabilised Eisenstein series, with constant term the Kubota–Leopoldt p-adic
zeta"* (RJW §8 Thm 8.2(b); Serre 1973; Hida–Wiles; Katz). It is the documented **headline of its file**
("RJW §8 Theorem (TeX 2399–2407), p-adic half"). Yet all four mechanical buckets fail their gates, for
the same reason that governed every sibling in this file (`eisensteinFamily`, `twistedZetaHalf_moments`,
`divisorMeasure_moment`, `unitsTwist`, `sigmaP`, `twistedZetaHalf`, …): the Lean statement lives
**entirely on a substrate mathlib does not have** — the linear-functional p-adic measures
`PadicMeasure := C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the Iwasawa algebra `Λ(ℤ_p^×)` and its total fraction ring
`Q(ℤ_p^×) = QuotientField`, the pseudo-measure predicate, the Kubota–Leopoldt `padicZeta`, the x-twist,
the divisor-sum measures, and the *twisted-pseudo-measure witness* encoding (erratum #11) in which the
constant-coefficient leg is phrased. **NO-mathlib-has-it** is wrong: Phase 5 found mathlib has only the
*rational value* `ζ(−k)`, none of the carrier objects nor the family nor the interpolation engine, so
there is no ≤1-line specialisation. **NO-composable-from-mathlib** is wrong: Phase 6 is NOT-COMPOSABLE —
the statement is not expressible over mathlib, and the proof's substance is two project lemmas
(`twistedZetaHalf_moments`, `divisorMeasure_moment`) bundled over project objects (and it exceeds the
3-call bar anyway). **YES-add-as-is** is wrong: Phase 4 is STRICTLY NARROWER (Dirichlet twist / general
`𝒪_L` / higher rank / the `0<k` weakening are all available), and — decisively — the theorem sits atop
the entire RJW §3–§4 + §8 prerequisite tower (`PadicMeasure`, `Λ(ℤ_p^×)`, `Q(ℤ_p^×)`, the pseudo-measure
formalism, `padicZeta` + its interpolation, the x-twist), which would have to be upstreamed first; a
terminal theorem cannot be "added as-is" ahead of its whole foundation. **YES-but-generalise-first** is
wrong as the headline verdict: Phase 5 shows the more general forms (and the carrier algebra itself) are
*also* absent from mathlib, so the move is "upstream an entire theory and then state the interpolation
theorem in its general Dirichlet/`𝒪_L`/higher-rank form", not a mechanical generalise-first of this
theorem — and the verdicts reference explicitly flags that whole-development, EXPENSIVE situation as a
BORDERLINE "is the bigger thing worth it / in what form?" call, not a self-resolving downgrade. The
decisive question — *should the underlying RJW p-adic-measure / Kubota–Leopoldt / Eisenstein-family layer
go to mathlib at all, and if so is the right headline this interpolation theorem, the family object
`eisensteinFamily`, or `padicZeta` itself; in the trivial-character or full Dirichlet generality; with
or without the twisted-witness `½` encoding?* — is exactly the mathematical-taste / project-policy
judgment the skill must not make alone. The call-sites signal (`K = 0`, terminal headline, 0 external
consumers) is consistent with "this is the output of the project, a candidate public theorem to upstream
*if* the foundation goes", not "inline-able wrapper" and not "dead code". Notably the sibling report for
the def `eisensteinFamily` names **this very theorem** as one of the three candidate mathlib headlines
(family object vs. *this interpolation theorem* vs. `padicZeta`) — choosing among them is the human call.

**Numbered questions (≤5):**

1. **Foundation-first.** `eisensteinFamily_interpolation` cannot reach mathlib before its whole tower
   (`PadicMeasure` on `ℤ_p^×` = the continuous dual / Iwasawa algebra `Λ(ℤ_p^×)`, the total fraction ring
   `Q(ℤ_p^×)`, the pseudo-measure formalism, `padicZeta` and its interpolation `padicZeta_moments`, the
   x-twist `unitsTwist`/`quotientTwist`, the divisor-sum measures). Is upstreaming that **foundation** to
   mathlib a goal? If **no**, this theorem stays project-local and the assessment ends as "keep" — there
   is nothing to PR. If **yes**, proceed to Q2–Q5. (This is the same gating question raised by every
   sibling report in this file; answering it once resolves the whole §8 file.)
2. **Which object is the real mathlib headline?** Given the foundation, is the mathlib-worthy headline
   (a) **this coefficientwise interpolation theorem** `eisensteinFamily_interpolation`, (b) the **family
   object** `eisensteinFamily` (with the interpolation as a characterising theorem), or (c) the **p-adic
   zeta and its interpolation** `padicZeta` + `padicZeta_moments` (the engine, with the Eisenstein family
   as an application)? The skill reads all three as legitimate; the sibling reports list exactly this
   choice as open.
3. **Trivial character vs. Dirichlet / higher rank.** The literature standard (RJW §5/§8; Hida–Wiles;
   Kawamura; Eischen) is the family over arbitrary Dirichlet `χ` of p-power conductor (and over higher-rank
   groups / general `𝒪_L`). Should any mathlib contribution state the interpolation in that fuller form
   (the project's `Interpolation/` development) rather than the trivial-character GL(2)/ℚ case formalised
   here?
4. **Statement shape & witness/`½` packaging.** This theorem is a **conjunction** of a witness-encoded
   constant-term leg (erratum #11: `(b·[b]−1)·A₀ ∈ Λ` with the `(b^k−1)` factor, because `A₀` is not a
   pseudo-measure) and a higher-coefficient leg. Would mathlib want this combined, twisted-witness
   statement, or a cleaner factorisation — e.g. the un-twisted engine `∫x^k ζ_p = (1−p^{k−1})ζ(1−k)` (over
   the genuine pseudo-measure `ζ_p`) plus separate "family coefficients" lemmas, with the half/twist
   applied at the family-assembly site? (mathlib style — `/cleanup` audit item 12 STRUCTURE — generally
   disfavours combined `∧` statements whose components are separate facts.)
5. **`4 ≤ k` vs. `0 < k`, and `zetaNeg` vs. mathlib.** Independently of mathlib: (a) the **p-adic legs of
   this theorem only need `0 < k`** (`4 ≤ k` is carried solely for the complex identification in
   `EisensteinComplex.lean`) — do you want a `0 < k` p-adic version factored out in the project (CHEAP)?
   (b) mathlib's `riemannZeta_neg_nat_eq_bernoulli` equals `zetaNeg`; should any upstreamed statement use
   mathlib's `riemannZeta`/`bernoulli` value directly, and is the project's separate rational `zetaNeg`
   (kept to avoid importing complex analysis) the right interface at the mathlib boundary?

**Next action:** user answers Q1 first. If Q1 = no → close as project-local (no mathlib action; this is
the file's terminal headline and stays put). If Q1 = yes → treat upstreaming the `PadicMeasure` +
`padicZeta` + pseudo-measure layer as a separate large effort, decide which object is the headline (Q2),
at what generality (Q3), with what statement shape / witness packaging (Q4) — and ship this interpolation
theorem, if at all, as (or alongside) the headline of that much larger upstreaming, after the foundation
lands. Re-run `/mathlibable PadicLFunctions.eisensteinFamily_interpolation` once Q1–Q4 are decided. Q5(a)
(the `k`-weakening) and Q5(b) (the `zetaNeg` interface) can be actioned regardless.

---

## Next step

User answers the numbered questions (Q1 is the gate: is the RJW p-adic-measure / Kubota–Leopoldt /
Eisenstein-family layer mathlib-bound?). If no, `eisensteinFamily_interpolation` stays project-local
(the file's terminal headline result). If yes, treat upstreaming the foundation as a separate large
effort, decide which object is the mathlib headline (Q2 — this theorem, the family `eisensteinFamily`,
or `padicZeta`) and at what generality and statement shape (Q3–Q4); this interpolation theorem ships, if
at all, as part of that effort once the foundation lands. Re-run `/mathlibable` thereafter. The `0 < k`
weakening (Q5a) and `zetaNeg`↔`riemannZeta` interface (Q5b) can be actioned regardless of the mathlib
decision.

---

### Sources (Phase 3)
- https://arxiv.org/abs/2309.15692 / https://arxiv.org/pdf/2309.15692 — Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions* (THE source; §8 "The p-adic family of Eisenstein series", Def 8.1 + Thm 8.2)
- https://msp.org/ent/2025/4-1/ent-v4-n1-p03-p.pdf — the published version (Essential Number Theory 4(1), 2025)
- https://arxiv.org/abs/1207.0198 / https://arxiv.org/pdf/2302.13009 — Kawamura, *A semi-ordinary p-stabilization of Siegel Eisenstein series … and its p-adic interpolation* (constant term interpolated by the Kubota–Leopoldt / Deligne–Ribet p-adic L-function; "natural generalisation of the ordinary Λ-adic Eisenstein series of Hida and Wiles for GL(2)/ℚ")
- https://warwick.ac.uk/fac/sci/maths/people/staff/rockwood/interpslides.pdf — Rockwood, *p-adic interpolation of Eisenstein series* (overview slides)
- https://sites.math.duke.edu/~dasgupta/papers/EvilEisenstein.pdf — Dasgupta, *The p-adic L-functions of evil Eisenstein series*
- https://arxiv.org/pdf/1302.7229 — Eischen, *A p-adic Eisenstein measure for vector-weight automorphic forms* (Eisenstein measure interpolating Fourier expansions; families of measures on ℤ_p^×)
- https://arxiv.org/pdf/2412.11332 — *p-adic properties of Eisenstein–Kronecker cocycles … and p-adic interpolation* (2024; active generalisation line)
- https://ncatlab.org/nlab/show/p-adic+modular+form — nLab (ambient p-adic-modular-form concept à la Serre/Katz; no isolated Eisenstein-family interpolation theorem)
- Mathlib: `riemannZeta_neg_nat_eq_bernoulli` (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`) — the *rational value* `ζ(−k) = (−1)^k bernoulli(k+1)/(k+1)`, equal to the project's `zetaNeg`; the only mathlib piece of the formula's RHS, and the full extent of mathlib's overlap.
