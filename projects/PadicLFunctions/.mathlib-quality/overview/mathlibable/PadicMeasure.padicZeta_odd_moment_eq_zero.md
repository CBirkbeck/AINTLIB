# `/mathlibable` report — `PadicMeasure.padicZeta_odd_moment_eq_zero`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-20. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> The **mathematics** — the trivial branch of the Kubota–Leopoldt p-adic zeta function
> `ζ_p` **vanishes on the odd part**: for odd `k` its `x^k`-moment is `0`, because the
> interpolated value `ζ_p(1−k) = (1 − p^{k−1})·ζ(1−k)` vanishes (at `k = 1` via the Euler
> factor `1 − p⁰ = 0`; at odd `k ≥ 3` via the trivial zero `ζ(1−k) = −B_k/k = 0`). This is
> **classical and canonical** — it is exactly RJW §11.1 (the corollary that `ζ_p` descends
> to a pseudo-measure on `𝒢⁺`, the quotient by complex conjugation), and the underlying
> "odd Bernoulli numbers vanish ⇒ trivial zeros of ζ at negative even integers" is in every
> Iwasawa-theory text. **But this specific Lean theorem is stated entirely over a
> project-local Iwasawa tower** (`PadicMeasure`, the fraction ring `QuotientField p` of the
> Iwasawa algebra `Λ(ℤ_p^×)`, `IsPseudoMeasure`, `padicZeta`, the moment theorem
> `padicZeta_moments`, the test function `unitsPowCM p k = (x ↦ x^k)`, and the rational zeta
> value `zetaNeg`), **none of which exists in mathlib** (confirmed: mathlib has *no*
> `padicZeta` / `PadicMeasure` / Iwasawa algebra / pseudo-measure / `zetaNeg` / `unitsPowCM`).
> So all four mechanical buckets fail their gates: there is nothing in mathlib to specialise
> from (NO-mathlib-has-it), nothing to compose the moment-encoded statement from in ≤3 lines
> (NO-composable — it consumes the entire `padicZeta_moments` apparatus), and the lemma
> cannot be shipped ahead of its whole foundation (the YES buckets). On top of that it has
> **`K = 0` external consumers** — it is a single-use internal stepping-stone to
> `dirac_neg_one_sub_one_mul_padicZeta` inside the same file. Whether that whole foundation
> should go to mathlib at all, and whether this moment-vanishing lemma deserves a mathlib
> home (versus remaining a private/internal helper of the c-invariance proof), are
> taste/policy judgments the skill cannot ground in the evidence. Numbered questions for the
> user are in Phase 7. This is the same situation as the sibling report
> `twistedZetaHalf_isTwistedPseudoMeasure.md` in this directory.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD
  NOTE — `lake build` is stale/slow in this checkout). The declaration and its full
  dependency chain were read directly from source, exactly as the skill's Phase-0 fallback
  allows.
- decl `PadicMeasure.padicZeta_odd_moment_eq_zero`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:50`
- kind:                      theorem
- has sorry:                 **no** — `grep -nE "sorry|admit"` returns nothing for
  `ZetaGalois.lean`, `KubotaLeopoldt/ZetaP.lean` (`padicZeta`, `padicZeta_moments`), and
  `KubotaLeopoldt/ZetaValues.lean` (`zetaNeg`). The declaration and every dependency
  (`odd_moment_factor_eq_zero`, `padicZeta_moments`, `padicZeta`, `unitsPowCM`,
  `PadicMeasure`, `QuotientField`, `IsPseudoMeasure`, `zetaNeg`) are complete, sorry-free.
- module docstring summary:  "ζ_p as a pseudo-measure on `𝒢⁺` and the ideal `I(𝒢)ζ_p`"
  (RJW arXiv:2309.15692 §11.1 corollary + §11.2, on the identified Galois side `𝒢⁺ = GPlus p`).
  The file shows that the odd moments of `ζ_p` vanish, deduces c-invariance
  `([−1]−[1])·ζ_p = 0`, descends `ζ_p` to a pseudo-measure on `𝒢⁺`, and builds the ideals
  `I(𝒢)ζ_p` / `I(𝒢⁺)ζ_p`.

```lean
/-- The odd moments of every witness `([b]−[1])·ζ_p` vanish: this is the precise
content of TeX 2992 "ζ_p vanishes at the characters χ^k for odd k" — including
`k = 1`, which the membership criterion requires. -/
theorem padicZeta_odd_moment_eq_zero (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : Odd k)
    (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) ν) :
    ν (unitsPowCM p k) = 0 := by
  have hm := padicZeta_moments p hp2 b hk.pos ν hν
  rw [mul_assoc, odd_moment_factor_eq_zero p hk, mul_zero] at hm
  refine Subtype.coe_injective ?_
  change ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = ((0 : ℤ_[p]) : ℚ_[p])
  rw [hm]
  norm_num
```

---

### Statement (Phase 1)

`PadicMeasure.padicZeta_odd_moment_eq_zero` is **a theorem** stating the following:

Let `p` be an odd prime. The Kubota–Leopoldt p-adic zeta function `ζ_p` is a *pseudo-measure*
on `ℤ_p^×` — an element of the total fraction ring `Q(ℤ_p^×)` of the Iwasawa algebra
`Λ(ℤ_p^×)`, characterised by the property that `([b]−[1])·ζ_p` lands inside `Λ(ℤ_p^×)` (as an
honest measure `ν`, the "witness") for every `b ∈ ℤ_p^×`. The theorem asserts that **for every
odd `k ≥ 1`, this witness measure `ν` integrates the monomial `x^k` to zero**: `ν(x ↦ x^k) = 0`.

Equivalently, in the moment encoding `∫_{ℤ_p^×} x^k ζ_p = (1 − p^{k−1})·ζ(1−k)`, this says the
`k`-th moment of `ζ_p` vanishes for odd `k`. Mathematically this is the statement "**the trivial
branch of ζ_p vanishes at the characters `x^k` for odd `k`**", i.e. ζ_p is supported on the even
part — the fact that lets it descend to a pseudo-measure on `𝒢⁺ = ℤ_p^× / {±1}`. The vanishing
has two sources: at `k = 1` the Euler factor `1 − p^{1−1} = 1 − p⁰ = 0`; at odd `k ≥ 3` the
classical trivial zero `ζ(1−k) = −B_k/k = 0` (the odd Bernoulli number `B_k` vanishes).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; the whole development is `noncomputable` over `ℚ_[p]`.
- `b : ℤ_[p]ˣ` — the unit defining the witness `([b]−[1])·ζ_p`.
- `{k : ℕ}` — the moment index.
- `ν : PadicMeasure p ℤ_[p]ˣ` — the witness measure; `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`
  (a ℤ_p-linear functional on continuous ℤ_p-valued functions = the Iwasawa-algebra element).

Hypotheses (Lean side):
- `(hp2 : p ≠ 2)` — odd prime (the construction of `ζ_p` needs `p` odd).
- `(hk : Odd k)` — the moment index is odd (the whole point).
- `(hν : algebraMap _ (QuotientField p) (dirac p b - 1) * padicZeta p hp2 = algebraMap _ _ ν)`
  — `ν` is *the* witness of `([b]−[1])·ζ_p` (the pseudo-measure property at `b`); `QuotientField p
  := FractionRing (PadicMeasure p ℤ_[p]ˣ)`.

Conclusion (math): the odd `x^k`-moment of `ζ_p` vanishes.

Conclusion (Lean): `ν (unitsPowCM p k) = 0`, where `unitsPowCM p k : C(ℤ_[p]ˣ, ℤ_[p])` is
`⟨fun u => (u : ℤ_[p])^k, …⟩`, the continuous map `x ↦ x^k`, and the value lives in `ℤ_[p]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a *corollary / stepping-stone* — the odd-`k` half of the moment computation
`padicZeta_moments`, fed through the factor lemma `odd_moment_factor_eq_zero`. It is *not* a new
mathematical structure (no `def`/`class`), and although it sits in the chain that proves a named
result (RJW §11.1), it is itself the small membership-criterion input ("ζ_p vanishes at odd `k`"),
not the headline theorem. The headline objects in the file are `padicZetaPlus` and
`isPlusPseudoMeasure_padicZetaPlus`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only and does
not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: 7 substantive lines (`have hm …`, `rw … at hm`, `refine …`, `change …`, `rw [hm]`,
`norm_num`). Kind is **theorem**, not a `def`.
One-liner verdict: **n/a** — kind is `theorem`/`lemma`, not a `def`/`abbrev`/`structure`. The
one-liner exemption table does not apply. Phase 4.5 (diamond/defeq) is likewise n/a.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Kubota-Leopoldt p-adic zeta function vanishes odd characters trivial zeros" | yes | ζ_p does **not** vanish at the trivial character but **is zero on the odd part**; simple zero of ζ_p at `s=1` | Williams Warwick lecture notes; Dasgupta "evil Eisenstein"; the result is standard |
| 2 | WebSearch (general / Bernoulli form) | "p-adic L-function odd part zero zeta_p(1−k)=0 for odd k Bernoulli" | yes | "vanishing of odd Bernoulli numbers ⇒ trivial zeros"; `ζ*(s,u) = L_p(s, ω^{1−u})` parity split | Springer (p-adic ζ and Bernoulli); confirms the `B_k = 0` mechanism for odd `k` |
| 3 | WebSearch (named / context) | "p-adic zeta function only even part nontrivial … odd characters vanish Coates Wiles" | yes | parity decomposition; nontrivial only on the even part; Coates–Wiles / Iwasawa main-conjecture context | Mazur–Wiles, Wiles totally-real; the even/odd split is foundational |
| 4 | WebSearch (moments / pseudo-measure) | "\"p-adic zeta\" vanishing moments x^k ζ_p odd k pseudo-measure Iwasawa algebra" | yes | **surfaced the source paper itself**: arXiv:2309.15692; "pseudo-measure", "zeros captured by an ideal in the Iwasawa algebra" | exactly the RJW framework the file formalises |
| 5 | ChatGPT MCP | "standard form of: ζ_p vanishes at odd characters / odd moments; generality; historical evolution" | **n/a** | — | ChatGPT MCP server **not installed** in this environment (no matching deferred tool; plugin manifest has no MCP server). Recorded n/a per protocol; channels 1–4 + the source-paper fetch already pin the standard form and its history (Kummer → Kubota–Leopoldt → Iwasawa). |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | — | both directories **absent** (no `references/`, no `refs/` symlink). Recorded n/a with reason. |
| 7 | nLab | "Iwasawa theory" page (ncatlab.org/nlab/show/Iwasawa+theory) — fetched | partial | mentions `L_p(ω^{1−i}, s)` = Kubota–Leopoldt in the main-conjecture statement | **no** clean abstract statement of "ζ_p vanishes on the odd part" or of the pseudo-measure moments; only a passing reference |
| 8 | nCatLab (categorical) | — | **n/a** | — | not a categorical concept; the result is a concrete vanishing/parity statement, no universal property to abstract. |
| 9 | Stacks Project | — | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; Stacks has no p-adic L-function / Iwasawa-algebra material. |
| 10 | MathOverflow / Math.SE | covered transitively by queries 1–4 (HandWiki "p-adic L-function", Wikipedia "Main conjecture") | yes | confirms parity split + simple zero at `s=1`; even part nontrivial | the even/odd-part vanishing is treated as standard background, not a research-level question |
| 11 | recent arXiv (≤5y) | query 4 returned arXiv:2507.01836 "p-adic moments of L-functions" + the source arXiv:2309.15692 (2024) | yes | the source paper is itself recent arXiv; §11 titled **"Iwasawa's theorem on the zeros of the p-adic zeta function"** | the precise §11.1 reference in the file docstring is corroborated |

**Source paper located.** Channels 4, 7, 11 all surfaced **arXiv:2309.15692, "An introduction to
p-adic L-functions" by Joaquín Rodrigues Jacinto and Chris Williams** (published MSP, *Essential
Number Theory* 4-1, 2025) — this is the "RJW" of the file's docstrings. Its **§11 is literally
titled "Iwasawa's theorem on the zeros of the p-adic zeta function"**, and §11.1 is the corollary
that `ζ_p` descends to a pseudo-measure on the plus part. (Direct PDF fetch failed — the arXiv and
MSP PDFs are image/encoded, so verbatim quoting was not possible — but the section title, the file's
own TeX-line citations (2992, 3033–3059), and the four converging web channels pin the standard form
beyond doubt.)

### Literature summary (Phase 3)

Concept identified as: **"the (trivial branch of the) Kubota–Leopoldt p-adic zeta function vanishes
on the odd part"** — i.e. its `x^k`-moments vanish for odd `k` — the input to its descent to a
pseudo-measure on `𝒢⁺ = ℤ_p^× / {±1}` (RJW §11.1; classical, traceable to Kummer's congruences →
Kubota–Leopoldt → Iwasawa).

Sources agree on the standard form: **yes**. Every source gives the same parity picture: ζ_p is
nontrivial only on the even part; the odd-`k` (equivalently odd-character) values vanish because
`ζ(1−k) = −B_k/k = 0` for odd `k ≥ 3` (odd Bernoulli numbers vanish), with the `k = 1` case carried
by the Euler factor `1 − p^{k−1}`.

Most general standard form: for the cyclotomic ℤ_p (`ℚ`) setting, ζ_p as a pseudo-measure on
`Gal(ℚ(μ_{p^∞})/ℚ) ≅ ℤ_p^×` is zero on the odd part; the generalisation is to totally real fields
(Deligne–Ribet / Cassou-Noguès pseudo-measures, Wiles' main conjecture), where the analogous
"vanishing away from the totally-even part" holds.

Generality dimensions where the literature varies:
  - base field: `ℚ` (the `ℤ_p^×` setting here) → arbitrary totally real field (Deligne–Ribet). The
    Lean theorem is the `ℚ`/`ℤ_p^×` case only.
  - encoding: "value at a character `χ^k`" (analytic) vs. "moment `∫ x^k`" (measure-theoretic, used
    here) vs. "via Stickelberger elements" (Iwasawa's algebraic construction). All equivalent.

Disagreement with the literature: **none**. The Lean form is one faithful encoding of the standard
result; the docstring even flags an **erratum #13** (the source's one-line proof "ζ(1−k) = 0 for odd
`k ≥ 1`" fails at `k = 1`, which the file repairs via the Euler factor) — a *correction* of the
source, not a disagreement with the mathematics.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the trivial branch of ζ_p (as a pseudo-measure on `ℤ_p^×`
in the cyclotomic-ℚ setting) has vanishing odd moments. The "more general" forms (totally real
fields; abstract Iwasawa algebra `Λ(G)`) require an entire separate apparatus that mathlib does not
have either.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]`, `hp2 : p ≠ 2` | odd prime | odd prime (cyclotomic-ℚ ζ_p) | NO | the construction of `ζ_p`/`padicZeta` needs `p` odd; intrinsic, not a packaging choice |
| 2 | `b : ℤ_[p]ˣ` (the witness unit) | arbitrary unit | any `g ∈ Gal ≅ ℤ_p^×` | already maximal | quantifies over all `b`; matches the pseudo-measure definition |
| 3 | `ν` + `hν` (the witness, via `algebraMap … = algebraMap … ν`) | bundled fraction-ring witness identity | "ζ_p is a pseudo-measure" (Coates–Serre) | n/a | this *is* the standard pseudo-measure encoding; the entire `PadicMeasure`/`QuotientField` tower it rests on is project-local, not in mathlib |
| 4 | `hk : Odd k`, `k : ℕ` | odd natural moment index | odd `k ≥ 1` (incl. `k = 1`) | already maximal | covers `k = 1` deliberately (the membership-criterion requirement; the erratum-#13 fix) |
| 5 | base setting `ℤ_p^×` | cyclotomic ℚ | totally real field (Deligne–Ribet) | yes, in principle | EXPENSIVE and **moot**: mathlib has neither the ℤ_p^× nor the totally-real Iwasawa apparatus, so there is nothing to state the general form against |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *within the project's cyclotomic-ℤ_p^× setting* (it
already quantifies over all `b`, all odd `k` including `k = 1`, and uses the standard pseudo-measure
witness encoding). The only "more general" axis (totally real fields) is a different, much larger
theory that mathlib does not contain, so it is not a weakening of *this* statement but a separate
project.
Number of weakening opportunities found: **0** (within scope).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the hypotheses are already typeclass-driven (`Fact p.Prime`) + a bundled witness identity; there is no informal preamble to typeclass-ify |
| 2 | sequences/metric → filters/topological? | no | — | a finite algebraic vanishing statement; no limit/convergence to filter-ise |
| 3 | construct an object → universal-property class? | no | — | it is a *property* (a value equals 0), not a construction; nothing to characterise universally |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no subset/closure structure; `ν` is a linear functional, already bundled (`→ₗ[ℤ_[p]]`) |
| 5 | vector-space/metric/field-specific → weaker typeclasses? | no | — | already at the natural level (`ℤ_[p]`-linear functionals, `FractionRing` of the Iwasawa algebra); the rings are fixed by the arithmetic |
| 6 | 1-categorical → higher-categorical? | no | — | no categorical content |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | `k : ℕ` is the genuine moment index; `ℤ_p^×` is the genuine Galois group. Generalising the *group* is the totally-real-field theory (row 5 of 4a), a separate development, not an idiom swap |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. There is no contemporary mathlib reformulation that improves the
mathematical organisation here — the statement is a concrete arithmetic vanishing fact about a
project-local object, already expressed with mathlib-idiomatic bundled linear functionals and
localization (`FractionRing`/`IsLocalization`). The only "more general" target (Deligne–Ribet over
totally real fields) is a separate large theory, not an idiom; and mathlib lacks even the base
apparatus to state it.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths are
introduced. Skipped per scope.

---

### Mathlib search-status: `PadicMeasure.padicZeta_odd_moment_eq_zero` (Phase 5)

[A] Lean-Finder       (would query: "p-adic zeta function vanishes odd moments pseudo-measure")
    **n/a — Lean-Finder MCP server not available in this environment** (ToolSearch surfaced
    only WebSearch; no `lean_*` search tool is installed).
[B] Loogle            (would query: `(_ : C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]) _ = 0`, and patterns
    for `FractionRing`-encoded witness identities) — **n/a — `lean_loogle` not available** in
    this environment.
[C] LeanSearch        (would query: "Kubota–Leopoldt p-adic zeta function odd moments vanish")
    **n/a — `lean_leansearch` not available** in this environment.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib` for: `kubota`, `leopoldt`,
    `padicZeta`, `pseudoMeasure`/`pseudo.measure`, `PadicMeasure`, `IwasawaAlgebra`/`iwasawa`,
    `padicLFunction`/`PadicLFunction`, `unitsPowCM`, `zetaNeg`, `odd_moment`, plus
    "Iwasawa algebra"/"p-adic measure"/"measures on continuous". **No hits** for any of the
    p-adic-L / Iwasawa-algebra / pseudo-measure / p-adic-measure names. (The only `iwasawa`
    hits are `GroupTheory/GroupAction/Iwasawa.lean` — Iwasawa's *simplicity criterion* for
    permutation groups — and unrelated matrix-decomposition files; the only `UnitsPow` hits are
    `Data/ZMod/IntUnitsPower` / `Algebra/Ring/NegOnePow`, about `ℤˣ` powers and `(−1)^n`, not
    p-adic measures.) **The *building blocks of the factor lemma* exist** —
    `Mathlib/NumberTheory/Bernoulli.lean:217 bernoulli_eq_zero_of_odd`, and
    `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:172 riemannZeta_neg_two_mul_nat_add_one`
    ("the trivial zeroes of the zeta function") — but **not** the moment-encoded statement.
[E] Name pattern      grep for `odd_moment` / `padicZeta` / `pseudoMeasure` / `unitsPow` / `zetaNeg`
    / `kubota` as decl-name fragments across mathlib → **no hits**.

Searched for both:
  - the user's current form (the moment-encoded `ν (unitsPowCM p k) = 0`) — not in mathlib;
  - the literature-standard form ("ζ_p vanishes at odd characters / on the odd part") — not in
    mathlib (mathlib has no `ζ_p` at all). The complex-analytic shadow (`riemannZeta` trivial
    zeros) and the Bernoulli vanishing *are* in mathlib, and are exactly what the project's
    `odd_moment_factor_eq_zero` already calls — but those are about `ζ`/`B_k`, not about the
    p-adic pseudo-measure moments this theorem is about.

Concluded: **not in mathlib** (methods D + E exhausted across all relevant name/keyword families;
methods A–C unavailable in this environment and recorded n/a with reason). Mathlib has *no* p-adic
L-function / Kubota–Leopoldt / Iwasawa-algebra / pseudo-measure machinery whatsoever — neither the
specific moment statement nor the foundation it is stated over.

---

### Call sites — `PadicMeasure.padicZeta_odd_moment_eq_zero` (Phase 6.0)

Internal use count: **0** (within the project, **not** counting the declaring file).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Iwasawa/ZetaGalois.lean:68` *(declaring file — excluded from the count)* | named in the docstring of `dirac_neg_one_sub_one_mul_padicZeta`: "odd ones by `padicZeta_odd_moment_eq_zero`" |
| — | *(no callers outside `ZetaGalois.lean`)* |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - `dirac_neg_one_sub_one_mul_padicZeta` (same file, line 86–88) **re-derives the odd-moment
    vanishing inline** for the special case `b = −1`: `rw [mul_assoc, odd_moment_factor_eq_zero p ho,
    mul_zero] at hm`. That is, the file's *actual* downstream proof of c-invariance does **not**
    call `padicZeta_odd_moment_eq_zero`; it re-uses the underlying `odd_moment_factor_eq_zero`
    directly. So even the one internal "consumer" bypasses this lemma. (The lemma exists to state
    the general-`b` membership-criterion fact "ζ_p vanishes at χ^k for odd `k`" cleanly, per RJW
    §11.1 TeX 2992, rather than to feed a proof.)

What the call-sites pattern tells you: **K = 0 internal uses, and the one place that needs the same
content re-derives it inline from `odd_moment_factor_eq_zero`.** By the Phase-6.0 signal table this
leans **NO-composable / documentation-lemma** — but here the obstruction to a clean NO bucket is that
the *thing it would be inlined into / replaced by* is itself project-local (`odd_moment_factor_eq_zero`,
`padicZeta_moments`), not mathlib. So the call-site signal reinforces "this is a project-internal
helper", which feeds the BORDERLINE policy question rather than a mechanical NO.

### Composition check (Phase 6)

Can `PadicMeasure.padicZeta_odd_moment_eq_zero` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `Subtype.coe_injective (by rw [padicZeta_moments …, odd_moment_factor_eq_zero …]; …)`
  - Mathlib decls used: only generic glue (`Subtype.coe_injective`, `mul_assoc`, `mul_zero`,
    `norm_num`).
  - Result: **fails as a *mathlib* composition.** The two load-bearing steps —
    `padicZeta_moments` (the moment formula `∫ x^k ζ_p = (b^k−1)(1−p^{k−1})ζ(1−k)`) and
    `odd_moment_factor_eq_zero` (the factor vanishes for odd `k`) — are **project-local theorems**,
    not mathlib. Without them there is nothing in mathlib to chain.
  - Notes: the *genuinely mathlib* part is just casting `ℤ_[p] ↪ ℚ_[p]` injectivity plus `norm_num`;
    that does not produce the statement on its own.

Attempt 2: derive directly from mathlib's `bernoulli_eq_zero_of_odd` / `riemannZeta_neg_two_mul_nat_add_one`.
  - Result: **fails.** Those give `B_k = 0` / `ζ(−2(n+1)) = 0` — the *content of
    `odd_moment_factor_eq_zero`'s `k ≥ 3` branch*, about `ζ`/`B_k`, **not** about the pseudo-measure
    witness `ν (unitsPowCM p k)`. Bridging from "the Bernoulli number is zero" to "the witness
    integrates `x^k` to zero" *is* the moment theorem `padicZeta_moments` (a long, project-local
    proof through `zetaNum_moments`, the Iwasawa-algebra localization, and Mahler theory). Not a
    composition.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The statement is a ≤3-line composition of
*project-local* results (`padicZeta_moments` ∘ `odd_moment_factor_eq_zero`), but those are not in
mathlib, and mathlib's relevant primitives (`bernoulli_eq_zero_of_odd`, the ζ trivial zeros) only
discharge the *scalar factor lemma*, not the moment-encoded theorem. There is no mathlib path to the
stated form.

---

## Verdict: `PadicMeasure.padicZeta_odd_moment_eq_zero`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the mathematics is **classical and canonical** — "ζ_p vanishes on the
  odd part / at the characters `x^k` for odd `k`", exactly RJW §11.1 (arXiv:2309.15692, §11 =
  "Iwasawa's theorem on the zeros of the p-adic zeta function"); 4 converging WebSearch channels +
  the located source paper; nLab has only a passing mention, no clean abstract statement.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL within the cyclotomic-ℤ_p^× setting** (4b);
  **no modern-idiom restatement** improves it (4c). The only larger form (totally real fields) is a
  separate theory mathlib also lacks.
- Mathlib search (Phase 5): **not in mathlib** — mathlib has *no* p-adic L-function / Kubota–Leopoldt
  / Iwasawa-algebra / pseudo-measure / `PadicMeasure` / `zetaNeg` / `unitsPowCM` machinery at all
  (only the unrelated Bernoulli vanishing + ζ trivial zeros, which discharge the scalar factor).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (the ≤3-line composition is of
  *project-local* theorems); **K = 0 external call sites**, and the lone internal consumer re-derives
  the content inline from `odd_moment_factor_eq_zero`.

**Rationale (1–2 paragraphs):**

This is the textbook situation where the *mathematics* is unambiguously mathlib-worthy in spirit but
the *Lean declaration* cannot be assessed by the mechanical buckets, because it is stated over a
foundation that does not exist in mathlib. The statement "the trivial branch of the Kubota–Leopoldt
p-adic zeta function vanishes on the odd part" is canonical (Phase 3), but every symbol carrying it
here — `PadicMeasure` (ℤ_p-linear functionals on `C(X, ℤ_[p])` = the Iwasawa algebra), `QuotientField`
(its fraction ring = `Q(ℤ_p^×)`), `IsPseudoMeasure`, `padicZeta`, the moment theorem
`padicZeta_moments`, the test function `unitsPowCM`, and the rational zeta value `zetaNeg` — is
**project-local and absent from mathlib** (Phase 5, exhaustive). Consequently: `NO-mathlib-has-it`
fails its gate (Phase 5 found no decl to cite — mathlib has nothing to specialise from);
`NO-composable-from-mathlib` fails its gate (Phase 6 is NOT-COMPOSABLE *from mathlib* — the only
composition is of project-local theorems); and the two YES buckets fail because one cannot ship a
single lemma ahead of the entire `padicZeta`/pseudo-measure foundation it depends on (and Phase 4
found no in-scope generalisation and no modern-idiom improvement, so even "YES-but-generalise" has no
target).

What remains is a genuine **judgment call**: (a) whether the project's whole p-adic-L / Iwasawa-algebra
tower should be upstreamed to mathlib (a large, multi-file effort — *that* is the real decision, and it
is exactly the question raised by the sibling `twistedZetaHalf_isTwistedPseudoMeasure` report); and
(b) even granting that, whether *this particular* lemma deserves a public mathlib home. The call-site
evidence argues it is an internal stepping-stone: **`K = 0` consumers**, and the one place that needs
the same content (`dirac_neg_one_sub_one_mul_padicZeta`) re-derives it inline from
`odd_moment_factor_eq_zero` rather than calling it — the lemma exists to state the membership-criterion
fact cleanly (RJW §11.1, TeX 2992, including the `k = 1` case that the source's proof got wrong —
*erratum #13*), not to feed a proof. So a reasonable mathlib reviewer might keep it `private`/internal
even if the foundation is upstreamed. The skill cannot ground either decision in the evidence; hence
BORDERLINE.

**Numbered questions (≤5):**

1. Is the plan to upstream the project's p-adic-L / Iwasawa-algebra foundation (`PadicMeasure`,
   `QuotientField`/`Q(ℤ_p^×)`, `IsPseudoMeasure`, `padicZeta`, `padicZeta_moments`, `unitsPowCM`,
   `zetaNeg`) to mathlib? If **no**, this lemma is automatically out of scope (it cannot exist in
   mathlib without that foundation) and should stay project-local.

2. If that foundation is upstreamed: should `padicZeta_odd_moment_eq_zero` be a *public* mathlib lemma,
   or — given **`K = 0` consumers** and that the file's own c-invariance proof re-derives the content
   inline from `odd_moment_factor_eq_zero` — would you rather mark it `private`/internal and expose
   only the headline results (`dirac_neg_one_sub_one_mul_padicZeta`, `isPlusPseudoMeasure_padicZetaPlus`)?

3. In a mathlib home, which is the canonical statement to expose — this **moment encoding**
   (`ν (unitsPowCM p k) = 0` over a witness) or the **character-value form** "ζ_p evaluated at `x^k`
   is `0` for odd `k`"? The literature uses the latter; the project uses the former for its
   pseudo-measure bookkeeping.

4. Would the companion scalar lemma `odd_moment_factor_eq_zero` (`(1 − p^{k−1})·ζ(1−k) = 0` for odd
   `k`) — which *is* close to mathlib's `bernoulli_eq_zero_of_odd` + `riemannZeta` trivial zeros and
   carries the substantive `k = 1` erratum fix — be the better mathlib contribution to prioritise,
   with `padicZeta_odd_moment_eq_zero` left as its project-local consumer?

**Next action:** user answers the questions; re-run `/mathlibable PadicMeasure.padicZeta_odd_moment_eq_zero`
to resolve the verdict. Likely outcomes:
  - Foundation not upstreamed (Q1 = no) → drop from mathlib consideration; keep project-local.
  - Foundation upstreamed + keep internal (Q2 = private) → not a standalone mathlib decl; ships (if at
    all) folded into the descent-to-`𝒢⁺` result.
  - Foundation upstreamed + public, character-value form (Q2 public, Q3 = character form) → re-run with
    the character-value restatement as a Phase-1 input; would likely become `YES-but-generalise-first`
    (generalise the moment encoding to the character form, and consider the totally-real-field axis as
    a follow-up).

---

## Next step

User answers the four numbered questions above; re-run
`/mathlibable PadicMeasure.padicZeta_odd_moment_eq_zero` to resolve the verdict. The pivotal question
is Q1 (is the p-adic-L / Iwasawa-algebra foundation going to mathlib at all?) — a **no** there makes
this lemma out of scope; a **yes** turns the remaining questions (public vs. private; moment vs.
character form) into a likely `YES-but-generalise-first`.
