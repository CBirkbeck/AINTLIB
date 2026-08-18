# `/mathlibable` report — `PadicLFunctions.tendsto_branch_denom_div`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build is stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.tendsto_branch_denom_div`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:231`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — analyticity/pole of the Kubota–Leopoldt p-adic L-function branches at s = 1; this theorem is decomposition node **R7.2c = RJW Lemma 7.2(ii)** (the branch denominator has a simple zero at s = 1).

---

### Statement (Phase 1)

`tendsto_branch_denom_div` is a **theorem** stating the following:

> Let `p` be an odd prime (`p ≠ 2`) and `u : ℤ_[p]ˣ` a unit (downstream: a topological generator of
> `ℤ_[p]ˣ`). Write `⟨a⟩ = angleUnit p u` for the "angle/principal-unit" part of `u` (the projection
> `u ↦ ω(u)⁻¹·u` into `1 + pℤ_p`), and `branchChar p (p−1) (1−s) u` for the branch character value
> `ω(u)^{p−1}·⟨u⟩^{1−s} = ⟨u⟩^{1−s}` (since `ω(u)^{p−1} = 1`). Then the **branch denominator**
> `⟨a⟩^{1−s} − 1`, divided by `s − 1`, converges p-adically:
> `lim_{s → 1, s ≠ 1} (s−1)⁻¹·(⟨a⟩^{1−s} − 1) = −log_p⟨a⟩`,
> where `log_p` is the (integral) p-adic logarithm `pZpLog`.

Mathematically this is: **the p-adic power map `s ↦ ⟨a⟩^{1−s}` has a simple zero of its `(·) − 1` at
`s = 1`, with derivative `−log_p⟨a⟩`.** Equivalently, the tangent line of `s ↦ a^{1−s}` at `s = 1` is
`1 − (s−1)·log_p⟨a⟩`. It is the difference-quotient (`Tendsto`/filter) spelling of "`d/ds [a^{1−s}] |_{s=1} = −log_p⟨a⟩`".

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `u : ℤ_[p]ˣ` — a p-adic unit (implicit).

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — oddness, needed for the project's exp/log bridge (`pZpLog`/`pZpExp` are odd-`p` objects).

Conclusion (Lean):
```lean
Filter.Tendsto (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1)⁻¹
      * ((((branchChar p (p - 1) (1 - s) u : ℤ_[p])) : ℚ_[p]) - 1))
    (nhdsWithin 1 {s | s ≠ 1})
    (nhds (-((pZpLog p ((PadicInt.angleUnit p u : ℤ_[p]))) : ℚ_[p])))
```

**Proof shape.** Via the exp/log bridge `padicExp_smul_padicLog_eq_onePAdicPow`, the branch value is
`⟨a⟩^{1−s} = exp((1−s)·L)` with `L = log_p⟨a⟩` (using `ω^{p−1} = 1`). Writing `w = (1−s)·L`, the
difference quotient minus its limit is `(s−1)⁻¹·(exp w − 1 − w)` (an algebraic identity closed by
`linear_combination`). The key estimate is the **quadratic exp-tail bound**
`norm_padicExp_sub_one_sub_self_le` (the sibling lemma, R7.1a): `‖exp w − 1 − w‖ ≤ p·‖w‖²`. Combined
with `‖w‖ = ‖s−1‖·‖L‖`, this gives `‖difference‖ ≤ p·‖L‖²·‖s−1‖`, which `→ 0` (continuity of the
norm, `nhdsWithin_le_nhds`, `const_mul`). The conclusion follows by `squeeze_zero_norm'` then adding
back the constant `−L`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a decomposition helper (node R7.2c) supplying one analytic input — the simple-zero /
derivative of the branch denominator — consumed by the residue theorem. It is not a `def`/structure
and not a `## Main results` entry (the file's headline is the residue/pole statement
`tendsto_sub_one_mul_zetaPBranch`, which *calls* this lemma).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a**.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | p-adic L-function residue simple pole s=1 derivative branch denominator `⟨a⟩^{1−s} − 1` log_p           | yes  | the **residue/simple-pole** picture (`ζ_{p,p−1}` simple pole at `s=1`, residue `1−p⁻¹`; branches `ζ_{p,i}`, `i≠p−1`, analytic) is canonical; the denominator `ω(a)^i⟨a⟩^{1−s} − 1` is exactly the standard Iwasawa-construction quotient | Rodrigues Jacinto–Williams *An introduction to p-adic L-functions* (arXiv 2309.15692 — the project's RJW source); Williams Warwick lecture notes; MSP ENT survey |
|  2 | WebSearch (general / derivative form) | derivative of p-adic power function `a^s` at `s=0` equals `log_p(a)`, limit `(a^s − 1)/s`            | yes  | the **derivative law** `d/ds a^s = log_p(a)`, equivalently `(a^s − 1)/s → log_p(a)` as `s→0`, is standard p-adic analysis: `a^s = exp(s·log_p a)` is a `ℤ_p`-coefficient power series in `s` with linear term `log_p(a)·s` | Leiden p-adic notes (Evertse Ch. 8); arXiv 1502.04607 (Semmes, "analysis related to p-adic numbers"); PlanetMath "p-adic exponential and p-adic logarithm"; Wikipedia "P-adic exponential function" |
|  3 | WebSearch (named-after / context) | Kubota–Leopoldt zeta `p−1` analytic functions per residue class; branch analytic at s=1                | yes  | "the p-adic zeta function is **not** analytic but comes from `p−1` analytic functions, one per residue class mod `p−1`"; pole/residue at `s=1` standard | uni.lu Ploner notes; Guitart "Mazur's construction of Kubota–Leopoldt"; HandWiki "p-adic L-function"; ResearchGate Kubota–Leopoldt-zeroes |
|  4 | ChatGPT MCP                      | (intended: "standard p-adic form of the derivative/simple-zero of `a^{1−s} − 1` at `s=1`; its generality + history") | n/a  | —                                | ChatGPT MCP / Codex CLI not configured in this environment (`/setup-chatgpt` not run; `which codex` → not found). Recorded n/a; WebSearch (3 levels) + the RJW source's own statement (Lemma 7.2(ii), TeX 2224–2226) + standard p-adic-analysis notes cover the standard-form question. |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                  | n/a  | (no references dir; no `refs/` symlink) | both absent — recorded n/a. The module docstring's inline citations (RJW §7, `thm:residue` TeX 2187–2194, Lemma 7.2(ii) TeX 2224–2226) serve as the literature anchor. |
|  6 | nLab                             | p-adic logarithm / p-adic exponential / derivative of power function                                    | partial | nLab routes p-adic exp/log through the general nonarchimedean-analytic picture (radius `p^{−1/(p−1)}`, `log_p(xy)=log_p x + log_p y`); no dedicated "derivative of `a^s`" or "simple zero of branch denominator" page | not a categorical concept; the derivative-of-power-map fact is folklore, not an nLab headline |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (an analytic limit / `Tendsto` over `ℤ_p`). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (p-adic analytic limit, not scheme/sheaf theory). |
|  9 | MathOverflow / Math.StackExchange| derivative of `a^s` p-adic `= log_p a`; `a^s = exp(s log a)` power series linear term                   | partial | community treats `(a^s−1)/s → log_p a` (`s→0`) as "immediate from `a^s = exp(s·log a)`"; nobody states the `1−s`-reparametrised, branch-character-specific form | recurring Q&A on p-adic exp/log; the fact is regarded as a routine corollary, not a named result |
| 10 | recent arXiv (last 5 years)      | recent p-adic L-function residue `1−p⁻¹`; Lean formalization of p-adic L-functions                      | yes  | the residue/pole picture recurs unchanged in modern work; **Narayanan, "Formalization of p-adic L-functions in Lean 3" (arXiv 2302.14491)** formalised Kubota–Leopoldt in Lean 3 (mathlib3) — relevant precedent, but its API was **not** ported into the current (Lean 4) mathlib | confirms no modern reformulation supersedes the classical derivative/residue statement; and confirms the p-adic-L machinery is still **absent from Lean-4 mathlib** |

Protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (the specific
branch-denominator/residue form / the general derivative-of-`a^s` law / the Kubota–Leopoldt
`p−1`-analytic-branches context); ChatGPT MCP recorded n/a with reason (server absent); local
references recorded n/a with reason (dir + symlink absent); nLab checked; nCatLab / Stacks recorded
n/a with reason; MathOverflow and recent arXiv each checked (the latter surfacing the Lean-3
formalization precedent).

### Literature summary (Phase 3)

Concept identified as: **the first-order (tangent-line) behaviour of the p-adic power map
`s ↦ ⟨a⟩^{1−s}` at `s = 1` — i.e. the simple zero of the branch denominator `⟨a⟩^{1−s} − 1` with
derivative `−log_p⟨a⟩` — phrased as the difference-quotient limit
`(s−1)⁻¹(⟨a⟩^{1−s} − 1) → −log_p⟨a⟩`.**

Sources agree on the standard form: **yes, on the underlying mathematics; not on this exact spelling.**
Two literature anchors converge here:

1. **The derivative law (general).** `a^s = exp_p(s·log_p a)` is a `ℤ_p`-coefficient power series in
   `s` whose linear coefficient is `log_p(a)`; hence `d/ds[a^s]|_{s=0} = log_p(a)` and
   `(a^s − 1)/s → log_p(a)` as `s → 0`. This is textbook p-adic analysis (Leiden notes, PlanetMath,
   Wikipedia, MathOverflow folklore). The target is this law **reparametrised** to the exponent `1−s`
   evaluated at `s = 1` (giving the sign flip and the angle-unit base `⟨a⟩`).

2. **The residue/pole context (RJW Lemma 7.2(ii), the project's exact source).** In every standard
   treatment of Kubota–Leopoldt, `ζ_p` "comes from `p−1` analytic functions, one per residue class mod
   `p−1`", with `ζ_{p,p−1}` having a simple pole at `s = 1` of residue `1 − p⁻¹`. The simple zero of
   the denominator `⟨a⟩^{1−s} − 1` at `s = 1`, with this precise derivative `−log_p⟨a⟩`, is the lemma
   that produces that residue. RJW state it as their **Lemma 7.2(ii)** (`thm:residue` neighbourhood,
   TeX 2224–2226) — i.e. the target *is* a named lemma in the source, at `s = 1`. The Lean theorem
   strengthens "the derivative is `−log_p⟨a⟩`" to the explicit topological `Tendsto`.

Most general standard form: the derivative law for the p-adic power map over `1 + pℤ_p` (or
`1 + 𝔪` in any complete nonarchimedean field ⊇ ℚ_p): for `a ≡ 1 mod p`,
`lim_{s→0,s≠0} s⁻¹(a^s − 1) = log_p(a)`. The target is a specialisation (exponent `1−s` at `s=1`;
base = `⟨a⟩` the angle-unit of a specific `u : ℤ_[p]ˣ`; with the `ω^{p−1}=1` simplification baked in).

Generality dimensions where the literature varies / the Lean form is narrower:
- **Base.** Literature: any `a ∈ 1 + pℤ_p` (or `1 + 𝔪`). Lean: `⟨a⟩ = angleUnit p u` for a unit `u`,
  via `branchChar p (p−1) (1−s) u` (which equals `⟨u⟩^{1−s}` only after using `ω(u)^{p−1} = 1`). The
  branch-character wrapper is **strictly narrower and L-function-specific**.
- **Exponent / evaluation point.** Literature: general "`d/ds a^s = log_p a` at `s=0`". Lean: the
  fixed `1−s` reparametrisation at `s=1`. A cosmetic narrowing.
- **Field.** Literature: any complete nonarch. field ⊇ ℚ_p. Lean: `ℤ_[p]`/`ℚ_[p]` concretely.

Disagreement with the literature: none on content. The gap is purely **organisational** — the
literature's object is the *general derivative of the p-adic power map* (or, in RJW, a clean
`s=1` lemma about `⟨a⟩^{1−s} − 1`); the Lean statement bolts the general fact onto the
project-specific `branchChar`/`angleUnit` plumbing and the `p−1`-branch.

---

### Generality analysis — `tendsto_branch_denom_div`

Literature-standard form (from Phase 3): the derivative/tangent-line law for the p-adic power map,
`lim_{s→0,s≠0} s⁻¹(a^s − 1) = log_p a` for `a ∈ 1 + pℤ_p` (specialising / reparametrising to the
target's `1−s`-at-`s=1` and `−log_p⟨a⟩`).

| # | Parameter / hypothesis                          | Current Lean form                                   | Literature-standard form                          | Weaker / more-general form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|-----------------------------------------------------|---------------------------------------------------|-------------------|---------------------------------|
| 1 | the function: `branchChar p (p−1) (1−s) u`      | the `(p−1)`-branch character at exponent `1−s`      | the bare power map `a ↦ a^σ` (`σ = 1−s`)          | **YES**           | `branchChar p (p−1) (1−s) u = ⟨u⟩^{1−s}` only because `ω(u)^{p−1}=1` (used inside the proof, `hpow1`). The genuinely-general statement is about `onePAdicPow` / `addChar_of_value_at_one` at base `⟨u⟩ ∈ 1+pℤ_p`, with **no** `branchChar`, no `p−1`, no `ω`. The `branchChar (p−1)` wrapper is purely an L-function-presentation artefact. |
| 2 | base `⟨a⟩ = angleUnit p u` (for a unit `u`)     | the angle-unit of `u : ℤ_[p]ˣ`                       | any `a ∈ 1 + pℤ_p` (any principal unit)           | **YES**           | nothing in the math needs the base to be an *angle-unit of a unit*; it only needs `a − 1 ∈ pℤ_p` (so that `log_p a` is defined and `a^σ = exp(σ log_p a)`). Generalising the base to an arbitrary principal unit is CHEAP. |
| 3 | exponent reparam. `1 − s`, evaluation at `s=1`  | `σ = 1−s`, limit as `s→1`                            | `σ → 0` form `σ⁻¹(a^σ − 1) → log_p a`             | **YES** (cosmetic)| the `1−s`/`s=1`/sign-flip is a fixed affine change of variable; the underlying limit is the `σ→0` derivative. Trivial to restate. |
| 4 | target field `ℤ_[p]`/`ℚ_[p]`                    | concrete                                            | any complete nonarch. field ⊇ ℚ_p (e.g. ℂ_p)      | possible but EXPENSIVE | would require porting `pZpLog`/`pZpExp`/`onePAdicPow` to the general field (they are stated for `ℤ_[p]`); a real development, not a mechanical weakening. Not the primary lever. |
| 5 | `hp2 : p ≠ 2`                                    | oddness assumed                                     | the derivative law holds for `p=2` too (on `1+4ℤ_2`) | partial         | `pZpLog`/`pZpExp` are project odd-`p` objects (the convergence ball `‖w‖^{p−1}<p⁻¹` and `‖2⁻¹‖_2=2` corner). The general fact is true for `p=2` on the right ball, but the project's log/exp API would need the `p=2` extension first. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.** The hypotheses on `p` are mild, but the
*statement* is wrapped in three project-specific specialisations that the literature-standard form
does not have: (1) the `branchChar p (p−1) (1−s) u` envelope instead of the bare power map; (2) the
base restricted to `angleUnit p u` instead of an arbitrary principal unit; (3) the fixed `1−s`-at-`s=1`
reparametrisation instead of the clean `σ→0` derivative.
Number of weakening opportunities found: **3 cheap/cosmetic (axes 1–3) + 2 expensive/structural (axes 4–5).**

Proposed restatement (the mathlib-shaped general form — derivative of the p-adic power map):

```lean
-- the genuinely-general, branchChar-free statement (over the project's onePAdicPow / pZpLog):
theorem tendsto_onePAdicPow_sub_one_div {a : ℤ_[p]}
    (ha : a - 1 ∈ Ideal.span {(p : ℤ_[p])}) (hp2 : p ≠ 2) :
    Filter.Tendsto (fun s : ℤ_[p] => (s : ℚ_[p])⁻¹
        * (((PadicInt.onePAdicPow p a ha s : ℤ_[p]) : ℚ_[p]) - 1))
      (nhdsWithin 0 {s | s ≠ 0})
      (nhds ((pZpLog p a : ℤ_[p]) : ℚ_[p])) := …
```

i.e. `s⁻¹(a^s − 1) → log_p a` as `s → 0`, for any principal unit `a`. The current
`tendsto_branch_denom_div` is then the affine specialisation (`s ↦ 1−s`, base `⟨u⟩`, sign flip, plus
`branchChar (p−1) = ⟨·⟩^{·}` via `ω^{p−1}=1`).

Cost of restatement: **CHEAP–MODERATE.** Axes 1–3 are mechanical (strip the `branchChar` wrapper,
generalise the base hypothesis, change variable). The proof body barely changes — it already factors
through `onePAdicPow`/`padicExp`/`pZpLog` and the quadratic exp-tail bound. (Cost does not change the
bucket — see gate.) The expensive axes (4–5: general nonarch. field, `p=2`) are out of scope of a
mechanical generalisation and would be separate developments.

### Modern-idiom check (Phase 4c) — the Bourbaki-2.0 question

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | hypotheses are already minimal (`p ≠ 2`, a unit); nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | **already done** | — | the statement is *already* a filter `Tendsto` with `nhdsWithin` — the idiomatic modern spelling of a one-sided/punctured limit. No improvement available; this is the target form. |
|  3 | construct an object → universal-property class?                                                            | no       | — | it is a limit statement, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | partial  | the base hypothesis `a − 1 ∈ Ideal.span {p}` could be a `[·]`-membership in the principal-units subgroup `1 + pℤ_p` once that is a bundled object | minor; the real modernisation is the *derivative* framing below |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                           | partial  | generalise `ℤ_[p]` to a complete nonarch. field (axis 4 of Phase 4b) | enables ℂ_p / extension use, but EXPENSIVE (needs `pZpLog`/`onePAdicPow` ported); a def-layer decision |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary structure?                                                               | no       | — | n/a |
|  8 | **`Tendsto` difference-quotient → `HasDerivAt` / `deriv`?** (the genuine modern-idiom lever here)          | **YES**  | restate as `HasDerivAt (fun s => (onePAdicPow p a ha s : ℚ_[p])) (log_p a) 0`, i.e. give the p-adic power map an actual *derivative* in mathlib's `HasDerivAt` framework, with this `Tendsto` as the unfolded consequence | **this is the real downstream consequence**: a `HasDerivAt` statement composes with mathlib's entire calculus API (`HasDerivAt.comp`, chain rule, `deriv_add`, uniqueness), turning a one-off limit into reusable p-adic differential calculus. The current `Tendsto` form is a bespoke limit that composes with nothing. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it lives one layer down, at the def/API level, not in this
signature.** The Bourbaki-2.0 move is **not** to re-spell *this* theorem (it is already an idiomatic
filter `Tendsto`), but to recognise that the *right mathlib object* is a `HasDerivAt` for the p-adic
power map `s ↦ a^s` (derivative `log_p a` at `s = 0`), built on a mathlib-native p-adic
exponential/logarithm — which **mathlib does not have at all** (Phase 5). With concrete downstream
consequences: a `HasDerivAt`/`deriv` statement plugs into mathlib's calculus toolbox (chain rule,
linearity, uniqueness of derivative), whereas the standalone `Tendsto` difference quotient is inert.
So the modern-idiom finding is real and has teeth, but it points at a **definitional development**
(p-adic `exp`/`log` + their `HasDerivAt` API), of which this lemma would be a corollary — not at a
restatement the skill can apply to the lemma in isolation.

---

### Diamond / defeq risk — `tendsto_branch_denom_div`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status (Phase 5): `tendsto_branch_denom_div`

Searched the user's current form, the literature-standard general form (derivative of the p-adic power
map / `(a^s−1)/s → log_p a`), AND the modern-idiom form (`HasDerivAt` of the power map).

[A] Lean-Finder       "p-adic power function derivative log", "tendsto (a^s - 1)/s p-adic", "derivative of p-adic exponential / a^s at 0"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D) + name-pattern (E) for every candidate name/shape.

[B] Loogle (substitute: grep for the type shape)   `Tendsto (fun s => s⁻¹ * (addChar … s - 1)) …`, `HasDerivAt (onePAdicPow …) …`, any `Tendsto`/`deriv` attached to `addChar_of_value_at_one`   **no hits.** grep of `addChar_of_value_at_one` / `mahlerSeries` across all of mathlib returns only the *construction* + *continuity* API (`addChar_of_value_at_one`, `continuous_addChar_of_value_at_one`, `coe_addChar_of_value_at_one`, `addChar_of_value_at_one_def`, `eq_addChar_of_value_at_one`) in `Mathlib/NumberTheory/Padics/AddChar.lean`. **No `HasDerivAt`, no `Tendsto`-difference-quotient, no `nhds`/`deriv` lemma** is attached to it anywhere.

[C] LeanSearch        "derivative of p-adic power function equals p-adic logarithm", "limit of (a to the s minus 1) over s p-adic"   n/a (LeanSearch tool not callable) → substituted with [D]/[E]. No equivalent surfaced by grep.

[D] Grep mathlib src  `grep -rn "padicLog\|Padic.*[Ll]og" .lake/packages/mathlib/Mathlib/` (excluding `padicVal*`)   **EMPTY.** Mathlib has **no p-adic logarithm at all** (and hence no "derivative of `a^s` = `log_p a`" lemma). The `Mathlib/Analysis/SpecialFunctions/{ExpDeriv,Pow/Deriv,Complex/LogDeriv}.lean` files exist but are **archimedean** (`Real`/`Complex` exp/log/rpow) — they do not apply to a p-adic field. `Mathlib/NumberTheory/Padics/` contains `AddChar.lean`, `Complex.lean`, `MahlerBasis.lean`, … but **no exp/log/derivative** development.

[E] Name pattern      `padicExp`, `padicLog`, `pZpLog`, `onePAdicPow`, `addChar_of_value_at_one`, `HasDerivAt … Padic`   `padicExp`/`padicLog`/`pZpLog`/`onePAdicPow` exist **only in the project** (`PadicLFunctions/PadicExp.lean`, `Interpolation/Branches.lean`), not in mathlib. The Lean-3 mathlib precedent (Narayanan, arXiv 2302.14491) was **not** ported to Lean-4 mathlib (`grep` for `teichmuller`/`padic_L_function` in `Mathlib/NumberTheory/` → empty).

Concluded: **not in mathlib (all methods exhausted, plus both the literature-standard general form and
the modern `HasDerivAt` form).** Mathlib supplies exactly **one** relevant primitive —
`PadicInt.addChar_of_value_at_one` (the Mahler-series continuous additive character `s ↦ y^s`, the base
on which the project's `onePAdicPow` is built) — but it carries **no analytic theory** (no derivative,
no tangent line, no difference-quotient limit). Everything analytic here (`padicExp`, `padicLog`,
`pZpLog`, the quadratic tail bound, the squeeze) is project-local.

---

### Call sites — `tendsto_branch_denom_div` (Phase 6.0)

Internal use count: **1** (within the project, NOT counting the declaring theorem)
External-to-file callers: **0 distinct files** (the single use is in the *same* file)

| Caller file:line               | Usage pattern (one-line excerpt)                                              |
|--------------------------------|-------------------------------------------------------------------------------|
| ResidueZeta.lean:1797          | `rw [hLq]; exact tendsto_branch_denom_div p hp2 (u := u)` — supplies the **denominator limit** (Step 2 of `tendsto_sub_one_mul_zetaPBranch`, **RJW Theorem 7.1(ii)**, the residue/simple-pole statement). The `(s−1)⁻¹·denom → −Lq` limit is then inverted (`hden.inv₀`) and multiplied by the numerator limit to get residue `1 − p⁻¹`. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the only other occurrences of the `(s−1)⁻¹·(⟨a⟩^{1−s} − 1)` difference-quotient pattern
    are inside `tendsto_branch_denom_div` itself; the residue theorem *calls* it rather than re-deriving.

What the call-sites pattern tells you: **K = 1 internal use, no external/downstream consumers, no
inline re-derivation.** Per the Phase-6.0 signal table this leans "possibly the wrong abstraction /
could be inlined" — but here the single use is a genuine multi-step analytic argument (a real squeeze
through the exp-tail bound, not a one-liner), and it is the *exact* lemma RJW factor out (Lemma 7.2(ii))
feeding their Theorem 7.1. So it is not junk. The signal's real message: this lemma's mathlib-worth
does **not** rest on heavy local reuse — it rests entirely on the upstreaming decision about the
p-adic exp/log/power machinery as a whole (cf. its sibling `norm_padicExp_sub_one_sub_self_le`, same
K=1, same conclusion).

---

### Composition check (Phase 6)

Can `tendsto_branch_denom_div` be derived from mathlib in ≤3 chained calls?

Attempt 1: a mathlib "derivative of `a^s` = `log_p a`" lemma, specialised.
  - Mathlib decls used: (none exist).
  - Result: **fails** — Phase 5 shows mathlib has no p-adic logarithm and no derivative/tangent-line
    lemma for the p-adic power map. Nothing to specialise.

Attempt 2: a `HasDerivAt`/`deriv` of `s ↦ a^s` plus `hasDerivAt.tendsto_slope`.
  - Mathlib decls used: `HasDerivAt`, `hasDerivAt_iff_tendsto_slope` (these *exist* generically).
  - Result: **fails** — the generic `HasDerivAt` machinery is real, but there is **no** `HasDerivAt`
    *instance/lemma* for the p-adic power map (`onePAdicPow`/`addChar_of_value_at_one`) to feed it.
    Establishing that `HasDerivAt` is itself the missing content (it would require `padicExp`/`padicLog`
    and the quadratic tail bound — the project's own development).

Attempt 3: assemble from the project primitives + mathlib's squeeze.
  - Mathlib decls used: `squeeze_zero_norm'`, `Tendsto.const_mul`, `nhdsWithin_le_nhds`,
    `continuous_norm`, `IsUltrametricDist`-tail infra.
  - Result: **this is exactly the project's proof** — and it is *not* a ≤3-call composition: it needs
    the exp/log bridge `padicExp_smul_padicLog_eq_onePAdicPow`, the quadratic tail bound
    `norm_padicExp_sub_one_sub_self_le` (itself resting on Legendre's `v_p(n!)` estimate), an algebraic
    `linear_combination` identity, the squeeze, and the constant add-back. A genuine multi-lemma
    analytic proof, not a composition.

Conclusion: **NOT-COMPOSABLE.** There is no p-adic exp/log/power-derivative in mathlib to compose
against; mathlib's generic `HasDerivAt`/`squeeze` tools are present but have no p-adic input to act on.

---

## Verdict: `tendsto_branch_denom_div`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the content is **standard** — both (i) the general derivative law
  `(a^s − 1)/s → log_p a` (textbook p-adic analysis) and (ii) RJW's **Lemma 7.2(ii)** (the project's
  exact source: the simple zero of `⟨a⟩^{1−s} − 1` at `s=1`, derivative `−log_p⟨a⟩`, producing the
  residue `1 − p⁻¹`). The Lean statement bolts this onto the project-specific `branchChar`/`angleUnit`
  envelope. A Lean-3 mathlib formalization of the surrounding p-adic-L machinery exists (Narayanan)
  but was **not** ported to Lean-4 mathlib.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 cheap/cosmetic narrowings
  (the `branchChar (p−1)` wrapper; base restricted to an angle-unit; the `1−s`-at-`s=1` reparam.) over
  the clean general "derivative of the p-adic power map", plus 2 expensive structural ones (general
  nonarch. field, `p=2`).
- Modern-idiom (Phase 4c): the genuine Bourbaki-2.0 lever is a **`HasDerivAt`** for the p-adic power
  map (concrete downstream: composes with mathlib's calculus API) — but it lives at the def/API layer
  mathlib lacks, not in this signature.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic logarithm, no p-adic power-map derivative,
  no analytic theory on `addChar_of_value_at_one`; the archimedean `ExpDeriv`/`Pow/Deriv` lemmas do
  not apply.
- Composition check (Phase 6): **NOT-COMPOSABLE** (nothing p-adic-analytic to compose from; the
  generic `HasDerivAt`/`squeeze` tools have no p-adic input).

**Rationale (why BORDERLINE, not a YES/NO):**

This is a *true, genuinely missing-from-mathlib* p-adic analytic fact, proved sorry-free — so it is
**not a NO** (Phase 5 NOT-found, Phase 6 NOT-COMPOSABLE). But four things block a clean YES, and each
is a judgment call the skill cannot ground in evidence alone:

1. **It cannot be PR'd standalone — it sits atop a definitional stack mathlib lacks entirely.** The
   statement mentions `branchChar`, `angleUnit`, `onePAdicPow`, and `pZpLog` — all project-local —
   and its proof runs through `padicExp` and the quadratic exp-tail bound. Mathlib has **no** p-adic
   logarithm, **no** p-adic exponential, and **no** analytic theory on its one relevant primitive
   (`addChar_of_value_at_one`). Upstreaming this lemma necessarily means upstreaming a whole p-adic
   exp/log/power development first. Whether to undertake that BIG, multi-decl effort is a
   project/community-policy decision — exactly what the skill defers to the human. (This is the same
   blocker as its sibling `norm_padicExp_sub_one_sub_self_le`, with which it should travel.)

2. **The statement is in the wrong (project-specific) shape for mathlib (Phase 4b).** Mathlib's bar is
   "the right, general statement". The mathlib-appropriate object is the derivative of the *bare* p-adic
   power map `s ↦ a^s` for any principal unit `a` — not `branchChar p (p−1) (1−s) u` with the
   `ω^{p−1}=1` simplification and the `1−s`-at-`s=1` reparametrisation baked in. Whether to ship the
   general form (cheap restatement, but a deliberate API choice) is a human call.

3. **The truly idiomatic target is a `HasDerivAt`, not a `Tendsto` (Phase 4c).** A mathlib reviewer
   would likely want `HasDerivAt (s ↦ a^s) (log_p a) 0` (which composes with the calculus API) with
   this `Tendsto` as a corollary — i.e. the contribution is really a *derivative lemma for the p-adic
   power map*, a packaging/scope decision.

4. **It is a derived corollary, not the headline.** In RJW the headline is the residue Theorem 7.1;
   this is the supporting Lemma 7.2(ii). If anything from this circle is "the" mathlib contribution it
   is the p-adic exp/log + the power-map derivative API, with this branch-specific limit as a minor
   specialisation — a packaging judgment for the human.

The K=1 single-call-site (no external consumers, no inline re-derivation — Phase 6.0) reinforces that
the lemma's mathlib-worth does *not* come from local reuse pressure; it comes entirely from the
upstreaming decision about the p-adic-exp/log/power machinery as a whole. That is a human call.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic **exponential / logarithm / power-map** development
   to mathlib as a unit (`padicExp`, `padicLog`/`pZpLog`, the convergence-ball API, `onePAdicPow`)?
   This lemma is meaningless without that stack — it should travel *with* it (and with its sibling
   `norm_padicExp_sub_one_sub_self_le`), not alone.
2. If yes to (1): should the contribution be the **general** derivative of the p-adic power map —
   `s⁻¹(a^s − 1) → log_p a` (as `s→0`) for any principal unit `a`, stripped of the `branchChar`/`p−1`/
   angle-unit envelope (Phase 4b restatement) — rather than this branch-character-specific form?
3. If yes to (1): should it be stated as a **`HasDerivAt`** (`HasDerivAt (s ↦ a^s) (log_p a) 0`) so it
   composes with mathlib's calculus API (Phase 4c), with the current `Tendsto` form derived as a
   corollary?
4. Should this be generalised from `ℤ_[p]`/`ℚ_[p]` to an arbitrary complete nonarchimedean field
   ⊇ ℚ_p (e.g. ℂ_p), and/or extended to `p = 2` — accepting that both are EXPENSIVE (they require the
   underlying `pZpLog`/`onePAdicPow` machinery to be generalised first)?
5. If you do **not** plan to upstream the p-adic exp/log/power machinery: then this lemma is correctly
   a permanent project-local helper (K=1 use in the residue theorem) and should be dropped from
   mathlib consideration entirely. Is that the case?

**Next action:** user answers; re-run `/mathlibable tendsto_branch_denom_div` — ideally **together
with** `/mathlibable PadicLFunctions.padicExp` and `…norm_padicExp_sub_one_sub_self_le`, since all
three are governed by the single upstreaming decision on the p-adic exp/log/power development. Likely
resolutions:
  - "Upstream the development" + general/`HasDerivAt` restatement → flips to
    **YES-but-generalise-first** (target = the bare power-map derivative, ideally `HasDerivAt`, shipped
    as part of the nonarchimedean-exp/log PR series).
  - "Keep project-local" → drop from mathlib consideration; it stays a fit-for-purpose helper feeding
    the residue/pole proof (RJW Theorem 7.1(ii)).

---

## Next step

User answers the five numbered questions above; re-run `/mathlibable tendsto_branch_denom_div`
(preferably alongside `/mathlibable PadicLFunctions.padicExp` and the sibling tail-bound lemma, since
this theorem's verdict is governed by the upstreaming decision on the p-adic exp/log/power definitions
it is built on) to resolve to either **YES-but-generalise-first** (upstream the development, restated
as the general — ideally `HasDerivAt` — derivative of the p-adic power map) or
drop-from-consideration (keep as a project-local helper).
