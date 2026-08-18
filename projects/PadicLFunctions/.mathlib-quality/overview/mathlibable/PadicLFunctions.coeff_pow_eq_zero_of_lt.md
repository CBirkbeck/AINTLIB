# `/mathlibable` report — `PadicLFunctions.coeff_pow_eq_zero_of_lt`

**Final verdict: `NO-composable-from-mathlib`** (with strong cross-project duplication: the same
statement is re-derived ≥4 times across AINTLIB and is a 1–3 call composition of existing mathlib
lemmas — no new lemma is justified).

---

### Baseline (Phase 0)

- lake build:               not re-run (per task build note: stale/slow); **reasoned from source**.
  All dependencies read directly from `.lake/packages/mathlib/` and project files.
- decl `PadicLFunctions.coeff_pow_eq_zero_of_lt`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:752`
- kind:                      `theorem`
- has sorry:                 no (the whole file has 0 `sorry`/`admit`; lemma body lines 752–755 are sorry-free)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — convergence of
  `exp`/`log` on a complete ultrametric `ℚ_[p]`-algebra; this lemma is a small power-series-order
  helper used inside the evaluation/summability bridge.

The declaration (verbatim):

```lean
omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- `[Xᵏ](Gⁿ) = 0` for `k < n` when `[X⁰]G = 0` (order of `Gⁿ` is `≥ n`). -/
theorem coeff_pow_eq_zero_of_lt (G : PowerSeries ℚ_[p]) (hc0 : constantCoeff G = 0)
    {n k : ℕ} (hkn : k < n) : (coeff k (G ^ n) : ℚ_[p]) = 0 :=
  coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hkn)
    (le_order_pow_of_constantCoeff_eq_zero n hc0))
```

`open PowerSeries` is in scope (line 463), so `coeff`, `constantCoeff`, `order` here are mathlib's
`PowerSeries.*`. Both lemmas in the proof body are **mathlib lemmas** (see Phase 5).

---

### Statement (Phase 1)

`PadicLFunctions.coeff_pow_eq_zero_of_lt` is a theorem stating the following:

Let `G ∈ ℚ_p[[X]]` be a formal power series with zero constant term (`[X⁰]G = 0`). Then for every
`n` and every `k < n`, the `k`-th coefficient of `Gⁿ` vanishes: `[Xᵏ](Gⁿ) = 0`. Equivalently:
`Xⁿ ∣ Gⁿ` whenever `X ∣ G`, so the order of `Gⁿ` is at least `n`.

This is the elementary super-additivity of the `X`-adic order: `ord(G) ≥ 1` (constant term zero) ⇒
`ord(Gⁿ) ≥ n·ord(G) ≥ n` ⇒ all coefficients below index `n` vanish.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the prime; only used so the coefficient ring is `ℚ_[p]`.
- `(G : PowerSeries ℚ_[p])` — the power series. The coefficient ring `ℚ_[p]` plays **no role**
  (the result holds over any `Semiring`); confirmed by the `omit` on the three analysis typeclasses.
- `{n k : ℕ}` — exponent and coefficient index.

Hypotheses (Lean side):
- `(hc0 : constantCoeff G = 0)` — `G` has zero constant term (i.e. `X ∣ G`).
- `(hkn : k < n)` — index strictly below the exponent.

Conclusion (math): `[Xᵏ](Gⁿ) = 0`.
Conclusion (Lean): `(coeff k (G ^ n) : ℚ_[p]) = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step power-series-order helper lemma (not a named theorem, not a `## Main results`
entry, not a new structure). It is a corollary of standard order/divisibility facts.

(Note: literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a `term`-mode proof). One-liner verdict: **n/a — kind is
`theorem`, not `def`** (the 2b exemption machinery applies to definitions). Recorded as a note only.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "formal power series order of f^n coefficient vanishes constant term zero X^n divides"                  | yes  | `ord(0)=∞`; constant term ≠ 0 ⇔ invertible ⇔ not divisible by `X`; composition needs no constant term | impan.pl notes, Wikipedia FPS, ScienceDirect — all elementary/standard |
|  2 | WebSearch (general form)         | "order of formal power series superadditive valuation X-adic order of power f^n at least n times order" | yes  | `ord` is a valuation: `ord(0)=∞`, `ord(φ)=min index of nonzero coeff`; complete valued field `R((X))` | nLab "power series", arXiv math/0307238 (monomial valuations on `k[[X]]`), Encyclopedia of Math |
|  3 | WebSearch (named-after / aliases)| "Stanley Enumerative Combinatorics order of power series product superadditive ord(fg) ≥ ord f + ord g"  | yes  | super-additivity of order; standard in Stanley *EC* (Vol. 1 §1, formal power series), Ch. 6 algebraic FPS | the property is bookwork; no special name |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of order/valuation on `R[[X]]`")          | n/a  | —                                | **MCP server not configured in this environment.** Substituted by extra WebSearch breadth (rows 1–3, 9–10). |
|  5 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                      | n/a  | (directories absent)             | recorded n/a — no references dir present |
|  6 | nLab                             | "power series" (ncatlab.org/nlab/show/power+series)                                                     | yes  | order/valuation on `R[[X]]`; `(X)`-adic completion of `R[X]`; `X`-divisibility ↔ vanishing constant term | clean abstract statement of the order |
|  7 | nCatLab (categorical)            | (same page; categorical angle)                                                                          | n/a  | —                                | not a categorical concept beyond the valuation already in row 6 |
|  8 | Stacks Project (alg geom)        | order / valuation of power series                                                                       | n/a  | —                                | the `(X)`-adic order is a commutative-algebra fact; Stacks covers it under DVRs/valuations but adds nothing beyond rows 2/6 — recorded n/a (not the right venue for this elementary corollary) |
|  9 | MathOverflow / Math.StackExchange| "nLab formal power series order valuation X-adic constant coefficient divisibility"                     | yes  | PlanetMath "formal power series": constant term ≠ 0 ⇔ unit ⇔ not divisible by `X` | standard Q&A material; nothing nonstandard |
| 10 | recent arXiv (last 5 years)      | "an invitation to formal power series" (arXiv:2205.00879); arXiv:1803.09646 (FPS solutions of ODEs)     | yes  | order/valuation `ord`; `ord(fg)=ord f+ord g` over a domain | confirms super-additivity (equality over a domain); modern survey, same elementary statement |

The protocol passed: WebSearch ran ≥3 distinct queries at different generality levels (specific
coefficient-vanishing form, general valuation/super-additivity form, named/textbook form); local
references checked (absent → n/a); nLab checked (hit); Stacks/nCatLab/MathOverflow/arXiv each
checked with reason. ChatGPT MCP is unavailable here and is recorded n/a with its query substituted
by additional WebSearch breadth.

### Literature summary (Phase 3)

Concept identified as: **the `X`-adic order (valuation) of a formal power series, and its
super-additivity under products** — equivalently `X^n ∣ φ ⟺ coeff m φ = 0 ∀ m < n`.
Sources agree on the standard form: **yes**. The order `ord : R[[X]] → ℕ∞` with `ord(0)=∞`,
`ord(φ)=` least index of a nonzero coefficient, is a valuation; `X ∣ φ ⟺` constant term `= 0`;
`ord(φ·ψ) ≥ ord φ + ord ψ` (equality when `R` is a domain), hence `ord(φⁿ) ≥ n·ord φ`.
Most general standard form: holds over **any commutative semiring/ring** `R` (the field `ℚ_[p]`
is irrelevant). The specific statement here — "constant term zero ⇒ `Gⁿ` has no coefficient below
index `n`" — is a textbook one-liner (Bourbaki *Algèbre* IV, Atiyah–Macdonald, Stanley *EC1* §1).
Generality dimensions where the literature varies: only the coefficient ring (field → domain →
general (semi)ring); the literature's most general form is the (semi)ring form, which mathlib has.
Disagreement with the literature: **none**.

---

### Generality analysis — `PadicLFunctions.coeff_pow_eq_zero_of_lt` (Phase 4)

Literature-standard form (from Phase 3): over any `Semiring R`, if `constantCoeff φ = 0` then
`coeff k (φ^n) = 0` for `k < n` (`Xⁿ ∣ φⁿ`).

| # | Parameter / hypothesis        | Current Lean form                  | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------|--------------------------|---------------------|---------------------------------|
| 1 | coefficient ring `ℚ_[p]`     | `PowerSeries ℚ_[p]` (a complete field) | any `Semiring R`     | **yes**             | proof uses only `order`/`X`-divisibility, which mathlib states over `[Semiring R]`; `ℚ_[p]` plays no role (the `(... : ℚ_[p])` cast is the identity coercion on the coefficient — `coeff k (G^n)` already lives in `ℚ_[p]`) |
| 2 | `(hc0 : constantCoeff G = 0)` | constant term zero                  | constant term zero       | NO                  | this is the essential hypothesis (`X ∣ G`); without it the conclusion is false |
| 3 | `(hkn : k < n)`               | strict inequality                   | strict inequality        | NO                  | sharp: `coeff n (G^n)` need not vanish |
| 4 | `[Fact p.Prime]`             | prime `p`                           | (not needed)             | yes                 | only present to name `ℚ_[p]`; the general form drops it entirely |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `ℚ_[p]` specialisation of a
fact that holds over any semiring).
Number of weakening opportunities found: 2 (coefficient ring; drop `[Fact p.Prime]`).
Proposed maximally-general restatement:

```lean
theorem PowerSeries.coeff_pow_eq_zero_of_lt {R : Type*} [Semiring R]
    {φ : R⟦X⟧} (hc0 : constantCoeff φ = 0) {n k : ℕ} (hkn : k < n) :
    coeff k (φ ^ n) = 0 :=
  coeff_of_lt_order _ ((Nat.cast_lt.2 hkn).trans_le (le_order_pow_of_constantCoeff_eq_zero n hc0))
```

Cost of restatement: **CHEAP** — the proof is identical; only the ring is generalised.

**However**, Phase 5 shows mathlib *already has the building blocks for the general form* (the
order/`X`-divisibility lemmas are stated over `[Semiring R]`), and Phase 6 shows the general form is
itself a 1–3-call composition. So the right action is not "generalise this project lemma and PR it"
(`YES-but-generalise-first`) but "inline the existing mathlib composition" — see the verdict.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Downstream |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                          | no       | already typeclass-driven (`[Semiring R]`) | — |
|  2 | sequences/metric → filters/topological?                                                           | no       | purely algebraic; no convergence here | — |
|  3 | constructs an object where a universal-property class would characterise it?                      | no       | it's a coefficient-vanishing fact, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | n/a | — |
|  5 | vector-space/field-specific → modules/(semi)ring?                                                 | **yes**  | drop `ℚ_[p]` to `[Semiring R]` (same as 4a row 1) | every `R⟦X⟧` development reuses it — but **mathlib already supports this generality** in the building blocks |
|  6 | 1-categorical → higher-categorical?                                                               | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoids?                                                       | no       | the indices `n,k : ℕ` are intrinsic to one-variable power series order | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (typeclass-weaken `ℚ_[p]` → `[Semiring R]`), but this is the *same*
weakening as 4a/4b — and crucially the mathlib **order API already lives at exactly that
generality**, so the "modernisation" is not a new contribution: it is what mathlib already provides.
Real mathematical improvement: none beyond what mathlib already has — this is a redundancy to
remove, not a form to upstream.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder        natural-language ("coeff of power of series with zero constant term") — **n/a: Lean-Finder MCP not configured in this environment**
[B] Loogle             `coeff _ (_ ^ _) = 0`, `constantCoeff _ = 0 → _` — **n/a: `lean_loogle` MCP not configured**
[C] LeanSearch         "coefficient of nth power of power series vanishes below n / X^n divides f^n" — **n/a: `lean_leansearch` MCP not configured**
[D] Grep mathlib src   `coeff_of_lt_order`, `le_order_pow_of_constantCoeff_eq_zero`, `order_pow`, `X_dvd_iff`, `X_pow_dvd_iff`, `coeff_pow_eq_zero`, `eventually_coeff_pow_eq_zero` over `.lake/packages/mathlib/` — **HITS** (see below)
[E] Name pattern       grep for `coeff_of_lt_order` / `le_order_pow` / `X_pow_dvd_iff` decl heads — **HITS**

Searched for both the user's `ℚ_[p]` form and the literature-standard `[Semiring R]` form.

Findings (all in `Mathlib/RingTheory/PowerSeries/`):

- `PowerSeries.coeff_of_lt_order` — `Order.lean:93`, over `[Semiring R]`:
  `(n : ℕ) (h : ↑n < order φ) : coeff n φ = 0`. **Used verbatim in the target's proof.**
- `PowerSeries.le_order_pow_of_constantCoeff_eq_zero` — `Order.lean:231`, over `[Semiring R]`:
  `(n : ℕ) (hf : φ.constantCoeff = 0) : n ≤ (φ ^ n).order`. **Used verbatim in the target's proof.**
- `PowerSeries.le_order_pow` — `Order.lean:202`: `n • order φ ≤ order (φ ^ n)`.
- `PowerSeries.order_pow` — `Order.lean:444`: `order (φ ^ n) = n • order φ` (the sharp version).
- `PowerSeries.X_dvd_iff` — `Basic.lean:501`: `X ∣ φ ↔ constantCoeff φ = 0`.
- `PowerSeries.X_pow_dvd_iff` — `Basic.lean:492`: `Xⁿ ∣ φ ↔ ∀ m, m < n → coeff m φ = 0`.
- `pow_dvd_pow_of_dvd` — `Mathlib/Algebra/Divisibility/Basic.lean:201`: `a ∣ b → aⁿ ∣ bⁿ`.
- `PowerSeries.HasSubst.eventually_coeff_pow_eq_zero` — `Substitution.lean:145`: the *filter-level*
  cousin (`∀ᶠ m, ∀ n' ≤ n, coeff n' (f^m) = 0`); different shape, not the exact statement.

Concluded: **"not in mathlib as a single named lemma `coeff k (φ^n) = 0 from k < n ∧ constantCoeff = 0`,
but mathlib has all the building blocks (the `order` API and the `X_dvd`/`X_pow_dvd` characterisation),
each stated at full `[Semiring R]` generality — composition yields our form."** (Methods A–C
unavailable here; D and E exhaustively confirm the building blocks. The target's own proof body is
the proof that the composition works.)

---

### Call sites — `PadicLFunctions.coeff_pow_eq_zero_of_lt` (Phase 6.0)

Internal use count: **1** (within the PadicLFunctions project, excluding the declaring file).
External-to-file callers: 1 file (the declaring file uses it once internally too).

| Caller file:line                                   | Usage pattern (one-line excerpt)                                            |
|----------------------------------------------------|------------------------------------------------------------------------------|
| `PadicLFunctions/PadicExp.lean:790` (declaring file)| `rw [coeff_pow_eq_zero_of_lt p G hG0 hlt, mul_zero, zero_smul]`              |

Inline-derivation / duplicate grep (was the equivalent re-derived elsewhere instead of using this?):

- **`PadicLFunctions/IwasawaProof/GaloisAction.lean:706`** — a *separate* `private theorem
  coeff_pow_eq_zero_of_lt` over `PowerSeries ℂ_[p]`, used at lines 767, 786, 789. Proof:
  `PowerSeries.X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hG0) n) k hkn`.
  → a second, independent copy of the *same lemma* inside the *same project* (different field).
- **`FltRegularBernoulli/.../DworkParameter/Part3.lean:305`** — `coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero`
  over generic `[CommRing A]` (polynomial-coerced); proof identical:
  `coeff_of_lt_order d ((ENat.coe_lt_coe.mpr hdn).trans_le (le_order_pow_of_constantCoeff_eq_zero n hconst))`.
- **`FltRegularBernoulli/.../FiniteArtinHasseFormal.lean:33`** and **`FiniteLogAdditivity.lean:34`** —
  same two-line `le_order_pow_of_constantCoeff_eq_zero` + `coeff_of_lt_order` pattern inline.
- **`HasseWeil/.../FormalGroup/Logarithm.lean:340` and `:359`** — same pattern again (twice).

So the statement is independently re-derived in **≥4 AINTLIB files across 3 projects** (and twice
within PadicLFunctions itself). This is a textbook NO-composable signal: a thin wrapper around two
mathlib lemmas that everyone re-discovers because there is no single mathlib lemma to reach for.

### Composition check (Phase 6)

Can `coeff_pow_eq_zero_of_lt` be derived from mathlib in ≤3 chained calls? **Yes — two independent ways**, both already exhibited in the repo.

Attempt 1 (order API — the target's own proof, 2 calls):
```lean
example {R} [Semiring R] {φ : R⟦X⟧} (hc0 : constantCoeff φ = 0) {n k : ℕ} (hkn : k < n) :
    coeff k (φ ^ n) = 0 :=
  coeff_of_lt_order _ ((Nat.cast_lt.2 hkn).trans_le (le_order_pow_of_constantCoeff_eq_zero n hc0))
```
- Mathlib decls used: `PowerSeries.coeff_of_lt_order`, `PowerSeries.le_order_pow_of_constantCoeff_eq_zero`.
- Result: **succeeds** (this is literally the target's body, modulo the irrelevant `ℚ_[p]` cast).

Attempt 2 (divisibility API — `GaloisAction.lean`'s proof, 3 calls):
```lean
example {R} [Semiring R] {φ : R⟦X⟧} (hc0 : constantCoeff φ = 0) {n k : ℕ} (hkn : k < n) :
    coeff k (φ ^ n) = 0 :=
  X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hc0) n) k hkn
```
- Mathlib decls used: `PowerSeries.X_dvd_iff`, `pow_dvd_pow_of_dvd`, `PowerSeries.X_pow_dvd_iff`.
- Result: **succeeds** (verbatim the sister copy's proof).

Conclusion: **COMPOSABLE** (≤3 mathlib calls, two routes; both are real compositions per the Phase 6
heuristics — projection/`.1`/single-application chains, no `rw;ring_nf;aesop` glue, no intermediate
reasoning).

---

## Verdict: `PadicLFunctions.coeff_pow_eq_zero_of_lt`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the `X`-adic order is a standard valuation (`ord(fg) ≥ ord f + ord g`);
  "constant term zero ⇒ `Gⁿ` vanishes below index `n`" is textbook (nLab, Wikipedia, Stanley *EC1*,
  Encyclopedia of Math). No special name; most general form is over any (semi)ring.
- Generality analysis (Phase 4): **STRICTLY NARROWER** than standard (the `ℚ_[p]` specialisation of a
  semiring fact) — but the general form is exactly the generality mathlib's `order` API *already*
  provides, so this is a redundancy to remove, not a form to upstream.
- Mathlib search (Phase 5): no single named lemma, but **all building blocks present** at full
  `[Semiring R]` generality (`coeff_of_lt_order`, `le_order_pow_of_constantCoeff_eq_zero`,
  `X_dvd_iff`, `X_pow_dvd_iff`, `pow_dvd_pow_of_dvd`).
- Composition check (Phase 6): **COMPOSABLE** in 2 mathlib calls (order route) or 3 (divisibility
  route) — both already exhibited verbatim elsewhere in the repo.

**Rationale (1–2 paragraphs):**

This lemma is the `ℚ_[p]`-specialisation of a one-line commutative-algebra fact, and mathlib already
ships the machinery to prove it directly. The declaration's own proof is nothing but
`coeff_of_lt_order _ (… le_order_pow_of_constantCoeff_eq_zero n hc0)` — two mathlib lemmas, both
stated over `[Semiring R]`, both in scope in this file via the transitive import of
`Mathlib.RingTheory.PowerSeries.Order`. There is no missing API and no new mathematical content: the
order/valuation framework (`order_pow`, `le_order_pow_of_constantCoeff_eq_zero`) and the
`X`-divisibility characterisation (`X_dvd_iff`, `X_pow_dvd_iff`) cover this completely. A standalone
`ℚ_[p]` lemma adds only a redundant name.

The call-site evidence reinforces NO decisively rather than YES. The lemma has just **one** internal
use, and the *identical statement is independently re-derived at least four more times across the
repo* — a second `private` copy over `ℂ_[p]` in `IwasawaProof/GaloisAction.lean:706` (used 3×),
a `[CommRing A]` copy in `FltRegularBernoulli/.../Part3.lean:305`, and inline two-line repeats in
`FltRegularBernoulli/.../FiniteArtinHasseFormal.lean`, `.../FiniteLogAdditivity.lean`, and
`HasseWeil/.../Logarithm.lean` (twice). Everyone re-discovers the same `coeff_of_lt_order ∘
le_order_pow_of_constantCoeff_eq_zero` composition because there is no single mathlib lemma to reach
for. The fix is not to PR a `ℚ_[p]` wrapper (it would not even be the right generality), but to
inline the 2–3-call mathlib composition at the (few) call sites — or, at most, to extract **one**
project-local `Common/` helper over `[Semiring R]` to absorb all the duplicates. Whether mathlib
should gain a convenience lemma `coeff_pow_eq_zero_of_lt` is a separate, weak question (see the note
under Next step); on its own merits this specific declaration is composable-from-mathlib and should
not ship as-is.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is a ≤3 mathlib-call composition.

Mathlib building blocks (full paths):
- `PowerSeries.coeff_of_lt_order` — `.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Order.lean:93`
- `PowerSeries.le_order_pow_of_constantCoeff_eq_zero` — `…/PowerSeries/Order.lean:231`
- `PowerSeries.X_dvd_iff` — `…/PowerSeries/Basic.lean:501`
- `PowerSeries.X_pow_dvd_iff` — `…/PowerSeries/Basic.lean:492`
- `pow_dvd_pow_of_dvd` — `.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean:201`

Composition sketch (≤3 lines, pick either):
```lean
-- order route (2 calls — the target's own body):
coeff_of_lt_order _ ((Nat.cast_lt.2 hkn).trans_le (le_order_pow_of_constantCoeff_eq_zero n hc0))
-- divisibility route (3 calls — GaloisAction.lean's body):
X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hc0) n) k hkn
```

Call sites in our project (from Phase 6.0): **K = 1** for this declaration
(`PadicExp.lean:790`), plus the same statement re-derived in ≥4 other locations across the repo.

Refactor plan:
1. At `PadicExp.lean:790`, replace `coeff_pow_eq_zero_of_lt p G hG0 hlt` with the order-route
   composition above (`hG0` is the `constantCoeff G = 0` hypothesis; `hlt` is `k < n`); the
   surrounding `rw [..., mul_zero, zero_smul]` is unchanged. Then delete the `theorem` at
   `PadicExp.lean:752` (and its `omit`).
2. Optionally (recommended, to kill all duplication at once): extract a single
   `PowerSeries.coeff_pow_eq_zero_of_lt {R} [Semiring R] …` into the project's `Common/` and point
   the `ℚ_[p]` site (`PadicExp.lean:790`), the `ℂ_[p]` copy (`GaloisAction.lean:706`, 3 uses), the
   `[CommRing A]` copy (`FltRegularBernoulli Part3.lean:305`), and the inline repeats
   (`FiniteArtinHasseFormal.lean:33`, `FiniteLogAdditivity.lean:34`, `HasseWeil Logarithm.lean:340,359`)
   all at it. This is a cross-project dedup ticket, not a mathlib PR.

Next action: delete `PadicLFunctions.coeff_pow_eq_zero_of_lt` and inline the mathlib composition at
its single call site (`PadicExp.lean:790`); raise a cross-project `Common/`-extraction cleanup ticket
to absorb the ≥4 sibling duplicates over `[Semiring R]`.

---

## Next step

Delete `PadicLFunctions.coeff_pow_eq_zero_of_lt` and inline the 2-call mathlib composition
`coeff_of_lt_order _ ((Nat.cast_lt.2 hkn).trans_le (le_order_pow_of_constantCoeff_eq_zero n hc0))`
at its one call site (`PadicExp.lean:790`). Recommended follow-up: a cross-project cleanup ticket to
extract a single `[Semiring R]` helper in `Common/` (or upstream a convenience
`PowerSeries.coeff_pow_eq_zero_of_lt` to mathlib's `RingTheory/PowerSeries/Order.lean` if a reviewer
wants the named convenience lemma) and route all ≥4 in-repo duplicates through it. The mathlib-PR
angle is at most a *minor convenience lemma*, not a content gap — hence the verdict stays
NO-composable-from-mathlib for this specific declaration.
