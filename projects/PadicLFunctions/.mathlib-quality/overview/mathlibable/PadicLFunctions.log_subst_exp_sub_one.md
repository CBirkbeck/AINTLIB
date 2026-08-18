# `/mathlibable` report — `PadicLFunctions.log_subst_exp_sub_one`

**Final verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING — the
statement is the classical "log inverts exp" formal-power-series identity, but it is
stated only over `ℚ_[p]` when the proof and the literature both live over any
characteristic-zero / `ℚ`-algebra commutative ring).

---

### Baseline (Phase 0)
- lake build:               build NOT re-run; reasoned from source (per task note — `lake build` is stale/slow in this checkout; the declaration and every dependency were read directly from source under `.lake/packages/mathlib/` and the project tree).
- decl `PadicLFunctions.log_subst_exp_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:540`
- kind:                      theorem
- has sorry:                 no (file `grep -c sorry\|admit` = 0)
- module docstring summary:  the p-adic `exp`/`log` power series (RJW Lem 5.14): `exp` converges on `‖x‖ < p^{−1/(p−1)}`, `log(1+y)` for `‖y‖ < 1`, and they invert each other on matched balls — realising `x^s := exp(s·log x)` for `s ∈ ℤ_p`, `x ∈ 1+pℤ_p`.

---

### Statement (Phase 1)

`PadicLFunctions.log_subst_exp_sub_one` is a **theorem** stating the following:

As formal power series over `ℚ_[p]`, substituting `exp − 1` into the logarithm
series `log(1+X) = X − X²/2 + X³/3 − ⋯` returns the identity series `X`. In standard
notation this is `log(1 + (exp(X) − 1)) = log(exp(X)) = X`: the algebraic statement
that the formal logarithm is a left/compositional inverse of the formal exponential.
It is exactly mathlib's `PowerSeries.logOf (exp) = X` (since
`PowerSeries.logOf f = (log A).subst (f − 1)`), specialised to `A = ℚ_[p]`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — fixes the prime; used **only** to name the coefficient ring `ℚ_[p]`.
- (implicit) the coefficient ring is `ℚ_[p]`, a complete normed field that is in particular a characteristic-zero commutative `ℚ`-algebra.

Hypotheses (Lean side):
- none beyond the ambient `p`/`Fact p.Prime` (the proof's `hg : HasSubst (exp ℚ_[p] − 1)` is discharged internally by `PowerSeries.HasSubst.exp_sub_one`).

Conclusion (math): `log(exp) = X` as formal power series — exp and log are mutually inverse over a ℚ-algebra.

Conclusion (Lean): `(PowerSeries.log ℚ_[p]).subst (exp ℚ_[p] − 1) = PowerSeries.X`

Both `exp` and `PowerSeries.log` here are **mathlib's** `PowerSeries.exp` /
`PowerSeries.log` (the file `open`s `PowerSeries`; there is no project-local `exp`/`log`
definition). The full proof uses only mathlib's formal-power-series API
(`derivative_subst`, `derivative_exp`, `derivative_X`, `Derivation.map_one_eq_zero`,
`coe_substAlgHom`, `subst_mul`, `subst_add`, `subst_X`, `constantCoeff_subst_eq_zero`,
`constantCoeff_exp`, `constantCoeff_log`, and `PowerSeries.derivative.ext`) plus the
project-local helper `oneAddX_mul_derivative_log` — which is itself already stated over
`(A : Type*) [CommRing A] [Algebra ℚ A]`. **Nothing `ℚ_[p]`-specific appears in the proof.**

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline — treated as BIG)
Reason: it is one of the two named "formal identities" the module is organised around
(decomposition E4 / RJW Lem 5.14), it is a theorem with a classical, literature-named
content (exp and log are inverse), and mathlib's own `Derivative.lean` docstring cites
the sibling identity as a motivating example. Not a mere helper lemma.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~18 substantive lines (a two-branch `derivative.ext` proof).
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "formal power series log(1+(exp(X)−1)) = X exp and log inverse"                                          | yes  | `log(exp(X)) = X`; `exp(log(1+X)) = 1+X` as formal series | Confirms it is the textbook inverse pair; identity reduces to `log(exp)=X`. Sources: UWaterloo CO430 notes, behind-the-clouds FPS notes. |
|  2 | WebSearch (general form)         | "exp and log formal power series mutually inverse compositional inverse over Q-algebra char zero"        | yes  | Over a field `k` of char 0 (or `ℚ`-algebra), `exp : k⟪J⟫₀ → 1+k⟪J⟫₀` and `log` are mutual inverses | **char-0 / ℚ-algebra is the stated generality**; ε := exp−1 has the Mercator log series as compositional inverse. Sources: impan FPS (Wikipedia), arXiv:2403.05827. |
|  3 | WebSearch (named-after / aliases)| "miraculous inverse relation between E (exp) and L (log) formal power series"                            | yes  | same inverse pair, called the E↔L relation            | Wildberger "Wild Egg" note explicitly frames `E` and `L` as inverse FPS operators; arXiv invitation-to-FPS (2205.00879). |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of log∘exp = id for formal series")        | n/a  | —                                                    | **`chatgpt-math` MCP server is configured in user settings but NOT enabled in this session** (only `lean-lsp` is in `enabledMcpjsonServers`); the tool is unavailable. Recorded n/a; the standard-form + generality questions are answered conclusively by channels 1, 2, 5, 9. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                             | n/a  | (no references directory; no `refs/` symlink)         | Directory absent — recorded n/a per protocol. (`--refs` pointed at the plugin's generic skill references, not project PDFs.) |
|  6 | nLab                             | formal exponential / logarithm power series inverse                                                     | yes  | exp/log give a bijection primitive ↔ group-like elements; mutual inverses on `1 + (FPS)₀` | nLab "Hopf algebra"; the exp↔log inverse pair is the standard char-0 statement. |
|  7 | nCatLab (categorical)            | exp/log as inverse maps primitives ↔ grouplikes in a Hopf algebra                                       | yes  | same as #6 — categorical framing of the same inverse pair | A genuine higher-structure home exists (Hopf algebras), but it is a *consumer*, not a more-general statement of this FPS identity. |
|  8 | Stacks Project (alg geom)        | formal power series exp/log inverse                                                                      | n/a  | —                                                    | Not an algebraic-geometry concept; Stacks has formal-group machinery but not this elementary FPS identity. Recorded n/a. |
|  9 | MathOverflow / Math.StackExchange| exp and log formal power series compositional inverse, generality                                       | yes  | confirmed over any char-0 ring / ℚ-algebra            | The constraint repeatedly stated: **characteristic-zero coefficients** (so `1/n!`, `1/n` exist). Nothing `p`-adic-specific. |
| 10 | recent arXiv (last 5 years)      | "exponential series without denominators"; "automorphisms/derivations on algebras with formal sums"     | yes  | arXiv:1201.5043, arXiv:2403.05827 — exp/log inverse over char-0 / ℚ-algebra; variants tracked | Modern treatments keep the ℚ-algebra hypothesis; confirms the standard generality is *not* `ℚ_[p]`. |

The protocol passed: WebSearch ran 3 distinct generality levels (specific / most-general /
named-after), ChatGPT MCP recorded n/a with the concrete reason (server not enabled this
session) and the question fully covered by other channels, local references checked (absent →
n/a), nLab + nCatLab + MathOverflow + arXiv each checked, Stacks recorded n/a with reason.

### Literature summary (Phase 3)

Concept identified as: **the inverse relationship of the formal exponential and formal
logarithm power series** — "`log ∘ exp = id`" / "`exp` and `log` are mutually
inverse (compositional) formal power series". The two halves are `exp(log(1+X)) = 1+X`
and `log(1 + (exp−1)) = log(exp) = X`; this declaration is the second half.

Sources agree on the standard form: **yes** — the identity is uniform across every source.
Most general standard form: over any **commutative ring of characteristic zero** /
equivalently any **commutative `ℚ`-algebra** `A`, the series `exp A = ∑ Xⁿ/n!` and
`log A = ∑ (−1)^{n+1}Xⁿ/n` satisfy `(log A).subst (exp A − 1) = X` (and the dual
`(exp A).subst (log A) = 1 + X`). The char-0 / ℚ-algebra hypothesis is *essential*
(the coefficients `1/n!`, `1/n` must exist) and is the standard ceiling.

Generality dimensions where the literature varies:
  - coefficient ring: from `ℚ` itself, to any char-0 field, to any commutative `ℚ`-algebra. **The most general is "commutative `ℚ`-algebra" (`[CommRing A] [Algebra ℚ A]`)**, which is exactly mathlib's `PowerSeries.exp`/`PowerSeries.log` setting. `ℚ_[p]` is one such algebra — a strict, gratuitous specialisation.
  - framing: elementary FPS identity (this decl) vs. the Hopf-algebra primitives↔grouplikes bijection (a downstream *consumer* of it, not a generalisation of the FPS statement).

Disagreement with the literature: **none on content**; the only mismatch is **generality** —
the literature/standard form is over a ℚ-algebra, the user's form fixes `ℚ_[p]`.

---

### Generality analysis — `PadicLFunctions.log_subst_exp_sub_one` (Phase 4)

Literature-standard form (from Phase 3): for any `[CommRing A] [Algebra ℚ A]`,
`(PowerSeries.log A).subst (PowerSeries.exp A − 1) = PowerSeries.X`.

| # | Parameter / hypothesis            | Current Lean form         | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|---------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | coefficient ring `ℚ_[p]`          | complete normed `p`-adic field | any commutative `ℚ`-algebra `[CommRing A] [Algebra ℚ A]` | **yes** | The proof uses *only* mathlib's ℚ-algebra FPS API (`derivative_subst`, `derivative_exp`, `subst_mul/add/X`, `coe_substAlgHom`, `constantCoeff_subst_eq_zero`, `constantCoeff_exp/log`) + `oneAddX_mul_derivative_log` (already over `[CommRing A] [Algebra ℚ A]`) + `derivative.ext` (needs `[CommRing R] [IsAddTorsionFree R]`, automatic for a ℚ-algebra). No norm, valuation, completeness, or prime is touched. |
| 2 | `[Fact p.Prime]`                  | prime hypothesis          | (none)                                 | **yes — drop entirely** | Used only to *form* `ℚ_[p]`. Vanishes once the ring is a generic `A`. |
| 3 | torsion-freeness of coefficients  | implicit (`ℚ_[p]` is a field) | `[IsAddTorsionFree A]` (free for a ℚ-algebra) | n/a — it is the genuinely-needed hypothesis | `derivative.ext` needs `IsAddTorsionFree`; for `[Algebra ℚ A]` commutative rings this holds automatically (char 0). This is the one real hypothesis and it matches the literature ceiling. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 2 (generalise the coefficient ring `ℚ_[p]` → any `[CommRing A] [Algebra ℚ A]`; drop `[Fact p.Prime]`).

Proposed restatement (literature-standard target):

```lean
namespace PowerSeries
variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal logarithm inverts the formal exponential:
`log(1 + (exp − 1)) = X` as power series over a ℚ-algebra. -/
theorem log_subst_exp_sub_one : (log A).subst (exp A - 1) = (X : A⟦X⟧) := by
  ...  -- the existing proof verbatim, with `ℚ_[p]` replaced by `A`
end PowerSeries
```

Equivalently, stated through mathlib's own `logOf`: `logOf (exp A) = X`.

Cost of restatement: **CHEAP — mechanical rewrite** (replace `ℚ_[p]` by `A`; the proof
already only invokes ℚ-algebra-level lemmas, so it transports unchanged).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let `A` be a foo" preamble → typeclass? | already a typeclass | `[CommRing A] [Algebra ℚ A]` (already idiomatic once generalised) | n/a — generalisation, not a structural reformulation |
| 2 | sequences/metric → filters/topology? | no | — | This is a purely algebraic FPS identity; no convergence/topology in the statement. |
| 3 | construct an object → universal property? | no | — | The object (`X`) is already canonical; nothing to characterise universally. |
| 4 | set+closure-predicate → bundled substructure? | no | — | No substructure involved. |
| 5 | vector-space/field-specific → weaken typeclass? | **yes (the core move)** | `ℚ_[p]` (field) → `[CommRing A] [Algebra ℚ A]` | Every ℚ-algebra (incl. `ℚ`, `ℝ`, `ℂ`, `ℚ_[p]`, polynomial/MvPowerSeries ℚ-algebras) gets the inverse identity for free; composes with the whole `PowerSeries.exp`/`log`/`logOf`/`subst` ecosystem. |
| 6 | 1-categorical → higher-categorical? | no (out of scope) | — | The Hopf-algebra primitives↔grouplikes framing is a *consumer*, not a replacement for this elementary identity. |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | — | No numeric index in the statement. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is the *same* move as Phase 4b row 1/5
(weaken the coefficient typeclass from a specific field to a general `ℚ`-algebra). It is
not a *structural* reformulation distinct from the literature-weakening.
  - Proposed mathlib-idiomatic restatement: as in Phase 4b (over `[CommRing A] [Algebra ℚ A]`), placed in `Mathlib/RingTheory/PowerSeries/Log.lean` next to `logOf`.
  - Cost: CHEAP.
  - Mathlib downstream this enables: `logOf (exp A) = X` becomes a one-liner; the `padicLog`/`padicExp` inversion in this very project (and any future ℝ/ℂ/`p`-adic exp-log work) specialises from it; pairs with the existing `logOf_one_add_X`.
  - Real mathematical improvement: it removes a *spurious* restriction to `ℚ_[p]` from a fact that is true (and proved) over every ℚ-algebra — the textbook modules-not-vector-spaces correction.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced). Skipped.

---

### Mathlib search-status: `PadicLFunctions.log_subst_exp_sub_one` (Phase 5)

[A] Lean-Finder       (web UI unavailable this session)                              n/a: endpoint not reachable; covered by [B]/[C]/[D].
[B] Loogle            `PowerSeries.subst PowerSeries.log` (via loogle.lean-lang.org) hits: full subst API enumerated — `subst_mul`, `subst_add`, `subst_X`, `coe_substAlgHom`, `constantCoeff_subst_eq_zero`, `subst_substInv_left/right`, `substInvOfIsUnit_*`, `logOf_eq` — but **NO `log_subst_exp` / `exp_subst_log` / `logOf_exp` round-trip identity**.
[C] LeanSearch        `logarithm of exponential power series equals X`                n/a: leansearch.net API returned HTTP 404 (endpoint moved); compensated by [B] + [D].
[D] Grep mathlib src  `(theorem|lemma).*(log.*exp|exp.*log|logOf|expOf)` over `Mathlib/RingTheory/PowerSeries/*.lean`; and `log_exp` repo-wide   **Only 4 log-subst theorems exist** in `Log.lean`: `HasSubst.exp_sub_one`, `logOf_eq`, `constantCoeff_logOf`, `logOf_one_add_X`. None is the inverse identity. All other `log_exp` hits are `Real.log_exp`/`Complex.log_exp` in analysis — unrelated to formal power series.
[E] Name pattern      `exp_subst_log`, `log_subst_exp`, `logOf_exp`, `expOf`         no hits in mathlib (these names exist only in this project).

Searched for both:
  - the user's current form (`(log ℚ_[p]).subst (exp ℚ_[p] − 1) = X`)
  - the literature-standard form (`(log A).subst (exp A − 1) = X` over any ℚ-algebra; equivalently `logOf (exp A) = X`).

Concluded: **not in mathlib (Loogle subst-API enumeration + exhaustive grep of `Log.lean`/`Exp.lean` + name-pattern search exhausted, for both the `ℚ_[p]` form and the general ℚ-algebra form).** Mathlib has the *building blocks* — `exp`, `log`, `logOf`, the full `subst` API, the `derivative.ext` engine, and even an abstract compositional-inverse `substInv` with `subst_substInv_right : P.subst (substInv P) = X` — but the **named exp↔log round-trip identity is absent**. (Notably, `Mathlib/RingTheory/PowerSeries/Derivative.lean:22` advertises `exp(log(1+X)) = 1+X` as the motivating example of "prove identities by differentiating twice" yet never states it as a theorem — a self-identified gap.)

---

### Call sites — `PadicLFunctions.log_subst_exp_sub_one` (Phase 6.0)

Internal use count: **1** (within the project, excluding the declaring file's own line).
External-to-file callers: 1 distinct location, same file (`PadicExp.lean`).

| Caller file:line          | Usage pattern (one-line excerpt)                                            |
|---------------------------|------------------------------------------------------------------------------|
| PadicExp.lean:969         | `… master_bridge … HasSubst.exp_sub_one …, log_subst_exp_sub_one, eval_X]` — used to rewrite `(log).subst(exp−1)` to `X` inside the `padicLog (exp …) = …` evaluation bridge (proving log inverts exp at the *analytic/value* level via the formal identity). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **(none)** — the identity is proved once and consumed once; its sibling `exp_subst_log` (PadicExp.lean:487) is the dual, used analogously at line 945.

Signal: K = 1 internal use. Per the call-sites table this is normally a "lean toward
NO-composable" signal — **but** the single consumer is itself a substantive analytic
bridge (`master_bridge`), not a trivial wrapper, and Phase 6 below shows the lemma is
**not** composable from mathlib in ≤3 calls. The low internal count reflects that this is a
*named mathematical fact* (one of two inversion identities), not an over-abstracted helper.

### Composition check (Phase 6)

Can `log_subst_exp_sub_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: via `subst_substInv_right` / `subst_substInv_left`.
  - Mathlib decls used: `PowerSeries.substInv`, `PowerSeries.subst_substInv_right` (`P.subst (substInv P) = X`), `PowerSeries.subst_substInv_left`.
  - Result: **fails.** `subst_substInv_right` gives `(exp−1).subst (substInv (exp−1)) = X`, where `substInv (exp−1)` is the *abstractly recursion-constructed* inverse. To reach our statement one must first prove `substInv (exp−1) = log` (equivalently `substInv log = exp−1`), i.e. identify the abstract inverse with the named `log` series. That identification is a genuine uniqueness theorem — **not in mathlib**, and of difficulty comparable to proving the target itself (the project instead proves the target *directly* via `derivative.ext`). So this is a proof, not a composition.
  - Notes: also, our identity is `log.subst(exp−1) = X` (the *left* inverse direction relative to `substInv (exp−1)`), so even with `substInv (exp−1) = log` in hand one needs `subst_substInv_left`, adding another nontrivial step.

Attempt 2: via `logOf_one_add_X` + `exp_subst_log`.
  - Mathlib decls used: `PowerSeries.logOf_one_add_X` (`logOf (1+X) = log A`), plus the dual `exp(log) = 1+X`.
  - Result: **fails.** `logOf_one_add_X` is about `1+X`, not `exp`. Chaining through the dual identity `(exp).subst(log) = 1+X` (which is the project's *other* lemma `exp_subst_log`, itself not in mathlib) and then inverting requires the injectivity/inverse-pair reasoning that is precisely the content here. Not ≤3 mathlib calls.

Conclusion: **NOT-COMPOSABLE.** The building blocks (`exp`, `log`, `subst`, `substInv`,
`derivative.ext`) are present, but assembling them into `log(exp) = X` requires a real
proof (either the `derivative.ext` argument the project uses, or an abstract-inverse
uniqueness theorem mathlib lacks) — well beyond a 1–3 call composition.

---

## Verdict: `PadicLFunctions.log_subst_exp_sub_one`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the identity is the classical "log inverts exp" formal-power-series fact, **standard over any characteristic-zero / `ℚ`-algebra ring** (≥6 channels agree; the char-0 hypothesis is the essential, standard ceiling).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — stated over `ℚ_[p]` though the proof uses only ℚ-algebra FPS API; generalises CHEAP-ly to `[CommRing A] [Algebra ℚ A]`.
- Mathlib search (Phase 5): **not in mathlib** under either the `ℚ_[p]` form or the general ℚ-algebra form (Loogle + exhaustive grep + name-pattern). Mathlib has the pieces (`exp`, `log`, `logOf`, `subst`, `substInv`, `derivative.ext`) but not the named round-trip identity; `Derivative.lean`'s docstring even advertises the dual as a worked example without stating it.
- Composition check (Phase 6): **NOT-COMPOSABLE** — `substInv`-based assembly needs an abstract-inverse uniqueness theorem mathlib lacks; otherwise it is a full `derivative.ext` proof.

**Rationale:**

The mathematical content — `log(exp) = X` for formal power series — is genuinely
missing from mathlib and worth adding: mathlib added `PowerSeries.exp`, `PowerSeries.log`
and `PowerSeries.logOf` in 2026 but never closed the loop with the inverse-pair identities,
even though `Mathlib/RingTheory/PowerSeries/Derivative.lean:22` explicitly names
`exp(log(1+X)) = 1+X` as *the* canonical demonstration of its `derivative.ext` tool. That
is a concrete, self-identified API gap: the very lemma the library motivates its
machinery with is absent. So the answer is not NO.

But the declaration as written specialises a ℚ-algebra fact to `ℚ_[p]` for no reason —
the entire proof goes through mathlib's `derivative_subst`, `derivative_exp`,
`subst_mul/add/X`, `coe_substAlgHom`, `constantCoeff_subst_eq_zero`, and the helper
`oneAddX_mul_derivative_log` (which is *already* stated over `[CommRing A] [Algebra ℚ A]`),
with `derivative.ext`'s only real requirement (`IsAddTorsionFree`) holding automatically
for any ℚ-algebra. This is the textbook modules-not-vector-spaces situation: ship the
general form. Per the skill's gate, a Phase-4b "STRICTLY NARROWER" result must be
`YES-but-generalise-first`, not `YES-add-as-is`.

**Reason for the generalisation:** LITERATURE-WEAKENING — Phase 4b found the `ℚ_[p]` form
strictly narrower than the literature-standard ℚ-algebra form, and the weakening is a
CHEAP mechanical rewrite the existing proof survives unchanged. (Phase 4c flags the same
coefficient-typeclass weakening; it is not a *separate* structural modernisation.)

**Proposed restatement:**

```lean
namespace PowerSeries
variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal logarithm inverts the formal exponential:
`log(1 + (exp − 1)) = X` as power series over a ℚ-algebra
(equivalently `logOf (exp A) = X`). -/
theorem log_subst_exp_sub_one : (log A).subst (exp A - 1) = (X : A⟦X⟧) := by
  sorry  -- the current ℚ_[p] proof verbatim with `ℚ_[p]` → `A`; expected to survive as-is
end PowerSeries
```

Estimated cost of regeneralisation: **CHEAP** (mechanical `ℚ_[p]` → `A` substitution; no
new ideas — every lemma invoked is already ℚ-algebra-level).

Mathlib downstream this enables:
- `PowerSeries.logOf (exp A) = X` becomes a one-line corollary, completing the `logOf` API alongside `logOf_one_add_X`.
- The project's own `padicLog`/`padicExp` inversion (PadicExp.lean:969) specialises from the mathlib lemma instead of carrying a bespoke `ℚ_[p]` proof.
- Any future formal exp/log work over `ℚ`, `ℝ`, `ℂ`, or other `p`-adic fields reuses it for free; it pairs with the existing `subst`/`derivative.ext` ecosystem.
- Closes the gap that `Derivative.lean`'s docstring advertises but does not fill.

**PR grouping (REQUIRED):** ship together with the project's sibling
`PadicLFunctions.exp_subst_log` (PadicExp.lean:487 — the dual `(exp A).subst (log A) = 1+X`,
likewise stated over `ℚ_[p]` but proved with only ℚ-algebra API). The two inverse-pair
identities belong in one PR `feat(RingTheory/PowerSeries): exp and log are inverse formal
power series`, both placed in `Mathlib/RingTheory/PowerSeries/Log.lean`. The shared helper
`oneAddX_mul_derivative_log` overlaps mathlib's existing `deriv_log` and should be
reconciled (likely inlined or proved from `deriv_log`) rather than added separately.

Next action: run `/generalise PadicLFunctions.log_subst_exp_sub_one` (it will tension the
`ℚ_[p]` → `[CommRing A] [Algebra ℚ A]` weakening against the literature-standard form from
Phase 3 and confirm the proof transports), do the same for `exp_subst_log`, then
`/cleanup` the pair and open the single mathlib PR above.

---

## Next step

Run `/generalise PadicLFunctions.log_subst_exp_sub_one` to restate over a general
`ℚ`-algebra (`[CommRing A] [Algebra ℚ A]`, the literature-standard generality), confirm the
existing `derivative.ext` proof survives the `ℚ_[p]` → `A` substitution, then ship it
together with the dual `PadicLFunctions.exp_subst_log` in one
`feat(RingTheory/PowerSeries): exp and log are inverse formal power series` PR into
`Mathlib/RingTheory/PowerSeries/Log.lean` (reconciling `oneAddX_mul_derivative_log` with
mathlib's `deriv_log`).
