# /mathlibable report — `WeierstrassCurve.Universal.polyToField_φ_ne_zero`

> Assessed 2026-06-22 against the pinned AINTLIB mathlib (`lakefile.toml`: leanprover-community/mathlib4,
> pin `d90090f`). Local AINTLIB build is stale (per task note); reasoning is from the source statement +
> direct grep of a synced mathlib checkout at
> `~/.cache/lean-lsp-mcp/loogle/repo/.lake/packages/mathlib` (same EC/EDS files as the pin) and from the
> sibling `/overview` reports in this directory. `lean_loogle`/`lean_leansearch` were not loadable in this
> environment; the **direct mathlib source grep is the decisive Phase-5 method** and was run exhaustively.

---

### Baseline (Phase 0)

- lake build:               (not re-run — local build stale per task note; reasoning from source)
- decl `WeierstrassCurve.Universal.polyToField_φ_ne_zero`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:148` (statement + proof, lines 148–152).
- **Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.polyToField_φ_ne_zero`.
  At line 148 the open namespaces are `namespace WeierstrassCurve` (line 76) → `namespace Universal`
  (line 86); the inner `namespace Affine` only opens at line 157 (> 148) and `Universal` closes at
  line 546. No `section` renaming. So the parsed name in the task prompt is correct.
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Integer multiples of a rational point on an elliptic curve in terms of
  division polynomials" — proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)` in
  Jacobian coords. This file is part of the project's **fork/extension** of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`, building the bespoke **universal pointed
  Weierstrass curve** machinery (`Universal.curve`, `polyToField`, `cusp`, `ringEval`) that is **not**
  upstream.

---

### Statement (Phase 1)

`polyToField_φ_ne_zero` states: the image of the universal `n`-th auxiliary division polynomial `φₙ`
under the project-local ring homomorphism `polyToField : Poly →+* Universal.Field` is **nonzero** (for
every `n : ℤ`, including `n = 0`, where `φ₀ = 1`).

```lean
lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h
```

Mathematically: in the universal field `Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩)` (the function field of the
generic pointed Weierstrass curve), the auxiliary division polynomial `φₙ = X·ψₙ² − ψₙ₊₁ψₙ₋₁` is a
**nonzero** element. This is the numerator-nonvanishing fact that makes the rational function
`smulX n = φₙ / ψₙ²` — the `X`-coordinate of `n • (X,Y)` — well-defined / nonzero.

Variables / typeclasses (Lean side):
- `{n : ℤ}` — the multiplication index (free variable; the statement is for all `n`).
- All other data are **fixed project-local objects** (no typeclass generality): `polyToField`,
  `curve : Affine (MvPolynomial Coeff ℤ)`, `Universal.Field`, `Universal.Poly`.

Hypotheses (Lean side): none (besides the implicit `n`).

Conclusion (math): the generic auxiliary division polynomial `φₙ` is nonzero in the universal function
field.

Conclusion (Lean): `polyToField (curve.φ n) ≠ 0`.

Proof mechanism (verbatim above): if `polyToField (curve.φ n) = 0`, then since `polyToField` factors
through the injective `algebraMap Universal.Ring Universal.Field` (`IsFractionRing.injective`), the
class `AdjoinRoot.mk _ (curve.φ n)` is `0` in `Universal.Ring`. Apply the **cusp specialization**
ring hom `ringEval cusp_equation_one_one : Universal.Ring →+* ℤ` (specialize coefficients to the
cuspidal cubic `Y² = X³`, i.e. `cusp = ⟨0,0,0,0,0⟩`, then `(X,Y) := (1,1)`). By `ringEval_mk` and the
project lemma `polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1`, the image is `1`, but `map_zero`
makes the image `0` — so `(1 : ℤ) = 0`, contradicting `one_ne_zero`. (Mechanism: a nonzero element of
the domain is detected by **one** ring-hom specialization at which it is nonzero — here the cusp.)

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper lemma — not a `def`/`class`, not named after a person/place, not a `## Main results`
entry. It is denominator/numerator-nonvanishing bookkeeping that feeds the affine `smulX` development
(`smulX n = φₙ/ψₙ²` well-defined; see Phase 6 call site `ZSMul.lean:204`).

(Note: literature width is EXHAUSTIVE regardless. The SMALL classification is for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner-def exemption table is **n/a**. (For
the record the proof is a 4-step `fun h ↦ by …` contradiction; pure specialization plumbing over
project-local infrastructure — a weak negative signal for independent mathlib inclusion.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial phi_n psi_n nonzero nonvanishing universal coordinate ring"        | partial | `φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁`; `x∘[n] = φₙ/ψₙ²` | Sutherland MIT 18.783 L#6; arXiv 1801.02664 (Division Polynomial PIT), 1108.3051. The "universal coordinate ring" angle is not a named theorem. |
|  2 | WebSearch (general form / coprimality) | "Weierstrass division polynomial phi_n coprime to psi_n^2 x-coordinate multiplication by n"   | yes  | **`φₘ` and `ψₘ²` are relatively prime** in the coordinate ring; `x∘[m] = φₘ/ψₘ²` | This is the *strong* literature fact; `φₙ ≠ 0` is a weak corollary (a coprime-to-something element, and the numerator of the well-defined `x∘[n]`). arXiv 1801.02664, 1303.4327. |
|  3 | WebSearch (named-after / aliases) | (covered by #1/#2) "division polynomial PIT supersingularity" / "homogeneous division polynomials Weierstrass" | yes | division polys are nonzero / coprime as the standard setup for the `[n]`-map | No author/place name attaches to "`φₙ ≠ 0`"; it is folklore bookkeeping under the EDS/division-polynomial theory (Ward, Silverman *AEC* Ex. 3.7). |
|  4 | ChatGPT MCP                      | "standard form + generality of: the n-th auxiliary division polynomial φₙ is nonzero in the function field; history" | n/a | — | MCP server down in this environment (per task note); fallbacks (WebSearch ×3 + direct mathlib grep + sibling reports) used. The standard-form question is settled by #1/#2: `φₙ ≠ 0` is the weak consequence of the coprimality fact `gcd(φₙ, ψₙ²) = 1`. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                 | n/a  | (directory absent)               | No `references/` dir and no `refs/` store for NagellLutz — recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | —                                | nLab has no division-polynomial / EDS page with a `φₙ ≠ 0` statement; not a categorical concept. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "Weierstrass equation"                                                          | n/a  | —                                | Stacks treats EC abstractly (no explicit division polynomials / `φₙ`); no corresponding tag. |
|  9 | MathOverflow / Math.StackExchange| "are division polynomials φ_n ψ_n nonzero / coprime"                                                    | yes  | coprimality + nonvanishing is the standard well-definedness fact for `x∘[n]` | Consistently treated as a routine consequence of the recursion + degree theory, not a citable standalone result. |
| 10 | recent arXiv (last 5 years)      | "division polynomial PIT", "p-adic division polynomials elliptic divisibility sequences"               | yes  | arXiv 1801.02664, math/0404412   | These study **degrees / valuations / identity-testing** of `ψₙ, φₙ`; nonvanishing is assumed background, never the headline. |

The protocol passed: WebSearch ran 3 distinct queries (specific form / coprimality-general / aliases);
ChatGPT MCP recorded n/a with reason (server down) and the question is settled by the WebSearch hits;
local refs / nLab / nCatLab / Stacks / MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **non-vanishing of the auxiliary division polynomial `φₙ`** in the
function-field / coordinate-ring of a Weierstrass curve — the numerator of the multiplication-by-`n`
`x`-coordinate `x∘[n] = φₙ/ψₙ²`.
Sources agree on the standard form: yes — but the *named* fact in the literature is the **stronger**
coprimality statement `gcd(φₙ, ψₙ²) = 1` (so `x∘[n]` is in lowest terms); `φₙ ≠ 0` is the weak
corollary used for well-definedness.
Most general standard form: for a Weierstrass curve over **any** base (the universal/generic case
specializes to all), `φₙ` is a nonzero element of the coordinate ring / function field for all `n`,
and indeed coprime to `ψₙ²`.
Generality dimensions where the literature varies:
  - base ring/field: from a fixed `𝔽_q` (Sutherland, PIT papers) up to the **generic/universal** curve
    over `ℤ[a₁..a₆]` (the maximally-general anchor — which is exactly what this lemma states).
  - strength: `φₙ ≠ 0` (this lemma) vs. `gcd(φₙ, ψₙ²) = 1` (the stronger literature fact).
Disagreement with the literature: none — this lemma is the (weaker) `φₙ ≠ 0` half, at the (maximal)
universal generality, of a standard well-definedness fact.

---

### Generality analysis — `polyToField_φ_ne_zero` (Phase 4)

Literature-standard form (from Phase 3): `φₙ ≠ 0` (indeed `gcd(φₙ, ψₙ²) = 1`) for a Weierstrass curve
over any base; the universal/generic curve is the maximal case and specializes to all others.

| # | Parameter / hypothesis           | Current Lean form                          | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------|--------------------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | base object `curve` + `polyToField` | the **fixed universal** pointed curve over `ℤ[A₁..A₆,X,Y]`, mapped to `Universal.Field` | Weierstrass curve over any base (universal is maximal) | n/a — already maximal **but not parametric** | The statement is hard-wired to the *one* project-local `Universal.curve`/`polyToField`; it is the maximal *generality* in spirit, but expressed via a bespoke fixed object, not a typeclass-parametric `W : WeierstrassCurve R`. A mathlib version would be `∀ {R} [CommRing R] [...] (W : WeierstrassCurve R), (W.φ n).map(...) ≠ 0` over the appropriate domain — a **different, parametric statement**. |
| 2 | target field                     | `Universal.Field = FractionRing Universal.Ring` (project-local) | function field of `W`                     | n/a                 | `Universal.Field`/`Universal.Ring` are project-local types not in mathlib; the mathlib analogue would use `W`'s `CoordinateRing` / its fraction field. |
| 3 | index `n`                        | `n : ℤ` (all `n`, incl. 0)                 | `n : ℤ`                                   | NO                  | Already fully general in `n`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** in *expression* (it is pinned to the single
project-local universal object `polyToField`/`curve`, not stated for a parametric
`W : WeierstrassCurve R`), even though it sits at the maximal *mathematical* generality (the universal
curve specializes to all). The mathlib-worthy statement is the **parametric**
`(W.φ n).map(algebraMap …) ≠ 0` over the coordinate ring of an arbitrary base — a **different
declaration**, not a mechanical weakening of this one.
Number of re-expression opportunities found: the lemma's *kernel* is the parametric division-polynomial
nonvanishing/coprimality over an arbitrary `WeierstrassCurve R`.
Cost of restatement: **EXPENSIVE** — it is not a signature tweak; one must first build the parametric
nonvanishing (most naturally via the universal-curve specialization technique, or via mathlib's degree
theory `natDegree_Φ`/`leadingCoeff_Φ` over a suitable base), then this lemma falls out by specialization.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                   | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                            | no       | already instance-driven (`CommRing`, `IsDomain` via `IsFractionRing`)                  | — |
|  2 | sequences/metric → filters/topological?                                                                    | no       | no analytic/limit content                                                              | — |
|  3 | construct object → universal-property class?                                                               | borderline (umbrella) | the **whole** universal-curve package (`curve`/`polyToField`/`ringEval`) could be a `WeierstrassCurve.IsUniversal`-style corepresented-functor class | This is the real idiomatic home for the *package*, but it reshapes `ringEval`/`Universal.*` (see `ringEval.md`), **not** this one nonvanishing lemma. mathlib has none of it today. |
|  4 | set+closure-predicate → bundled substructure?                                                              | no       | —                                                                                      | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                                          | no (already general) | the parametric form would be over a domain / integral coordinate ring                 | — |
|  6 | 1-categorical → higher-categorical?                                                                         | no       | —                                                                                      | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                            | no       | `n : ℤ` is already the right index for division polynomials                            | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this* lemma). The only "modernisation" in the vicinity is to ship
the entire universal-pointed-curve apparatus as a represented-functor/universal-property class — that is
a decision about `ringEval`/`Universal.*` as a *package* (tracked in `ringEval.md`, `cusp.md`,
`polyToField.md`), not a reshaping of `polyToField_φ_ne_zero`. As a standalone nonvanishing fact there
is no contemporary-idiom restatement that improves mathlib organisation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (no new definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `polyToField_φ_ne_zero` (Phase 5)

[A] Lean-Finder       not loadable in env → n/a (covered by direct grep [D] + sibling reports).
[B] Loogle            not loadable in env → n/a (covered by direct grep [D]).
[C] LeanSearch        not loadable in env → n/a (covered by direct grep [D]).
[D] **Grep mathlib src** (decisive) — exhaustive grep over the synced pin
    (`~/.cache/lean-lsp-mcp/loogle/repo/.lake/packages/mathlib/Mathlib/`):
    - `polyToField` — **0 hits in all of mathlib**. The subject ring hom does not exist upstream.
    - `namespace Universal` under `EllipticCurve/` — **0 hits** (the only `namespace Universal` in
      mathlib is in `AlgebraicGeometry/Morphisms/UniversallyOpen.lean`, unrelated). No universal pointed
      Weierstrass curve upstream.
    - `def cusp` / `ringEval` (the proof crux's vocabulary) under `EllipticCurve/` — **0 hits**.
    - division-polynomial **nonvanishing / coprimality** — `grep -niE "Coprime|IsCoprime|ne_zero|≠ 0"`
      over `EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` for `φ/ψ/Φ/Ψ`: the only nonzero facts
      are **degree/coefficient** lemmas (`coeff_Ψ₂Sq_ne_zero`, `natDegree_Φ`, `leadingCoeff_Φ`) — there
      is **no** `Φ ≠ 0`, no `IsCoprime (Φ ..) (Ψ .. ^ 2)`, no fraction-field/coordinate-ring nonvanishing.
      `DivisionPolynomial/Basic.lean` `## Main definitions` confirms the file's scope is *defining*
      `ψ/Φ/φ/ω`, not their nonvanishing.
[E] Name pattern      `polyToField_φ_ne_zero` — exists in exactly two project files (NagellLutz
    `ZSMul.lean:148` + a duplicate in HasseWeil `Auxiliary/DivisionPolynomial.lean:227`); 0 in mathlib.

Searched for both:
  - the user's current form (`polyToField (curve.φ n) ≠ 0`) — subject `polyToField`/`curve` is
    **project-local; 0 mathlib hits**.
  - the literature-standard parametric form (`(W.Φ n) ≠ 0` / `IsCoprime (W.Φ n) (W.ΨSq n)` over a base)
    — **also absent**: mathlib's `DivisionPolynomial` has degrees + leading coefficients but no
    nonvanishing/coprimality of `Φ`.

Concluded: **not in mathlib** — neither the user's project-local form nor the parametric
literature-standard form. mathlib provides only **building blocks** (`IsFractionRing.injective`,
`map_eq_zero_iff`, `one_ne_zero`, `map_zero`) plus the *unused-here* degree theory; the crux machinery
(`cusp`, `ringEval`, `polyEval_cusp_φ`) is fork-local. Not NO-mathlib-has-it.

---

### Call sites — `polyToField_φ_ne_zero` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring line): **1**.
External-to-file callers (across the repo): the lemma is **duplicated** verbatim in HasseWeil.

| Caller file:line                                                  | Usage pattern (one-line excerpt)                                           |
|-------------------------------------------------------------------|-----------------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:204`                   | `div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)` — proves `smulX n = φₙ/ψₙ² ≠ 0` |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:227` | **duplicate declaration** of the identical lemma (HasseWeil fork copy)   |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:262` | `div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)` (HasseWeil's own use) |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - The structurally **identical twin** for `ψ`, `ψᵤ_ne_zero` (`ZSMul.lean:142`), sits one declaration
    above with the same 4-step cusp-specialization proof (`ψ`↔`φ`, `polyEval_cusp_ψ`↔`polyEval_cusp_φ`,
    `h0`↔`one_ne_zero`). The two are a matched pair feeding `smulX`/`smulY` well-definedness.

Signal: **K = 1 internal use** (a single consumer making `φₙ/ψₙ²` nonzero), plus a **cross-project
duplicate** in HasseWeil → leans NO/BORDERLINE: this is fork-internal scaffolding, not an exported API
with broad consumption, and it is a consolidation/dedup candidate on `main`.

### Composition check (Phase 6)

Can `polyToField (curve.φ n) ≠ 0` be derived from **mathlib alone** in ≤3 chained calls? **No.**

Attempt 1: mirror the actual proof. The 4 steps are `polyToField_apply` (project `rfl`) →
`map_eq_zero_iff _ (IsFractionRing.injective _ _)` (mathlib) → `congr(ringEval cusp_equation_one_one $h)`
+ `ringEval_mk` + `polyEval_cusp_φ` (**all project-local**) → `map_zero` + `one_ne_zero` (mathlib).
  - Mathlib decls used: `IsFractionRing.injective`, `map_eq_zero_iff`, `map_zero`, `one_ne_zero`.
  - Project-local decls used (decisive): `ringEval`, `cusp_equation_one_one`, `ringEval_mk`,
    `polyEval_cusp_φ` (and the subject `polyToField`, `curve`, `cusp` themselves).
  - Result: **fails as a mathlib-only composition** — the load-bearing specialization
    `polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1` is a fork lemma (its own report:
    `polyEval_cusp_φ.md` → NO-composable, project-local), transitively needing `cusp`/`ringEval`, none
    of which is in mathlib.

Attempt 2: derive from mathlib's parametric division-polynomial API instead. mathlib has
`natDegree_Φ`/`leadingCoeff_Φ` (degrees over a suitable base) from which `Φ ≠ 0` would follow — but
that is a **different statement** about the parametric `W.Φ` over an arbitrary base, **not** about the
project-local `polyToField (curve.φ n)`; bridging the two needs the (absent-from-mathlib) universal-curve
plumbing. Not a ≤3-mathlib-call composition of *this* statement.

Conclusion: **NOT-COMPOSABLE from mathlib alone.** (It *is* a 4-line composition from **fork + mathlib**
— `polyToField_apply` + `IsFractionRing.injective`/`map_eq_zero_iff` + the fork crux `polyEval_cusp_φ` +
`one_ne_zero`/`map_zero` — but "fork + mathlib" is not the NO-composable bar, which is mathlib-only.)

---

## Verdict: `WeierstrassCurve.Universal.polyToField_φ_ne_zero`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): `φₙ ≠ 0` (the numerator of `x∘[n] = φₙ/ψₙ²`) is standard well-definedness
  bookkeeping; the *named* literature fact is the stronger coprimality `gcd(φₙ, ψₙ²) = 1`. No standalone
  citable "`φₙ ≠ 0`" theorem; the universal/generic curve is the maximal-generality anchor (Sutherland
  MIT 18.783; arXiv 1801.02664, 1303.4327).
- Generality (Phase 4): **STRICTLY NARROWER in expression** — pinned to the single project-local
  universal object `polyToField`/`curve`, not a parametric `W : WeierstrassCurve R`. The mathlib-worthy
  kernel is the **parametric** `Φ ≠ 0` / coprimality over an arbitrary base — a *different* declaration
  (cost EXPENSIVE). Modern-idiom (4c): none for this lemma alone.
- Mathlib search (Phase 5): **absent** under both forms. `polyToField`/`Universal`/`cusp`/`ringEval`
  have **0** mathlib hits; mathlib's `DivisionPolynomial` has degrees + leading coefficients but **no**
  `Φ`-nonvanishing/coprimality. Only generic building blocks (`IsFractionRing.injective`,
  `map_eq_zero_iff`, `one_ne_zero`, `map_zero`) exist. Not NO-mathlib-has-it.
- Composition (Phase 6): **NOT-COMPOSABLE from mathlib alone** — the crux `polyEval_cusp_φ` is a fork
  lemma needing `cusp`/`ringEval`. (It is a 4-line *fork + mathlib* composition, not mathlib-only.)

**Rationale:**

`polyToField_φ_ne_zero` is **fork-internal scaffolding**, not an independent mathlib candidate. Its very
*statement* names project-only objects — `polyToField` (the structure map into the universal function
field), `curve` (the generic pointed Weierstrass curve over `ℤ[A₁..A₆,X,Y]`), and implicitly
`Universal.Field`/`Universal.Ring` — every one of which is **absent from mathlib** (0 grep hits; the
universal-pointed-curve apparatus is precisely the part of this project's fork of
`Mathlib.AlgebraicGeometry.EllipticCurve.*` that is not upstream). So it cannot be proposed to mathlib
as written. The mathematical content — `φₙ ≠ 0` in the function field, the numerator-nonvanishing half of
the standard fact that `x∘[n] = φₙ/ψₙ²` is well-defined (and in lowest terms) — is realised by
specializing the generic `φₙ` to the cuspidal cubic via `polyEval_cusp_φ` (`= 1`). That crux is itself
**fork-local and absent from mathlib** (`polyEval_cusp_φ.md` → NO-composable; depends on `cusp`,
`ringEval`, `cusp_equation_one_one`), so the lemma is **not** a clean composition of mathlib primitives
either — it is recoverable only relative to the fork's own API. This is exactly the configuration of its
near-identical sibling `universalNormEDS_ne_zero` (same directory) — statement names fork-only
vocabulary **and** proof is not mathlib-composable — which the `NO-composable` gate disqualifies (that
gate requires Phase 6 to conclude COMPOSABLE-from-mathlib-alone, which it does not). What remains is a
judgment call about the fork's universal-curve strategy → **BORDERLINE**.

The genuinely mathlib-able object in this vicinity is the **parametric** non-vanishing / coprimality of
the auxiliary division polynomial — `(W.Φ n) ≠ 0` (and `IsCoprime (W.Φ n) (W.ΨSq n)`) for any
`W : WeierstrassCurve R` over a suitable base — which mathlib **lacks** (its `DivisionPolynomial` files
stop at degrees/leading coefficients) and which is the natural next layer above mathlib's existing
`natDegree_Φ`/`leadingCoeff_Φ`. That is a **separate, generalise-first / future-PR** target, not this
decl; this decl is the universal-case glue used to *prove* the project's `smulX`/`smulY`
well-definedness (`ZSMul.lean:204`).

**Numbered questions (BORDERLINE — ≤5):**
1. The mathlib-worthy object here is the **parametric** `(W.Φ n) ≠ 0` — ideally the stronger
   `IsCoprime (W.Φ n) (W.ΨSq n)` — for `W : WeierstrassCurve R` over a domain/integral coordinate ring,
   sitting directly above mathlib's existing `natDegree_Φ`/`leadingCoeff_Φ`. Pursue *that* as the mathlib
   contribution (keeping `polyToField_φ_ne_zero` as the fork-internal specialization that uses it)? (yes/no)
2. If yes to (1): prove it the **parametric/degree** way (from `natDegree_Φ` ⇒ `Φ ≠ 0` over a base where
   the leading coefficient is nonzero) — the direct mathlib-native route — rather than via this project's
   universal-curve/cusp machinery? (degree-route / universal-route)
3. Should the universal-pointed-curve apparatus (`curve`/`polyToField`/`cusp`/`ringEval` and the
   `_ne_zero` corollaries) ever be proposed to mathlib *as a package* (a represented-functor /
   universal-property class for Weierstrass curves — see `ringEval.md`, `cusp.md`), or kept permanently
   project-local? (mathlib-package / keep-local)
4. Independently of mathlib: consolidate the **cross-project duplicate** of this lemma (NagellLutz
   `ZSMul.lean:148` and HasseWeil `Auxiliary/DivisionPolynomial.lean:227, used at 262`) into one shared
   `Common/` copy on `main`? (yes/no)

**WHY (refactor-actionable) — supporting the BORDERLINE call:**
Not a standalone mathlib PR as written: the decl references fork-only vocabulary
(`polyToField`/`curve`/`cusp`/`ringEval`) and its proof depends on a fork-only crux lemma
(`polyEval_cusp_φ`); it only makes sense bundled with the project's universal-pointed-curve development.
The honest mathlib action is to upstream the **parametric** `Φ`-nonvanishing/coprimality (a real gap
above mathlib's degree theory), at which point this universal-case lemma either becomes a corollary by
specialization or is simply the project's internal proof device — which is the human call (Q1/Q2).

Mathlib building blocks (what the proof reuses):
- `IsFractionRing.injective` — `Mathlib/RingTheory/Localization/FractionRing.lean:123`
- `map_eq_zero_iff` (generic, via the injective ring hom), `map_zero`, `one_ne_zero`
- (for the *parametric* alternative route) `WeierstrassCurve.natDegree_Φ` / `leadingCoeff_Φ` —
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

Fork-local (travels with the development, NOT in mathlib):
- subject: `polyToField` (`Universal.lean:108`), `curve` (`Universal.lean:84`), `Universal.Field/Ring`
- crux: `polyEval_cusp_φ` (`ZSMul.lean:118`), `ringEval` (`Universal.lean:215`), `ringEval_mk`,
  `cusp_equation_one_one`, `cusp`

Composition sketch (the existing proof — **fork + mathlib**, NOT mathlib-only):
```lean
fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h   -- polyEval_cusp_φ: fork-local crux
  exact one_ne_zero h
```

Refactor plan:
- **Primary (cross-project dedup, do regardless):** this lemma is **duplicated** in NagellLutz
  (`ZSMul.lean:148`) and HasseWeil (`Auxiliary/DivisionPolynomial.lean:227`). Consolidate to one shared
  copy (coordinator-level dedup on `main`) before any mathlib consideration. (Its sibling `ψᵤ_ne_zero`
  and the whole universal-curve block are similarly duplicated — dedup as a unit.)
- **Mathlib disposition:** none for this decl as written. If/when the **parametric**
  `Φ`-nonvanishing/coprimality is upstreamed (a genuine gap above mathlib's `natDegree_Φ`), revisit —
  the universal-case lemma then folds into it by specialization.

Next action: answer Q1–Q4. Default recommendation absent further input: do **not** open a standalone
mathlib PR for `polyToField_φ_ne_zero` (its statement and crux both live only in the fork); de-duplicate
the cross-project copy with HasseWeil; keep this as a local helper bundled with the universal-curve
development; and — separately, as a real mathlib contribution — pursue the **parametric**
`(W.Φ n) ≠ 0` / `IsCoprime (W.Φ n) (W.ΨSq n)` above mathlib's existing division-polynomial degree theory.

---

## Next step

Human call (BORDERLINE): decide Q1–Q4 — pursue the *parametric* `Φ`-nonvanishing/coprimality upstream
(yes/no), choose the degree-route vs. universal-route proof, decide propose-or-keep-local for the
universal-curve package, and de-duplicate the NagellLutz/HasseWeil copy. Absent input, treat
`polyToField_φ_ne_zero` as fork-internal scaffolding (its statement names `polyToField`/`curve` and its
crux `polyEval_cusp_φ` are project-local; not mathlib-composable) and pursue the parametric `Φ ≠ 0` as
the separate, generalise-first mathlib contribution.
