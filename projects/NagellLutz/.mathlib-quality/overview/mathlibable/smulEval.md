# /mathlibable report — `WeierstrassCurve.smulEval`

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task note — reasoning from source)
- decl `WeierstrassCurve.smulEval`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:551`
- qualified name:           `WeierstrassCurve.smulEval` — defined inside `namespace WeierstrassCurve` (opened l.76) but **outside** the inner `Universal` namespace (which `end`s at l.546). So the name is `WeierstrassCurve.smulEval`, **not** `WeierstrassCurve.Universal.smulEval`.
- kind:                     `abbrev`  (⇒ Phase 2b one-liner check **applies**; Phase 4.5 diamond/defeq risk **applies** — `abbrev` = `@[reducible] def`)
- has sorry:                no
- module docstring summary: Proves `WeierstrassCurve.zsmul_eq_smulEval`: in Jacobian coordinates `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` for any integer `n` and nonsingular affine point `P=(x,y)` on a Weierstrass curve over a field.

### Statement (Phase 1)

`smulEval` is a **definition** (`abbrev`). It packages the three division polynomials `φₙ, ωₙ, ψₙ`, evaluated at a point `(x,y)`, into the `Fin 3 → R` **Jacobian coordinate vector** of the multiple `n · (x,y)`:

> For a Weierstrass curve `W` over a commutative ring `R`, a point `(x,y) ∈ R²`, and `n : ℤ`,
> `smulEval W x y n := evalEval x y ∘ ![φₙ, ωₙ, ψₙ]  :  Fin 3 → R`,
> i.e. the triple `(φₙ(x,y), ωₙ(x,y), ψₙ(x,y))` read as Jacobian `(2,3,1)`-weighted projective coordinates.

The whole point of the file is the theorem `zsmul_eq_smulEval` (l.590): for a nonsingular affine point `P=(x,y)` over a **field**, `(n • P).point = ⟦smulEval W x y n⟧` — the Jacobian point of `n • P` is exactly this triple. So `smulEval` is the **API object the entire division-polynomial ↔ group-law bridge is phrased in terms of**: `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, and `zsmul_eq_smulEval` are all statements about `smulEval`.

Variables / typeclasses involved (Lean side):
- `{R : Type*} [CommRing R]` — the base ring (most general algebraic setting; the *definition* needs only `CommRing`).
- `(W : WeierstrassCurve R)` — the curve (dot-notation receiver: `W.smulEval x y n`).
- `(x y : R)` — the affine coordinates of the base point (section `variable (x y)`).
- `(n : ℤ)` — the multiplier.
- Dependencies: `evalEval` (mathlib, `Mathlib/Algebra/Polynomial/Bivariate.lean:44`); `![·,·,·]` / `Fin 3 → R` Jacobian coords + `comp_fin3` (mathlib, `Jacobian/Basic.lean`); `W.ψ`, `W.φ` (mathlib `DivisionPolynomial/Basic.lean`); **`W.ω`** (NOT mathlib — project-defined at `LutzNagell/DivisionPolynomialOmega.lean:74`; mathlib lists `ωₙ` as an explicit **TODO**).

Hypotheses (Lean side): none (it is a definition).

Conclusion (math): n/a — definition. (It *names* the Jacobian-coordinate division-polynomial triple `(φₙ : ωₙ : ψₙ)` of `[n]P`.)

Conclusion (Lean): n/a — definition. Type: `Fin 3 → R`.

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It introduces a **named mathematical object** — the Jacobian-coordinate division-polynomial triple of `[n]P` — and is the headline definition behind a project **main result** (`zsmul_eq_smulEval`, named in the module docstring l.11). The underlying concept (multiplication-by-n via division polynomials / homogeneous division polynomials) is classical and named (Silverman; "homogeneous division polynomials", arXiv 1303.4327).
(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence                                                                                               |
|-----------------------------------|----------|---------------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | It is an `abbrev` (deliberately **reducible**) — the design *relies* on it unfolding (e.g. `simp only [smulEval, …]` at `PIDIntegralMultiple.lean:54`, and `rw [smulEval, comp_fin3]` throughout). It is the opposite of a defeq barrier. |
| Avoid typeclass diamonds         | no       | No instance is keyed on it; it is a plain `Fin 3 → R` value, not a structure carrying typeclasses.       |
| Mark semantic intent / API name  | **yes**  | This is the load-bearing reason: `smulEval` is the **named API surface** the whole `…Eval` lemma family and `zsmul_eq_smulEval` are stated against, and it has ≥3 external consumers (`PIDPrimeOrder.lean:67`, `PIDIntegralMultiple.lean:50,52,54`) plus a verbatim cross-project copy in HasseWeil with 7 consuming files. Renaming/inlining it would break all of these. The docstring + name *are* the API contract. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / stable-API-name). The exemption is genuine: a reducible named anchor that an entire theorem family and two projects depend on.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve multiplication by n Jacobian coordinates division polynomials (φₙ:ωₙ:ψₙ) point"        | **yes** | `nP = (φ_n : ω_n : ψ_n)` in Jacobian coords; also `nP = [φₙ·ψₙ : ωₙ : ψₙ³]` in standard projective | MIT 18.783 Lecture 6 (Sutherland), arXiv 1103.4560. **The Jacobian triple IS a named standard object.** |
|  2 | WebSearch (general form)         | "ω division polynomial elliptic curve definition bivariate R[X,Y] standard form Silverman"             | yes  | `ωₙ ∈ ℤ[a₁..a₆,x,y]`; `4yωₙ = Ψ_{n−1}²Ψ_{n+2} − Ψ_{n−2}Ψ_{n+1}²`; affine `[n]P=(φ/ψ², ω/ψ³)` | Silverman, *Arithmetic of Elliptic Curves*; jtnb (coeffs of division polys). Standard, char-sensitive `4y` denominators. |
|  3 | WebSearch (named-after / homogeneous) | "Homogeneous division polynomials for Weierstrass elliptic curves" (arXiv 1303.4327)             | **yes** | constructs homogeneous `αₙ,βₙ,γₙ` with `nP=(αₙ(P):βₙ(P):γₙ(P))` "starting from the classical division polynomials", **over an arbitrary ring** | This is *exactly* `smulEval`'s object: the projective/Jacobian triple of `[n]P` from classical `(φ,ω,ψ)`, ring-general. A dedicated paper on it. |
|  4 | ChatGPT MCP                      | (MCP down per task note — substituted by WebFetch of arXiv 1303.4327 abstract + mathlib4_docs, the standard-form + mathlib-state authorities) | yes | confirms `nP=(αₙ:βₙ:γₙ)` projective triple from classical division polys, arbitrary-ring; mathlib has ψ,φ,Ψ,Φ but `ωₙ` is TODO | Establishes both the literature standard form AND that mathlib lacks the `ω`/triple. |
|  5 | Local references                 | `ls .mathlib-quality/references/` (NagellLutz)                                                          | n/a  | directory absent                 | No project refs dir. Recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | —                                | nLab has no dedicated division-polynomial page; classical arithmetic geometry, not categorical. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "elliptic curve [n] multiplication coordinates"                                 | n/a  | —                                | Stacks treats elliptic curves abstractly; no explicit division-polynomial coordinate formulas. |
|  9 | MathOverflow / Math.SE           | covered transitively by #1 (MathOverflow "Motivation for Jacobian coordinates" thread in result set)    | yes  | same `nP=(φₙ:ωₙ:ψₙ)` Jacobian motivation | Confirms the Jacobian triple is the standard motivation for Jacobian coords on elliptic curves. |
| 10 | recent arXiv (last 5y)           | "division polynomials in Mumford coordinates" (2412.10284); "recurrence relation for EDS" (2102.07573); "Sequences associated to elliptic curves" (1909.12654) | yes | generalisations of the *model* (genus-2 / Mumford); Weierstrass case `nP=(φₙ:ωₙ:ψₙ)` as in #1,#3 | Modern work generalises the model/coordinates; the Weierstrass projective triple is settled. |

### Literature summary (Phase 3)

Concept identified as: **the Jacobian (resp. projective) coordinates of the multiplication-by-n map `[n]P` on a Weierstrass curve, expressed via division polynomials** — i.e. the triple `[n]P = (φₙ : ωₙ : ψₙ)` in `(2,3,1)`-weighted Jacobian coordinates. Equivalently "homogeneous division polynomials" (arXiv 1303.4327).
Sources agree on the standard form: **yes.** Classical affine `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` (Silverman); the **denominator-cleared Jacobian/projective triple `(φₙ : ωₙ : ψₙ)`** is the standard projective rendering (MIT 18.783, arXiv 1103.4560, arXiv 1303.4327). The auxiliary polynomials are the standard `φₙ = xψₙ² − ψ_{n−1}ψ_{n+1}` and `4yωₙ = ψ_{n−1}²ψ_{n+2} − ψ_{n−2}ψ_{n+1}²`.
Most general standard form: **over an arbitrary commutative ring** (arXiv 1303.4327 builds the homogeneous triple "over an arbitrary ring"), which is exactly the `[CommRing R]` generality of the Lean `abbrev`.
Generality dimensions where the literature varies:
  - Coordinate system: affine (with `ψ²`,`ψ³`, `4y` denominators) ↔ **Jacobian/projective triple** (denominator-free). `smulEval` uses the Jacobian triple — the more general/uniform choice.
  - Coefficient ring: from a fixed field up to an **arbitrary ring** (1303.4327). The `abbrev` is stated at `[CommRing R]` = maximal.
Disagreement with the literature: **none.** `smulEval` is a faithful Lean rendering of the standard Jacobian division-polynomial triple of `[n]P`. (Correction to the sibling `addXYZ_smulField` report, which called the Jacobian triple "formalization-native": channels #1 and #3 show it *is* a literature object — there is a dedicated paper, arXiv 1303.4327.)

---

### Generality analysis — `WeierstrassCurve.smulEval`

Literature-standard form (from Phase 3): the Jacobian triple `[n]P = (φₙ : ωₙ : ψₙ)` over an arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring `[CommRing R]` | `CommRing` | arbitrary commutative ring (1303.4327) | NO | already maximal — the *definition* needs only `CommRing` (the polynomials and `evalEval` are defined over any `CommRing`). The downstream *theorem* `zsmul_eq_smulEval` needs a field, but the `abbrev` itself does not. |
| 2 | curve `W : WeierstrassCurve R` | any Weierstrass curve | any Weierstrass curve | NO | maximal. |
| 3 | point `(x y : R)` | arbitrary ring elements | a point on the curve | (looser, intentionally) | the `abbrev` does not even require `(x,y)` to lie on `W` — it is a pure formula. That is *more* general than "a point on the curve", which is correct for a definition (the on-curve hypothesis enters only in the theorems). |
| 4 | multiplier `n : ℤ` | arbitrary integer | arbitrary integer | NO | intrinsic (integer-multiplication map). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** The `abbrev` is stated over an arbitrary `CommRing` with no on-curve hypothesis — exactly the generality of the literature's "homogeneous division polynomials over an arbitrary ring" (arXiv 1303.4327), and strictly more permissive than any field-specific textbook form.
Number of weakening opportunities found: 0.
Proposed restatement: none needed.
Cost of restatement: n/a.

The *only* obstruction to mathlib is not generality but a **missing dependency**: `smulEval` is defined via `W.ω`, and mathlib has no `ωₙ` (it is a documented TODO in `DivisionPolynomial/Basic.lean`). So `smulEval` cannot be added to mathlib *until/unless* `ω` is upstreamed first.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | already typeclass-driven (`[CommRing R]`); no bundled hypotheses to convert. |
|  2 | sequences/metric → filters/topology? | no | — | purely algebraic; no analysis. |
|  3 | construction → universal-property class? | no | — | `smulEval` is intentionally a *concrete computable formula* (the point of the file is to *compute* `n • P`); a universal-property wrapper would defeat its purpose. |
|  4 | set+closure-pred → bundled substructure? | no | — | n/a (it is a vector, not a substructure). |
|  5 | field/metric-specific → weaken typeclass? | **already done** | the `abbrev` is at `[CommRing R]`, the weakest sensible class; the field only appears later in `zsmul_eq_smulEval`. | the `CommRing`-level definition is what lets the universal-ring machinery (`smulRing`/`smulPoly`) and arbitrary-base specialisations (`ringEval`) compose. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index ℤ → general additive structure? | no | `n : ℤ` is intrinsic (integer multiples of a point). | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** `smulEval` is already in the contemporary mathlib idiom — a `CommRing`-general, dot-notation `abbrev` built from mathlib's `evalEval` and `Fin 3 → R` Jacobian-coordinate API. It is, in fact, the *consumer-facing* modern form that the sibling `Universal.*` lemmas exist to support. No reorganisation improves it.

---

### Diamond / defeq risk — `WeierstrassCurve.smulEval`  (kind = `abbrev`, so this phase RUNS)

| # | Risk                          | Verdict   | Evidence / rationale                                                |
|---|-------------------------------|-----------|---------------------------------------------------------------------|
| 1 | Typeclass diamond            | none      | The result type is a bare `Fin 3 → R`; no instance is declared on `smulEval` and it participates in no typeclass search. No diamond possible. |
| 2 | Reducibility leak            | **low**   | `abbrev` ⇒ `@[reducible]`, so the body `evalEval x y ∘ ![φₙ,ωₙ,ψₙ]` is exposed to defeq/`simp`/unification everywhere. This is **intended** (consumers do `simp only [smulEval]`, `rw [smulEval, comp_fin3]`). The body is a small composition, not a heavy computation, so the reducibility cost is mild. Were this upstreamed, a maintainer might prefer a sealed `def` + a `@[simp] smulEval_def` unfolding lemma over a bare `abbrev`, to control where it unfolds — a style call, not a correctness issue. |
| 3 | Non-canonical unfolding      | low       | `rfl`/`simp` unfold it to `evalEval x y ∘ ![…]`, which is exactly what every consumer wants. No surprising unfolding direction. |
| 4 | Instance priority collision  | n/a       | Not an `instance`. |
| 5 | Universe-polymorphism issues | none      | Monomorphic in `Type` (`R : Type*`, output `Fin 3 → R`); no universe annotation forced. |
| 6 | Coercion ambiguity           | none      | No `CoeFun`/`CoeSort`; it is an ordinary function value. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW.**
Top risks: only the (intended) reducibility leak from `abbrev` — row 2. Acceptable: the whole API is designed around `smulEval` unfolding.
Recommended mitigation (style, optional): if upstreamed, consider `def` + `@[simp]`-tagged unfolding lemma instead of `abbrev`, so unfolding is opt-in. Does not affect the verdict.

---

### Mathlib search-status: `WeierstrassCurve.smulEval`

[A] Lean-Finder       n/a (mathlib index unavailable in-session; substituted by direct mathlib-source grep [D] + mathlib4_docs WebFetch in Phase 3 #4)
[B] Loogle            type pattern `WeierstrassCurve → _ → _ → ℤ → (Fin 3 → _)` / `_ ∘ ![_, _, _]` over Weierstrass — covered by [D]; no such `def` in mathlib
[C] LeanSearch        "Jacobian coordinates of n times a point as division polynomials" — covered by Phase-3 #4 (mathlib4_docs: only `DivisionPolynomial.Basic` *polynomials* exist; no point-triple)
[D] Grep mathlib src  `smulEval`, `def ω|abbrev ω`, `![.*φ.*ω.*ψ]`, `evalEval.*∘`, `Jacobian.*divisionPolynomial`, `zsmul.*divisionPolynomial`, `Point.*φ` → **`smulEval`: 0 hits; `ω`: 0 def (TODO only); no triple/coordinate construct**
[E] Name pattern      `WeierstrassCurve.smulEval`, `*smul*Eval`, `divisionPolynomialEval`, `toJacobian.*φ` → **0 hits in mathlib**

Searched for both:
  - the user's current form (`smulEval` = `evalEval x y ∘ ![φₙ,ωₙ,ψₙ]`) — **not in mathlib**
  - the literature-standard form (the projective/Jacobian triple `[n]P=(φₙ:ωₙ:ψₙ)`, "homogeneous division polynomials") — **not in mathlib** (mathlib has `ψ,φ,Ψ,Φ` polynomials only; **no `ω`** (TODO), and no construct giving `[n]P`'s coordinates)

Mathlib pieces that DO exist and that `smulEval` is **built from**:
  - `Polynomial.evalEval` — `Mathlib/Algebra/Polynomial/Bivariate.lean:44` (the bivariate evaluation `p(x,y)`)
  - `Fin 3 → R` Jacobian-coordinate `SMul` + `comp_fin3` + `![·,·,·]` — `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean:130,137`
  - `WeierstrassCurve.ψ`, `WeierstrassCurve.φ` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:401,448`

Mathlib piece that is **MISSING** (the blocker):
  - `WeierstrassCurve.ω` — **not in mathlib**; explicit `TODO: the bivariate polynomials ωₙ.` in `DivisionPolynomial/Basic.lean` (l.71). Supplied by this project at `LutzNagell/DivisionPolynomialOmega.lean:74`.

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form).** mathlib has two of `smulEval`'s three division-polynomial inputs and all of the wrapping machinery (`evalEval`, `![…]`, Jacobian `SMul`), but is **missing `ω`** and has **no point-coordinate construct**. The `abbrev` itself is also **duplicated verbatim across two AINTLIB projects** (see Phase 6).

---

### Call sites — `WeierstrassCurve.smulEval`

Internal use count (NagellLutz, excluding the declaring file `ZSMul.lean`): **2 files / ≥4 sites** —
- `LutzNagellTheorem/PIDPrimeOrder.lean:67` — via `zsmul_eq_smulEval (curveK R K W) hns n` (the bridge theorem, which is *stated* in terms of `smulEval`).
- `LutzNagellTheorem/PIDIntegralMultiple.lean:50,52,54` — both via `zsmul_eq_smulEval` and **directly**: `smulEval (curveK R K W) x y n ≈ ![x', y', 1]` (l.52) and `simp only [smulEval, Function.comp, …]` (l.54).

Within the declaring file `ZSMul.lean`: **20 occurrences** — the entire `…Eval` lemma family (`ringEval_comp_smulRing`, `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, `zsmul_eq_smulEval`) is phrased in terms of `smulEval`.

External-to-project: **duplicated verbatim in HasseWeil.** `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:625` defines the **byte-identical** `abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]`, consumed across **7 HasseWeil files** (`MulByIntPullback`, `EC/MulByIntUnramified`, `EC/GenericPointZsmul`, `EC/MulByIntSamePlace`, `EC/IsogenyAG/CovarianceDischarge`, `WeilPairing/TorsionKernelRational`, plus the declaring `Auxiliary/DivisionPolynomial`). E.g. `smulEval_generic_Z/X/Y` and `jacobian_equation_smulEval` in `MulByIntPullback.lean` are all about it.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| NagellLutz `PIDPrimeOrder.lean:67` | `have heval := zsmul_eq_smulEval (curveK R K W) hns n` |
| NagellLutz `PIDIntegralMultiple.lean:52` | `show smulEval (curveK R K W) x y n ≈ ![x', y', 1]` |
| NagellLutz `PIDIntegralMultiple.lean:54` | `simp only [smulEval, Function.comp, Matrix.cons_val_zero, …]` |
| HasseWeil `MulByIntPullback.lean:241` | `smulEval (W_KE W) (x_gen W) (y_gen W) n 2 = ψ_ff W n` (component projection) |
| HasseWeil `MulByIntPullback.lean:266` | `WeierstrassCurve.Jacobian.Equation (W_KE W).toJacobian (smulEval (W_KE W) …)` |

Inline-derivation grep: the **entire `abbrev` is re-declared verbatim in HasseWeil** — the strongest possible "this is shared infrastructure living in two places" signal.

Call-site reading: this is firmly the **K ≥ 3 internal uses, real API** row of the heuristic table (≥4 NagellLutz sites across 2 files + 20 in-file + a second project with 7 consuming files). Combined with the Phase-2b semantic-name exemption, `smulEval` is a genuine, heavily-used, public-facing API definition — not a wrapper consumers bypass.

---

### Composition check (Phase 6)

Can `smulEval` be obtained from mathlib in ≤3 chained calls?

This is a **definition**, so "composition" means: is its body just a mathlib expression that should be inlined at call sites rather than named?

Attempt 1: inline `evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]` directly at each call site.
  - Mathlib decls used: `Polynomial.evalEval`, `comp_fin3`, `![·,·,·]`, `W.φ`, `W.ψ`.
  - Result: **fails — one input is not mathlib.** `W.ω` is **not in mathlib** (TODO). The body cannot be written purely in mathlib terms; it depends on the project's `ω` definition. So inlining "from mathlib" is impossible until `ω` is upstreamed.
  - Even granting `ω`: inlining would *de-name* the object that `zsmul_eq_smulEval`, `dblXYZ_smulEval`, `addXYZ_smulEval`, and ~30 call sites across two projects are stated against. Per the Phase-2b semantic-API exemption and the K≥3 call-site signal, the named anchor is justified, not a candidate for inlining.

Conclusion: **NOT-COMPOSABLE-FROM-MATHLIB.** (a) Its body references `ω`, which mathlib lacks; (b) it is a deliberately-named, heavily-reused API surface, not a wrapper to inline. The right move is *not* "inline using mathlib" but "upstream `ω` + this triple together".

---

## Verdict: `WeierstrassCurve.smulEval`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the object — the Jacobian/projective triple `[n]P = (φₙ : ωₙ : ψₙ)` over an arbitrary ring — **is** a named standard construction ("homogeneous division polynomials", arXiv 1303.4327; MIT 18.783; arXiv 1103.4560). `smulEval` is a faithful Lean rendering. mathlib does not have it.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `[CommRing R]`, no on-curve hypothesis on `(x,y)`, matching the literature's arbitrary-ring homogeneous form. Phase 4c: already in the modern mathlib idiom; no reorganisation improves it.
- Diamond/defeq risk (Phase 4.5): **LOW** (only the intended `abbrev` reducibility leak).
- Mathlib search (Phase 5): **NOT in mathlib.** Built from mathlib `evalEval` + `Fin 3` Jacobian API + `ψ,φ`, but **`ω` is missing (a documented mathlib TODO)** and there is no point-coordinate construct.
- Composition check (Phase 6): **NOT-COMPOSABLE-FROM-MATHLIB** — body references the non-mathlib `ω`, and it is a deliberately-named API anchor with K≥3 consumers across two projects.

**Rationale:**

`smulEval` is mathlib-*worthy in spirit and form*: it names a standard literature object (the Jacobian division-polynomial triple of `[n]P`), at maximal generality (`CommRing`, arbitrary ring — matching arXiv 1303.4327), in the contemporary mathlib idiom (dot-notation `abbrev` over mathlib's `evalEval` and `Fin 3 → R` Jacobian-coordinate API), with low defeq risk and a genuine semantic-name exemption (Phase 2b). It is the public face of the division-polynomial ↔ Jacobian-group-law bridge — `zsmul_eq_smulEval` and the whole `…Eval`/`…smul*` family are stated against it — and that bridge is a real, TODO-shaped hole between mathlib's `DivisionPolynomial/Basic` (polynomials only) and mathlib's Jacobian group law (Angdinata–Xu, ITP 2023). It is also **duplicated verbatim across two AINTLIB projects** (NagellLutz `ZSMul.lean:551` ≡ HasseWeil `Auxiliary/DivisionPolynomial.lean:625`), the canonical "should be shared, ideally upstream" signal.

What makes the verdict **BORDERLINE rather than a clean YES** are two coupled judgments the skill must not make alone:

1. **A hard dependency blocker.** `smulEval` is *defined via* `W.ω`, and **mathlib has no `ω`** — it is an explicit `TODO` in `DivisionPolynomial/Basic.lean`. `smulEval` literally cannot be added to mathlib until `ω` is upstreamed first. So this decl is not a standalone PR; it is the tip of a bundle (`ω` → the `Universal`/`smul*` engine → `smulEval` → `zsmul_eq_smulEval`) that must go up together, in order. And the project **forks** mathlib's `EllipticDivisibilitySequence`/`DivisionPolynomial` (to swap the EDS implementation), so that fork must be reconciled before any of this lands. Both are maintainer-level decisions.

2. **Packaging granularity + the `abbrev`-vs-`def` style call** (same family-level question as the sibling `addXYZ_smulField` report). Whether `smulEval` ships as a public `abbrev`, a sealed `def` with a `@[simp]` unfolding lemma, or stays an internal name with only `zsmul_eq_smulEval` exported, and under which file — is a design decision that must be made for the whole `smul*`/`…Eval` family at once, not lemma-by-lemma.

This is **not** a cost-driven downgrade (the decl is trivial; the generality is already maximal; nothing needs re-proving). It is genuinely "the dependency ordering (`ω` first), the fork reconciliation, and the public-API granularity for upstreaming need a human/maintainer call" — exactly what BORDERLINE is for. Independently of upstreaming, the **cross-project verbatim duplication should be de-duplicated into AINTLIB `Common/`** as a cleanup ticket.

**Numbered questions (≤5):**
  1. `smulEval` depends on `W.ω`, which is a **mathlib TODO** (not yet upstreamed). Should `ω` be contributed to mathlib's `DivisionPolynomial/Basic.lean` **first**, as the prerequisite, with `smulEval` following in the same PR series? (yes/no)
  2. Should the upstream unit be the **whole** division-polynomial↔Jacobian bridge — `ω`, `smulPoly/Ring/Field`, `dblXYZ_smul*`, `addXYZ_smul*`, `smulEval`, `zsmul_eq_smulEval` — shipped together (e.g. `…/DivisionPolynomial/Jacobian.lean`), with `smulEval` as a **public** named definition? (yes/no)
  3. Style: ship `smulEval` as a reducible `abbrev` (current), or as a sealed `def` + `@[simp] smulEval_def` unfolding lemma (more control over where it unfolds)? (abbrev / def)
  4. The `abbrev` is **duplicated verbatim in HasseWeil** (`Auxiliary/DivisionPolynomial.lean:625`). Regardless of upstreaming, should this be de-duplicated into an AINTLIB `Common/` module first (a cleanup ticket)? (yes/no)
  5. The project **forks** mathlib's `EllipticDivisibilitySequence`/`DivisionPolynomial`. Must that fork be reconciled with mathlib before `ω`/`smulEval` can be upstreamed, and is that a blocker or a parallel track? (blocker / parallel)

Next action: user/maintainer answers 1–5; the decisive gate is Q1 (`ω` must be upstreamed before `smulEval` can be). Once the bundle/ordering/style are decided, re-run `/mathlibable WeierstrassCurve.smulEval` or commit directly to YES-add-as-is (the decl is maximally general, low-risk, with a valid one-liner exemption). Independently, file an AINTLIB cleanup ticket to de-duplicate the NagellLutz/HasseWeil copies into `Common/`.

---

## Next step

Answer questions 1–5 above. The mathematics is mathlib-worthy and NOT in mathlib (the Jacobian division-polynomial triple of `[n]P` — a named literature object — is a genuine gap), and the decl is maximally general, low defeq-risk, with a valid semantic-API one-liner exemption. The blockers are not the decl itself but (i) its **missing dependency `ω`** (a mathlib TODO that must land first), (ii) reconciling the project's EDS/DivisionPolynomial **fork** with mathlib, (iii) the **public-API granularity/style** for upstreaming the `smul*`/`…Eval` family as one ordered PR series, and (iv) the verbatim NagellLutz/HasseWeil **duplication** to resolve into `Common/`.
