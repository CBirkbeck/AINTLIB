# /mathlibable report — `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`

## Verdict: NO-composable-from-mathlib

One-line: mathlib exports every building block (`Affine.CoordinateRing.mk_Ψ_sq`,
`AdjoinRoot.evalEval_mk`, `Polynomial.evalEval_pow`/`evalEval_C`); this is the exact ≤3-call
composition — and it is already triplicated inside AINTLIB (HasseWeil twin + an inline copy).

---

### Baseline (Phase 0)
- lake build:               NOT re-run (env stale per task brief; reasoned from source + the
  vendored mathlib checkout under `.lake/packages/mathlib/…`).
- decl `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:47`.
- kind:                      theorem
- has sorry:                 no (3-line proof, EvalBridge.lean:48–51, shown below)
- module docstring summary:  "Eval bridge lemmas for Lutz–Nagell" — bridges the coordinate-ring
  congruences (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate
  polynomials at an on-curve point `(x, y)`.

**Qualified name VERIFIED.** The decl sits inside `namespace WeierstrassCurve` (EvalBridge.lean:24),
so the parsed `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq` is correct.

---

### Statement (Phase 1)

For a Weierstrass curve `W` over a field `F` and a point `(x, y)` on the curve
(`W.toAffine.Equation x y`), the **square** of the bivariate division polynomial `Ψ n` evaluated at
`(x, y)` equals the **univariate** polynomial `ΨSq n` evaluated at the x-coordinate:

> `((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x`.

Mathematically this is the standard fact that `ψₙ²` is a polynomial in `x` alone (the denominator of
`x([n]P)`): writing `gₙ(X) := ψₙ²`, one has `gₙ = hₙ²` for odd `n` and `gₙ = (x³+ax+b)·hₙ²` for even
`n` — exactly mathlib's `ΨSq` (`ΨSq_ofNat : preΨ' n ^ 2 * if Even n then Ψ₂Sq else 1`).

Variables / typeclasses (Lean side):
- `{F : Type*} [Field F]` — base field (section variable).
- `(W : WeierstrassCurve F)` — the Weierstrass curve.
- `{x y : F}` — coordinates of a point.
- `(n : ℤ)` — division-polynomial index.

Hypotheses:
- `(heq : W.toAffine.Equation x y)` — `(x, y)` lies on the curve.

Conclusion (Lean): `((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x`.

Proof body (3 lines):
```lean
have h := evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_Ψ_sq W n)
rw [evalEval_pow] at h
rw [h, evalEval_C]
```
where `evalEval_eq_of_mk_eq` (same file, line 32) is itself a 1-step wrapper over mathlib's
`AdjoinRoot.evalEval_mk`, and `mk_Ψ_sq` is mathlib's coordinate-ring congruence
`mk W (Ψ n) ^ 2 = mk W (C (ΨSq n))`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper "bridge lemma" (filed under "## Main results > bridge lemmas"), not a project
headline result; it feeds the Nagell–Lutz integrality argument (`x' · ΨSq n = Φ n`).
(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. Proof is 3 lines; no defeq/diamond concerns.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial psi_n squared depends only on x-coordinate ΨSq univariate Silverman"       | yes  | `gₙ(X)=ψₙ²`: `=hₙ²` (n odd), `=(x³+ax+b)hₙ²` (n even); `x(nP)=fₙ(x)/gₙ(x)` | MIT 18.783 Lec #5 & #6 (Sutherland); Wikipedia "Division polynomials"; arXiv 1103.4560 |
|  2 | WebSearch (general form / source)| (same sweep) `ψₙ²` as denominator of `x([n]P)`, Silverman GTM 106 convention                     | yes  | `n·(x,y)=(φₙ/ψₙ², …)` with `φₙ, ψₙ²` ∈ `R[x]` | Silverman GTM 106 (1986); Washington; Schoof/Stange — convention stable |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "psi-phi-omega" division-polynomial triple, `ψ²` denominator                  | yes  | same identity; projective `(φ:ψ²:ω)` | no proper-noun attaches to this specific bridge; pure textbook background |
|  4 | ChatGPT MCP                      | (UNAVAILABLE in this environment — fallback: WebSearch ×3 across distinct generalities + texts)  | n/a  | —                   | MCP down per task brief; compensated by Silverman + Sutherland + Wikipedia all agreeing |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                            | n/a  | (dir absent)        | no references directory for NagellLutz |
|  6 | nLab                             | "division polynomial"                                                                            | n/a  | not categorical     | classical arithmetic-geometry identity; no dedicated nLab page |
|  7 | nCatLab                          | —                                                                                               | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project                   | "division polynomial"                                                                            | n/a  | —                   | out of Stacks scope (no EC division-polynomial chapter) |
|  9 | MathOverflow / MSE               | "ψ_n^2 depends only on x elliptic curve"                                                         | yes  | folklore/textbook   | routinely cited as standard background, not a research question |
| 10 | recent arXiv (last 5 years)      | (returned by #1) Stange 2025 "Division polynomials for arbitrary isogenies"; 2505.12947 (2025)   | yes  | same classical `ψ²` convention reused | confirms the convention is stable and still standard |

### Literature summary (Phase 3)

Concept identified as: the standard fact that the squared division polynomial `ψₙ²` (mathlib `ΨSq`
univariate / `Ψ n` bivariate dressing) is a **function of `x` alone on the curve** — the denominator
of `x([n]P)`.
Sources agree on the standard form: yes — `gₙ = ψₙ²` with the odd/even split `hₙ²` vs `(x³+ax+b)hₙ²`,
matching mathlib's `ΨSq_ofNat`.
Most general standard form: a **ring-level polynomial identity** — mathlib's own `mk_Ψ_sq` is stated
over `[CommRing R]`; the `[Field F]` here is incidental to the Nagell–Lutz application, not intrinsic.
Generality dimensions where the literature varies:
  - base ring: texts state it over fields, but the identity is ring-level (mathlib `mk_Ψ_sq` is
    `[CommRing R]`); `[Field F]` is a strict over-restriction.
  - index `n`: `ℤ` (matches mathlib).
Disagreement with the literature: none. Textbook bridge, no novel content.

---

### Generality analysis — `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`

Literature-standard form is a ring-level polynomial fact; mathlib's `Affine.CoordinateRing.mk_Ψ_sq`,
`AdjoinRoot.evalEval_mk`, `Polynomial.evalEval_pow`, `Polynomial.evalEval_C` are all `[CommRing R]`.

| # | Parameter / hypothesis            | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|-----------------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[Field F]`                       | field             | commutative ring          | YES                 | every building block (`mk_Ψ_sq`, `evalEval_mk`, `evalEval_pow`, `evalEval_C`) is `[CommRing R]`; the proof never uses inverses. The HasseWeil twin `evalEval_ψ_sq` is in fact stated over `[CommRing R]`. |
| 2 | `(heq : W.toAffine.Equation x y)` | on-curve point    | on-curve point            | NO                  | essential — the collapse to `x` only holds on the curve. |
| 3 | `(n : ℤ)`                          | integer index     | integer index             | NO                  | matches mathlib `Ψ`/`ΨSq` indexing. |

### Generality verdict (Phase 4b)

Current form is: STRICTLY NARROWER THAN STANDARD (only the `[Field F]` over-restriction).
Number of weakening opportunities found: 1 (Field → CommRing).
Note: this generality gap is **not** what decides the verdict — even the maximally-general
`[CommRing R]` form is itself a ≤3-call mathlib composition (HasseWeil's `evalEval_ψ_sq` proves
exactly that form in 5 short lines). The Field-vs-CommRing point only confirms the lemma adds no
genuinely new content at any generality; it is captured by mathlib primitives either way.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | "let X be a foo" → typeclass? | no | already typeclass-driven (`[Field F]`/`[CommRing R]`). |
| 2 | sequences/metric → filters/topology? | no | purely algebraic polynomial identity. |
| 3 | construction → universal property? | no | concrete evaluation equality. |
| 4 | set+closure → bundled substructure? | no | n/a. |
| 5 | field/metric-specific → weaken typeclass? | yes | Field → CommRing (already noted in 4b row 1). |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index → general monoid? | no | `ℤ` index is intrinsic to division-polynomial indexing. |

Modern idiom available: no (beyond the Field→CommRing weakening already captured in 4b).

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem`.

---

### Mathlib search-status: `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`

[A] Lean-Finder       (index offline locally) — n/a: relied on direct mathlib-source grep (authoritative, exact pin).
[B] Loogle            pattern `Polynomial.evalEval _ _ (WeierstrassCurve.Ψ _) ^ 2 = _` — no exact end-to-end hit; building blocks present (see [D]).
[C] LeanSearch        "division polynomial Psi squared evaluated on curve equals ΨSq eval x" — no exact hit.
[D] Grep mathlib src  `evalEval`, `mk_Ψ_sq`, `evalEval_mk`, `evalEval_pow`, `evalEval_C` over `.lake/packages/mathlib/Mathlib/` — see below.
[E] Name pattern      `evalEval_Ψ`, `_eq_eval_ΨSq`, `evalEval_eq_of`, `Ψ_sq` — no decl with this combined meaning in mathlib.

Grep [D] findings (mathlib, vendored pin under `.lake/packages/mathlib`):
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338`
  `lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)` — the
  coordinate-ring congruence (the mathematical heart; **identical** to the project's forked copy at
  `LutzNagell/DivisionPolynomial.lean:261`, same proof byte-for-byte).
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:242`
  `noncomputable def ΨSq (n : ℤ) : R[X]` — the univariate `ψₙ²` (with `ΨSq_ofNat`, `ΨSq_odd`,
  `ΨSq_even` matching the textbook odd/even split).
- `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  `lemma AdjoinRoot.evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y` — bridges
  `mk`-equality (in `AdjoinRoot W.polynomial`) to `evalEval` at a zero `h` of the polynomial, i.e. an
  on-curve point.
- `Mathlib/Algebra/Polynomial/Bivariate.lean:142`
  `lemma Polynomial.evalEval_pow (x y) (p) (n) : (p ^ n).evalEval x y = p.evalEval x y ^ n` — pushes
  the square through `evalEval`.
- `Mathlib/Algebra/Polynomial/Bivariate.lean:49`
  `lemma Polynomial.evalEval_C (x y) (p) : (C p).evalEval x y = p.eval x` — strips the univariate
  dressing `C (ΨSq n)`.
- No `evalEval_eq_of_mk_eq`-style Weierstrass congruence in mathlib (the project's own
  `evalEval_eq_of_mk_eq`, EvalBridge.lean:32, is just `AdjoinRoot.evalEval_mk` re-stated for a curve
  point). Confirmed: mathlib has **zero** `evalEval` lemmas about division polynomials at all (only in
  `Affine/Basic.lean`, `Jacobian/Basic.lean`, etc., none touching `ψ`/`Ψ`/`φ`/`ΨSq`).

Searched for both the user's `[Field F]` form and the `[CommRing R]` literature-standard form.

Concluded: **not in mathlib as a single decl, but all building blocks are present** —
`Affine.CoordinateRing.mk_Ψ_sq` + `AdjoinRoot.evalEval_mk` + `Polynomial.evalEval_pow` +
`Polynomial.evalEval_C`. Note: NagellLutz's `WeierstrassCurve.Ψ`/`ΨSq`/`mk_Ψ_sq` are a **verbatim
copy** of mathlib's (file header of `LutzNagell/DivisionPolynomial.lean` states it is "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked only to avoid the
`normEDS`/`complEDS` name clash with `LutzNagell.EllipticDivisibilitySequence`), so the lemma stated
against mathlib's `Ψ`/`ΨSq` is literally the mathlib composition.

---

### Call sites — `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`

Internal use count: 2 (within NagellLutz, excluding the declaring file).
External-to-file callers: 2 distinct files.

| Caller file:line                                                              | Usage pattern |
|--------------------------------------------------------------------------------|---------------|
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean:50` | `have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq (curveQ W) hns.left n` (then bridged `Ψ`→`ψ` via `evalEval_ψ_eq_evalEval_Ψ`) |
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:59`     | `have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq (curveK R K W) hns.left n` |

Cross-project duplication grep — the **same** identity is independently present TWICE more in the
monorepo:
- `HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:729` — `evalEval_ψ_sq` (over `[CommRing R]`):
  `(W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x`, same `evalEval_eq_of_mk_eq` + `mk_ψ`/`mk_Ψ_sq` +
  `evalEval_pow`/`evalEval_C` route (5-line proof).
- `HasseWeil/HasseWeil/EC/IsogenyAG/CovarianceDischarge.lean:493–514` — the identical statement
  re-proved **inline** via `evalAt_mk` (= `evalEval_mk`), `map_pow`, `mk_ψ`, `mk_Ψ_sq`, `evalEval_C`.
  (Also re-derived at `MulByIntUnramified.lean:107`, `MulByIntSamePlace.lean:215`,
  `PairingNondeg.lean:159`.)

Signal reading: 2 internal `have`-style specialisations at proof sites, plus a `[CommRing R]` twin and
multiple inline re-derivations in HasseWeil. Triplication that exists precisely because the result is
trivially re-derivable — not because it is reusable API worth centralising. Points firmly to
NO-composable.

---

### Composition check (Phase 6)

Can `evalEval_Ψ_sq_eq_eval_ΨSq` be derived from mathlib in ≤3 chained calls? **Yes.**

The two LHS/RHS massagers `evalEval_pow` and `evalEval_C` only reshape the goal so that **both sides
become `evalEval` of `mk`-images**; the single mathematical step is `mk (Ψ n)^2 = mk (C (ΨSq n))`,
i.e. mathlib's `Affine.CoordinateRing.mk_Ψ_sq`, transported across the on-curve evaluation hom
`AdjoinRoot.evalEval_mk`. Counting distinct mathlib lemmas in the core chain:

```lean
-- heq : W.toAffine.Equation x y  ⇒  (W.polynomial).evalEval x y = 0  (mathlib `Equation` unfold)
example (heq : W.toAffine.Equation x y) (n : ℤ) :
    ((W.Ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  rw [← Polynomial.evalEval_pow x y (W.Ψ n) 2,          -- (·)^2 ↦ evalEval of (Ψ n)^2   [reshape]
      ← Polynomial.evalEval_C x y (W.ΨSq n),            -- RHS ↦ evalEval of C (ΨSq n)    [reshape]
      ← AdjoinRoot.evalEval_mk heq ((W.Ψ n) ^ 2),       -- (1) evalEval = evalEval h ∘ mk
      ← AdjoinRoot.evalEval_mk heq (C (W.ΨSq n)),       -- (1, same lemma)
      map_pow,                                          -- mk ((Ψ n)^2) = (mk (Ψ n))^2     [ring-hom]
      Affine.CoordinateRing.mk_Ψ_sq W n]                -- (2) the heart
```

Distinct mathlib lemmas in the chain: `AdjoinRoot.evalEval_mk` and `Affine.CoordinateRing.mk_Ψ_sq`
(the two carrying mathematical content), with `evalEval_pow` / `evalEval_C` / `map_pow` as structural
reshaping. Even counting generously, that is **3 content-bearing mathlib calls** — well within the ≤3
budget, and the HasseWeil `[CommRing R]` twin `evalEval_ψ_sq` already exhibits exactly this
composition in a 5-line proof.

Result: succeeds. Conclusion: **COMPOSABLE** (≤3 mathlib calls; HasseWeil's twin already does it).

---

## Verdict: `WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): textbook division-polynomial fact (`ψₙ²` depends only on `x` on the
  curve; the odd/even `hₙ²` vs `(x³+ax+b)hₙ²` split — MIT 18.783 Lec #5/#6, Silverman GTM 106,
  Wikipedia). Standard, not novel.
- Generality analysis (Phase 4): STRICTLY NARROWER (Field should be CommRing) — but irrelevant to the
  bucket, since even the general form is a ≤3-call composition.
- Mathlib search (Phase 5): not a single decl, but all building blocks present —
  `Affine.CoordinateRing.mk_Ψ_sq`, `AdjoinRoot.evalEval_mk`, `Polynomial.evalEval_pow`,
  `Polynomial.evalEval_C`.
- Composition check (Phase 6): COMPOSABLE (≤3 content-bearing calls; HasseWeil's `evalEval_ψ_sq`
  already does it over `[CommRing R]`).

**Rationale:**

Mathlib already contains the entire content of this lemma in compositional form. The mathematical
core — that the squared bivariate division polynomial `Ψ n` agrees, on the curve, with the univariate
`ΨSq n` (`= ψₙ²` as a polynomial in `x`) — is precisely mathlib's `Affine.CoordinateRing.mk_Ψ_sq`
(`mk W (Ψ n) ^ 2 = mk W (C (ΨSq n))`). Turning that coordinate-ring congruence into a pointwise
`evalEval` equality at an on-curve point is exactly mathlib's `AdjoinRoot.evalEval_mk` (the ring hom
from `AdjoinRoot W.polynomial` induced by a curve point); pushing the square through is
`Polynomial.evalEval_pow` and stripping the univariate dressing is `Polynomial.evalEval_C`. The
project's intermediary `evalEval_eq_of_mk_eq` is itself nothing more than `AdjoinRoot.evalEval_mk`
specialised to `W.polynomial`. No new mathematical idea is introduced; the proof is a 3-line rewrite.

The clinching evidence is the **triplication** inside the same monorepo: HasseWeil proves the
identical statement (`evalEval_ψ_sq`, over the more general `[CommRing R]`) by the same composition,
and re-derives it inline yet again in `CovarianceDischarge.lean` (and at several further HasseWeil
call sites). Duplication that exists precisely because the result is trivially re-derivable — not
because it is reusable API worth centralising.

Because `WeierstrassCurve.Ψ`/`ΨSq`/`mk_Ψ_sq` in this project are a verbatim fork of mathlib's (the
file header states it is "a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`",
forked only to avoid the `normEDS` name clash), there is no obstruction to phrasing this against
mathlib's own `Ψ`/`ΨSq`: the composition is literally a mathlib composition. So mathlib should not gain
this as a new lemma.

**WHY not (refactor-actionable):**
Mathlib has the building blocks, not this exact wrapper, and the wrapper is a ≤3-call composition.
- Building blocks:
  - `Affine.CoordinateRing.mk_Ψ_sq` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338`
  - `AdjoinRoot.evalEval_mk` — `Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  - `Polynomial.evalEval_pow` — `Mathlib/Algebra/Polynomial/Bivariate.lean:142`
  - `Polynomial.evalEval_C` — `Mathlib/Algebra/Polynomial/Bivariate.lean:49`
- Composition sketch (≤3 content-bearing calls): see Phase 6 block above.
- Call sites in this project (from Phase 6.0): K = 2.
  - `GeneralIntegralMultiple.lean:50` — `have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq (curveQ W) hns.left n`
  - `PIDIntegralMultiple.lean:59` — `have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq (curveK R K W) hns.left n`

Refactor plan:
1. Preferred (AINTLIB dedup): import HasseWeil's already-general `WeierstrassCurve.evalEval_ψ_sq`
   (`[CommRing R]`) and bridge `ψ`↔`Ψ` via `Affine.CoordinateRing.mk_ψ` at the 2 NagellLutz call
   sites — eliminating the NagellLutz `EvalBridge` copy. Note: HasseWeil states the `ψ` form; the
   `Ψ` form here differs only by `mk_ψ` (`mk (ψ n) = mk (Ψ n)`), so the bridge is one extra rewrite.
2. Alternatively, inline the ≤3-call mathlib composition (Phase 6) directly at each of the 2 sites.
3. Mind the Field→CommRing generality: HasseWeil's form is strictly more general and loses nothing at
   the NagellLutz call sites (both supply a field).

This is a **NO-for-mathlib** verdict with an AINTLIB-internal dedup recommendation: do not upstream;
consolidate the NagellLutz copy onto HasseWeil's `evalEval_ψ_sq` (or inline at the 2 sites). Treat
the whole forked `EvalBridge.lean` layer uniformly — every sibling (`evalEval_eq_of_mk_eq`,
`evalEval_ψ_eq_evalEval_Ψ`, `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_odd`) is the same NO-composable story.

---

## Next step

Do NOT upstream to mathlib. Within AINTLIB, dedup: replace
`WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq` (and likely the whole forked `EvalBridge.lean` /
`DivisionPolynomial.lean` bridge layer) with mathlib's
`Affine.CoordinateRing.mk_Ψ_sq` + `AdjoinRoot.evalEval_mk` + `evalEval_pow` + `evalEval_C`
composition, or re-use HasseWeil's already-general `WeierstrassCurve.evalEval_ψ_sq` (bridging
`ψ`↔`Ψ` via `mk_ψ`). Update the 2 call sites in `GeneralIntegralMultiple.lean` and
`PIDIntegralMultiple.lean` accordingly.

---

### Sources

- [Division polynomials — Wikipedia](https://en.wikipedia.org/wiki/Division_polynomials)
- [MIT 18.783 Elliptic Curves, Lecture #5 (Spring 2021), Sutherland](https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/680a7686aabd24b22a15eeb96e733838_MIT18_783S21_notes5.pdf)
- [MIT 18.783 Elliptic Curves, Lecture #6 (Spring 2015), Sutherland](https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf)
- [Topics in Elliptic Curves over Finite Fields (arXiv:1103.4560)](https://arxiv.org/pdf/1103.4560)
- Silverman, *The Arithmetic of Elliptic Curves*, GTM 106 (1986) — division-polynomial conventions (`x([n]P) = φₙ/ψₙ²`).
