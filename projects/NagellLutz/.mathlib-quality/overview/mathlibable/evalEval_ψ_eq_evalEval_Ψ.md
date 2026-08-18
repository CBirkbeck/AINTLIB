# /mathlibable report — `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`

## Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read from source.
  HOWEVER the upstream mathlib sources are present locally under
  `.lake/packages/mathlib/` (pin: leanprover/lean4 v4.32.0-rc1), so every mathlib claim
  below was VERIFIED against actual upstream source, not just reasoned from the statement.
- decl `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`: resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/EvalBridge.lean:42`

### Re-verification pass (independent of prior report text)
- `Affine.CoordinateRing.mk_ψ`: **present upstream**, `CommRing`-level, at
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`
  — and is duplicated **byte-for-byte** in the project fork
  (`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:361`, header line 12 declares it "a copy
  of `Mathlib...DivisionPolynomial.Basic`"). So the lemma's mathlib input is genuine upstream, not a
  fork-only artefact; the fork changes only which EDS file it imports.
- `AdjoinRoot.evalEval_mk`: **present upstream**, `CommRing`-level, at
  `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Bivariate.lean:391`
  (its hypothesis is literally `h : p.evalEval x y = 0`, `variable ... [CommRing R]` at line 383).
- `Equation`: `def Equation (x y) : Prop := W.polynomial.evalEval x y = 0`
  (`.lake/.../Affine/Basic.lean:149`). Hence `heq : Equation x y` is **defeq** to the exact
  hypothesis `evalEval_mk` wants (with `p := W.toAffine.polynomial`) — the composition needs **no**
  massaging step. Confirms the Phase-6 defeq caveat.
- Eval bridge upstream: an exhaustive name-pattern sweep of all of `Mathlib/`
  (`evalEval_ψ|evalEval_Ψ|evalEval_φ|evalEval_eq_of_mk|psi.*evalEval`) returns **empty**, and the
  whole `DivisionPolynomial/` dir contains **zero** `evalEval`/`Equation` mentions → the bridge is
  genuinely absent from mathlib. (The `evalEval` hits in the EllipticCurve tree are all about
  `polynomial`/`polynomialX`, i.e. the curve equation, never the division polynomials.)
- `[Field F]`: the proof term `evalEval_eq_of_mk_eq W heq (mk_ψ W n)` invokes only
  `AdjoinRoot.evalEval_mk` + `mk_ψ`, both `CommRing`-level → the `Field` hypothesis is **genuinely
  unused**, confirming the Phase-4 "strictly narrower than standard" finding.

All prior-report claims survived this independent re-check; verdict unchanged.
- kind:                     theorem
- has sorry:                no (proof: `evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)`)
- module docstring summary: "Eval bridge lemmas for Lutz–Nagell" — bridges the coordinate-ring
  congruence lemmas (`mk_ψ`, `mk_φ`, `mk_Ψ_sq`) to concrete equalities after evaluating bivariate
  polynomials at an on-curve point `(x, y)`.

Qualified name **VERIFIED** from source: the file opens `namespace WeierstrassCurve`, so the
fully-qualified name is `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`. ✓

---

## Statement (Phase 1)

`WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ` is a theorem stating:

Let `W` be a Weierstrass curve over a field `F`, and let `(x, y)` be a point on the affine curve
(i.e. `W.toAffine.Equation x y`). Then for every integer `n`, the bivariate `n`-division polynomial
`ψ n ∈ F[X][Y]` and its univariate-dressed coordinate-ring representative `Ψ n ∈ F[X][Y]` evaluate
to the **same value** at `(x, y)`:
`(ψ n).evalEval x y = (Ψ n).evalEval x y`.

Mathematically: in the coordinate ring `F[W] = F[X][Y]/(W.polynomial)`, mathlib already proves
`mk W (ψ n) = mk W (Ψ n)` (`Affine.CoordinateRing.mk_ψ`). This lemma transports that congruence
across the quotient map down to an honest numerical equality at any chosen on-curve point — i.e. it
discharges the standard slogan "evaluating at a rational point recovers the relation, avoiding the
coordinate ring".

Variables / typeclasses involved (Lean side):
- `{F : Type*} [Field F]` — the base field
- `(W : WeierstrassCurve F)` — the curve
- `{x y : F}` — coordinates of the evaluation point

Hypotheses (Lean side):
- `(heq : W.toAffine.Equation x y)` — `(x, y)` lies on the curve (Weierstrass polynomial vanishes)
- `(n : ℤ)` — the division-polynomial index

Conclusion (math): `ψ_n(x, y) = Ψ_n(x, y)` for any on-curve `(x, y)`.
Conclusion (Lean): `(W.ψ n).evalEval x y = (W.Ψ n).evalEval x y`

---

## Size classification (Phase 2a)

Verdict: SMALL
Reason: a glue/specialisation lemma — its entire body is one application of the file-local parent
`evalEval_eq_of_mk_eq` to the mathlib congruence `mk_ψ`. Not a named theorem, not a new structure,
not a `## Main results` headline of the project (the headline is the Nagell–Lutz theorem itself).

(Literature width is EXHAUSTIVE regardless; recorded for framing.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line *definition* check is n/a.
Note: the proof term is a single line (`evalEval_eq_of_mk_eq W heq (mk_ψ W n)`); this makes it a
**glue lemma** (single application of the parent over a mathlib input), which is the dominant
signal in Phases 6–7.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial evaluation coordinate ring point Weierstrass"          | yes  | ψ_n(P) recovers relation up to Weierstrass eqn | Surfaced the mathlib `DivisionPolynomial/Basic` doc verbatim: "evaluating these polynomials at a rational point on W recovers their original definition … hence also avoiding the need to work in the coordinate ring." |
|  2 | WebSearch (general / math form)  | "division polynomial psi_n evaluated at point P elliptic curve definition Silverman"       | yes  | ψ_n(P)=0 ⟺ P is n-torsion; [n]P = (φ/ψ², ω/ψ³) | Standard (Wikipedia, MIT 18.783, Silverman); the *content* (ψ_n evaluated at a point) is classical and ubiquitous |
|  3 | WebSearch (Lean/mathlib aliases) | "Mathlib WeierstrassCurve division polynomial evalEval coordinate ring AdjoinRoot"         | yes  | `AdjoinRoot.evalEval`, `mk_ψ`, `evalEval_mk` | Confirms the building blocks live in mathlib; the *bridge to evaluation* does not appear in the docs hit list |
|  4 | ChatGPT MCP                      | (MCP down per task note — substituted by extra primary-source reads of mathlib source + Wikipedia/MIT notes) | n/a  | — | Fallback used: read mathlib `Basic.lean` docstring + `Affine/Basic.lean` `Equation ↔ evalEval = 0` directly |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/`                                            | n/a  | (no references dir) | Neither `projects/NagellLutz/.mathlib-quality/references/` nor `refs/` exists — recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                   | n/a  | — | nLab has no dedicated division-polynomial entry; concept is elementary algebraic, not categorical — n/a |
|  7 | nCatLab (categorical)            | —                                                                                          | n/a  | — | Not a categorical concept (a polynomial identity under evaluation) — n/a |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                                      | n/a  | — | Stacks does not treat division polynomials of Weierstrass curves — n/a |
|  9 | MathOverflow / MSE               | "division polynomial evaluated at point coordinate ring"                                   | yes  | confirms #2 | Routine: ψ_n(P) is the universal value specialised at P; no novelty |
| 10 | arXiv (recent)                   | "explicit valuations of division polynomials integral points" (1108.3051), "p-adic properties of division polynomials" (math/0404412) | yes  | division polys evaluated at points are the working object throughout | These papers *use* ψ_n(P) constantly; the evaluation step is assumed, never a named lemma |

The protocol passed: WebSearch ran 3 distinct queries (specific / general-math / Lean-alias);
ChatGPT MCP was unavailable and explicitly substituted with extra primary-source reads; local refs,
nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: *evaluation of the n-th division polynomial at a point of the curve* —
classical (Silverman, *Arithmetic of Elliptic Curves*, exercise 3.7 / III.§; MIT 18.783 Lecture 5;
Wikipedia "Division polynomials"). The mathlib-specific framing is: transport the coordinate-ring
congruence `mk_ψ` (already in mathlib) along the evaluation map `AdjoinRoot.evalEval` (already in
mathlib) to a numerical equality at an on-curve point.

Sources agree on the standard form: yes — ψ_n(P) is a completely standard object; the equality
"the bivariate ψ_n and its univariate dressing agree when evaluated on the curve" is the routine
specialisation of the coordinate-ring identity at a point. No source treats it as a *named* result;
it is a one-line consequence of "P is on the curve ⟹ the Weierstrass relation evaluates to 0".

Most general standard form: holds over any commutative ring `R` for any point with
`W.polynomial.evalEval x y = 0` (the on-curve condition). Field is not needed.

Generality dimensions where the literature varies:
  - base: any commutative ring (literature/universal-ring version) ↔ field (this Lean form). The
    universal form is strictly more general.
  - the statement is really about *any* pair `p, q` with `mk W p = mk W q`, not specifically ψ/Ψ —
    i.e. the parent `evalEval_eq_of_mk_eq` is the general statement and this is a ψ-instance.

Disagreement with the literature: none — the Lean form is a faithful (slightly specialised)
rendering of a routine classical step.

---

## Generality analysis — `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`

Literature-standard form (from Phase 3): for any commutative ring `R`, any on-curve `(x, y)`, and
any `n`, `ψ_n` and `Ψ_n` agree under evaluation; more fundamentally, *any* two coordinate-ring-equal
bivariate polynomials agree under evaluation at an on-curve point.

| # | Parameter / hypothesis      | Current Lean form            | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[Field F]`                 | base is a field              | any commutative ring `R`         | yes                 | Proof uses only `AdjoinRoot.evalEval_mk` + `mk_ψ`, both stated over `CommRing`. `Field` is unused. The parent `evalEval_eq_of_mk_eq` and `mk_ψ` are already ring-level in mathlib — the field restriction here is gratuitous (inherited from the Lutz–Nagell context, not the lemma). |
| 2 | `W.toAffine.Equation x y`   | on-curve via `Equation`      | `W.polynomial.evalEval x y = 0`  | NO (already minimal)| This *is* the minimal hypothesis; `Equation` unfolds to exactly `polynomial.evalEval x y = 0`. Cannot weaken. |
| 3 | specialised to `ψ`/`Ψ`      | the ψ/Ψ pair                 | any `mk`-equal pair `p, q`       | yes                 | The general statement is the parent `evalEval_eq_of_mk_eq`; this lemma is its ψ-instance. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (on the base-ring axis: `Field F` is unused;
the proof is ring-level).
Number of weakening opportunities found: 2 (drop `Field` → `CommRing`; and it is itself a
specialisation of the more-general parent lemma).

Proposed restatement (ring-level), *if one were upstreaming the bridge*:
```lean
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
theorem evalEval_ψ_eq_evalEval_Ψ (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
  evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)
```
Cost of restatement: CHEAP — the proof term is unchanged; only the typeclass on the base is relaxed.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass? | no | — | Already typeclass-based (`CommRing`/`Field`). |
| 2 | sequences/metric → filters/topology? | no | — | Purely algebraic polynomial identity; no analysis. |
| 3 | construct → universal property? | no | — | The universal-ring construction already lives upstream in mathlib's EDS; this is its evaluation, not a construction. |
| 4 | set+closure-pred → bundled substructure? | no | — | No substructure here. |
| 5 | field/metric-specific → weaken typeclass? | **yes** | drop `Field F` → `CommRing R` (see 4b) | The whole `evalEval`/`mk` API is `CommRing`-level; ring-level statement composes with the universal-ring and base-change lemmas mathlib already has. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general structure? | no | — | `n : ℤ` is already the right index (EDS are ℤ-indexed); cannot generalise further. |

### Modern-idiom verdict (Phase 4c)
Modern idiom available: yes (only row 5 — the `Field → CommRing` weakening, already captured in 4b).
- Proposed mathlib-idiomatic restatement: the `CommRing` version above.
- Cost: CHEAP.
- Mathlib downstream this enables: ring-level evaluation bridge usable directly inside the universal
  characteristic-0 ring `𝓡[X,Y]` that mathlib's EDS machinery is built on, without a field detour.
- Real mathematical improvement: yes — matches the generality of `mk_ψ` and `AdjoinRoot.evalEval_mk`
  it is built from; the field hypothesis is genuinely unused.

(Phase 4.5 Diamond/defeq risk: n/a — declaration kind is `theorem`.)

---

## Mathlib search-status: `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`

[A] Lean-Finder       (index offline locally) — substituted by direct mathlib source grep    n/a: index not callable here
[B] Loogle            `(WeierstrassCurve.ψ _).evalEval _ _ = _`, `_ .evalEval _ _ = _ .evalEval _ _` (over EllipticCurve)   no hits in mathlib EllipticCurve tree
[C] LeanSearch        "division polynomial evaluated at point equals" (via WebSearch surfacing mathlib docs)  no hit — only `mk_ψ` (coordinate-ring form) surfaces, not an eval form
[D] Grep mathlib src  `evalEval_ψ`, `evalEval_Ψ`, `evalEval.*ψ`, `evalEval` in `DivisionPolynomial/`   **no hits** — `DivisionPolynomial/Basic.lean` and `Degree.lean` never mention `evalEval`/`Equation` at all
[E] Name pattern      `evalEval_ψ_eq_evalEval_Ψ`, `evalEval_eq_of_mk_eq` across mathlib   no hits (exists only in the project)

Searched for both:
  - the user's current form (`(ψ n).evalEval = (Ψ n).evalEval`) — absent from mathlib;
  - the literature-standard / building-block form — **present**: `Affine.CoordinateRing.mk_ψ`
    (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`),
    `AdjoinRoot.evalEval_mk` (`Mathlib/Algebra/Polynomial/Bivariate.lean:391`),
    `AdjoinRoot.evalEval` (`Bivariate.lean:388`), `evalEval_C` (`Bivariate.lean:49`),
    `evalEval_pow` (`Bivariate.lean:142`), and `Equation ↔ polynomial.evalEval = 0`
    (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:150`).

Concluded: **not in mathlib** (all methods exhausted, including the building-block form). Mathlib
holds every primitive — the coordinate-ring congruence `mk_ψ`, the factorisation `AdjoinRoot.evalEval`
+ `evalEval_mk`, and the `Equation ↔ evalEval = 0` translation — but the *composed* eval bridge does
not exist anywhere in the mathlib tree. (Note: mathlib's `DivisionPolynomial/Basic.lean` is *forked*
into the project nearly verbatim; the fork adds nothing here, and the bridge is genuinely new
project content built on top of unmodified mathlib `Bivariate`/`Affine` API.)

---

## Call sites — `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`

Internal use count: 2  (within the project, excluding the declaring file)
External-to-file callers: 2 distinct files (the General* and PID* duplicated tracks)

| Caller file:line                                   | Usage pattern (one-line excerpt)                                  |
|----------------------------------------------------|-------------------------------------------------------------------|
| LutzNagellTheorem/GeneralIntegralMultiple.lean:51  | `rw [← evalEval_ψ_eq_evalEval_Ψ (curveQ W) hns.left n] at hΨSq`    |
| LutzNagellTheorem/PIDIntegralMultiple.lean:65      | `rw [← evalEval_ψ_eq_evalEval_Ψ (curveK R K W) hns.left n] at hΨSq`|

Also used once internally in the declaring file (EvalBridge.lean:70, inside `evalEval_ψ_odd`).

Inline-derivation grep: the sibling lemmas `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`,
and the parent `evalEval_eq_of_mk_eq` all follow the identical pattern in the same file and are
likewise used across both the General* and PID* tracks — confirming a real, reused mini-API, not
dead code. (The two call sites are the "same" proof duplicated across the project's General-field
and PID tracks.)

Signal reading: K = 2 external + 1 internal, no bypassing inline re-derivation → a genuine,
reused helper. Leans toward the bridge *family* being worth keeping; but this specific member is a
glue specialisation of its parent (see Phase 6).

---

## Composition check (Phase 6)

Can `evalEval_ψ_eq_evalEval_Ψ` be derived from mathlib in ≤3 chained calls?

Attempt 1 — direct, via the project's own parent + a mathlib congruence:
  `evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_ψ W n)`
  - This is *literally the proof in the file*. But `evalEval_eq_of_mk_eq` is **not** in mathlib — it
    is the file-local parent. So this is not a pure-mathlib composition.

Attempt 2 — inline the parent against pure mathlib (what a mathlib call site would write):
  ```lean
  example (heq : W.toAffine.Equation x y) (n : ℤ) :
      (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
    have hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq   -- mathlib
    exact hev (W.ψ n) ▸ hev (W.Ψ n) ▸ congrArg _ (Affine.CoordinateRing.mk_ψ W n)  -- mathlib mk_ψ
  ```
  - Mathlib decls used: `AdjoinRoot.evalEval_mk`, `Affine.CoordinateRing.mk_ψ` (+ `congrArg`,
    `▸`). Two named mathlib lemmas, rewritten twice. Result: **succeeds** as a ≤3-step composition.
  - Caveat: `heq : Equation x y` must be massaged to `polynomial.evalEval x y = 0` for the
    `AdjoinRoot.evalEval` hypothesis — definitionally equal (`Equation` is *defeq* to that), so no
    extra step is needed.

Conclusion: **COMPOSABLE** — the user's statement is a ≤3-call composition of two mathlib lemmas
(`AdjoinRoot.evalEval_mk`, `Affine.CoordinateRing.mk_ψ`). The project factors the common
`AdjoinRoot.evalEval_mk` step out as `evalEval_eq_of_mk_eq`; *given that parent*, this lemma is a
one-application glue specialisation.

---

## Verdict: `WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the object "ψ_n evaluated at a point" is classical and routine; the
  equality is the standard specialisation of the coordinate-ring relation at an on-curve point.
  Mathlib's own `DivisionPolynomial/Basic.lean` docstring (lines 79–81) names this exact step.
- Generality analysis (Phase 4): STRICTLY NARROWER (unused `Field`; ring-level proof) — so a YES
  bucket would in any case be YES-but-generalise-first, not YES-add-as-is.
- Mathlib search (Phase 5): not in mathlib; **all building blocks present** (`AdjoinRoot.evalEval_mk`,
  `Affine.CoordinateRing.mk_ψ`, `evalEval_C`, `Equation ↔ evalEval = 0`).
- Composition check (Phase 6): COMPOSABLE — ≤3 mathlib calls.

**Rationale:**

This theorem is a thin glue lemma: its entire proof is one application of the file-local parent
`evalEval_eq_of_mk_eq` to the mathlib congruence `Affine.CoordinateRing.mk_ψ`. Unfolding the parent,
it is a ≤3-call composition of exactly two named mathlib lemmas — `AdjoinRoot.evalEval_mk` and
`Affine.CoordinateRing.mk_ψ` — over the definitional unfolding `Equation x y ⟺ polynomial.evalEval x
y = 0`. Mathlib supplies every primitive; what is missing is only the act of composing them, which
is precisely the NO-composable-from-mathlib signature. The result is not "new mathematics": mathlib's
*own* division-polynomial module docstring already states the underlying fact ("evaluating these
polynomials at a rational point on W recovers their original definition … avoiding the need to work
in the coordinate ring") — this lemma is just that sentence, formalised, for the single ψ/Ψ pair.

The one genuinely reusable piece of the file is the **parent** `evalEval_eq_of_mk_eq` (the
`AdjoinRoot.evalEval`-factorisation that turns *any* `mk`-equality into an evaluation equality);
that abstraction is the part worth a separate mathlibable look and would be the natural thing to
upstream (ring-level) if anything in this file is. The ψ/Ψ specialisation assessed here rides on
top of it and, at a mathlib call site, would simply be inlined. Adding it standalone would not pay
its way: it bakes in an unused `Field` hypothesis and duplicates a two-lemma composition. Note this
is **not** a cost-driven downgrade — the composition is cheap; it is a genuine "mathlib already has
the pieces" verdict.

WHY not (refactor-actionable):
  Mathlib has the building blocks; the form is a 1–3 mathlib-call composition. The two mathlib
  building blocks are:
    - `AdjoinRoot.evalEval_mk`  (`Mathlib/Algebra/Polynomial/Bivariate.lean:391`)
    - `Affine.CoordinateRing.mk_ψ`  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:438`)
  Composition sketch (≤3 lines):
  ```lean
  -- with hev := AdjoinRoot.evalEval_mk (p := W.toAffine.polynomial) heq
  example (heq : W.toAffine.Equation x y) (n : ℤ) :
      (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
    (AdjoinRoot.evalEval_mk heq (W.ψ n)) ▸ (AdjoinRoot.evalEval_mk heq (W.Ψ n)) ▸
      congrArg _ (Affine.CoordinateRing.mk_ψ W n)
  ```
  Call sites in the project (from Phase 6.0): K = 2 external (+1 internal).
  Refactor plan (for an eventual mathlib upstreaming, NOT for the project itself — see caveat below):
    at each of the 2 external `rw [← evalEval_ψ_eq_evalEval_Ψ …]` sites, the same effect is obtained
    by rewriting with the parent `evalEval_eq_of_mk_eq … (mk_ψ …)` (or, fully inlined, the 3-line
    composition above). Argument flow is identical (`W`, `heq`/`hns.left`, `n`); only the lemma name
    changes.

**Project caveat (do not delete locally).** This verdict answers the mathlib question
("should *mathlib* carry this standalone?" → no, it is composable). It is **not** a recommendation
to delete the lemma from the NagellLutz project: within the project the `EvalBridge` family
(`evalEval_eq_of_mk_eq` + the ψ/Ψ/φ/ΨSq members) is a legitimate, reused local mini-API that keeps
the Nagell–Lutz integrality proofs readable, and it is exactly the kind of WIP helper AINTLIB
tolerates on a dev branch. The composable verdict means: if this were ever proposed *to mathlib*,
it would be inlined at call sites (or, better, only the parent `evalEval_eq_of_mk_eq` would be
upstreamed, ring-level, and the ψ-specialisation dropped).

---

## Next step

Do not propose `evalEval_ψ_eq_evalEval_Ψ` to mathlib as a standalone lemma — it is a ≤3-call
composition of `AdjoinRoot.evalEval_mk` and `Affine.CoordinateRing.mk_ψ`. If any part of
`EvalBridge.lean` is to be upstreamed, route a separate `/mathlibable` (and then `/generalise`) at
the **parent** `WeierstrassCurve.evalEval_eq_of_mk_eq` — the ring-level `mk`-to-`evalEval` transport
is the genuinely reusable abstraction; the ψ/Ψ specialisation then becomes a one-line corollary or
an inlined call. Keep the lemma in the project as-is in the meantime.
