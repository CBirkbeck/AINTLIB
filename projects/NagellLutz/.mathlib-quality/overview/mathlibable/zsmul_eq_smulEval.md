# /mathlibable report — `WeierstrassCurve.zsmul_eq_smulEval`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl elaborates per source.
- decl `WeierstrassCurve.zsmul_eq_smulEval`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:590`
- namespace nesting:        `namespace WeierstrassCurve` (line 76) … `end` (627); the theorem sits *outside* the
                            inner `Universal` namespace (which closes at 545) ⇒ qualified name is
                            **`WeierstrassCurve.zsmul_eq_smulEval`** (confirmed: parsed name is correct).
- kind:                     theorem
- has sorry:                no
- module docstring summary: "Integer multiples of a rational point on an elliptic curve in terms of division
                            polynomials" — this file *proves* `WeierstrassCurve.zsmul_eq_smulEval`, i.e.
                            `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates, for any integer `n`
                            and any nonsingular rational point `P` over a field. Copyright (c) 2024 **Junyan Xu**
                            (author of mathlib's division-polynomial files).

---

### Statement (Phase 1)

`zsmul_eq_smulEval` is the **general-field, Jacobian-coordinate multiplication-by-`n` formula** for a Weierstrass
curve.

Let `W` be a Weierstrass curve over a field `F`, and let `P = (x, y)` be a nonsingular affine rational point on
`W` (so `P ∈ W.Point` via `Point.fromAffine (Affine.Point.some _ _ h)`). For **every** integer `n`, the scalar
multiple `n • P` — taken in the elliptic-curve group `W.Point` — has, as its underlying Jacobian point class,
the explicit triple obtained by evaluating the division polynomials at `(x, y)`:

  `(n • P).point = ⟦ (φₙ(x,y), ωₙ(x,y), ψₙ(x,y)) ⟧`   in `PointClass F = (Fin 3 → F)/≈`,

where `ψₙ` is the `n`-th (bivariate) division polynomial, `φₙ = X·ψₙ² − ψₙ₊₁·ψₙ₋₁`, and `ωₙ` is the associated
`y`-numerator polynomial. Equivalently, this is the classical `[n]P = [φₙ·ψₙ : ωₙ : ψₙ³]` (projective) /
`(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) formula, packaged in Jacobian coordinates so that it holds for *all* `n` — including
the `n` for which `ψₙ(x,y) = 0` (i.e. `P` is `n`-torsion, where `n • P = O = ⟦(1,1,0)⟧` falls out automatically
because the third coordinate vanishes).

Variables / typeclasses (Lean side):
- `{F : Type*} [Field F]` — the base field.
- `(W : WeierstrassCurve F)` — the curve.
- `{x y : F}` — the affine coordinates of the point.
- `(n : ℤ)` — the multiplier.

Hypotheses (Lean side):
- `(h : Affine.Nonsingular W x y)` — `(x,y)` is a nonsingular point of `W` (so it gives a genuine group element).

Conclusion (math): `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates, for all `n ∈ ℤ`.
Conclusion (Lean):
`(n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧`
where `smulEval W x y n = evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]` (ZSMul.lean:551).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the named main result of the file (module docstring line 10–11 — "This file proves the formula
`WeierstrassCurve.zsmul_eq_smulEval`"), and it is a theorem of a classical, literature-standard fact — the
multiplication-by-`n` / division-polynomial coordinate formula (Silverman, *The Arithmetic of Elliptic Curves*,
Exercise III.3.7 & Cor III.6.4(b)). It is the *field-level Jacobian* member of the same family whose affine
sibling `Universal.Affine.zsmul_point_eq_smulX_smulY` was assessed BIG / YES-add-as-is in the prior overview.

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. Proof body is a ~35-line `Int.negInduction` reducing to
a strong even/odd induction in Jacobian coordinates (`dblXYZ_smulEval` for `2m`, `addXYZ_smulEval₁` for `2m+1`),
with the negative case handled by `smulRing_neg`. Definitely not a one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                       | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|-------------------------------------------|-------|
|  1 | WebSearch (specific form)        | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` Silverman                                                                 | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; **proj. `nP=[φₙψₙ : ωₙ : ψₙ³]`** | Multiple sources state exactly this; the *projective* form is explicitly the Jacobian-coordinate one this decl proves. |
|  2 | WebSearch (general / Jacobian)   | division polynomials Jacobian coordinates `[n]P` projective homogeneous                             | yes  | same; `ψₙ` zero ⇔ `[n]P = ∞`              | Confirms the coordinate form and that the `ψₙ=0 ⇔ n·P = O` case is intrinsic to it. |
|  3 | WebSearch (named-after / source) | Silverman *Arithmetic of Elliptic Curves* Exercise III.3.7 / Cor III.6.4(b)                          | yes  | `y(nP)=ωₙ/ψₙ³` (Silverman)                | The canonical textbook reference. |
|  4 | ChatGPT MCP                      | standard form + generality + Jacobian validity for all `n` + universal-curve route                  | n/a  | (MCP down — Codex exec failed, as briefed) | Attempted with gpt-5.4 high; tool errored. Covered by #1–#3, #6, #9, #10. |
|  5 | Local references                 | `.mathlib-quality/references/` for division polynomial / mult formula                                | n/a  | (no references dir; no `refs/NagellLutz/`)  | Both directories absent — recorded n/a. |
|  6 | nLab                             | elliptic curve / division polynomials                                                              | no   | —                                         | nLab's elliptic-curve page does not cover division polynomials / the mult formula. |
|  7 | nCatLab (categorical)            | n/a                                                                                                | n/a  | —                                         | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | division polynomial / multiplication-by-n                                                           | n/a  | —                                         | Stacks has no division-polynomial / coordinate-mult entry. |
|  9 | WebFetch Wikipedia               | "Division polynomials" — multiplication-by-n formula, generality                                    | yes  | `nP=(φₙ/ψₙ², ωₙ/ψₙ³)`, ω via ψ₂ₙ          | Verbatim: stated "over an **arbitrary field K**"; `ψₙ², ψ₂ₙ/y, φₙ ∈ K[x]`. |
| 10 | recent arXiv / lecture notes     | division polynomials `[n]P` coordinates (MIT 18.783 LN6; arXiv 1103.4560, 2102.07573, 2302.03650)   | yes  | same form; projective `nP=[φₙψₙ:ωₙ:ψₙ³]`  | MIT 18.783 Lecture 6 is the canonical modern reference; arXiv sources use the same coordinate form. |

Protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific affine form;
Jacobian/projective form; named-after Silverman). ChatGPT MCP attempted (down → n/a with reason). Local refs
checked (absent). nLab checked. Stacks / nCatLab recorded n/a with reason. Wikipedia + arXiv/MIT consulted.

### Literature summary (Phase 3)

Concept identified as: **the multiplication-by-`n` (division-polynomial / `[n]P`) coordinate formula** for
elliptic / Weierstrass curves — Silverman, *The Arithmetic of Elliptic Curves*, Exercise III.3.7 & Cor
III.6.4(b); MIT 18.783 Lecture Notes 6; Wikipedia "Division polynomials".
Sources agree on the standard form: **yes**. Affine: `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`, `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`.
**Projective / Jacobian: `[n]P = [φₙ·ψₙ : ωₙ : ψₙ³]`, i.e. Jacobian coordinates `(φₙ, ωₙ, ψₙ)`** — this is exactly
the form `zsmul_eq_smulEval` proves, and it is the standard way to state it when one wants validity for *all* `n`
(the affine rational-function form is only valid away from torsion; the projective/Jacobian form absorbs the
`ψₙ = 0` case as `[n]P = O`).
Most general standard form: the coordinate identity over **any field** (Wikipedia states it over an arbitrary `K`);
the deepest underlying statement is the *universal* one over `ℤ[A₁,…,A₆,X,Y]` (generic point), from which every
field case — including char 2, 3 — specializes. The user's decl is the **general-field** specialization of that
universal root (the universal/affine root being its sibling `zsmul_point_eq_smulX_smulY`).
Generality dimensions where the literature varies:
  - curve model: short Weierstrass `y²=x³+Ax+B` (Wikipedia/MIT, char ≠ 2,3) ↔ **general Weierstrass over any field**
    (this decl) ↔ universal curve over ℤ (the proof's engine). The decl is at the general-Weierstrass-over-any-field
    end — strictly more general than the short-Weierstrass textbook statement.
  - coordinates: affine rational functions (textbook) ↔ **Jacobian/projective** (this decl). The Jacobian form is
    the more robust one (valid for all `n`).
Disagreement with the literature: none. The Lean form is the canonical projective/Jacobian form, generalized to an
arbitrary base field and arbitrary general Weierstrass curve.

---

### Generality analysis — `zsmul_eq_smulEval`

Literature-standard form (from Phase 3): `[n]P = [φₙψₙ : ωₙ : ψₙ³]` (Jacobian), `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`; stated over
an arbitrary field; valid for all `n`.

| # | Parameter / hypothesis        | Current Lean form                          | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | base field `[Field F]`        | arbitrary field `F`                        | arbitrary field `K`                        | partially — see note | The group law `W.Point` is set up over a field in mathlib; the *universal/generic-point* engine that proves this (its sibling) lives over `ℤ[A₁,…,A₆,X,Y]` and is the maximally-general root. This **field** statement is the intended consumer-facing specialization; it already matches the literature's "over an arbitrary field" exactly. The universal root is a *separate* (already-present) declaration, not a weakening of this one. |
| 2 | curve `WeierstrassCurve F`    | general Weierstrass curve                  | general Weierstrass (or short over char≠2,3) | NO (already general) | This is the *general* Weierstrass curve — strictly more general than the short-Weierstrass textbook form. Cannot be weakened further. |
| 3 | `Affine.Nonsingular W x y`    | nonsingular affine point                   | a point `P` on the curve                   | NO                  | Needed for `(x,y)` to define a group element of `W.Point`; this is the standard hypothesis. |
| 4 | multiplier `n : ℤ`            | all integers `n`                           | all `n` (incl. torsion via `ψₙ=0 ⇒ O`)     | NO (already maximal) | The Jacobian form is chosen *precisely* to hold for every `n` with no `ψₙ ≠ 0` side condition — strictly stronger than the affine form. No weakening; this is the maximal range. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (general Weierstrass curve over an arbitrary field; Jacobian
coordinates so it holds for *all* `n`, including torsion `n`; the only "more general" statement is the *universal*
generic-point root over `ℤ[Aᵢ,X,Y]`, which is a *separate, already-existing* declaration — `zsmul_point_eq_smulField`
/ `zsmul_point_eq_smulX_smulY` — from which this field statement is specialized, not a weakening of it).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | no  | Already uses `WeierstrassCurve`/`Field` instances; the curve/point are values, the natural form. | — |
| 2 | sequences/metric → filters/topology? | no  | Purely algebraic identity in a field; no limits or topology. | — |
| 3 | construct → universal-property class? | no  | The proof *already* routes through the universal curve / generic point over `ℤ[Aᵢ]` (mathlib's idiomatic device) and specializes via `ringEval`. This field statement is the intended specialization. | — |
| 4 | set+closure → bundled substructure? | no  | n/a. | — |
| 5 | field/metric-specific → weaken typeclass? | no  | The `W.Point` group law is field-based in mathlib; the *ring/universal* generality is captured by the separate generic-point root. This is the right consumer-facing field form. | — |
| 6 | 1-categorical → higher-categorical? | no  | n/a. | — |
| 7 | concrete index → general algebraic? | no  | Index is `ℤ` (the multiplier of a group element) — intrinsic; the literature formula is itself indexed by `n ∈ ℤ`. | — |
| 8 | concrete-via-abstract (proof betrays a more general form)? | no  | The proof *uses* the nonsingular point and the curve essentially (specializes the universal identity to this exact `(x,y)`); the named objects do not vanish from the proof. The abstract engine it specializes from is already its own declaration. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This already *is* the contemporary mathlib idiom: it is built on mathlib's
EDS-based division-polynomial design and proved via the universal-curve / generic-point technique (the modern way
to reach char-2 fields), then specialized to the consumer-facing "general Weierstrass curve over a field" form.
Indeed the whole development *extends* mathlib's own division-polynomial files (same author, Junyan Xu), supplying
the `ωₙ` family that mathlib still lists as a TODO.

---

### Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `zsmul_eq_smulEval`

[A] Lean-Finder       (index tool not loaded in this env)                              n/a — tool unavailable
[B] Loogle            (index tool not loaded in this env)                              n/a — tool unavailable
[C] LeanSearch        (index tool not loaded in this env)                              n/a — tool unavailable
[D] Grep mathlib src  `smulEval / smulRing / smulField / zsmul_eq_smulEval` over `.lake/.../Mathlib/`  → **no hits**
                      `nsmul/zsmul` lemmas in EC `Affine/Point.lean` + `Jacobian/Point.lean` → only the abstract
                      group recursion `nsmulBinRec` / `zsmulRec` (def of `n • P` by repeated addition) and `smul`
                      lemmas about **representative rescaling** `u • P` with `[IsUnit u]` (projective-equivalence
                      plumbing: `neg_smul`, `add_smul_of_equiv`, `toAffine_smul`, …) and the `CoordinateRing`
                      module action — **none** relate the *group-law* `n • P` to division-polynomial coordinates.
                      `def ω / def omega / WeierstrassCurve.ω` in `Mathlib/.../AlgebraicGeometry/` → **no hits**
                      (mathlib lacks `ωₙ` entirely; `DivisionPolynomial/Basic.lean:71` reads
                      "TODO: the bivariate polynomials `ωₙ`").
[E] Name pattern      grep `zsmul_eq_smulEval` across mathlib → **no hits** (it appears only in this monorepo, and
                      is *duplicated* in HasseWeil at `Auxiliary/DivisionPolynomial.lean:667`).

Searched for both:
  - user's current form (general-field Jacobian `(n • P).point = ⟦(φₙ,ωₙ,ψₙ)(x,y)⟧`): not in mathlib.
  - literature-standard / projective form (`[n]P = [φₙψₙ : ωₙ : ψₙ³]`, any field): not in mathlib — mathlib's EC
    `Point` `nsmul`/`zsmul` are defined by abstract recursion with **no** coordinate formula, and the `ωₙ`
    polynomial the middle/`y`-coordinate needs is itself absent (an open TODO).

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard general/projective
form, plus the prerequisite `ωₙ`). Mathlib has the *inputs* (`ψₙ`, `φₙ`, the EDS machinery, the Jacobian `Point`
group law) but neither `ωₙ` nor any multiplication-by-`n` coordinate theorem.

---

### Call sites — `zsmul_eq_smulEval`

Internal use count (this monorepo, excluding the declaring lines in `ZSMul.lean`): **~15 usages across 9 files in
TWO projects** — this is the heavily-used central node of the whole division-polynomial-multiplication apparatus
(notably *more* used than its affine sibling `zsmul_point_eq_smulX_smulY`).

| Caller file:line                                                            | Usage pattern (one-line excerpt) |
|-----------------------------------------------------------------------------|-----------------------------------|
| NagellLutz/.../LutzNagellTheorem/PIDIntegralMultiple.lean:50                | `have hsmul := zsmul_eq_smulEval (curveK R K W) hns n` |
| NagellLutz/.../LutzNagellTheorem/PIDPrimeOrder.lean:67                      | `have heval := zsmul_eq_smulEval (curveK R K W) hns n` |
| HasseWeil/.../MulByIntPullback.lean:271, :289                               | `rw [← zsmul_eq_smulEval (W_KE W) hns n]` (the file's stated method) |
| HasseWeil/.../EC/MulByIntUnramified.lean:73, :287                           | `have h1 := WeierstrassCurve.zsmul_eq_smulEval (W := W) h_ns n` ("converse-reading: affine image ⇒ Z = ψₙ ≠ 0") |
| HasseWeil/.../EC/GenericPointZsmul.lean:415, :498, :587                     | `have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W_KE W) …` |
| HasseWeil/.../EC/MulByIntSamePlace.lean:90                                  | `have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W) hPns ℓ` |
| HasseWeil/.../EC/IsogenyAG/CovarianceDischarge.lean:131                     | `have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := V) h_ns m` |
| HasseWeil/.../WeilPairing/TorsionKernelRational.lean:55                     | `have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := V) h_ns m` |
| HasseWeil/.../Auxiliary/DivisionPolynomial.lean:667 (**verbatim duplicate**), :794 (own consumer) | `theorem zsmul_eq_smulEval … := …` — an *entire re-fork* of the statement + proof |

Inline-derivation grep: HasseWeil's `Auxiliary/DivisionPolynomial.lean` (which describes itself as a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`) re-proves `zsmul_eq_smulEval` from scratch
(line 667) — i.e. the equivalent was re-derived in a second project because it is not upstream. That is the
textbook cross-project-duplication signal.

Signal reading: **K ≫ 3 internal uses across two independent NT developments, plus a verbatim cross-project
duplicate.** This is real, load-bearing public API — the strongest possible "consumers depend on it" signal — and
the duplication is exactly the redundancy mathlib inclusion eliminates. Not dead code; not a wrapper consumers
bypass.

---

### Composition check (Phase 6)

Can `zsmul_eq_smulEval` be derived from mathlib in ≤3 chained calls?

Attempt 1: is there a mathlib lemma giving the Jacobian coordinates of `n • P`?
  - Mathlib decls available: `WeierstrassCurve.Jacobian.Point` group structure with `zsmul := zsmulRec` (abstract
    recursion); division polynomials `ψ`, `φ` (but **no** `ω`); `addMap_eq` / `negMap_eq` (the group law on
    `PointClass`).
  - Result: **fails** — mathlib has no lemma relating the group-law `n • P` to division-polynomial coordinates,
    and the very polynomial `ωₙ` the formula's middle coordinate needs is absent (open TODO).

Attempt 2: build it inline from the EDS + doubling/addition formulas?
  - That is exactly the ~35-line proof in this file: `Int.negInduction` → strong even/odd induction, dispatching
    `2m` via `dblXYZ_smulEval` and `2m+1` via `addXYZ_smulEval₁`, which themselves reduce (through
    `ringEval_comp_smulRing`, the universal ring/field, `dblXYZ_smulRing`/`addXYZ_smulRing`) to polynomial
    identities on the *universal* curve — a multi-file apparatus (`Universal.lean`, `DivisionPolynomialOmega.lean`),
    most of which is not in mathlib. This is a genuine theorem, not a 1–3-call composition.

Conclusion: **NOT-COMPOSABLE**. Deriving this requires the whole universal-curve + EDS + `ωₙ` + addition/doubling
apparatus, the bulk of which mathlib does not yet have.

---

## Verdict: `WeierstrassCurve.zsmul_eq_smulEval`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the canonical multiplication-by-`n` formula; its **projective/Jacobian** form
  `[n]P = [φₙψₙ : ωₙ : ψₙ³]` is standard (Silverman III.3.7 / III.6.4(b); MIT 18.783 LN6; Wikipedia "Division
  polynomials", stated over an arbitrary field) and is precisely what this decl proves. Standard, named, undisputed.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — general Weierstrass curve over an arbitrary field, Jacobian
  coordinates valid for *all* `n` (incl. torsion). The only "more general" object is the universal generic-point
  root, which is a *separate already-existing* declaration this one specializes from. No modern-idiom move (it is
  already the modern, char-2-capable formulation).
- Mathlib search (Phase 5): NOT in mathlib, in any form. Mathlib's EC `Point` `zsmul` is abstract recursion with no
  coordinate formula; the prerequisite `ωₙ` is an explicit open mathlib TODO.
- Composition check (Phase 6): NOT-COMPOSABLE — needs the universal-curve + EDS + `ωₙ` + addition/doubling apparatus.

**Rationale:**

`zsmul_eq_smulEval` is the **field-level, Jacobian-coordinate** statement of a classical, named theorem — the
multiplication-by-`n` / division-polynomial coordinate formula for elliptic curves (Silverman, *The Arithmetic of
Elliptic Curves*, Exercise III.3.7 & Cor III.6.4(b)) — in its maximally general form (any field, any general
Weierstrass curve, *all* integers `n`), and mathlib does not have it in any form. Mathlib's elliptic-curve `Point`
defines `nsmul`/`zsmul` purely by abstract group-law recursion (`nsmulBinRec` / `zsmulRec`); the only `smul` lemmas
present are about representative rescaling `u • P` (projective-equivalence plumbing) and the coordinate-ring module
action — none connect the group multiple `n • P` to division-polynomial coordinates. Moreover, the polynomial the
formula's coordinate needs, `ωₙ`, is an explicit open TODO in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71`, and the file `DivisionPolynomialOmega.lean`
in this very project exists to fill exactly that gap ("This file extends the division polynomial development from
mathlib with the `ω` family"). The whole `Universal.lean` / `ZSMul.lean` development is Copyright (c) 2024 **Junyan
Xu** — the author of mathlib's own division-polynomial files — and reads as a mathlib-bound contribution that simply
has not landed yet.

The decisive composability signal is the **call-site pattern**: `zsmul_eq_smulEval` is used ~15 times across 9 files
in *two* independent number-theory developments (NagellLutz's PID/General Lutz–Nagell tracks and the entire HasseWeil
mul-by-`n` / Weil-pairing apparatus), and HasseWeil contains a **verbatim re-fork** of the theorem at
`Auxiliary/DivisionPolynomial.lean:667`. Two projects each had to re-derive the same machinery — precisely the
redundancy mathlib inclusion removes. This is the heavily-used central node of the family (more so than its affine
sibling `Universal.Affine.zsmul_point_eq_smulX_smulY`, which the prior overview already assessed YES-add-as-is); the
present decl is the *consumer-facing* Jacobian form and should ship together with it. It is sorry-free, maximally
general, and at the right level of abstraction, and the Jacobian-coordinate packaging (valid for all `n`, with the
`ψₙ=0` torsion case absorbed as `O`) is the robust, modern statement — strictly stronger than the affine
rational-function form. This is a clean YES-add-as-is.

WHY add it (refactor-actionable):
- **New content mathlib is missing:** the multiplication-by-`n` coordinate formula for elliptic curves. There is
  literally no `n • P = (…)` division-polynomial statement anywhere in
  `Mathlib/AlgebraicGeometry/EllipticCurve/` — mathlib's `Point` group law has no explicit coordinate description of
  `n • P` at all. This is the canonical such statement.
- **The named gap:** it directly advances `DivisionPolynomial/Basic.lean:71` ("TODO: the bivariate polynomials
  `ωₙ`") and the implementation-notes TODO at line 83 — the formula's `ωₙ`-coordinate is the canonical *reason* to
  define `ωₙ` in the first place; and it adds the multiplication theorem that the existing `ψ`/`φ`/`Ψ`/`Φ`
  machinery was built to support but which mathlib never stated.
- **Composition with mathlib API:** once added, mathlib's `EllipticCurve.Point` / `Jacobian.Point` group law gains
  an explicit coordinate description of `n • P`, unlocking division-polynomial-based torsion / reduction / isogeny /
  Weil-pairing arguments (Nagell–Lutz, Hasse–Weil) that currently each re-fork the apparatus — both projects in this
  monorepo would then `import` the upstream and delete their copies.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Multiplication.lean` (a new
file in the existing `DivisionPolynomial/` directory), built on `DivisionPolynomial/Basic.lean` once `ωₙ` lands
there, plus a new home for the universal generic-point machinery.

Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): multiplication-by-n formula via division polynomials`

PR grouping (REQUIRED — this decl is not a standalone PR): ship as one coherent series with the rest of the
Junyan-Xu universal-curve development it belongs with —
  - the `ωₙ` family + `ψc` + `invar` (`DivisionPolynomialOmega.lean`) — fills the mathlib `ωₙ` TODO (prerequisite);
  - the universal curve / generic-point machinery (`Universal.lean`);
  - the universal/affine root `Universal.Affine.zsmul_point_eq_smulX_smulY` (+ `zsmul_point_eq_smulField`,
    `nonsingular_smulX_smulY`, `zsmul_point_ne_zero`, `zsmul_point_ne`);
  - **this** field-level Jacobian corollary `WeierstrassCurve.zsmul_eq_smulEval`, the consumer-facing node.
Because the same `zsmul_eq_smulEval` is duplicated in HasseWeil, the upstream must be a **shared** mathlib home that
both projects then import and delete their forks of.

Pre-PR checklist before opening:
- [ ] First land `ωₙ` in `DivisionPolynomial/Basic.lean` (closes its own TODO) — hard prerequisite.
- [ ] De-duplicate: reconcile the NagellLutz `ZSMul.lean:590` and HasseWeil `Auxiliary/DivisionPolynomial.lean:667`
      copies into the single upstreamed version; repoint all ~15 call sites at it.
- [ ] `/generalise WeierstrassCurve.zsmul_eq_smulEval` — confirm no further weakening (expected: none; the universal
      root is already separate).
- [ ] `/cleanup projects/NagellLutz/LutzNagell/ZSMul.lean WeierstrassCurve.zsmul_eq_smulEval` — full audit before PR.
- [ ] Coordinate with Junyan Xu (original author / mathlib division-polynomial maintainer) and pick a reviewer from
      recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits.

---

## Next step

Land the development as a grouped mathlib PR series (prereq: upstream `ωₙ` to close the existing
`DivisionPolynomial/Basic.lean:71` TODO; then the universal-curve machinery; then the multiplication formula in
both its universal/affine form `zsmul_point_eq_smulX_smulY` and this field-level Jacobian form
`zsmul_eq_smulEval`). De-duplicate the NagellLutz and HasseWeil copies of `zsmul_eq_smulEval` into the single
upstream home and repoint its ~15 call sites. Run `/generalise` then `/cleanup` on the decl, and coordinate with
Junyan Xu as author/reviewer.
