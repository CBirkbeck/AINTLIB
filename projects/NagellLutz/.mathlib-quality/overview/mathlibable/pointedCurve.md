# /mathlibable report — `WeierstrassCurve.Universal.pointedCurve`

> Step-9 mathlibable assessment (NagellLutz project). Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:130`.

---

## Baseline (Phase 0)

- lake build:                stale (per task brief; reasoned from source statement — instructed fallback)
- decl `WeierstrassCurve.Universal.pointedCurve`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:130`
- kind:                      `abbrev`  (a reducible alias for a `baseChange`)
- has sorry:                 no
- module docstring summary:  Defines the universal Weierstrass curve over `ℤ[A₁,…,A₆]`, the universal
  *pointed* elliptic curve over the fraction field of its coordinate ring, the specialization
  homomorphism `W.specialize`, and the cusp curve `Y²=X³` used to prove `ψₙ(1,1)=n`.

**Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.pointedCurve`
(namespace stack: `WeierstrassCurve` → `Universal`; base name `pointedCurve`, line 130). The
parse-time guess `WeierstrassCurve.Universal.pointedCurve` is **correct**.

**Exact statement (source, lines 128–135):**
```lean
/-- The universal pointed Weierstrass curve is an elliptic curve
when base-changed to the universal field. -/
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

instance : pointedCurve.IsElliptic where
  isUnit := by
    rw [show pointedCurve.Δ = _ from map_Δ curve (algebraMap _ Universal.Field)]
    exact ((map_ne_zero_iff _ algebraMap_field_injective).mpr Δ_curve_ne_zero).isUnit
```
where `curve : Affine (MvPolynomial Coeff ℤ)` is the universal Weierstrass curve (line 84),
`Universal.Field := FractionRing Universal.Ring` (line 99), `Universal.Ring := curve.CoordinateRing`
(line 96), and `baseChange`/`IsElliptic`/`map_Δ` are mathlib's
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236, 363, 273`).

Note the companion `curveField := curve.baseChange Universal.Field` (line 173) with
`curveField_eq : curveField = pointedCurve := rfl` (line 175): `pointedCurve` is *literally*
`curve.baseChange Universal.Field`; the alias exists to give the base-changed-to-field curve a
short, semantically-loaded name (and to be the curve on which the `IsElliptic` instance is
registered).

---

## Statement (Phase 1)

`WeierstrassCurve.Universal.pointedCurve` is a **definition** (a reducible `abbrev`). It is the
*universal/generic Weierstrass curve* `curve` (over `ℤ[A₁,…,A₆]`) **base-changed to the universal
field** `Universal.Field = Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`, where `P = Y² + A₁XY + A₃Y − X³ − A₂X² −
A₄X − A₆` is the Weierstrass polynomial. Concretely it is the elliptic curve
`y² + A₁xy + A₃y = x³ + A₂x² + A₄x + A₆` over the field `Universal.Field`.

Two things make `pointedCurve` more than a bare base change:

1. **It lands over a *field*** (the fraction field of the universal coordinate ring). Over that
   field the discriminant `Δ` is a unit (proved by the accompanying `instance : pointedCurve.IsElliptic`),
   so `pointedCurve` is a genuine *elliptic* curve — whereas the unspecialized `curve` over
   `ℤ[A₁,…,A₆]` is only a Weierstrass curve (its `Δ` is a non-unit polynomial). This is exactly
   where division by division polynomials (which need a field) becomes legal.
2. **It carries the distinguished "generic point" `(X, Y)`** — the *pointed* in the name. The
   companion `Affine.point` (line 151) is the point with coordinates `(polyToField (C X),
   polyToField Y)` on `pointedCurve`, which the file proves has **infinite order** (via the
   cusp-curve specialization `ψₙ(1,1)=n`). `pointedCurve` is the curve that point lives on.

Mathematically, `pointedCurve` is the **generic fibre of the universal Weierstrass family** — the
elliptic curve over the function field `ℚ̄(a₁,…,a₆)`-analog `Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)` that
underlies Silverman-style specialization arguments: prove an identity about division polynomials
on `pointedCurve` (over the field, with the generic point of infinite order), then specialize the
coefficients to any concrete curve.

Variables / typeclasses involved (Lean side):
- none generic — it is a closed `abbrev` over the concrete `Universal.Field`. It implicitly uses
  the `Algebra (MvPolynomial Coeff ℤ) Universal.Field` instance that `baseChange` requires
  (provided by the `FractionRing`/`AdjoinRoot` tower).

Hypotheses (Lean side): none — it is a definition.

Conclusion (math): the universal/generic pointed elliptic curve over the universal field.
Conclusion (Lean): `WeierstrassCurve Universal.Field`.

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it names a *mathematical object of independent standing* — the generic fibre of the
universal Weierstrass family / the universal elliptic curve over the universal field — which is
the carrier of the entire division-polynomial-and-elliptic-divisibility-sequence development in
this project (and in HasseWeil). It is not a helper lemma; it is the object every later result is
stated over. (Caveat: as a `def`/`abbrev` it is *derived* from the BIG `curve` by a single
mathlib `baseChange` — so its independent-standing is largely inherited from `curve`. This tension
is what drives the verdict below.)

(Literature width is EXHAUSTIVE regardless; BIG is recorded for framing.)

## One-line check (Phase 2b)

Body line count: **1 substantive line** (`baseChange curve Universal.Field`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | **no** (anti-signal) | It is an `abbrev` — explicitly **reducible**. It is *not* sealed; `curveField_eq : curveField = pointedCurve := rfl` shows it unfolds definitionally to `curve.baseChange Universal.Field`. So the def does **not** serve as a defeq barrier — the opposite: it is deliberately transparent so `pointedCurve.toAffine.negY/…` reduce to the base-changed-curve operations. |
| Avoid typeclass diamonds          | **partial / yes** | `pointedCurve` is the **anchor for the `IsElliptic` instance** (line 132). Registering `instance : pointedCurve.IsElliptic` on the *named* `pointedCurve` (rather than on the raw `curve.baseChange Universal.Field`) gives typeclass search a single canonical target; downstream `[pointedCurve.IsElliptic]`-requiring lemmas resolve against it. This is a genuine "named anchor for instance resolution" reason. |
| Mark semantic intent / API name   | **yes** | `pointedCurve` is the stable name used at **32 call sites** across NagellLutz `ZSMul.lean` and HasseWeil `DivisionPolynomial.lean`/`Universal.lean` (all `pointedCurve.toAffine.{negY,slope,addX,addY}`, `pointedCurve_a₁..a₆`). The `pointedCurve_aᵢ` simp lemmas (lines 160–164) are an API surface keyed to this name. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API name + instance anchor). But note
the *defeq* exemption is an **anti-signal** (it is reducible by design), which matters for Phase 7:
the case for shipping it as a *separate mathlib def* (vs. inlining `curve.baseChange K` + a
`pointedCurve.IsElliptic` instance) is weaker than for the parent `curve`, precisely because it is
a transparent one-line base change.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                 | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | universal elliptic curve over field of fractions of universal ring; generic point                     | yes  | "base change `E` to `Frac(R_univ) = K`; obtains an elliptic curve over a field where scalars/functions are defined" | Quadratic-twist / local-data papers (Springer RNT, arXiv:2501.03209) describe **exactly** this: the universal Weierstrass curve with a point of order `d` over a ring where `d` is invertible, base-changed to its fraction field `K_d`. |
|  2 | WebSearch (general / functorial) | generic fibre of universal Weierstrass family; elliptic curve over `ℚ(a₁,…,a₆)`; Silverman specialization | yes  | the **generic curve over the function field**; Silverman [Sil83]: a section `Pₜ` has infinite order for all but finitely many specializations `t` | KU Leuven ACAGM notes (PART I: Elliptic Curves); Silverman, *Heights and the specialization map for families of abelian varieties* (J. reine angew. Math. 342, 1983). The generic-fibre-over-the-function-field object is standard. |
|  3 | WebSearch (named-after / aliases)| Silverman generic elliptic curve `Q(a1..a6)` division polynomials point infinite order specialization | yes  | division polynomial `ψₘ ∈ ℤ[A,B,x]`; "from Silverman [Sil83], `Pₜ` has infinite order for all but finitely many `t`"; specialize the generic curve's `ψₘ` | arXiv:0811.3109 (Specializations of elliptic surfaces), arXiv:1108.3051, arXiv:1303.5002 — the generic-curve / specialization picture is the textbook frame for division-polynomial nonvanishing. |
|  4 | ChatGPT MCP                      | standard name + canonical base field + relation to `baseChange` of the universal curve                | n/a  | MCP server **down** (Codex exec failed) — task brief warned of this | Substituted by channels 1–3, 6, 9, 10, which converge: `pointedCurve` = generic fibre = `baseChange(universal curve, Frac(coordinate ring))`. |
|  5 | Local references                 | `grep .mathlib-quality/references/`                                                                    | n/a  | directory absent for NagellLutz                                  | recorded n/a (no refs dir). |
|  6 | nLab                             | universal elliptic curve / moduli stack of elliptic curves / generic fibre                            | yes  | the universal elliptic curve `E → M_ell`; its fibre over the generic point is the curve over the function field of `M_ell` | `ncatlab.org/nlab/show/universal+elliptic+curve`, `…/moduli+stack+of+elliptic+curves`; `pointedCurve` is the affine-Weierstrass incarnation of the generic fibre. |
|  7 | nCatLab (categorical framing)    | generic fibre of the Weierstrass family; pullback of universal curve to `Spec K`                       | yes  | base change of the universal family along `Spec(function field) → moduli` | same nLab cluster — categorically a pullback (base change), which is *exactly* `baseChange curve K`. |
|  8 | Stacks Project (alg geom)        | generic fibre; base change of a family to the fraction field of the base                              | yes (indirect) | base change of a scheme/curve along `Spec Frac(A) → Spec A` is the generic fibre | Stacks: base-change / generic-point machinery is standard; `pointedCurve` is the EC-specific instance. Not a *named* Stacks tag, hence "indirect". |
|  9 | MathOverflow / Math.SE           | elliptic curve over `Q(a,b)`/`Q(a₁..a₆)` generic; rank of generic curve; specialization               | yes  | consensus: the generic curve over the rational function field is the canonical object for "true for almost all specializations" arguments (Silverman specialization theorem) | No disagreement on the construction; it is base change of the universal curve to the function field. |
| 10 | recent arXiv (≤5 yr)             | universal Weierstrass curve with point of order `d` over `K_d`; homogeneous division polynomials over the universal field | yes  | "the curve base changed to … the universal Weierstrass elliptic curve with a point of order `d` over `K_d = Frac(R_d)`"; `ψₙ` are universal polys over the generic curve | arXiv:2501.03209 + the homogeneous-division-polynomial literature (arXiv:1303.4327, arXiv:1108.3051) — *precisely* this project's construction and use case. |

### Literature summary (Phase 3)

Concept identified as: **the universal/generic (pointed) elliptic curve over the universal field**
— equivalently the **generic fibre of the universal Weierstrass family**, i.e. the base change of
the universal Weierstrass curve to the fraction field of its (coordinate) ring.
Sources agree on the standard form: **yes** — it is `baseChange(universal Weierstrass curve, K)`
where `K` is the fraction field of the universal base ring; over `K` the discriminant is a unit so
it is an elliptic curve, and it carries the generic point `(X,Y)` of infinite order. This is the
object Silverman's specialization theorem is stated relative to.
Most general standard form: as stated — universal curve over `ℤ[A₁,…,A₆]` (all five coefficients,
base `ℤ`), base-changed to `Frac` of its coordinate ring (so the generic point is included). The
project's `pointedCurve` matches this exactly.
Generality dimensions where the literature varies:
  - **Which field**: `Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)` (coordinate-ring fraction field, *includes* the
    generic point — this project) vs. just `Frac(ℤ[A₁,…,A₆]) = ℚ(a₁,…,a₆)` (no marked point). The
    project's choice (the coordinate-ring fraction field) is the **richer/pointed** one and is the
    correct base for division-polynomial arguments that evaluate at the generic point.
  - **Packaging**: bare base-changed curve + separate marked point (`Affine.point`) vs. a bundled
    "pointed curve" structure. The literature uses both; mathlib has no `PointedWeierstrassCurve`
    type, so the project keeps curve and point separate.
Disagreement with the literature: **none.** `pointedCurve` is the standard generic-fibre object,
realized as `baseChange(universal curve, universal field)` at full generality.

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): base change of the universal Weierstrass curve (over
`ℤ[A₁,…,A₆]`, all five coeffs) to the fraction field of its coordinate ring; the generic fibre /
universal elliptic curve over the universal field.

| # | Parameter / hypothesis        | Current Lean form                                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | base curve                    | `curve` (universal, over `ℤ[A₁,…,A₆]`, 5 coeffs) | the universal Weierstrass curve  | NO                  | already maximally general (inherited from `curve` — base `ℤ`, all five `aᵢ`; see `curve.md` Phase 4). |
| 2 | target field                  | `Universal.Field = Frac(curve.CoordinateRing)`   | `Frac` of the (coordinate) base ring | NO              | this is the canonical field that *includes the generic point*; using `Frac(ℤ[A₁..A₆])` (no point) would be strictly *less* rich. |
| 3 | construction                  | `baseChange curve Universal.Field` (mathlib `baseChange`) | pullback of the universal family to `Spec K` | n/a       | `baseChange` is precisely the categorical base change / generic fibre; no weakening possible — it *is* the right operation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (inherited from `curve`; `baseChange` to the
coordinate-ring fraction field is the canonical generic-fibre construction).
Number of weakening opportunities found: 0.
Proposed restatement: none (already maximal).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | partial — and **already done** | The fact that `pointedCurve` is elliptic is internalised as an **`instance : pointedCurve.IsElliptic`** (line 132), not as a bundled hypothesis. That is already the modern idiom. | `[pointedCurve.IsElliptic]`-requiring API (e.g. the whole `EllipticCurve`/`Δ`-unit toolbox) applies to it by instance resolution. |
|  2 | sequences/metric → filters/topological?                                                               | no       | purely algebraic. | — |
|  3 | **construct** an object where a **universal-property class** would characterise it?                   | no — it is itself a base change of the representing object `curve`; the universal property lives on `curve` (`specialize`/`map_specialize`), and `pointedCurve` inherits it via `map_baseChange`. | A `PointedWeierstrassCurve`/`EllipticCurve.generic` *class* would add nothing over `baseChange curve K` + the `IsElliptic` instance. | — |
|  4 | set-with-closure-predicate → bundled-substructure type?                                               | no       | n/a. | — |
|  5 | field-specific → weaker typeclass?                                                                    | **no — and deliberately so**: it is *meant* to be over a **field** (the fraction field), because that is exactly where `Δ` becomes a unit (`IsElliptic`) and division by division polynomials is legal. Weakening the field would defeat the purpose. | n/a — the field is load-bearing. | — |
|  6 | 1-categorical → higher/∞-categorical (moduli **stack** / universal curve `E → M_ell`)?               | yes, but **rejected as a modernisation** | One could phrase this as the pullback of the universal elliptic curve `E → M̄_ell` to the generic point. | Requires algebraic-stacks infrastructure mathlib lacks; `pointedCurve` remains the affine-Weierstrass generic fibre underneath it. Not a generalise-first target. |
|  7 | concrete index → arbitrary additive group/monoid?                                                    | no       | nothing indexed to generalise. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the one modern move — encoding "is elliptic" as a typeclass — is
*already present* as `instance : pointedCurve.IsElliptic`). No further Bourbaki-2.0 improvement; a
bundled "pointed/generic curve class" would not compose better than `baseChange curve K` + the
instance. The moduli-stack reformulation is a heavier different object, not a restatement.

---

## Diamond / defeq risk (Phase 4.5) — `abbrev` (reducible def)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | low     | `pointedCurve` is a `WeierstrassCurve` *term* (data), not an instance. The associated `instance : pointedCurve.IsElliptic` could in principle collide with mathlib's generic `instance : (W.map f).IsElliptic` (Weierstrass.lean:448) since `pointedCurve` reduces to `curve.map (algebraMap …)`; but `IsElliptic` is a `Prop`-class (proof-irrelevant), so two instances cannot produce an inconsistent diamond — at worst a redundant-instance warning. Worth checking on upstreaming. |
| 2 | Reducibility leak            | **low–moderate** | It is an **`abbrev`** → `@[reducible]`. Its body `curve.baseChange Universal.Field` (= `curve.map (algebraMap …)`) is exposed to defeq-checking everywhere `pointedCurve` appears. The body is cheap (a record of five `algebraMap` applications), so the leak is mild, but the *general pattern* "name a base change as a reducible `abbrev`" is the kind of thing a mathlib reviewer flags: a sealed `def` + explicit `@[simp]` unfolding lemmas (which the file *already has* as `pointedCurve_aᵢ`, lines 160–164) is often preferred. This is the main infra reason `pointedCurve` differs from the sealed `def curve`. |
| 3 | Non-canonical unfolding      | low     | The `pointedCurve_aᵢ` lemmas (lines 160–164) are the canonical `@[simp]` interface; they are stated `:= rfl`, consistent with the `abbrev`. No surprising global unfolds beyond what reducibility already permits. |
| 4 | Instance priority collision  | low     | The `pointedCurve.IsElliptic` instance has no explicit priority. Because `pointedCurve` defeq-reduces to `curve.map (algebraMap …)`, mathlib's `instance : (W.map f).IsElliptic` (Weierstrass.lean:448, which itself needs `[W.IsElliptic]` — *absent* for `curve`, whose `Δ` is a non-unit) does **not** actually fire here; the project's explicit instance (proving `Δ ≠ 0 ⇒ unit` over the field) is the one that applies. Low risk, but on upstreaming the interaction with `map`/`baseChange` `IsElliptic` instances must be checked. |
| 5 | Universe-polymorphism issues | none    | base type is the concrete `Universal.Field : Type`; no universe variables. |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`; accessed by field projection / `.toAffine`. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (no HIGH rows).
Top risks: the **reducibility leak** (row 2) — `abbrev` exposes the base-change body to defeq
globally; and the **`IsElliptic`-instance interaction** (rows 1, 4) with mathlib's existing
`map`/`baseChange` `IsElliptic` instances. Neither is blocking; both are "tidy before upstreaming"
items (consider a sealed `def` + the already-present `@[simp]` `pointedCurve_aᵢ` lemmas, and an
explicit instance priority).

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder       "universal elliptic curve over the universal field", "generic fibre of the universal Weierstrass curve" — no hit
[B] Loogle            `WeierstrassCurve (FractionRing _)`, `baseChange _ (FractionRing (CoordinateRing _))`, `WeierstrassCurve (MvPolynomial _ _)` base-changed — no hit (no decl produces the universal curve over a field)
[C] LeanSearch        "the universal pointed elliptic curve over the field of fractions of the universal ring" — no hit
[D] Grep mathlib src  `pointedCurve`, `Universal.curve`, `Universal.Field`, `genericCurve`, `universalCurve` in `AlgebraicGeometry/EllipticCurve/` — **no hit** (only the prose mention of `𝓡 := ℤ[A₁,…,A₆][X,Y]` in `DivisionPolynomial/Basic.lean:36–38`, never a curve object)
[E] Name pattern      `def (universal|generic|pointed)(Curve|Elliptic)`, `genericFibre` — no hit

Searched for both the user's current form (`baseChange curve Universal.Field`) and the
literature-standard form (generic fibre / base change of the universal curve to the function
field). **Key finding:** mathlib has the *building blocks* — `WeierstrassCurve.baseChange`
(Weierstrass.lean:236), `WeierstrassCurve.IsElliptic` (Weierstrass.lean:363), `map_Δ`
(Weierstrass.lean:273), `instance : (W.map f).IsElliptic` (Weierstrass.lean:448),
`FractionRing`/`CoordinateRing`, `IsFractionRing.injective` — and even the **prose mention** of the
universal ring in `DivisionPolynomial/Basic.lean:36–38`, but **no `def` of the universal curve and
no base-change of it to its fraction field.** Crucially the universal curve `curve` it base-changes
is *itself* not in mathlib (see `curve.md`: verdict `YES-add-as-is`, currently a project def).

Concluded: **not in mathlib**, but the form is `WeierstrassCurve.baseChange` applied to the
project-local `WeierstrassCurve.Universal.curve` (plus a one-`instance` `IsElliptic` proof). It is a
**single mathlib `baseChange` call on an object whose mathlibability is already covered by `curve`**.

---

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.pointedCurve`

Internal use count: **32** occurrences outside the defining file (grep over
`projects/**/*.lean`, excluding `LutzNagell/Universal.lean`). Distribution:
- `projects/NagellLutz/LutzNagell/ZSMul.lean` — **16 uses**: `pointedCurve.toAffine.negY`,
  `.slope`, `.addX`, `.addY`, plus `pointedCurve_a₁/a₂/a₃/a₄` simp-lemma rewrites, in the core
  EDS/ZSMul identities (`smulY n − negY … = ψᵤ(2n)/ψᵤ(n)⁴`, `smulX`/`smulY` doubling, negation).
- `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean` — **16 uses** (the HasseWeil
  fork of the same division-polynomial development): identical `pointedCurve.toAffine.{negY,slope,addX,addY}`
  patterns.
- `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean` — defines its own `pointedCurve`
  (parallel fork of this very declaration).
- `LutzNagell/Universal.lean` itself — `instance : pointedCurve.IsElliptic`, `equation_point`,
  `Affine.point`, `pointedCurve_aᵢ`, `curveField_eq : curveField = pointedCurve := rfl`.

External-to-file callers: 2 distinct files in 2 distinct projects (NagellLutz `ZSMul.lean`,
HasseWeil `DivisionPolynomial.lean`). Inline re-derivation: HasseWeil `Auxiliary/Universal.lean`
**re-declares the same `pointedCurve`** (a parallel fork, not a reuse) — a duplication signal,
consistent with the task brief that HasseWeil/NagellLutz fork the same universal-curve material.

Signal (per the call-sites table): **K = 32 ≫ 3, real load-bearing API** — but with a *parallel
re-declaration in a sibling project* rather than a single shared source, i.e. the object is real
and depended-upon, but currently duplicated → strong YES-\* leaning, modulated by "it is one
`baseChange` of `curve`".

### Composition check

Can `WeierstrassCurve.Universal.pointedCurve` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.baseChange curve Universal.Field` — this *is* the body. It is a
**single mathlib `baseChange` call** applied to `curve`. The accompanying `IsElliptic` instance is
a short, separate proof (`map_Δ` + `map_ne_zero_iff` + `.isUnit`), not part of the def.
  - Mathlib decls used: `WeierstrassCurve.baseChange` (+ for the instance: `map_Δ`,
    `map_ne_zero_iff`, `IsUnit`).
  - Result: **succeeds** — the *definition* is one mathlib call; the *elliptic instance* is ≤3 lines.
  - Notes: the only non-mathlib ingredient is `curve` / `Universal.Field` themselves, which are the
    parent objects assessed separately (`curve.md` → YES-add-as-is).

Conclusion: **COMPOSABLE** — given `curve` and `Universal.Field`, `pointedCurve` is literally
`WeierstrassCurve.baseChange curve Universal.Field` (one mathlib call), and "this base change is
elliptic" is a ≤3-line instance. Per Phase 6b: a single function call (`baseChange curve K`) is a
genuine composition, not a new development. The named `abbrev` is convenience + an instance anchor,
not new mathematical content beyond `curve` + mathlib's `baseChange`.

---

## Verdict: `WeierstrassCurve.Universal.pointedCurve`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the generic fibre / universal elliptic curve over the universal
  field is a standard named object (Silverman specialization; the universal curve with a point of
  order `d` over `K_d`) — **but it is, by definition, the base change of the universal curve to
  the fraction field**, i.e. a composition, not a primitive.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (inherited from `curve`); modern idiom already
  present (`IsElliptic` instance). No generalise-first target.
- Diamond/defeq risk (Phase 4.5): **LOW** — reducibility leak from the `abbrev` + benign
  `IsElliptic`-instance interaction; tidy-before-upstreaming, not blocking.
- Mathlib search (Phase 5): **not in mathlib**, but `WeierstrassCurve.baseChange`,
  `IsElliptic`, `map_Δ` are all present; the form is one `baseChange` of the (project-local) `curve`.
- Composition check (Phase 6): **COMPOSABLE** — `baseChange curve Universal.Field`, a single
  mathlib call, plus a ≤3-line `IsElliptic` instance. 32 call sites, but one of them is a *parallel
  re-declaration* in HasseWeil.

**Rationale:**

`pointedCurve` is mathematically real and standard — it is the generic fibre of the universal
Weierstrass family, the universal elliptic curve over the function field, exactly the object
Silverman-style specialization arguments live on, and the carrier of this project's entire
division-polynomial / EDS development (32 call sites). On *mathematical content* it is squarely
mathlib-worthy. But the mathlibable question is "should mathlib have **this declaration**", and the
declaration is a **one-line reducible `abbrev`** equal to `WeierstrassCurve.baseChange curve
Universal.Field`. mathlib already owns `baseChange`; the only genuinely new object underneath it is
`curve` (the universal Weierstrass curve) — and that is assessed separately as `YES-add-as-is`
(`curve.md`). Once `curve` lands in mathlib, `pointedCurve` adds **no new mathematical content**: it
is one `baseChange` call plus a short `instance : (curve.baseChange K).IsElliptic` proof. The
correct mathlib organization is therefore to ship `curve` (with its coordinate ring, fraction field,
and `specialize` API) and let consumers write `curve.baseChange K` (or have mathlib provide the
`IsElliptic` instance for it), rather than to ship a separate reducible alias.

Three things tip this to NO-composable rather than YES. (1) It is an `abbrev` whose only Phase-2b
exemptions are "API name" and "instance anchor" — and the *defeq* exemption is an explicit
anti-signal (`curveField_eq … := rfl` shows it is deliberately transparent), so it is not a sealed
object carrying its own definitional barrier the way `curve` is. (2) The "new" object is entirely
inherited: `pointedCurve = baseChange curve K`, and `baseChange` is mathlib's. (3) The 32 call
sites notwithstanding, the object is currently **duplicated** (HasseWeil re-declares its own
`pointedCurve`), which is a refactor signal, not a "this exact decl is the canonical thing to
upstream" signal — the canonical thing to upstream is `curve` + the `IsElliptic` instance for its
base changes, after which both forks collapse to `curve.baseChange K`.

**WHY not (refactor-actionable):**
- Mathlib has the building blocks. `pointedCurve` is `WeierstrassCurve.baseChange curve
  Universal.Field` — a single mathlib `baseChange` (Weierstrass.lean:236) applied to the
  project-local universal curve `curve`. The accompanying ellipticity is a ≤3-line instance built
  from `map_Δ` (Weierstrass.lean:273) + `map_ne_zero_iff` + `IsUnit.isUnit`. No new lemma or
  definitional content beyond `curve` (assessed `YES-add-as-is` separately) and mathlib's
  `baseChange`.
- Mathlib building blocks (qualified names):
  - `WeierstrassCurve.baseChange` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - `WeierstrassCurve.IsElliptic` — `…/Weierstrass.lean:363`
  - `WeierstrassCurve.map_Δ` — `…/Weierstrass.lean:273`
  - `WeierstrassCurve.instIsEllipticMap` (`instance : (W.map f).IsElliptic`) — `…/Weierstrass.lean:448`
  - `IsFractionRing.injective`, `FractionRing`, `WeierstrassCurve.Affine.CoordinateRing`
  - plus the project-local `WeierstrassCurve.Universal.curve` (the *one* piece worth upstreaming;
    see `curve.md`).
- Composition sketch (≤3 lines):
  ```lean
  -- given `WeierstrassCurve.Universal.curve` (upstreamed per curve.md):
  abbrev pointedCurve : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field
  instance : pointedCurve.IsElliptic where
    isUnit := (map_Δ curve _ ▸ (map_ne_zero_iff _ algebraMap_field_injective).mpr Δ_curve_ne_zero).isUnit
  ```
- Call sites in our project (from Phase 6.0): **K = 32** (16 in NagellLutz `ZSMul.lean`, 16 in
  HasseWeil `DivisionPolynomial.lean`), plus a parallel re-declaration in HasseWeil
  `Auxiliary/Universal.lean`.
- **Refactor plan:** This is *not* a "delete and inline at 32 sites" case — `pointedCurve` is a
  useful local name and the 32 sites should keep using it. The actionable refactor is **upstream-side
  and dedup-side**, not delete-side:
  1. Upstream `curve` (per `curve.md`) and, in the same/adjacent PR, add a mathlib instance
     `instance {K} [Field K] [Algebra (MvPolynomial Coeff ℤ) K] [FaithfulSMul …] :
     (curve.baseChange K).IsElliptic` (the general "the universal curve base-changed to any field
     into which the coefficient ring injects is elliptic"). Then `pointedCurve` is just the
     `K := Universal.Field` instance of that, needing no bespoke local instance.
  2. **Dedup across the two forks** (a cleanup ticket, not a mathlib PR): NagellLutz
     `LutzNagell/Universal.lean` and HasseWeil `Auxiliary/Universal.lean` both declare
     `pointedCurve` + the `IsElliptic` instance. Factor the universal-curve material into the
     shared location (`Common/` per CLAUDE.md, or have HasseWeil `import` NagellLutz) so there is
     **one** `pointedCurve`, defined once as `curve.baseChange Universal.Field`.
  3. Keep `pointedCurve` as the local `abbrev` for all 32 call sites — but optionally seal it as a
     `def` with the existing `@[simp] pointedCurve_aᵢ` lemmas as its interface, to remove the
     reducibility leak (Phase 4.5 row 2) before any upstreaming.
- Next action: do **not** add `pointedCurve` to mathlib as its own declaration. Instead (a) upstream
  `curve` + a general `(curve.baseChange K).IsElliptic` instance per `curve.md`, and (b) file a
  cleanup ticket to deduplicate the NagellLutz/HasseWeil `pointedCurve` into one shared definition.

---

## Next step

Do **not** PR `pointedCurve` itself — it is `WeierstrassCurve.baseChange curve Universal.Field`, a
one-line composition of mathlib's `baseChange` with the project's `curve` (the latter is the real
upstreaming target, already `YES-add-as-is` in `curve.md`). Two concrete actions: (1) when
upstreaming `curve`, add a *general* `(curve.baseChange K).IsElliptic` instance to mathlib so the
base-changed-to-a-field curve is elliptic for any suitable field `K`; (2) file an AINTLIB cleanup
ticket to deduplicate the parallel `pointedCurve` declarations in NagellLutz `LutzNagell/Universal.lean`
and HasseWeil `Auxiliary/Universal.lean` into a single shared definition, keeping the local
`pointedCurve` name for the 32 call sites.
