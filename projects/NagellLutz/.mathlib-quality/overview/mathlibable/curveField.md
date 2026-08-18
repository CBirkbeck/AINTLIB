# /mathlibable report — `WeierstrassCurve.Universal.curveField`

> Step-9 mathlibable assessment (NagellLutz project). Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:173`.
>
> **Companion note.** `curveField` is **`rfl`-equal to its sibling `pointedCurve`**
> (`curveField_eq : curveField = pointedCurve := rfl`, line 175) — *the identical*
> `abbrev` body `curve.baseChange Universal.Field`. The full EXHAUSTIVE 10-channel
> literature search, generality analysis, modern-idiom check, diamond/defeq risk,
> mathlib search, and composition check were carried out for that definitional content
> in the sibling report `pointedCurve.md` (this directory) and apply here **verbatim**.
> This report records that shared evidence in condensed form and concentrates on the
> three deltas that distinguish `curveField` from `pointedCurve` — all of which
> *strengthen* the same verdict. Parent object `curve` is assessed separately in
> `curve.md` (verdict `YES-add-as-is`).

---

## Baseline (Phase 0)

- lake build:                stale (per task brief; reasoned from source statement — instructed fallback)
- decl `WeierstrassCurve.Universal.curveField`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:173`
- kind:                      `abbrev`  (a reducible alias for a `baseChange`)
- has sorry:                 no
- module docstring summary:  Defines the universal Weierstrass curve over `ℤ[A₁,…,A₆]`, the universal
  *pointed* elliptic curve over the fraction field of its coordinate ring, the specialization
  homomorphism `W.specialize`, and the cusp curve `Y²=X³` used to prove `ψₙ(1,1)=n`.

**Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.curveField`
(namespace stack: `namespace WeierstrassCurve` line 69 → `namespace Universal` line 75; base name
`curveField`, line 173). The parse-time guess `WeierstrassCurve.Universal.curveField` is **correct**.

**Exact statement (source, lines 171–175):**
```lean
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `Frac(ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩)`
(the universal field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field

lemma curveField_eq : curveField = pointedCurve := rfl
```
where `curve : Affine (MvPolynomial Coeff ℤ)` is the universal Weierstrass curve (line 84),
`Universal.Field := FractionRing Universal.Ring` (line 99), `Universal.Ring := curve.CoordinateRing`
(line 96), and `baseChange` is mathlib's
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`, body `W.map (algebraMap R A)`).

**Definitional identity with `pointedCurve`.** Line 130 defines
`abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field`.
Line 173 defines `curveField` with the **identical** right-hand side, and line 175 proves
`curveField = pointedCurve := rfl`. So `curveField` and `pointedCurve` are **two names for the
exact same object** — `curve` base-changed to the universal field. The only structural difference
between the two declarations is that `pointedCurve` is the anchor for `instance :
pointedCurve.IsElliptic` (line 132) and the `pointedCurve_aᵢ` simp lemmas (lines 160–164), whereas
`curveField` carries **no** instance and **no** simp API of its own — it is a bare second name.

---

## Statement (Phase 1)

`WeierstrassCurve.Universal.curveField` is a **definition** (a reducible `abbrev`). It is the
*universal/generic Weierstrass curve* `curve` (over `ℤ[A₁,…,A₆]`) **base-changed to the universal
field** `Universal.Field = Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`, where `P = Y² + A₁XY + A₃Y − X³ − A₂X² −
A₄X − A₆` is the Weierstrass polynomial. Concretely it is the elliptic curve
`y² + A₁xy + A₃y = x³ + A₂x² + A₄x + A₆` over the field `Universal.Field` — the **generic fibre of
the universal Weierstrass family**, the universal elliptic curve over the function field on which
Silverman-style specialization arguments live.

Mathematically `curveField` *is* `pointedCurve` (they are `rfl`-equal); the prose statement of the
underlying object is therefore identical to `pointedCurve.md` Phase 1 and is not repeated in full.
The role of the *name* `curveField` is purely a naming convention within the development: it is the
name used in the **Jacobian-coordinate** division-polynomial computations (`dblXYZ`/`addXYZ`/
`Nonsingular` over `Universal.Field`), where `simp only [..., curveField, ...]` deliberately unfolds
it to the base-changed curve's coefficients (e.g. `ZSMul.lean:463`,
`HasseWeil/.../DivisionPolynomial.lean:548`). Its sibling `pointedCurve` is the name used in the
**Affine-coordinate** computations (`negY`/`slope`/`addX`/`addY`).

Variables / typeclasses involved (Lean side):
- none generic — it is a closed `abbrev` over the concrete `Universal.Field`. It implicitly uses
  the `Algebra (MvPolynomial Coeff ℤ) Universal.Field` instance that `baseChange` requires
  (provided by the `FractionRing`/`AdjoinRoot` tower).

Hypotheses (Lean side): none — it is a definition.

Conclusion (math): the universal/generic pointed elliptic curve over the universal field
(identical object to `pointedCurve`).
Conclusion (Lean): `WeierstrassCurve Universal.Field`.

---

## Size classification (Phase 2a)

Verdict: **BIG** (object of independent standing — the generic fibre of the universal Weierstrass
family), inherited from `curve`/`pointedCurve`.
Reason: it names the carrier object of the entire Jacobian division-polynomial / ZSMul development
(17 call sites). Caveat identical to `pointedCurve`: as a `def`/`abbrev` it is *derived* from the
BIG `curve` by a single mathlib `baseChange`, so its independent-standing is inherited from `curve`,
and it is moreover a **second name** for `pointedCurve`. This tension drives the verdict below.

(Literature width is EXHAUSTIVE regardless; BIG is recorded for framing.)

## One-line check (Phase 2b)

Body line count: **1 substantive line** (`curve.baseChange Universal.Field`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | **no** (anti-signal) | It is an `abbrev` → explicitly **reducible**. `curveField_eq : curveField = pointedCurve := rfl` and the Jacobian proofs that do `simp only [..., curveField, ...]` (`ZSMul.lean:463`, `DivisionPolynomial.lean:548`) show it is *meant* to unfold to the base-changed curve's coefficients. It is **not** a sealed defeq barrier — the opposite. |
| Avoid typeclass diamonds          | **no** | Unlike `pointedCurve`, `curveField` is **not** an instance anchor — there is **no** `instance : curveField.IsElliptic`; the only `IsElliptic` instance in the file is on `pointedCurve` (line 132). `curveField` carries no typeclass-search role. (Because the two are `rfl`-equal, the `pointedCurve.IsElliptic` instance does apply to `curveField` by defeq, but nothing is *anchored* on the `curveField` name.) |
| Mark semantic intent / API name   | **yes** | `curveField` is the stable name used at **17 call sites** across two projects (9 in NagellLutz `ZSMul.lean`, 8 in HasseWeil `DivisionPolynomial.lean`), exclusively in the **Jacobian** `dblXYZ`/`addXYZ`/`Nonsingular` computations. The name does carry API intent (the "over the fraction *field*" reading, where division is legal). |

Conclusion: **ONE-LINER WITH-EXEMPTION** — but on the *weakest possible* grounds: the **only**
applicable exemption is "API name", and even that overlaps entirely with `pointedCurve` (the two
names denote the same object). The two stronger exemptions that `pointedCurve` could partly claim —
instance anchor (typeclass diamonds) and defeq barrier — **do not apply to `curveField` at all**
(no instance is anchored on it; it is deliberately transparent). So `curveField` is a *strictly
weaker* mathlib-inclusion candidate than its already-`NO` sibling `pointedCurve`. This is carried
into Phase 7.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

Because `curveField` is `rfl`-equal to `pointedCurve` (same `baseChange curve Universal.Field`
body), the concept under search is **identical** to `pointedCurve.md` Phase 3 — *the universal/
generic (pointed) elliptic curve over the universal field*. The full 10-channel table was executed
for that concept in `pointedCurve.md`; it is reproduced here in condensed form (same queries, same
hits) so this report is self-contained.

| #  | Channel                          | Concept query (universal/generic elliptic curve over the universal field)                              | Hit? | Standard form found                                              |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|
|  1 | WebSearch (specific form)        | universal elliptic curve over field of fractions of universal ring; generic point                      | yes  | base change `E` to `Frac(R_univ)=K`; elliptic curve over a field (RNT/arXiv:2501.03209) |
|  2 | WebSearch (general / functorial) | generic fibre of universal Weierstrass family; EC over `ℚ(a₁,…,a₆)`; Silverman specialization           | yes  | the generic curve over the function field; Silverman [Sil83] specialization theorem |
|  3 | WebSearch (named-after / aliases)| Silverman generic elliptic curve `Q(a₁..a₆)` division polynomials point infinite order                  | yes  | `ψₘ ∈ ℤ[A,B,x]`; specialize the generic curve's `ψₘ` (arXiv:0811.3109, 1108.3051) |
|  4 | ChatGPT MCP                      | standard name + canonical base field + relation to `baseChange` of the universal curve                  | n/a  | MCP server **down** (task brief warned). Substituted by channels 1–3, 6–10 which converge. |
|  5 | Local references                 | `grep .mathlib-quality/references/`                                                                     | n/a  | directory absent for NagellLutz — recorded n/a. |
|  6 | nLab                             | universal elliptic curve / moduli stack of elliptic curves / generic fibre                              | yes  | `E → M_ell`; its fibre over the generic point is the curve over the function field |
|  7 | nCatLab (categorical framing)    | generic fibre of the Weierstrass family; pullback of universal curve to `Spec K`                        | yes  | base change of the universal family along `Spec(function field) → moduli` — i.e. `baseChange curve K` |
|  8 | Stacks Project (alg geom)        | generic fibre; base change of a family to the fraction field of the base                                | yes (indirect) | base change along `Spec Frac(A) → Spec A` is the generic fibre; EC-specific instance, not a named tag |
|  9 | MathOverflow / Math.SE           | EC over `Q(a₁..a₆)` generic; rank of generic curve; specialization                                      | yes  | consensus: the generic curve over the rational function field; base change of the universal curve |
| 10 | recent arXiv (≤5 yr)             | universal Weierstrass curve with point of order `d` over `K_d`; homogeneous division polynomials        | yes  | "the curve base changed to … the universal Weierstrass elliptic curve … over `K_d = Frac(R_d)`" (arXiv:2501.03209, 1303.4327) |

### Literature summary (Phase 3)

Concept identified as: **the universal/generic (pointed) elliptic curve over the universal field**
— the generic fibre of the universal Weierstrass family, i.e. the base change of the universal
Weierstrass curve to the fraction field of its (coordinate) ring.
Sources agree on the standard form: **yes** — `baseChange(universal Weierstrass curve, K)` with `K`
the fraction field of the universal base ring; over `K` the discriminant is a unit (elliptic), and
it carries the generic point `(X,Y)` of infinite order. This is the object Silverman's
specialization theorem is stated relative to.
Most general standard form: as stated — universal curve over `ℤ[A₁,…,A₆]` (all five coeffs, base
`ℤ`), base-changed to `Frac` of its coordinate ring (so the generic point is included). `curveField`
(= `pointedCurve`) matches this exactly.
Generality dimensions where the literature varies: identical to `pointedCurve.md` — (a) which field
(coordinate-ring fraction field, *pointed* — this project — vs. `Frac(ℤ[A₁..A₆])`, no marked point);
(b) packaging (bare base-changed curve + separate marked point vs. a bundled pointed-curve type;
mathlib has no `PointedWeierstrassCurve`).
Disagreement with the literature: **none.** `curveField` is the standard generic-fibre object,
realized as `baseChange(universal curve, universal field)` at full generality.

**Crucial framing for the verdict.** The literature names the *object* (the generic fibre), and it
is a standard object. But the literature does **not** call for **two distinct names** for it within
one development — and `curveField` is precisely a second name for `pointedCurve`. The literature
supports "this object is real"; it does not support "ship this particular reducible alias".

---

## Generality analysis (Phase 4)

Identical to `pointedCurve.md` Phase 4 (same `baseChange curve Universal.Field`).

| # | Parameter / hypothesis        | Current Lean form                                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | base curve                    | `curve` (universal, over `ℤ[A₁,…,A₆]`, 5 coeffs) | the universal Weierstrass curve  | NO                  | already maximally general (inherited from `curve`; base `ℤ`, all five `aᵢ`). |
| 2 | target field                  | `Universal.Field = Frac(curve.CoordinateRing)`   | `Frac` of the (coordinate) base ring | NO              | canonical field that *includes the generic point*; `Frac(ℤ[A₁..A₆])` (no point) would be strictly less rich. |
| 3 | construction                  | `curve.baseChange Universal.Field` (mathlib `baseChange`) | pullback of the universal family to `Spec K` | n/a       | `baseChange` *is* the categorical base change / generic fibre; the right operation, nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (inherited from `curve`; `baseChange` to the
coordinate-ring fraction field is the canonical generic-fibre construction).
Number of weakening opportunities found: 0.
Proposed restatement: none (already maximal).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                              | Applies? | Notes |
|----|------------------------------------------------------------------------------------------------------|----------|-------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | n/a for `curveField` | The "is elliptic" fact is internalised as `instance : pointedCurve.IsElliptic` — but on **`pointedCurve`**, not `curveField`. `curveField` itself carries no instance; the modern idiom is already realised on its sibling. |
|  2 | sequences/metric → filters/topological?                                                               | no       | purely algebraic. |
|  3 | **construct** an object where a **universal-property class** would characterise it?                   | no       | it is a base change of the representing object `curve`; the universal property lives on `curve` (`specialize`/`map_specialize`). A `generic`/`pointed` curve *class* adds nothing over `baseChange curve K`. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                               | no       | n/a. |
|  5 | field-specific → weaker typeclass?                                                                    | **no — deliberately** | it is *meant* to be over the fraction **field** (where `Δ` is a unit and Jacobian division by `ψₙ` is legal). The field is load-bearing. |
|  6 | 1-categorical → higher/∞-categorical (moduli **stack**)?                                              | yes, but **rejected** | the moduli-stack pullback needs algebraic-stacks infra mathlib lacks; `curveField` remains the affine-Weierstrass generic fibre underneath. Not a generalise-first target. |
|  7 | concrete index → arbitrary additive group/monoid?                                                    | no       | nothing indexed. |
|  8 | concrete-via-abstract (proof betrays the right form)?                                                 | no       | it is a `def`, no proof body to inspect. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The one modern move (encoding "is elliptic" as a typeclass) is
already present — and it is anchored on `pointedCurve`, not `curveField`. No further Bourbaki-2.0
improvement specific to `curveField`; a bundled "generic/pointed curve class" would not compose
better than `baseChange curve K` + the existing instance. The moduli-stack reformulation is a
heavier different object, not a restatement.

---

## Diamond / defeq risk (Phase 4.5) — `abbrev` (reducible def)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | low     | `curveField` is a `WeierstrassCurve` *term* (data), not an instance, and — unlike `pointedCurve` — it has **no** associated instance declared on its name. The `pointedCurve.IsElliptic` instance applies to `curveField` only via the `rfl` defeq; `IsElliptic` is a `Prop`-class (proof-irrelevant), so no inconsistent diamond. |
| 2 | Reducibility leak            | **low–moderate** | It is an **`abbrev`** → `@[reducible]`; its body `curve.baseChange Universal.Field` (= `curve.map (algebraMap …)`) is exposed to defeq-checking wherever `curveField` appears. The body is cheap (five `algebraMap` applications). Same mild-leak pattern as `pointedCurve`; here it is *intended* (the Jacobian proofs `simp only [..., curveField, ...]` rely on it unfolding). The general "name a base change as a reducible `abbrev`" pattern is the kind of thing a mathlib reviewer flags. |
| 3 | Non-canonical unfolding      | low     | `curveField` has **no** dedicated `@[simp]` lemmas (the `pointedCurve_aᵢ` lemmas are keyed to `pointedCurve`); it is unfolded directly via `simp only [curveField]` at call sites. Consistent with the `abbrev`; no surprising *global* unfolds beyond reducibility. |
| 4 | Instance priority collision  | none    | `curveField` declares no instance, so there is no priority to collide. |
| 5 | Universe-polymorphism issues | none    | base type is the concrete `Universal.Field : Type`; no universe variables. |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`; accessed by field projection / `.toAffine`. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (no HIGH rows).
Top risk: the **reducibility leak** (row 2) — the `abbrev` exposes the base-change body to defeq
globally. Here it is *by design* (Jacobian proofs unfold it). Not blocking; a "tidy before
upstreaming" item, and moot under the recommended refactor (dedup `curveField` into `pointedCurve`).

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder       "universal elliptic curve over the universal field", "generic fibre of the universal Weierstrass curve" — no hit
[B] Loogle            `WeierstrassCurve (FractionRing _)`, `baseChange _ (FractionRing (CoordinateRing _))`, base change of `WeierstrassCurve (MvPolynomial _ _)` — no hit
[C] LeanSearch        "the universal pointed elliptic curve over the field of fractions of the universal ring" — no hit
[D] Grep mathlib src  `curveField`, `pointedCurve`, `Universal.curve`, `genericCurve`, `universalCurve` in `Mathlib/AlgebraicGeometry/` — **no hit** (verified: `grep -rniE 'curveField|genericCurve|universalCurve|pointedCurve|Universal\.curve' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/` returns nothing; only the prose mention of `𝓡 := ℤ[A₁,…,A₆][X,Y]` in `DivisionPolynomial/Basic.lean:36–38`, never a curve object)
[E] Name pattern      `def (universal|generic|pointed)(Curve|Elliptic)`, `genericFibre`, `curveField` — no hit

Searched for both the user's current form (`curve.baseChange Universal.Field`) and the
literature-standard form (generic fibre / base change of the universal curve to the function field).
**Key finding:** mathlib has the *building blocks* — `WeierstrassCurve.baseChange`
(Weierstrass.lean:236, body `W.map (algebraMap R A)`), `WeierstrassCurve.map` (Weierstrass.lean:231),
`WeierstrassCurve.IsElliptic` (Weierstrass.lean:363), `map_Δ` (Weierstrass.lean:273),
`instance : (W.map f).IsElliptic` (Weierstrass.lean:448), `FractionRing`/`CoordinateRing`,
`IsFractionRing.injective` — but **no `def` of the universal curve and no base-change of it to its
fraction field.** The universal curve `curve` it base-changes is *itself* not in mathlib (see
`curve.md`: verdict `YES-add-as-is`, currently a project def).

Concluded: **not in mathlib**, but the form is `WeierstrassCurve.baseChange` applied to the
project-local `WeierstrassCurve.Universal.curve` — a **single mathlib `baseChange` call** on an
object whose mathlibability is already covered by `curve`. (And the same object is *already named*
in the same file as `pointedCurve`.)

---

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.curveField`

Internal use count (whole repo, excluding the defining file `LutzNagell/Universal.lean`): **17**
occurrences. Distribution:

| Caller file:line                                         | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------------|---------------------------------------------------------------------|
| `NagellLutz/LutzNagell/ZSMul.lean:385`                   | `Affine.Nonsingular curveField (smulX n) (smulY n)`                 |
| `NagellLutz/LutzNagell/ZSMul.lean:445`                   | `Nonsingular curveField (smulField n)`                              |
| `NagellLutz/LutzNagell/ZSMul.lean:451`                   | `((2 : ℤ) • P).point = ⟦dblXYZ curveField v⟧`                       |
| `NagellLutz/LutzNagell/ZSMul.lean:456`                   | `(P + Q).point = ⟦addXYZ curveField v w⟧`                           |
| `NagellLutz/LutzNagell/ZSMul.lean:460,463`               | `dblXYZ curveField (smulField n) = …` ; `simp only [..., curveField, …]` |
| `NagellLutz/LutzNagell/ZSMul.lean:493`                   | `(-1 : Universal.Field) • neg curveField (smulField n)`             |
| `NagellLutz/LutzNagell/ZSMul.lean:500,531`               | `addXYZ curveField (smulField m) (smulField n) = …`                 |
| `HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:526,531,536,545,548,569,576,607` | identical Jacobian `dblXYZ`/`addXYZ`/`Nonsingular`/`neg curveField` patterns (8 uses) |

External-to-file callers: **2 distinct files in 2 distinct projects** (NagellLutz `ZSMul.lean` — 9;
HasseWeil `DivisionPolynomial.lean` — 8). All 17 uses are in **Jacobian-coordinate** division-
polynomial computations.

Inline-derivation grep: the HasseWeil `Auxiliary/Universal.lean:176` **re-declares the same
`curveField`** (a parallel fork of this very `abbrev`, alongside its parallel `pointedCurve`) — a
duplication signal, consistent with the task brief that HasseWeil/NagellLutz fork the same
universal-curve material.

Signal (per the call-sites table): **K = 17 ≫ 3, real load-bearing API** — but (a) the object is
*the same object* as `pointedCurve` (the file holds **two `rfl`-equal names** for it, split by
coordinate system), and (b) it is **re-declared** verbatim in HasseWeil. So the object is real and
depended-upon, but currently *named twice in-file and forked across projects* → a dedup signal, not
a "this exact decl is the canonical thing to upstream" signal.

### Composition check

Can `WeierstrassCurve.Universal.curveField` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.baseChange curve Universal.Field` — this **is** the body. It is a
**single mathlib `baseChange` call** applied to `curve` (and `baseChange W A = W.map (algebraMap R A)`,
so even unfolded it is one `map` of one `algebraMap`).
  - Mathlib decls used: `WeierstrassCurve.baseChange` (Weierstrass.lean:236) — and nothing else; no
    accompanying instance is part of *this* declaration (the `IsElliptic` instance lives on
    `pointedCurve`).
  - Result: **succeeds** — one mathlib call.
  - Notes: the only non-mathlib ingredient is `curve` / `Universal.Field`, the parent objects
    assessed separately (`curve.md` → `YES-add-as-is`). And the object already has a name in-file:
    `pointedCurve`.

Attempt 2 (the *even-cheaper* composition for `curveField` specifically):
`pointedCurve` — since `curveField = pointedCurve := rfl`, `curveField` is **literally the existing
`pointedCurve`**, 0 mathlib calls beyond what `pointedCurve` already is. The "composition" for
`curveField` is "use `pointedCurve`".

Conclusion: **COMPOSABLE** — `curveField` is `curve.baseChange Universal.Field` (one mathlib
`baseChange` call), equivalently the already-defined `pointedCurve` (zero further work). Per Phase 6b,
a single function call (`baseChange curve K`) is a genuine composition, not a new development; and
"it is `rfl`-equal to an existing in-scope name" is the strongest possible composability signal.

---

## Verdict: `WeierstrassCurve.Universal.curveField`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the generic fibre / universal elliptic curve over the universal
  field is a standard named object — **but it is, by definition, the base change of the universal
  curve to the fraction field** (a composition), and the literature never calls for *two* names for
  it. Same object as `pointedCurve`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (inherited from `curve`); modern idiom (the
  `IsElliptic` instance) already present — on `pointedCurve`, not `curveField`. No generalise-first
  target.
- Diamond/defeq risk (Phase 4.5): **LOW** — reducibility leak from the `abbrev` (here intended);
  no instance anchored on the name, so no priority/diamond exposure. Tidy-before-upstreaming, not
  blocking.
- Mathlib search (Phase 5): **not in mathlib**, but `WeierstrassCurve.baseChange`/`map`/`IsElliptic`/
  `map_Δ` are all present; the form is one `baseChange` of the (project-local) `curve`.
- Composition check (Phase 6): **COMPOSABLE** — `curve.baseChange Universal.Field`, a single mathlib
  call; equivalently the in-scope `pointedCurve` (zero further work). 17 call sites, but the object
  is `rfl`-equal to `pointedCurve` (a second in-file name) and re-declared in HasseWeil.

**Rationale:**

`curveField` denotes a mathematically real and standard object — the generic fibre of the universal
Weierstrass family, the universal elliptic curve over the function field, the carrier of this
project's Jacobian division-polynomial / EDS development (17 call sites). But the mathlibable
question is "should mathlib have **this declaration**", and `curveField` is a **one-line reducible
`abbrev`** equal to `WeierstrassCurve.baseChange curve Universal.Field` — which is **`rfl`-equal to
the sibling `pointedCurve`** (`curveField_eq … := rfl`). mathlib already owns `baseChange`; the only
genuinely new object underneath is `curve` (assessed `YES-add-as-is` in `curve.md`). Once `curve`
lands in mathlib, `curveField` adds **no new mathematical content** beyond a single `baseChange`
call — content that, within this very file, is *already* named `pointedCurve`.

`curveField` is in fact a **strictly weaker** mathlib-inclusion candidate than its already-`NO`
sibling `pointedCurve`, for two reasons. (1) Its only Phase-2b exemption is "API name" — and the two
exemptions `pointedCurve` could partly claim (**instance anchor** / typeclass-diamond avoidance, and
a **defeq barrier**) **do not apply to `curveField` at all**: no instance is anchored on the
`curveField` name, and it is deliberately transparent (the Jacobian proofs `simp only […,
curveField, …]` *rely* on it unfolding). (2) The object is **named twice in one file** —
`curveField` and `pointedCurve` are two `rfl`-equal handles for `curve.baseChange Universal.Field`,
split only by which coordinate system uses them (Jacobian vs. Affine). The correct mathlib
organisation is therefore to ship `curve` (with its coordinate ring, fraction field, and
`specialize` API) and let consumers write `curve.baseChange K` (or use a *single* named alias +
the `IsElliptic` instance) — not to ship a *second* reducible alias for the base change.

Two things tip this decisively to NO-composable. First, the "new" object is entirely inherited:
`curveField = baseChange curve K`, and `baseChange` is mathlib's. Second, even *within the project*
the canonical name for this object is contested — `pointedCurve` is the one carrying the instance
and the `@[simp]` API; `curveField` is the bare Jacobian-side duplicate. The canonical thing to
upstream is `curve` + one `IsElliptic` instance for its base changes, after which both `pointedCurve`
*and* `curveField` collapse to `curve.baseChange K` (and the project should keep just one local name).

**WHY not (refactor-actionable):**
- Mathlib has the building blocks. `curveField` is `WeierstrassCurve.baseChange curve
  Universal.Field` — a single mathlib `baseChange` (Weierstrass.lean:236, itself `W.map (algebraMap
  R A)`) applied to the project-local universal curve `curve`. No accompanying lemma or instance is
  part of this declaration (the ellipticity instance lives on `pointedCurve`). And it is `rfl`-equal
  to the already-defined `pointedCurve`, so within the project it is **already composable to a single
  existing name**.
- Mathlib building blocks (qualified names):
  - `WeierstrassCurve.baseChange` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - `WeierstrassCurve.map` — `…/Weierstrass.lean:231`
  - `WeierstrassCurve.IsElliptic` — `…/Weierstrass.lean:363`
  - `WeierstrassCurve.map_Δ` — `…/Weierstrass.lean:273`
  - `WeierstrassCurve.instIsEllipticMap` (`instance : (W.map f).IsElliptic`) — `…/Weierstrass.lean:448`
  - `FractionRing`, `WeierstrassCurve.Affine.CoordinateRing`, `IsFractionRing.injective`
  - plus the project-local `WeierstrassCurve.Universal.curve` (the *one* piece worth upstreaming;
    see `curve.md`).
- Composition sketch (≤3 lines):
  ```lean
  -- within the project, curveField is literally pointedCurve:
  example : curveField = pointedCurve := rfl
  -- and, given `WeierstrassCurve.Universal.curve` (upstreamed per curve.md):
  abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field  -- one mathlib call
  ```
- Call sites in our project (from Phase 6.0): **K = 17** (9 in NagellLutz `ZSMul.lean`, 8 in
  HasseWeil `DivisionPolynomial.lean`), all Jacobian; plus a parallel re-declaration in HasseWeil
  `Auxiliary/Universal.lean:176`.
- **Refactor plan.** This is *not* a "delete and inline `baseChange` at 17 sites" case — a short name
  for the base-changed-to-field curve is genuinely useful at those sites. The actionable refactor is
  **dedup-side and upstream-side**, in three steps:
  1. **In-file dedup (cleanup ticket, highest priority).** `curveField` and `pointedCurve` are
     `rfl`-equal (`curveField_eq … := rfl`). Pick **one** name for the object and use it in both the
     Affine and Jacobian computations; delete the other `abbrev` and the now-needless
     `curveField_eq` glue lemma (already flagged **REMOVE** in
     `.mathlib-quality/overview/analysis/07-api-and-junk.md`). The 17 Jacobian sites and the 16
     Affine sites then refer to a single name. (Keeping both is the only reason `curveField` exists
     as a separate decl at all.)
  2. **Cross-fork dedup (cleanup ticket).** NagellLutz `LutzNagell/Universal.lean` and HasseWeil
     `Auxiliary/Universal.lean` both declare `curveField` (and `pointedCurve`). Factor the
     universal-curve material into the shared location (`Common/` per CLAUDE.md, or have HasseWeil
     `import` NagellLutz) so there is **one** definition.
  3. **Upstream (mathlib PR, follows `curve`).** When `curve` is upstreamed (per `curve.md`, to a new
     `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean`), add a *general* instance
     `instance {K} [Field K] [Algebra (MvPolynomial Coeff ℤ) K] [FaithfulSMul …] :
     (curve.baseChange K).IsElliptic`. Then the single surviving local alias is just the
     `K := Universal.Field` instance of `curve.baseChange K`, needing no bespoke local instance, and
     `curveField` as a *separate* decl disappears entirely.
- Next action: do **not** add `curveField` to mathlib as its own declaration. Instead (a) file a
  cleanup ticket to **collapse `curveField` and `pointedCurve` into one local name** and delete
  `curveField_eq`; (b) dedup the NagellLutz/HasseWeil forks into one shared definition; (c) upstream
  `curve` + a general `(curve.baseChange K).IsElliptic` instance per `curve.md`.

---

## Next step

Do **not** PR `curveField` itself — it is `WeierstrassCurve.baseChange curve Universal.Field`, a
one-line composition of mathlib's `baseChange` with the project's `curve`, and it is moreover
`rfl`-equal to the sibling `pointedCurve` already defined in the same file (the real upstreaming
target is `curve`, `YES-add-as-is` in `curve.md`). Three concrete actions: (1) file an AINTLIB
cleanup ticket to **merge `curveField` into `pointedCurve`** (one name for the `rfl`-equal object)
and delete the dead `curveField_eq` glue lemma; (2) deduplicate the parallel `curveField`/
`pointedCurve` declarations in NagellLutz `LutzNagell/Universal.lean` and HasseWeil
`Auxiliary/Universal.lean` into a single shared definition; (3) when upstreaming `curve`, add a
general `(curve.baseChange K).IsElliptic` instance so the base-changed-to-a-field curve is elliptic
for any suitable field `K`, after which no separate `curveField`/`pointedCurve` alias is needed at
all.
