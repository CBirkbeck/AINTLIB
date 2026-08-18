# /mathlibable report — `WeierstrassCurve.Universal.curve`

> Step-9 mathlibable assessment (NagellLutz project). Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:84`.

---

## Baseline (Phase 0)

- lake build:                stale (per task brief; reasoned from source statement — instructed fallback)
- decl `WeierstrassCurve.Universal.curve`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:84`
- kind:                      `def`  (a bundled `WeierstrassCurve` record literal)
- has sorry:                 no
- module docstring summary:  Defines the universal Weierstrass curve over `ℤ[A₁,…,A₆]`, the universal
  pointed elliptic curve over the fraction field of its coordinate ring, the specialization
  homomorphism `W.specialize`, and the cusp curve `Y²=X³` used to prove `ψₙ(1,1)=n`.

**Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.curve`
(namespace stack: `WeierstrassCurve` → `Universal`; base name `curve`). The parse-time guess
`WeierstrassCurve.Universal.curve` is correct.

**Exact statement (source, lines 80–85):**
```lean
open MvPolynomial (X) in
/-- The universal Weierstrass curve over the polynomial ring in five variables
(the **universal polynomial ring** for Weierstrass curves),
corresponding to the five coefficients of the Weierstrass polynomial. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }
```
where `Coeff` is the five-element inductive `| A₁ | A₂ | A₃ | A₄ | A₆` (line 73) and `Affine R`
is mathlib's abbreviation for `WeierstrassCurve R`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:74`).

---

## Statement (Phase 1)

`WeierstrassCurve.Universal.curve` is a **definition** of the *universal* (a.k.a. *generic*)
Weierstrass curve: the Weierstrass curve over the polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]` (the
integers adjoined five indeterminates, one per Weierstrass coefficient) whose five structure
coefficients `a₁,…,a₆` are set equal to the five indeterminates `X A₁,…,X A₆` themselves. Its
generalized Weierstrass equation is therefore
`y² + A₁·x·y + A₃·y = x³ + A₂·x² + A₄·x + A₆` over `ℤ[A₁,…,A₆]`, with no relation imposed
among the `Aᵢ`.

The point of the object is its **universal property**, realized in the same file: for any
commutative ring `R` and any Weierstrass curve `W` over `R`, there is a unique ring homomorphism
`W.specialize : ℤ[A₁,…,A₆] →+* R` sending `Aᵢ ↦ (W.aᵢ)`, and
`Universal.curve.map W.specialize = W` (`map_specialize`, line 194). Thus `curve` is the
representing object for the functor `R ↦ {Weierstrass curves over R}`, and every Weierstrass
curve is a specialization of it.

Variables / typeclasses involved (Lean side):
- `Coeff` — the five-element index type of coefficients (project-local inductive).
- base ring is the concrete `MvPolynomial Coeff ℤ = ℤ[A₁,…,A₆]`; no typeclass parameters
  (it is a closed `def`, not generic in a ring).

Hypotheses (Lean side): none — it is a definition.

Conclusion (math): the generic/universal Weierstrass curve over `ℤ[a₁,…,a₆]`.
Conclusion (Lean): `Affine (MvPolynomial Coeff ℤ)` (i.e. `WeierstrassCurve (MvPolynomial Coeff ℤ)`).

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: introduces a *named mathematical object of independent standing* (the universal
Weierstrass curve / representing object of the Weierstrass-equation functor) — a concept with
its own entry in the moduli-of-elliptic-curves literature, not a helper lemma. It is the
foundation of the entire division-polynomial / EDS development in this project.

(Literature width is EXHAUSTIVE regardless; BIG is recorded for framing.)

## One-line check (Phase 2b)

Body line count: 1 substantive line (a single five-field record literal).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                 | partial  | `Δ_curve_ne_zero` (line 87) and `map_specialize` (line 194) `simp [curve]` *unfold* it deliberately; it is sealed (not `@[reducible]`) so the unfold is controlled, but the body is meant to be unfolded, not hidden. |
| Avoid typeclass diamonds          | no       | `curve` is a `WeierstrassCurve` *term* (data), not an instance; no instance search targets it. |
| Mark semantic intent / API name   | **yes**  | The name `Universal.curve` is the stable API anchor for `Universal.Ring`/`Universal.Field`/`pointedCurve`/`specialize` and ~101 downstream uses. Renaming/inlining the record would break the whole development's vocabulary. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic intent / API name — and it is the named
object the universal property is *about*, which is the strongest possible form of this exemption:
the def is not "a wrapper around a computation" but "the object a theorem is named after").

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                               | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | universal Weierstrass curve over `ℤ[a₁,…,a₆]`, coefficients as indeterminates                        | yes  | Weierstrass curve over `ℤ[a₁,…,a₆]`, `aᵢ` = generic indeterminates | Sage `ell_generic`; Wikipedia; Conrad *Minimal models*; confirms exactly this object. |
|  2 | WebSearch (general / functorial) | "universal elliptic curve" specialization homomorphism, ring of modular forms                       | yes  | representing object; `aᵢ` specialize to coefficients of any family | Hida *Elliptic Curves & Modular Forms* (Lec09); the `aᵢ` are the universal coordinates of `H⁰(M̄_ell,ω^*)`. |
|  3 | WebSearch (named-after / aliases)| "generic Weierstrass equation" representing object functor of Weierstrass curves; Tate              | yes  | "the functor sending R to its groupoid of Weierstrass curves … is representable by A" | Parson, *Moduli of Elliptic Curves* (Conrad VIGRE); A = the universal Weierstrass-coefficient ring. |
|  4 | ChatGPT MCP                      | standard name + universal property + canonical base ring + more-general form                        | n/a  | MCP server **down** (Codex exec failed) — task brief warned of this | Substituted by channels 1–3, 6, 8, 9 which already converge. |
|  5 | Local references                 | `grep .mathlib-quality/references/`                                                                  | n/a  | directory absent for NagellLutz                                  | recorded n/a (no refs dir). |
|  6 | nLab                             | moduli stack of elliptic curves / cubic curve / Weierstrass equation                                | yes  | "Locally … any elliptic curve is a Weierstrass equation `y²+a₁xy+a₃y=…`; the `aᵢ` parameterise the universal family" | `ncatlab.org/nlab/show/moduli+stack+of+elliptic+curves`; `…/cubic+curve`. |
|  7 | nCatLab (categorical framing)    | representability of the Weierstrass-curve functor                                                    | yes  | "functor of Weierstrass curves + coordinate transformations representable by `A` and `Γ`" | same nLab cluster; this is the stack `[A¹⁰/G]` story. |
|  8 | Stacks Project (alg geom)        | universal cubic / Weierstrass generic fiber `aᵢ` sections                                            | yes (indirect) | generic fiber of a Weierstrass fibration with `aᵢ` as sections; "map … universal for Weierstrass elliptic curves" | Surfaced via F-theory / Weierstrass-model notes + Mathew, *Families of elliptic curves* (Climbing Mount Bourbaki). |
|  9 | MathOverflow / Math.SE           | covered by #2/#3 generality discussion (representability, base = ℤ)                                  | yes  | consensus: base `ℤ`, full 5-coeff form, is the universal one          | No disagreement located. |
| 10 | recent arXiv (≤5 yr)             | homogeneous division polynomials for Weierstrass curves; `Ψₙ ∈ ℤ[a₁,…,a₆,x,y]`                       | yes  | "generic curve over `Frac(ℤ[a₁,…,a₆])`; `Ψₙ` are universal polynomials in the independent indeterminates `aᵢ,x,y`" | arXiv:1303.4327; arXiv:1108.3051 — *exactly* this project's use case (division polynomials via the universal curve). |

### Literature summary (Phase 3)

Concept identified as: **the universal Weierstrass curve** (equivalently *generic Weierstrass
curve*; the *representing object of the Weierstrass-equation functor*).
Sources agree on the standard form: **yes** — the Weierstrass curve over `ℤ[a₁,…,a₆]` with `aᵢ`
the five independent indeterminates, characterised by the universal property that every
Weierstrass curve over every commutative ring is a unique specialization of it.
Most general standard form: as stated — base ring `ℤ` (so it specializes to *every* ring), full
five-coefficient generalized Weierstrass form (so it covers *every* characteristic, not just
`char ≠ 2,3`).
Generality dimensions where the literature varies:
  - **Base ring**: some sources work over `ℤ[1/6]` and the *short* form `y²=x³+Ax+B`
    (2 indeterminates) when `char ≠ 2,3`; the maximally general / canonical choice is **`ℤ` with
    all five `aᵢ`** (the project's choice). Short-over-`ℤ[1/6]` is a *specialisation*, strictly
    less general.
  - **Packaging**: bare affine curve (this project) vs. the moduli *stack* `M̄_ell` /
    `[Spec ℤ[a₁,…,a₆] / G]` quotient by coordinate changes (higher-powered, but a different and
    much heavier object — see Phase 4c).
Disagreement with the literature: **none.** The project's `curve` is precisely the
literature-standard universal Weierstrass curve at its most general (base `ℤ`, all five `aᵢ`).

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the Weierstrass curve over `ℤ[a₁,…,a₆]` with `aᵢ` the
five indeterminates; base `ℤ`; full five-coefficient form.

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | base ring                     | `ℤ` (`MvPolynomial Coeff ℤ`)              | `ℤ` (canonical)                  | NO                  | `ℤ` is already the *initial* commutative ring; the universal property `map_specialize` works for **every** `R` precisely because the base is `ℤ`. Using `ℤ[1/6]` would be *less* general (loses char 2,3). |
| 2 | number of coefficients        | all five `a₁,a₂,a₃,a₄,a₆`                  | all five (generalized form)      | NO                  | Dropping to short form `y²=x³+Ax+B` is a *specialisation* (valid only over `ℤ[1/6]`); the five-coeff form is the maximally general one. |
| 3 | index type `Coeff`            | bespoke 5-element inductive               | `{1,2,3,4,6}` (informal)         | n/a                 | `Fin 5` or a sum type are isomorphic re-spellings; the inductive with named ctors `A₁,…,A₆` is the clean idiomatic choice and matches mathlib's own `ψ`/`φ`/`ω` naming. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: 0 (every "weakening" direction — `ℤ[1/6]`, short form —
is in fact a *specialisation*, i.e. strictly less general).
Proposed restatement: none (already maximal).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | no       | n/a — it is closed data over a concrete ring; no hypotheses to internalise. | — |
|  2 | sequences/metric → filters/topological?                                                               | no       | n/a — purely algebraic. | — |
|  3 | **construct** an object where a **universal-property class** would characterise it?                   | **yes (already done correctly)** | The universal property is realised by `specialize` + `map_specialize`, not asserted as a class. A `class IsUniversalWeierstrass` is *not* warranted — the concrete `ℤ[a₁,…,a₆]` model **is** the canonical representing object; mathlib's idiom for representing objects of such concrete polynomial functors is the explicit construction (cf. `MvPolynomial` adjunctions), plus lemmas (`map_specialize`) witnessing the property. | The explicit model auto-specialises to every `W` via `map`; a class would add nothing the concrete def + `map_specialize` doesn't. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                               | no       | n/a. | — |
|  5 | vector-space/field-specific → modules/(semi)ring weakening?                                           | no — but note the *base* is already the weakest possible (`ℤ`, the initial ring); the **point** of the universal curve is to be over `ℤ` and base-change/specialize down. | n/a | the project already provides `curvePoly`/`curveRing`/`curveField` base changes (lines 167–173). |
|  6 | 1-categorical → higher/∞-categorical (moduli **stack**)?                                              | yes, but **rejected as a modernisation** | One *could* phrase this via the moduli stack `M̄_ell = [Spec ℤ[a₁,…,a₆]/G]` (quotient by `VariableChange`). | This is a *different, much heavier* object requiring stacks infrastructure mathlib does not have. It is not a "restatement" of `curve`; `curve` is the correct affine chart / Weierstrass presentation that the stack is *built from*. Not a generalise-first target. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive group/monoid?                                             | no       | the index `Coeff` is intrinsically a 5-element set (the Weierstrass coefficients); nothing to generalise. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no real organisational improvement).
Reason: the concrete `ℤ[a₁,…,a₆]` model already *is* the representing object; its universal
property is correctly witnessed by `specialize`/`map_specialize` rather than bolted on as a
redundant class. The only "more abstract" alternative (the moduli stack `M̄_ell`) is a strictly
larger object requiring algebraic-stacks infrastructure mathlib lacks, and `curve` would remain
the affine Weierstrass chart underneath it regardless. No Bourbaki-2.0 move here is a genuine
improvement.

---

## Diamond / defeq risk (Phase 4.5) — `def`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | `curve` is a `WeierstrassCurve` *term* (data, in `Type`), not an `instance`/`class`; typeclass search never targets it. |
| 2 | Reducibility leak            | none    | Plain `def`, not `@[reducible]`. The body is unfolded only by explicit `simp [curve]` at the (few) call sites that want it (`Δ_curve_ne_zero`, `map_specialize`); elsewhere it is opaque. Correct sealing. |
| 3 | Non-canonical unfolding      | low     | `simp [curve]` unfolds the record to five `MvPolynomial.X _` terms; this is intentional and local. No global `@[simp]` on `curve`, so no surprise unfolds. |
| 4 | Instance priority collision  | none    | not an instance. |
| 5 | Universe-polymorphism issues | none    | base type is the concrete `MvPolynomial Coeff ℤ : Type`; no universe variables. |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`; it is a bundled record, accessed by field projection. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE / LOW.**
Top risks: none HIGH.
Mitigations: none required.

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder       "universal Weierstrass curve", "generic elliptic curve over polynomial ring"  — no hit (index has no universal-curve construction)
[B] Loogle            `WeierstrassCurve (MvPolynomial _ ℤ)` / `Affine (MvPolynomial _ _)`             — no hit (no decl produces a Weierstrass curve over an MvPolynomial ring)
[C] LeanSearch        "the universal Weierstrass curve over Z adjoin five coefficients"               — no hit
[D] Grep mathlib src  `Universal.curve`, `inductive Coeff`, `MvPolynomial Coeff`, record `{ a₁ := X … }` in `AlgebraicGeometry/EllipticCurve/`  — **no hit**
[E] Name pattern      `def (universal|generic)(Curve|Ring|Weierstrass)`, `universalRing`              — only `RingTheory/Polynomial/UniversalFactorizationRing.lean:537 UniversalCoprimeFactorizationRing` (unrelated)

Searched for both the user's current form and the literature-standard form (general functorial
representing object). **Key finding:** mathlib's `DivisionPolynomial/Basic.lean` (lines 36–38)
*describes in a docstring comment* "the characteristic 0 universal ring `𝓡[X,Y] :=
ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]` … and the associated universal morphism `𝓡[X,Y] → R[X,Y]` mapping
`Aᵢ ↦ aᵢ`" — and cites Katz–Mazur — **but never defines it.** Mathlib's `ψ`/`φ`/`ω` are built
directly over an arbitrary `R`; the universal ring/curve is invoked only as informal motivation,
not as an actual object.

Concluded: **not in mathlib** (all five methods exhausted, including the literature-standard
general form). Mathlib has the *building blocks* (`WeierstrassCurve`/`Affine`, `MvPolynomial`,
`baseChange`, `CoordinateRing`) and a *prose mention* of the concept, but no `def` of the universal
Weierstrass curve, no universal coefficient ring, and no `specialize` homomorphism.

---

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.curve`

Internal use count: **~101** occurrences of `curve` across the project outside the defining file
region (grep over `projects/NagellLutz/**.lean`, excluding the `Universal.lean` header/docstring
lines). Heavily used in:
- `LutzNagell/DivisionPolynomial.lean`, `DivisionPolynomialOmega.lean` — `curve.ψ`, `curve.φ`,
  `curve.ω`, `curve.preΨ₄`, `curve.Ψ₃`, the universal division polynomials.
- `LutzNagell/ZSMul.lean` — `curve.ψ n`, `polyEval … (curve.ψ n)`, `polyToField (curve.ψ n)`,
  `evalEval_ψ`/`evalEval_φ`/`evalEval_ω` (specialization of universal division polys to a concrete
  curve), `ψᵤ` (the universal `ψₙ` in the universal field).
- `Universal.lean` itself — `Universal.Ring := curve.CoordinateRing`, `pointedCurve := baseChange
  curve _`, `curvePoly`/`curveRing`/`curveField`, `specialize`, `map_specialize`,
  `curveRing_map_ringEval`.

External-to-file callers: multiple files in the same project (DivisionPolynomial*, ZSMul). No
inline re-derivation of the universal curve found elsewhere (it is *the* single source of the
object). Downstream-library callers: n/a (project not yet a published dependency).

Signal (per the call-sites table): **K ≫ 3, no inline re-derivation → real API; consumers depend
on it → YES-\* bucket.**

### Composition check

Can `WeierstrassCurve.Universal.curve` be derived from mathlib in ≤3 chained calls?

Attempt 1: `{ a₁ := MvPolynomial.X A₁, …, a₆ := MvPolynomial.X A₆ }` — this *is* the definition;
"composing" it from mathlib means re-typing the record literal at each of the ~101 call sites
(plus re-declaring `inductive Coeff`). That is not a composition of mathlib lemmas — it is the
*definition itself*, and inlining it would (a) require re-introducing the `Coeff` index type
everywhere and (b) destroy the `specialize` / `map_specialize` universal-property API that ~101
sites depend on by name.

Conclusion: **NOT-COMPOSABLE** as a throwaway inline. The record literal is short, but the *object*
(with its index type, its coordinate ring `Universal.Ring`, its fraction field `Universal.Field`,
its specialization homomorphism, and the universal-property lemma) is a genuine named API surface,
not a 1–3-call composition. (Per Phase 6b heuristics: re-typing a data literal at 101 sites with a
supporting index type and universal-property lemmas is "a new development in disguise", not a
`.symm`/`.trans`/single-call composition.)

---

## Verdict: `WeierstrassCurve.Universal.curve`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): unanimous across WebSearch ×6, nLab, nCatLab, Stacks-adjacent,
  arXiv — the *universal/generic Weierstrass curve* over `ℤ[a₁,…,a₆]` is a standard named object;
  the project's form is the maximally general one (base `ℤ`, all five `aᵢ`).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — every alternative (`ℤ[1/6]`, short form,
  moduli stack) is either a strict specialisation or a heavier different object; no generalise-first
  target. Modern-idiom check: no genuine Bourbaki-2.0 improvement.
- Diamond/defeq risk (Phase 4.5): **NONE/LOW** (plain bundled data, no instance, no reducibility
  leak, no coercion).
- Mathlib search (Phase 5): **not in mathlib** — and notably mathlib's `DivisionPolynomial/Basic`
  *names the concept in a docstring* (`𝓡 := ℤ[A₁,…,A₆]`, the universal morphism `Aᵢ ↦ aᵢ`, citing
  Katz–Mazur) without ever defining it.
- Composition check (Phase 6): **NOT-COMPOSABLE** as inline; **~101 internal call sites**, no inline
  re-derivation → real load-bearing API.

**Rationale:**

This is the universal Weierstrass curve — a canonical, named object of the elliptic-curve
literature (Silverman, Katz–Mazur, Hida, Conrad, Parson, the nLab moduli stack, and the explicit
homogeneous-division-polynomial papers all describe exactly the Weierstrass curve over `ℤ[a₁,…,a₆]`
with the coefficients as independent indeterminates). Its universal property — every Weierstrass
curve over every commutative ring is a unique specialization of it (`map_specialize`,
`Universal.lean:194`) — is the textbook characterization, realized faithfully in the project at the
most general level: base ring `ℤ` (so specialization reaches *every* `R` and *every* characteristic)
and the full five-coefficient generalized form. Phase 4 finds nothing to generalise (the alternatives
are specialisations or a heavier stack-theoretic object), and Phase 4.5 finds the def
infrastructurally clean.

The decisive mathlib-gap signal is concrete and citable, not a bare "didn't find it": mathlib's own
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:36–38` **invokes the universal
ring `𝓡[X,Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]` and the universal morphism `Aᵢ ↦ aᵢ` in its docstring** (to
justify that `2 ∣ ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²)` over the char-0 universal ring), citing Katz–Mazur — yet
mathlib never defines this object. It is a recurring "we'd argue via the universal curve" reformulation
that mathlib currently can only gesture at in prose; this project makes it a first-class def plus the
`specialize`/`map_specialize`/`polyEval`/`ringEval` API and the cusp-curve trick (`ψₙ(1,1)=n`) that
proves non-vanishing of the universal `ψₙ`. It is a one-liner *body*, but a one-liner WITH-EXEMPTION:
it is the object that the theorems `map_specialize`, `Δ_curve_ne_zero`, and `curveRing_map_ringEval`
are *named after*, and ~101 downstream uses depend on the stable name. Adding it to mathlib lets the
division-polynomial file replace its prose hand-wave with an actual `simp`-able specialization
argument, and composes directly with `WeierstrassCurve.baseChange`, `CoordinateRing`, and the existing
`ψ/φ/ω` API.

**WHY add it (refactor-actionable):**
- *New mathematical content mathlib is missing:* the universal Weierstrass curve as an actual object,
  its coordinate ring (`Universal.Ring`), its fraction field (`Universal.Field`), and — most
  importantly — the **specialization homomorphism** `W.specialize : ℤ[A₁,…,A₆] →+* R` with
  `Universal.curve.map W.specialize = W`. This is the representing-object / universal-property API for
  Weierstrass curves, which mathlib lacks entirely.
- *The specific gap (named, not asserted):* `DivisionPolynomial/Basic.lean:36–38` describes
  `𝓡[X,Y] := ℤ[A₁,…,A₆][X,Y]` and the universal morphism purely in a docstring to justify a
  divisibility fact, citing Katz–Mazur — a standing TODO-in-prose. The universal curve is the missing
  formal object behind that paragraph.
- *Composition with existing API:* once `curve` and `specialize` exist, `WeierstrassCurve.map` /
  `baseChange` / `map_Δ` / `CoordinateRing` / the `ψ/φ/ω` division polynomials all apply to it
  immediately; "prove a polynomial identity over the universal curve, then specialize" becomes a
  one-line `map_specialize ▸ …` pattern usable throughout the elliptic-curve library.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean` (a new file under
`EllipticCurve/`, imported by `DivisionPolynomial/Basic.lean` so the docstring's `𝓡` becomes the real
object), or folded into `DivisionPolynomial/Basic.lean` directly.
Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): add the universal Weierstrass curve and specialization homomorphism`.
PR grouping: ship `curve` **together** with its inseparable companions from this file — the index type
`WeierstrassCurve.Coeff`, `Universal.Ring`/`Universal.Field`, `WeierstrassCurve.specialize`,
`map_specialize`, and the supporting injectivity lemmas (`algebraMap_poly_injective`,
`algebraMap_injective'`) — as **one** PR; `curve` alone, without `specialize`/`map_specialize`, would
carry no universal-property content and would itself look like an unmotivated one-liner. The cusp-curve
material and `pointedCurve`/`IsElliptic` instance can follow in a second PR.
Pre-PR checklist before opening:
- [ ] `/generalise WeierstrassCurve.Universal.curve` — confirm no further weakening (expected: none; base is already `ℤ`).
- [ ] `/cleanup projects/NagellLutz/LutzNagell/Universal.lean WeierstrassCurve.Universal.curve` — full audit + style/diff gates (this project *forks* mathlib EC files, so reconcile naming with the upstream `DivisionPolynomial` conventions: `Aᵢ` vs `aᵢ`, `𝓡` notation).
- [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the division-polynomial / Weierstrass authors — incl. the `DivisionPolynomial` author and the file's original author Junyan Xu).

---

## Next step

Open a mathlib PR adding `WeierstrassCurve.Universal.curve` **bundled with** `WeierstrassCurve.Coeff`,
`Universal.Ring`/`Field`, `WeierstrassCurve.specialize`, and `map_specialize` (the universal-property
lemmas are what make `curve` worth shipping — do not PR the bare record alone). First run
`/generalise` (confirm maximality) and `/cleanup` on `Universal.lean` to reconcile with the upstream
`DivisionPolynomial` docstring's `𝓡`/`Aᵢ` conventions, then have it land so
`DivisionPolynomial/Basic.lean:36–38` can be upgraded from a prose mention to the real object.
