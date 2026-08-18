# /mathlibable report — `WeierstrassCurve.Universal.equation_point`

> Step-9 mathlibable assessment (NagellLutz project). Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:138`.

---

## Verdict: **NO-composable-from-mathlib**

> `equation_point` is the witness that the *tautological point* `(X, Y)` of the universal curve's
> coordinate ring lies on the curve. Its entire mathematical content is `AdjoinRoot.mk_self`
> ("the quotient by ⟨P⟩ kills P"), transported through the project-local `polyToField` and
> mathlib's `Affine.map_polynomial`. It is construction-bound plumbing, not an independently
> mathlib-worthy theorem: once the universal-curve **definitions** are in mathlib (the `curve` PR),
> this is a ≤3-call corollary of `polyToField_polynomial` (= `AdjoinRoot.mk_self`) +
> `Affine.map_polynomial`. It should ship *bundled with* `Affine.point`/`pointedCurve` (the second
> universal-curve PR), the way `polyToField` ships with `curve` — but it is not a standalone add.

---

## Baseline (Phase 0)

- lake build:                stale (per task brief; reasoned from source statement + the local mathlib tree under `.lake/packages/mathlib` — instructed fallback).
- decl `WeierstrassCurve.Universal.equation_point`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:138`.
- kind:                      `lemma` (Prop-valued; produces an `Equation` witness).
- has sorry:                 no.
- module docstring summary:  Additions to `Affine.Point` + the **universal elliptic curve** over `ℤ[A₁..A₆]`; defines `Universal.Ring/Field`, `polyToField`, the distinguished point `(X,Y)` (of infinite order), and the cusp-curve trick (`ψₙ(1,1)=n`).

**Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.equation_point`.
Namespace stack: `namespace WeierstrassCurve` (line 69) → `namespace Universal` (line 75); base name
`equation_point` (line 138). The parse-time guess `WeierstrassCurve.Universal.equation_point` is
**correct**.

**Exact statement (source, lines 137–147):**
```lean
open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  show evalEval (polyToField (C X)) (polyToField Y)
    ((curve.map (algebraMap _ Universal.Field)).toAffine.polynomial) = 0
  have h : (evalEvalRingHom (polyToField (C X)) (polyToField Y)).comp
      (mapRingHom <| mapRingHom (algebraMap _ Universal.Field)) = polyToField := by
    ext <;> simp [polyToField, algebraMap_field_eq_comp]
  have : ∀ p, evalEval (polyToField (C X)) (polyToField Y)
      (p.map (mapRingHom (algebraMap _ Universal.Field))) = polyToField p :=
    fun p ↦ congr($h p)
  rw [Affine.map_polynomial, this, polyToField_polynomial]
```
where (from the same file):
- `pointedCurve := curve.baseChange Universal.Field` (line 130), `curve` the universal Weierstrass
  curve over `ℤ[A₁,…,A₆] = MvPolynomial Coeff ℤ` (line 84);
- `Universal.Ring := curve.CoordinateRing = AdjoinRoot curve.polynomial = ℤ[A₁,…,A₆,X,Y]/⟨P⟩`
  (line 96), `Universal.Field := FractionRing Universal.Ring` (line 99);
- `polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)`
  (line 108), `Poly = (MvPolynomial Coeff ℤ)[X][Y]` (line 94);
- `polyToField_polynomial : polyToField curve.polynomial = 0` (line 120), itself proved by
  `AdjoinRoot.mk_self` + `map_zero`.

Note: an **identical** copy of this lemma exists in the HasseWeil project at
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:141` (same file, same author Junyan Xu; the
two projects fork the same universal-curve module). This is intra-AINTLIB duplication, a cleanup
concern, and reinforces that the object is a stable shared API surface.

---

## Statement (Phase 1)

`equation_point` asserts that the **distinguished point** `(x₀, y₀) := (polyToField (C X), polyToField Y)`
satisfies the Weierstrass equation of the universal pointed curve
`pointedCurve = curve.baseChange Universal.Field`. Here `x₀` and `y₀` are the images, in the
*function field* `Universal.Field = Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`, of the two adjoined indeterminates
`X` and `Y` — i.e. the **tautological / generic point** of the curve's own coordinate ring.

Mathematically this is the statement *"the generic point of an affine plane curve lies on the
curve."* It is true **by construction of the coordinate ring**: the coordinate ring is the quotient
`ℤ[A₁,…,A₆,X,Y]/⟨P⟩` of the polynomial ring by the Weierstrass relation `P = W(X,Y)`, so the classes
of `X, Y` satisfy `P(X,Y) ≡ 0`. Formally the proof rewrites the `Equation` (= `evalEval …
polynomial = 0`) by:
1. `Affine.map_polynomial` — the polynomial of a base-changed curve is the mapped polynomial
   (mathlib, `Affine/Basic.lean:270`);
2. the helper `h` / `this` — evaluating the mapped polynomial at `(polyToField (C X), polyToField Y)`
   equals applying `polyToField` to the original polynomial (a `RingHom` factorisation, via
   `algebraMap_field_eq_comp`);
3. `polyToField_polynomial` — `polyToField curve.polynomial = 0`, which **is** `AdjoinRoot.mk_self`
   (the quotient kills the relation) composed with `map_zero`.

Variables / typeclasses (Lean side): **none free** — every object is the fixed concrete
universal-curve datum (`curve`, `Universal.Field`, `polyToField`). It is a closed lemma about a
specific construction.

Hypotheses: none.

Conclusion (math): the generic/tautological point `(X mod ⟨P⟩, Y mod ⟨P⟩)`, pushed into the function
field, lies on the universal curve.
Conclusion (Lean): the `Prop` `pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y)`.

Its sole *raison d'être*: it is the existence witness fed to the affine-point constructor —
`Affine.point := WeierstrassCurve.Affine.Point.mk equation_point` (line 151) — producing the
distinguished point of the universal pointed curve, which (specialised to the cusp curve `Y²=X³`,
where `ψₙ(1,1)=n`) is shown to have **infinite order**, the linchpin of the non-vanishing argument
for the universal division polynomials `ψₙ`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an existence-witness obligation lemma (`(x,y)` is on the curve), not a named mathematical
result, not a `## Main results` entry, not named after a person/place. Its content collapses to
`AdjoinRoot.mk_self`. The *surrounding* universal-curve development is BIG infrastructure; this
particular lemma is a SMALL, construction-bound piece of it (sibling to `polyToField`,
`algebraMap_field_eq_comp`, `polyToField_polynomial` — all of which the family reports bucket NO).

(Per protocol, the literature sweep below is still run, because the *concept* "tautological/generic
point of a coordinate ring lies on the variety" deserves a standard-form check even though the lemma
is small.)

## One-line check (Phase 2b)

Kind is `lemma`, so the formal one-liner-*def* gate is n/a. The body is ~7 lines, but every step is
a single rewrite (`map_polynomial`, a `RingHom` `ext`, `polyToField_polynomial`); there is no genuine
mathematical case-work — it is "unfold `Equation`, push the homomorphism through, apply
`mk_self = 0`." Spirit of the gate: **this is glue around `AdjoinRoot.mk_self`, not content.**
Carried into Phase 6 / Phase 7.

---

## Literature search — protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | universal elliptic curve distinguished point `(X,Y)` satisfies Weierstrass equation / tautological point | yes  | "the distinguished point on a universal elliptic curve naturally satisfies the Weierstrass equation as part of its definition" | Confirms the fact is *definitional*, not a named theorem (MIT 18.783 L2; Wikipedia *Elliptic curve*; F-theory Weierstrass-model notes arXiv:1910.04095). |
|  2 | WebSearch (general / mechanism)  | `AdjoinRoot` quotient polynomial ring tautological generator satisfies defining relation `evalEval = 0` | yes  | `AdjoinRoot f = R[X]/⟨f⟩`; the adjoined root satisfies `f = 0` by construction (`eval₂_root`, `mk_self`) | The general mechanism is mathlib's `AdjoinRoot.mk_self` / `AdjoinRoot.eval₂_root` — the standard library form of "the generator satisfies the relation." |
|  3 | WebSearch (named-after / aliases)| "generic point of a plane curve lies on the curve" / "tautological point of the coordinate ring"        | yes  | classical: a variety's generic point satisfies its defining ideal *by definition* of the coordinate ring | No theorem is *named* for this; it is the defining property of `Spec(R/I)`. |
|  4 | ChatGPT MCP                      | self-contained: is "the tautological `(X,Y)` lies on the universal Weierstrass curve" a standard named theorem, or just `AdjoinRoot.mk_self`? Most general form? | n/a  | —                                                                                    | MCP / Codex server **down** (task brief warned). Substituted by channels 1–3, 6, 8, plus direct mathlib-source reading (Phase 5). |
|  5 | Local references                 | `grep .mathlib-quality/references/`                                                                     | n/a  | directory absent for NagellLutz                                                      | recorded n/a. |
|  6 | nLab                             | generic point / coordinate ring / Spec of a quotient ring                                              | yes  | the generic point of `Spec(R/I)` is the point at which exactly the functions in `I` vanish | `ncatlab.org/nlab/show/generic+point`; this is the abstract content, and it is a *definition*, not a deep theorem. |
|  7 | nCatLab (categorical framing)    | tautological / universal point via representability (Yoneda)                                           | yes (indirect) | the universal point = the identity map `Spec R(W) → Spec R(W)` corresponds to "the point lies on the curve" | The point `(X,Y)` is the *universal element* of the functor of points; "it lies on the curve" is the Yoneda tautology. Confirms BIG-object framing of `curve`, not of this lemma. |
|  8 | Stacks Project (alg geom)        | generic fibre / canonical point of `Proj`/`Spec` of a Weierstrass ring                                 | yes (indirect) | generic point of a Weierstrass fibration is a section satisfying the equation by construction | Same conclusion: definitional, no standalone lemma. |
|  9 | MathOverflow / Math.SE           | covered by #1/#3 — "does the generic point lie on the curve" is folklore/definitional                  | yes  | consensus: yes, by construction of the coordinate ring; nothing to cite             | — |
| 10 | recent arXiv (≤5 yr)             | homogeneous division polynomials via the universal curve `Frac(ℤ[a₁,…,a₆,x,y]/⟨P⟩)`                     | yes  | the universal curve is worked over its function field; the generic point is used implicitly | arXiv:1303.4327, arXiv:1108.3051 — they *use* the generic point but never state "it lies on the curve" as a lemma; it is taken as obvious. |

### Literature summary (Phase 3)

Concept identified as: **"the tautological / generic point of the universal Weierstrass curve lies on
the curve"** — i.e. the images of `X, Y` in the function field `Frac(ℤ[a₁,…,a₆,X,Y]/⟨P⟩)` satisfy the
Weierstrass equation.
Sources agree on the standard form: **yes** — and unanimously characterise it as a **definitional /
tautological** fact (a direct consequence of the coordinate ring being the quotient by `⟨P⟩`), not as
a separately-named theorem. The library-standard mechanism is `AdjoinRoot.mk_self` /
`AdjoinRoot.eval₂_root` ("the adjoined root satisfies the relation").
Most general standard form: for *any* affine variety, the generic point of `R/I` satisfies `I` by
construction; the Weierstrass instance is the case `I = ⟨P⟩`. The project's statement (over base `ℤ`,
full 5-coefficient form) is the maximally general Weierstrass instance.
Disagreement with the literature: **none.** The literature agrees this is "obvious by construction" —
which is *exactly* what its proof says (`polyToField curve.polynomial = 0`, i.e. `mk_self`).

---

## Generality analysis (Phase 4)

Literature-standard form: the generic point of the coordinate-ring quotient satisfies the defining
equation. The Lean lemma is the Weierstrass-over-`Universal.Field` instance.

| # | Parameter / hypothesis              | Current Lean form                                         | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|----------------------------------------------------------|---------------------------------------------------|---------------------|----------------------------------|
| 1 | base ring                           | `ℤ` (universal curve over `ℤ[A₁,…,A₆]`)                  | `ℤ` (canonical — specialises to every ring)       | NO                  | `ℤ` is the initial ring; this is already maximal (matches `curve` being over `ℤ`). |
| 2 | target where the point lives        | `Universal.Field = Frac(curve.CoordinateRing)`           | the function field of the curve                   | borderline          | One could state the analogue at the **coordinate-ring** level `Universal.Ring` (before localising), via `Equation.map (AdjoinRoot.mk _)`; the field version follows by `Equation.baseChange`/`.map` along `algebraMap`. The field statement is what the downstream `Affine.point` needs, so it is the right *target*. (This is a "which layer" choice, not a strict generalisation.) |
| 3 | number of coefficients              | all five `a₁,…,a₆`                                        | all five (generalized form)                       | NO                  | dropping to short form is a specialisation, less general. |
| 4 | abstraction of the statement        | bespoke to `curve` / `polyToField`                       | "generic point of `Spec(R/I)` satisfies `I`"      | YES (in principle)  | The *genuinely general* lemma is **not** about Weierstrass curves at all: it is "the tautological point of any `AdjoinRoot f` / coordinate ring satisfies `f`." But that abstract lemma is `AdjoinRoot.mk_self` / `eval₂_root` — **already in mathlib** (`RingTheory/AdjoinRoot.lean:217,256`). The Weierstrass-specific `equation_point` is the *application*, not the general theorem. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL as a Weierstrass statement**, but the *truly general* form of
its content (row 4) is the already-existing mathlib lemma `AdjoinRoot.mk_self`/`eval₂_root`. So there
is **no Weierstrass-level generalisation to perform** (it is already the universal curve over `ℤ`),
and the abstract generalisation is *already in mathlib*. This is a strong signal toward a NO bucket:
weakening "upward" lands on an existing mathlib lemma; there is no new, more-general statement to add.
Number of Weierstrass-level weakening opportunities: 0.
Proposed restatement: none at the Weierstrass level (the coordinate-ring-vs-field layer is a
target choice, not a generalisation).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                              | Applies? | Proposed reformulation | Downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|--------------------------|
|  1 | "let X be a foo" preamble → typeclass?                                                                | no       | closed lemma, no hypotheses to internalise | — |
|  3 | construct/witness where a **universal-property / generic-point** abstraction would characterise it?   | **yes — and it is the existing mathlib abstraction** | The generic-point fact is already abstracted by `AdjoinRoot.mk_self`/`eval₂_root`. `equation_point` is the Weierstrass *instance* of it; no new abstraction is warranted. | Reusing `AdjoinRoot.eval₂_root` + `Equation.map` *is* the modern idiom. |
|  4 | set-with-predicate → bundled-substructure?                                                            | no       | n/a | — |
|  5 | field-specific → ring/module weakening?                                                               | partial  | The coordinate-ring form (over `Universal.Ring`, no localisation) is a slightly more elementary layer; mathlib's `Equation.map`/`Equation.baseChange` already provide the transport `Ring → Field`. | confirms the lemma is a 1–2-step transport, not new content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it already exists in mathlib** (`AdjoinRoot.mk_self`/`eval₂_root`
for the generic-point content; `Affine.Equation.map` / `Equation.baseChange` for the transport). No
*new* abstraction should be introduced; the right move is to obtain `equation_point` *from* those.

---

## Diamond / defeq risk (Phase 4.5) — `lemma`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond             | none    | a `Prop`-valued lemma, not an instance/class; nothing in instance search. |
| 2 | Reducibility leak             | none    | not `@[reducible]`, not `@[simp]`. |
| 3 | Non-canonical unfolding       | none    | does not unfold anything globally. |
| 6 | Coercion ambiguity            | none    | `Equation` is a plain `Prop`; `polyToField`/`C`/`X` are explicit. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** It is a closed proof of a `Prop`; no infrastructural footprint.

---

## Mathlib search-status (Phase 5)

[A] Lean-Finder / LeanSearch  "tautological point on universal Weierstrass curve", "generic point satisfies Weierstrass equation"  — no hit (mathlib has no universal curve at all).
[B] Loogle                    `WeierstrassCurve.Affine.Equation (?f _) (?f _)` over a `FractionRing`/`CoordinateRing` — no hit producing such an `Equation` witness for a coordinate-ring point.
[C] Grep mathlib src          `equation_point`, `pointedCurve`, `polyToField`, `Universal.Field`, `Universal.curve` in `AlgebraicGeometry/EllipticCurve/` — **no hit** (entire universal-curve apparatus absent).
[D] Grep mathlib src (concept) generic/tautological/canonical *point* of `CoordinateRing` / `AdjoinRoot` of a Weierstrass curve — **no hit**. `Affine/Point.lean` builds `CoordinateRing` and uses `AdjoinRoot.mk_self` inside an *ideal-arithmetic* proof (`Point.lean:356`), but **never** constructs "the point of the curve over its own coordinate/function ring."
[E] Adjacent primitives that DO exist (the composition material):
   - `AdjoinRoot.mk_self` (`RingTheory/AdjoinRoot.lean:217`) and `AdjoinRoot.eval₂_root` (`:256`) — the generic point satisfies the relation. **This is the entire mathematical content of `equation_point`.**
   - `WeierstrassCurve.Affine.map_polynomial` (`Affine/Basic.lean:270`), `Equation.map` (`:275`), `Equation.baseChange` (`:307`), `map_equation` (`:279`) — transport of an `Equation` witness along `map`/`baseChange`.
   - `WeierstrassCurve.Affine.Point.mk` (`Affine/Point.lean:537`) — turns an `Equation` witness into a `Point` (the *consumer*).

Concluded: **the lemma itself is not in mathlib** (mathlib has no universal curve), but **its content
and all its proof ingredients are** — the generic-point fact is `AdjoinRoot.mk_self`, and the
transport to the base-changed curve is `Affine.map_polynomial` / `Equation.map` / `Equation.baseChange`.
What is missing from mathlib is only the *named universal object* `curve`/`polyToField` that this
lemma is phrased over.

---

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.equation_point`

- `Universal.lean:152` — `Affine.point := .mk equation_point` (the distinguished affine point; →
  `Jacobian.point` at line 156 via `fromAffine`).
- `ZSMul.lean:352` — `⟨Affine.equation_iff_nonsingular.mp equation_point, rfl⟩` (used to discharge a
  nonsingularity obligation for the universal point inside the `nsmul` X-coordinate computation).
- `DivisionPolynomial.lean:426` (HasseWeil twin file `Auxiliary/DivisionPolynomial.lean:426`) — same
  `equation_iff_nonsingular.mp equation_point` pattern.
- Duplicate definition: `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:141` (verbatim).

Internal use count: a handful (3–4 genuine consumers), all of the form "feed the witness to
`Point.mk` / `equation_iff_nonsingular`." No inline re-derivation elsewhere — it is the single source
of "the universal point is on the curve." So it is **real, named, load-bearing API** — but its role is
strictly to *produce the distinguished point*; it has no independent downstream use beyond that.

Signal: K small (≈3) and **every** use is `Point.mk equation_point` / `equation_iff_nonsingular.mp
equation_point` → it is the *witness coupled to one object* (`Affine.point`), not a general-purpose
lemma. This points to "ship it with `Affine.point`," i.e. a NO-composable-but-bundled disposition,
not a standalone YES.

### Composition check

Can `WeierstrassCurve.Universal.equation_point` be obtained from mathlib in ≤3 chained calls?

- **From mathlib primitives alone: NO.** The statement *mentions* `pointedCurve`, `polyToField`,
  `Universal.Field` — none of which exist in mathlib. You cannot even *write* the statement against
  mathlib, let alone prove it in ≤3 calls. (Same situation as the sibling `polyToField` /
  `algebraMap_field_eq_comp`, which the family buckets `NO-composable-from-mathlib`.)
- **Given the universal-curve definitions (i.e. once `curve`/`polyToField` are in mathlib): YES,
  trivially.** Its content is `AdjoinRoot.mk_self`, and the proof is a ≤3-step transport:
  `Affine.map_polynomial` → push `polyToField` through (a `RingHom.ext`, one line) →
  `polyToField_polynomial` (= `AdjoinRoot.mk_self ▸ map_zero`). Equivalently, at the coordinate-ring
  layer it is `Equation.map (AdjoinRoot.mk _) ⟨the relation⟩` followed by `Equation.baseChange`/`.map`
  along `algebraMap … Universal.Field`. Either way ≤3 mathlib calls **on top of the universal-curve
  defs**.

Conclusion: **COMPOSABLE conditional on the universal-curve definitions; NOT composable from mathlib
as it currently stands** (because the objects it is phrased over are absent). The decisive point for
the bucket: the lemma carries **no mathematical content of its own beyond `AdjoinRoot.mk_self`** — it
is the construction-bound witness that yields `Affine.point`. It is therefore a **NO-composable**
plumbing lemma that should travel *with* `Affine.point` in the pointed-curve PR, exactly as
`polyToField` travels with `curve`. Per Phase 6b heuristics (`.map`/`baseChange`/single-`ext`
composition off an existing `mk_self`), it is not a "new development in disguise."

---

## Verdict synthesis (Phase 7)

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature (Phase 3): unanimous that "the generic/tautological point lies on the curve" is a
  **definitional** fact, library-standard mechanism `AdjoinRoot.mk_self`/`eval₂_root`; **no
  standalone named theorem** exists for it.
- Generality (Phase 4): maximally general as a Weierstrass statement (base `ℤ`, all five `aᵢ`), and
  the *truly general* form of its content (row 4) is **already in mathlib** (`AdjoinRoot.mk_self`).
  Generalising "upward" lands on an existing lemma → NO signal, not a YES-but-generalise target.
- Risk (Phase 4.5): NONE (closed `Prop` proof, no instance/reducibility footprint).
- Mathlib search (Phase 5): the lemma is not in mathlib (no universal curve), but **its content and
  every proof ingredient are** — `AdjoinRoot.mk_self` (content) + `Affine.map_polynomial` /
  `Equation.map` / `Equation.baseChange` (transport) + `Affine.Point.mk` (consumer).
- Composition (Phase 6): **NOT composable from mathlib as-is** (objects absent), but a ≤3-call
  corollary of `polyToField_polynomial`/`AdjoinRoot.mk_self` + `Affine.map_polynomial` **once the
  universal-curve defs exist**. All ≈3 call sites are `Point.mk equation_point` /
  `equation_iff_nonsingular.mp equation_point` → witness coupled to one object (`Affine.point`).

**Rationale:**

`equation_point` is the witness that the distinguished point `(X, Y)` — the tautological point of the
coordinate ring `ℤ[A₁,…,A₆,X,Y]/⟨P⟩`, pushed into the function field — lies on the universal pointed
curve. Mathematically this is *"the generic point of a plane curve lies on the curve,"* which every
source (MIT 18.783, Wikipedia, the F-theory Weierstrass-model literature, nLab's `generic point`)
treats as **true by construction**, with no separate name. Its proof confirms exactly this: it
collapses to `polyToField curve.polynomial = 0`, i.e. `AdjoinRoot.mk_self` (the quotient kills the
relation) transported through `polyToField` by mathlib's `Affine.map_polynomial`. The genuinely
general statement of its content is *already in mathlib* as `AdjoinRoot.mk_self` / `eval₂_root`;
`equation_point` is the Weierstrass *application* of it, not a new theorem.

Hence it is **not an independently mathlib-worthy lemma**. It belongs to the same construction-bound
plumbing family as `polyToField`, `polyToField_polynomial`, `algebraMap_field_eq_comp` and
`algebraMap_injective'` — every one of which the parallel `/mathlibable` reports place in a NO bucket
(`NO-composable-from-mathlib`). The decisive contrast with the *named object* `curve` (which is
`YES-add-as-is`) is that `curve` introduces a concept of independent standing with a universal
property, whereas `equation_point` introduces no concept — it is a one-witness corollary that exists
solely to construct `Affine.point` (all ≈3 uses are `Point.mk equation_point` /
`equation_iff_nonsingular.mp equation_point`).

This is a **borderline NO** in the precise sense recorded for `polyToField`: the lemma is real,
named, and load-bearing *within the universal-curve API*, and it absolutely should accompany that API
into mathlib — but **bundled** with the `Affine.point` / `pointedCurve` definitions (the *second*
universal-curve PR that the `curve.md` report defers: *"The cusp-curve material and
`pointedCurve`/`IsElliptic` instance can follow in a second PR"*), not as a standalone `feat`. On its
own, against today's mathlib, it is non-composable (you cannot state it) and once the objects exist it
is a ≤3-call `mk_self`/`map_polynomial` corollary — in neither reading is it a self-justifying mathlib
addition.

**WHY NO-composable (not YES-add-as-is, not YES-but-generalise):**
- *No independent content:* the lemma = `AdjoinRoot.mk_self` (already in mathlib) + a one-line
  homomorphism push + `Affine.map_polynomial` (already in mathlib). The general form of its content
  is an *existing* mathlib lemma, so there is nothing new to *add* and nothing to *generalise*.
- *Witness coupled to one object:* every call site is `Affine.Point.mk equation_point` or
  `equation_iff_nonsingular.mp equation_point`; it exists to build `Affine.point`. It should ship as
  part of that object's PR, like `polyToField` ships with `curve`.
- *Not composable from mathlib as it stands* only because `pointedCurve`/`polyToField`/`Universal.Field`
  are absent — i.e. the gap is the *object*, already captured by the `YES-add-as-is` verdict on
  `curve`, not by this lemma.

**Bundling / refactor-actionable note:**
- Ship `equation_point` **with** `Affine.point`, `Jacobian.point`, `pointedCurve`, and the
  `IsElliptic` instance, in the *pointed-universal-curve* PR that follows the base `curve` +
  `specialize` PR. In mathlib these would live in the proposed
  `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean`.
- When porting, **prefer deriving it from mathlib's `Affine.Equation.map` / `Equation.baseChange` +
  `AdjoinRoot.mk_self`** rather than the bespoke `evalEvalRingHom` `ext` argument used here — i.e.
  the coordinate-ring point is on `curveRing` via `Equation.map (AdjoinRoot.mk curve.polynomial)`
  (whose hypothesis is `mk_self`), then `Equation.baseChange`/`.map` along `algebraMap … Universal.Field`.
  This is the modern-idiom (Phase 4c) realisation and removes the dependency on the glue lemma
  `algebraMap_field_eq_comp`.
- Cleanup (intra-AINTLIB): `equation_point` is **duplicated verbatim** in HasseWeil
  (`Auxiliary/Universal.lean:141`); the two universal-curve forks should be de-duplicated into a
  shared `Common/` module (a `main`-side `/cleanup` concern, independent of the mathlib question).

---

## Next step

Do **not** open a standalone mathlib PR for `equation_point`. Fold it into the pointed-universal-curve
PR (after the base `WeierstrassCurve.Universal.curve` + `specialize` PR lands), alongside
`Affine.point` / `Jacobian.point` / `pointedCurve` / `IsElliptic`. In that PR, re-derive it from
`AdjoinRoot.mk_self` + `Affine.Equation.map` / `Equation.baseChange` (dropping the bespoke
`algebraMap_field_eq_comp` glue). Separately, file a `main`-side `/cleanup` ticket to de-duplicate the
identical NagellLutz/HasseWeil copies into `Common/`.
