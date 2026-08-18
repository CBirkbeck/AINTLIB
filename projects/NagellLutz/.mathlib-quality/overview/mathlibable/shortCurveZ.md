## /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ`

### Name resolution

- decl `LutzNagell.LutzNagellTheorem.shortCurveZ`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:25`.

Qualified name VERIFIED from source: `LutzNagell.LutzNagellTheorem.shortCurveZ`
(file opens `namespace LutzNagell` → `namespace LutzNagellTheorem`, line 19–20; the def is named
`shortCurveZ`, line 25). The prompt's guessed `LutzNagell.LutzNagellTheorem.shortCurveZ` is correct.

Kind: `def` (a single anonymous-structure literal).

---

### Statement (unformalised)

> For integers `A B : ℤ`, `shortCurveZ A B` is the Weierstrass curve over `ℤ` with coefficients
> `a₁ = 0`, `a₂ = 0`, `a₃ = 0`, `a₄ = A`, `a₆ = B` — i.e. the short Weierstrass model
> `y² = x³ + A·x + B`.

Lean source:

```lean
/-- The short Weierstrass curve over `ℤ`: `y^2 = x^3 + A*x + B`. -/
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
```

This is a **project-local convenience definition**: a *specific* member of mathlib's
`WeierstrassCurve ℤ` family, picked out by two integer parameters. It carries no new mathematical
content beyond "the structure literal `⟨0, 0, 0, A, B⟩`". Its companion `shortCurveQ A B`
(line 29) is its base change along `algebraMap ℤ ℚ`, and the five `shortCurveZ_aᵢ`
projection lemmas + `shortCurveZ_delta` + `shortCurveQ_equation_iff` are the rewriting API around
it. Downstream Nagell–Lutz files use it as *the* curve to which the classical short-form theorem is
attached.

---

### Size classification

**SMALL — ONE-LINER (`def`).** The body is a single 5-field structure literal. By the def-exemption
spirit a one-line definitional alias biases toward a NO bucket (it is content-free wrapping of an
existing mathlib constructor), unless it introduces a genuinely new abstraction — which it does not.

---

### (1) Literature search

"Short Weierstrass form `y² = x³ + Ax + B`" is utterly standard — Silverman, *The Arithmetic of
Elliptic Curves*, Ch. III (the char ≠ 2,3 normal form); it is the form in which the Nagell–Lutz
theorem is classically stated. There is no named *object* here to find in the literature: it is just
"the elliptic curve with those coefficients". The mathematical weight lives in the **theorems** about
such curves (Nagell–Lutz, the discriminant `Δ = −16(4A³ + 27B²)`), not in the act of writing down
the coefficient tuple.

### (2) Mathlib search — is it there, or a more general form?

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/` already carries the full relevant
infrastructure:

| Method | Query | Result |
|---|---|---|
| [A] exact decl | `WeierstrassCurve.shortCurveZ` / `shortCurve` | **no hit** — `shortCurveZ` is project-local. |
| [B] the *general object* | `structure WeierstrassCurve` | `Weierstrass.lean:77`. `shortCurveZ A B` is literally a value of this structure: `⟨0,0,0,A,B⟩`. The anonymous constructor IS the general constructor. |
| [C] the *short-form abstraction* | `IsShortNF` | `NormalForms.lean:179` — `class IsShortNF` asserts `a₁ = a₂ = a₃ = 0`, "in other words `Y² = X³ + a₄X + a₆`". Full API: `a₂_of_isShortNF`, `b₄/b₆/b₈_of_isShortNF`, `c₄/c₆_of_isShortNF`, and **`Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`** (line 219) — exactly the project's `shortCurveZ_delta`. |
| [D] specific-curve constructors (precedent) | `ofJ0`, `ofJ1728`, `ofJNe0Or1728`, `ofJ` | `ModelsWithJ.lean:44,56,72,134` — mathlib DOES name specific Weierstrass curves *with the same `⟨…⟩` idiom* (`ofJ0 := ⟨0,0,1,0,0⟩`). But each is justified by a **mathematical role** (realising a prescribed j-invariant). `shortCurveZ A B` has no such role — it is the bare 2-parameter coefficient tuple. |
| [E] base-change / map | `WeierstrassCurve.map`, `baseChange` | `Weierstrass.lean:231,236` — these give `shortCurveQ` for free; further evidence the surrounding API is all present. |

So the *general object* (`WeierstrassCurve`), the *short-form property* (`IsShortNF`), and **the exact
discriminant lemma** are all in mathlib. What is NOT in mathlib is the literal name `shortCurveZ`
bound to `⟨0,0,0,A,B⟩` — and there is no reason it should be: it is a one-line alias for the
structure constructor.

### (3) Generality analysis

`shortCurveZ A B` is **strictly less general** than what mathlib already offers:

- It fixes the ring to `ℤ` (mathlib's `WeierstrassCurve R` is over any `CommRing`).
- It fixes `a₁ = a₂ = a₃ = 0` (mathlib's structure is fully general; the short-form constraint is
  captured *as a typeclass* `IsShortNF`, the modern idiom, rather than baked into a bespoke
  constructor).
- It is parameterised by exactly two scalars `A, B` — i.e. it is one orbit of the structure literal.

The project itself confirms the generality gap one layer up: its `lutz_nagell_integrality_general`
(`GeneralMain.lean:110`) and `lutz_nagell_discriminant_general` (`GeneralDiscriminant.lean:187`)
operate on an **arbitrary** `W : WeierstrassCurve ℤ`; `shortCurveZ` exists only so the *classical
short-form statement* of Nagell–Lutz (`lutz_nagell`, `lutz_nagell_integrality_short`) has a curve to
be stated about. The general engine does not need `shortCurveZ` at all.

The modern-idiom point is decisive: the mathlib-native way to say "this curve is in short form" is
`[W.IsShortNF]`, not `def shortCurveZ`. A bespoke specialised constructor is exactly the pattern
mathlib replaced with `IsShortNF` + `ofJ*`.

### (4) Composition check — can ≤3 mathlib calls give it?

**Yes — one.** `shortCurveZ A B` is *definitionally* the anonymous structure constructor:

```lean
shortCurveZ A B  =  ({ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B } : WeierstrassCurve ℤ)
                 =  (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ)        -- 1 mathlib constructor call
```

Every downstream fact the project derives is a one-step specialisation of mathlib:
- `shortCurveZ_delta` ⟸ `WeierstrassCurve.Δ_of_isShortNF` (after providing the trivial
  `IsShortNF` instance from `a₁=a₂=a₃=0`, which are `rfl`).
- `shortCurveQ_equation_iff` ⟸ `WeierstrassCurve.Affine.equation_iff`.
- `shortCurveZ_aᵢ` ⟸ `rfl` / the `IsShortNF` field lemmas.

So the definition composes from mathlib in a single constructor application, and its entire API
composes in ≤1 further mathlib call each. There is nothing to *add*: the abstraction already exists
(`WeierstrassCurve` + `IsShortNF`), and this decl is a thin renaming of an instance of it.

---

### Call sites

`shortCurveZ` is used throughout the Nagell–Lutz short-form layer (≈30+ references across
`ShortWeierstrass.lean`, `Main.lean`, `GeneralMain.lean`, and the overview inventory). All uses are
"the specific curve we are proving the classical theorem about" — internal plumbing for the
short-form deliverable, never a reusable mathematical primitive. Its companion `shortCurveQ` got the
same treatment and the same verdict (see `shortCurveQ.md` → NO-composable-from-mathlib).

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ`

**Category: NO-composable-from-mathlib**

`shortCurveZ A B` is definitionally `(⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ)` — a single application
of mathlib's already-existing `WeierstrassCurve` structure constructor, specialised to `ℤ` and to
short-form coefficients. The abstraction it might represent ("a curve in short Weierstrass form") is
**already in mathlib** as the `WeierstrassCurve.IsShortNF` typeclass, complete with the full b/c/Δ
API — including the exact lemma `Δ_of_isShortNF` that the project re-proves as `shortCurveZ_delta`.
The mathlib-native way to express this object is `(W : WeierstrassCurve ℤ) [W.IsShortNF]` (or, for a
concrete pair, the bare structure literal), not a bespoke 2-parameter `def`. It is therefore a
project-local naming convenience with no upstream value of its own.

- It is **not** `NO-mathlib-has-it`: no single mathlib decl *is* `shortCurveZ` verbatim — it is a
  (defeq) specialisation/composition, not an existing named object.
- It is **not** any YES bucket: it adds no new abstraction (the `WeierstrassCurve`/`IsShortNF`
  machinery it specialises already exists), and a one-line constructor alias is precisely what should
  *not* be upstreamed.
- It is **not** `YES-but-generalise-first`: the more-general object already exists in mathlib; there
  is nothing to generalise toward — generalising it just recovers `WeierstrassCurve` / `IsShortNF`,
  which are already there.
- It is **not** `BORDERLINE`: the composition is exact and trivial (1 constructor call; defeq), so
  the call is clear-cut.

**Note on the wider Nagell–Lutz upstreaming.** The *theorems* stated about this curve are a different
matter: `lutz_nagell_integrality_short` is assessed **YES-add-as-is** (classical named theorem, ship
with its general engine `lutz_nagell_integrality_general`). When that PR family lands, the natural
mathlib phrasing states those results for `(W : WeierstrassCurve ℤ)` (general) and for the short form
via `[W.IsShortNF]` or a concrete `⟨0,0,0,A,B⟩` — the helper `shortCurveZ` does **not** travel
upstream; it is replaced by mathlib's existing constructor + `IsShortNF`.

---

### Sources

- Mathlib `WeierstrassCurve` structure — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:77`
  (and `map`/`baseChange`, lines 231/236).
- Mathlib `IsShortNF` + short-form API incl. `Δ_of_isShortNF` —
  `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:179–243`.
- Mathlib specific-curve constructors `ofJ0`/`ofJ1728`/`ofJNe0Or1728`/`ofJ` —
  `Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean:44,56,72,134`
  ([mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.html)).
- Project source — `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:25`.
- Project general engine subsuming the short form —
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:110`,
  `GeneralDiscriminant.lean:187`.
- Sibling verdicts (consistency): `shortCurveQ.md` (NO-composable-from-mathlib),
  `shortCurveZ_a₂.md` / `shortCurveZ_a₃.md` (NO-composable-from-mathlib),
  `lutz_nagell_integrality_short.md` (YES-add-as-is).
- Background: Silverman, *The Arithmetic of Elliptic Curves*, Ch. III (short Weierstrass normal form;
  Nagell–Lutz).
