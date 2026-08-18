## /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ_a₄`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; decl elaborates, proof is `rfl`)
- decl `LutzNagell.LutzNagellTheorem.shortCurveZ_a₄`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:35`
- kind:                      lemma (theorem-kind → Phase 4.5 skipped)
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B` over ℤ and its
  base change to ℚ, plus basic rewriting lemmas (coefficients, equation, discriminant). Downstream
  Lutz–Nagell files import this instead of re-expanding `Δ`/`Equation`.

Qualified name VERIFIED from source: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₄`
(namespaces `LutzNagell` → `LutzNagellTheorem` at ShortWeierstrass.lean:19–20; lemma name
`shortCurveZ_a₄` at line 35). The parsed guess in the task header is correct.

Exact source text:
```lean
@[simp] lemma shortCurveZ_a₄ (A B : ℤ) : (shortCurveZ A B).a₄ = A := rfl
```
with
```lean
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
```

---

### Statement (Phase 1)

`shortCurveZ_a₄` states that the `a₄` Weierstrass coefficient of the project-local short curve
`shortCurveZ A B` equals the supplied parameter `A`:

> For all `A B : ℤ`, `(shortCurveZ A B).a₄ = A`.

Here `shortCurveZ A B : WeierstrassCurve ℤ` is the **project-local** definition
`{ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }`, i.e. the curve `y² = x³ + A·x + B`. The lemma is
the fourth of five sibling field-accessor `@[simp]` lemmas (`_a₁`…`_a₆`); it reads back the value of
the `a₄` field, which was *defined* to be `A`. Proof: `rfl` (pure structure projection).

**Distinction from the `=0` siblings.** Whereas `_a₁/_a₂/_a₃` assert that a coefficient is `0` (the
*defining property* of short form), `_a₄` reads back the **injected parameter** `A`. This matters for
the mathlib comparison: mathlib's short-normal-form typeclass `IsShortNF` fixes only `a₁=a₂=a₃=0` and
leaves `a₄` (and `a₆`) entirely free — so there is no mathlib statement "`a₄` of a short-NF curve
equals …" to compare against. `_a₄` is purely a read-back of the local constructor's own field.

Variables (Lean side):
- `A B : ℤ` — the coefficients of the short curve (mathematical role: the linear coefficient `A` and
  constant term `B` of `y² = x³ + A·x + B`).

Hypotheses: none.

Conclusion (math): the coefficient `a₄` of `y² = x³ + Ax + B` is `A`. True by definition of the
constructor.

Conclusion (Lean): `(shortCurveZ A B).a₄ = A`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a trivial `@[simp]` field-accessor lemma (`rfl`) about a project-local definition; not a new
structure, not a named theorem, not a `## Main results` entry.

(Note: literature width run EXHAUSTIVE regardless of SMALL, per the skill.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`).
One-liner verdict: n/a — kind is `lemma`, not `def`. (The Phase-2b exemption table gates `def`/`abbrev`/
`structure`; a `rfl` *lemma* is by nature a one-liner.) Recorded as a note: this is a glue/projection
lemma.

This is a **glue lemma** in the skill's technical sense (body `:= rfl`) about the parent
`def shortCurveZ`. Its verdict is governed by the status of that parent definition, and aligns with the
sibling reports for the identical-constructor accessors.

(Sibling precedent in this same directory: `shortCurveZ_a₁.md`, `shortCurveZ_a₂.md`, `shortCurveZ_a₃.md`
assessed the `a₁/a₂/a₃` accessors of the identical `shortCurveZ` definition — all three landed
**NO-composable-from-mathlib**. This report independently re-runs the protocol for `a₄` and confirms the
same verdict; the `a₄`-specific wrinkle — it reads the injected parameter `A`, not `0`, so mathlib's
`IsShortNF` has *nothing even analogous* — is noted under Phase 5.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | short Weierstrass `y²=x³+Ax+B`, discriminant `Δ=-16(4A³+27B²)`, coefficient `a₄=A`      | yes  | reduced/short form `y²=x³+Ax+B`; `a₄=A`, `a₆=B`         | Stanford crypto notes, UChicago REU (Kline), Fiveable, Wikipedia "Elliptic curve" — universally standard; `A` is the linear coefficient, `a₄`; reduction needs char ≠ 2,3 |
|  2 | WebSearch (general form)         | general Weierstrass `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆`, role of `a₄`; Nagell–Lutz integrality | yes  | `a₄` = coefficient of the linear `x` term; short form keeps it as `A` | the `aᵢ` naming is Tate/Silverman standard; `a₄` is the genuine field, not a derived quantity |
|  3 | WebSearch (named-after/aliases)  | "reduced Weierstrass form" / "short form" coefficient `a₄` / linear coefficient `A`     | yes  | same as #1; `a₄`↔`A` is the renaming convention        | name varies (short/reduced; `A` vs `a₄`); the *fact* `a₄=A` is by-construction, never a named lemma |
|  4 | ChatGPT MCP                      | (Codex MCP errored at call time — fallback to WebSearch #1–#3 + direct mathlib source reading) | n/a  | covered by #1–#3 + Phase 5 mathlib source              | "a₄ = A in the constructor" is definitional bookkeeping; no source elevates a per-constructor accessor to a citable result |
|  5 | Local references                 | `.mathlib-quality/references/` for "short Weierstrass" / "Nagell"                       | n/a  | directory absent (`references/` does not exist under `projects/NagellLutz/.mathlib-quality/`) | no PDF to consult; the accessor of a specific constructor is not a literature object anyway |
|  6 | nLab                             | "Weierstrass curve" / "elliptic curve" short form, coefficients                         | n/a  | nLab treats elliptic curves abstractly; no per-field accessor for a literal curve | not the level nLab works at |
|  7 | nCatLab (categorical)            | —                                                                                      | n/a  | not a categorical concept                              | a structure-field value, no categorical content |
|  8 | Stacks Project (alg geom)        | Weierstrass equation coefficients `a₄`                                                  | n/a  | Stacks has Weierstrass eqns but not "the a₄ field of THIS constructor equals A" | such a lemma is an implementation detail, not a Stacks tag |
|  9 | MathOverflow / Math.SE           | short Weierstrass `a₄` linear coefficient                                               | n/a  | only confirms #1 (definitional)                        | no MO/SE question treats this as nontrivial |
| 10 | recent arXiv (last 5 yrs)        | Nagell–Lutz / Weierstrass group-law formalization; Selmer-group computations            | yes  | formalization & Selmer papers manipulate `aᵢ` fields directly | none ship a named per-constructor accessor lemma; `aᵢ` reads are `rfl`/`simp` housekeeping |

### Literature summary (Phase 3)

Concept identified as: the **`a₄` coefficient of the short (reduced) Weierstrass form `y²=x³+Ax+B`
equals the linear coefficient `A`** — i.e. the constructor stores `A` in the `a₄` slot.
Sources agree on the standard form: **yes** — short Weierstrass form is universally
`y² = x³ + a₄·x + a₆` with `a₁=a₂=a₃=0`; the linear coefficient is `a₄` (often renamed `A` or `a`), the
constant is `a₆` (renamed `B` or `b`). The identity `a₄ = A` is just the naming dictionary between the
`A,B` presentation and Tate's `aᵢ` presentation.
Most general standard form: there is no "general" form — `a₄ = A` is definitional bookkeeping, not a
theorem with hypotheses. No source states "the a₄-accessor of a particular curve constructor" as a
result; it is a definitional unfolding, settled by `rfl`.
Generality dimensions where the literature varies:
  - underlying ring/field: the *reduction to* short form needs char ≠ 2,3, but here the curve is
    *constructed* with `a₄ := A` over ℤ, so the value is `A` over *any* base — no char hypothesis is
    even relevant. The lemma sits below the level at which generality is meaningful.
Disagreement with the literature: none. The lemma is true and trivially so; the literature does not
treat per-constructor field accessors as named objects.

---

### Generality analysis — `shortCurveZ_a₄`

Literature-standard / mathlib-idiom anchor (from Phase 3 + Phase 5): the short form is modelled in
mathlib by the **typeclass** `WeierstrassCurve.IsShortNF` (members `a₁ = 0`, `a₂ = 0`, `a₃ = 0`).
Crucially, `IsShortNF` says **nothing about `a₄`** — `a₄` is a free field. So unlike the `=0` siblings
(which shadow `a₁_of_isShortNF`/`a₂_of_isShortNF`/`a₃_of_isShortNF`), there is **no** mathlib theorem
`a₄_of_isShortNF` to compare to: `a₄` is exactly the data the short form leaves free.

| # | Parameter / hypothesis | Current Lean form              | Literature / mathlib-idiom form                    | Weaker form? | Reason |
|---|------------------------|--------------------------------|----------------------------------------------------|--------------|--------|
| 1 | `A B : ℤ`              | concrete literal curve over ℤ  | `W : WeierstrassCurve R` (no `IsShortNF` member constrains `a₄`) | n/a          | `a₄` is a *free field*; "`(shortCurveZ A B).a₄ = A`" is a read-back of the local constructor, not an instance of any general mathlib statement |

### Generality verdict (Phase 4b)

The current form is: **NOT a specialisation of any more-general mathlib statement** about `a₄`. It is a
projection of the project-local constructor onto its own input `A`. This is therefore NOT
`YES-but-generalise-first` (there is no more-general literature/mathlib statement of which this is the
narrow case — `IsShortNF` deliberately leaves `a₄` free). The only "generalisation" would be to stop
using a concrete constructor and work with `W : WeierstrassCurve R` directly, in which case `a₄` is just
a field read (`W.a₄`) needing no lemma at all.
Number of weakening opportunities: 0 meaningful (the value `A` is base-ring-agnostic already; there is
nothing to weaken in a read-back of an injected parameter).
Cost of restatement: n/a — no restatement wanted; the right move (if any) is deletion/inlining (Phase 7).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                                   | partially | work with `W : WeierstrassCurve R` directly (mathlib's `IsShortNF` idiom for the `=0` facts); then `a₄` is the field `W.a₄`, no lemma needed | mathlib's whole short-NF API — but note `IsShortNF` does NOT cover `a₄`, so this lemma has no `IsShortNF` analogue |
|  2 | sequences/metric → filters/topology?                                    | no — no analysis content | — | — |
|  3 | construct → universal-property class?                                   | no — it's a field read | — | — |
|  4 | set+closure-predicate → bundled substructure?                           | no | — | — |
|  5 | vector-space/field-specific → weaken typeclass?                         | no — value is `A` over any ring | — | — |
|  6 | 1-categorical → higher-categorical?                                     | no | — | — |
|  7 | concrete index (ℤ) → arbitrary monoid/group?                            | no — `a₄ := A` is the injected parameter, not an index to generalise | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no new idiom to contribute.** The contemporary mathlib way to talk about
short curves is the `IsShortNF` typeclass, but it intentionally constrains only `a₁,a₂,a₃`; the value of
`a₄` is *free data*, never the subject of a mathlib lemma. So `shortCurveZ_a₄` does not correspond to
any mathlib reformulation — it is a read-back of a project-local constructor's own field. This does NOT
push toward `YES-but-generalise-first`: there is no better-formed *new* decl to contribute (mathlib
deliberately leaves `a₄` unnamed). It reinforces `NO`.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (a `Prop`-valued `rfl` lemma introduces no typeclass-search path and
no new definitional equality beyond the one `rfl` already witnesses).

---

### Mathlib search-status: `shortCurveZ_a₄`

[A] Lean-Finder       "a₄ coefficient short Weierstrass curve constructor"   no hit for a per-constructor accessor; nearest concept is `IsShortNF` — which does NOT constrain `a₄`
[B] Loogle            `?W.a₄ = ?A` / `WeierstrassCurve.a₄ = _`               hits about `a₄` are `variableChange_a₄`, `map_a₄`, the char-3/2-NF lemmas `a₄_of_isCharThreeJNeZeroNF`/`a₄_of_isCharTwoJNeZeroNF` (these force `a₄ = 0` under extra hypotheses). NO `a₄_of_isShortNF` exists — `IsShortNF` leaves `a₄` free
[C] LeanSearch        "a₄ of short normal form Weierstrass curve"            hits: `WeierstrassCurve.IsShortNF`, `a₁/a₂/a₃_of_isShortNF` — but none for `a₄` (confirming `a₄` is unconstrained by short form)
[D] Grep mathlib src  `a₄` accessor lemmas in `Mathlib/AlgebraicGeometry/EllipticCurve/` →
                      `NormalForms.lean`: `IsShortNF` (members `a₁,a₂,a₃` only — NO `a₄`), `a₄_of_isCharThreeJNeZeroNF:301`/`a₄_of_isCharTwoJNeZeroNF:470` (`a₄=0` under char-NF hyps); `Weierstrass.lean`: `map_a₄` (`@[simps]`-generated). NO `…_a₄ = <param> := rfl` for any concrete constructor anywhere (checked `ofJ0`/`ofJ1728`/`ofJNe0Or1728`/`ofJ` in ModelsWithJ.lean — they ship only derived-invariant lemmas `ofJ0_c₄`, `ofJ0_Δ`, NOT bare `a₄`/`a₆` accessors)
[E] Name pattern      grep `shortCurveZ` / `shortCurve_a` / `_a₄ = … := rfl` in mathlib   no hits — `shortCurveZ` is project-local; the only `…_a₄ = … := rfl` accessors in mathlib are `VariableChange.variableChange_a₄` and the `@[simps]` `map_a₄` (accessors of genuine algebraic operations `C • W` / `W.map f`, not one-off literals)

Searched for both:
  - the user's current form (`(shortCurveZ A B).a₄ = A`) — **not in mathlib**; `shortCurveZ` doesn't
    exist there, and mathlib ships no concrete short-curve-from-(A,B) constructor.
  - the literature-standard / general form — there is **none for `a₄`**: mathlib's short-form abstraction
    (`IsShortNF`) constrains only `a₁,a₂,a₃` and leaves `a₄` free, so there is no general "`a₄` of a short
    curve" statement to be a specialisation of. (Contrast the `=0` siblings, which *do* shadow
    `a₁/a₂/a₃_of_isShortNF`.)

Concluded: **building blocks present (project-local def + `rfl`); no mathlib statement of this form
exists**, because (i) the subject `shortCurveZ` is project-local, and (ii) `a₄` is precisely the field
mathlib's short-form API leaves unconstrained. The lemma is a definitional unfolding of the project's own
constructor, discharged by `rfl` / `simp [shortCurveZ]` in one step. Not a candidate for mathlib; it is a
≤1-call composition / definitional unfolding to inline.

Note on the project's mathlib-fork: this project forks
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, and carries duplicated `General*`/`PID*` tracks —
but NONE of that touches this lemma. `shortCurveZ` / `shortCurveZ_a₄` are genuinely new project-local
glue (the def + its five accessors live only in `ShortWeierstrass.lean`); they are not a fork of any
mathlib decl. The relevant mathlib file here is `NormalForms.lean` (the upstream `IsShortNF` API), which
the project does NOT fork — it simply chose a concrete constructor and, for `a₄`, named a fact mathlib
never names.

---

### Call sites — `shortCurveZ_a₄`

Internal use count: **0** (within the project, excluding the declaring file) — the *name*
`shortCurveZ_a₄` appears nowhere outside its declaration line.
External-to-file callers: **0** distinct files for `a₄` specifically.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | `shortCurveZ_a₄` does not appear in any `simp only […]` set or term in the project |

Inline-derivation grep (was the equivalent re-derived elsewhere without the lemma?): none. No site reads
the `a₄` field of `shortCurveZ` at all — the downstream proofs only need the `=0` coefficients
(`shortCurveZ_a₁`, `shortCurveZ_a₃` appear in `simp only` sets at `GeneralMain.lean:167`, `Main.lean:54`,
`Main.lean:57`) and the discriminant (`shortCurveZ_delta`). `grep -rn shortCurveZ_a₄ --include=*.lean`
returns exactly the single declaration line.

Signal (per the Phase-6.0 table): **K = 0 internal uses, no inline re-derivation.** For an ordinary def
this would flag "dead code / brand-new-unused"; here it is benign and expected. `shortCurveZ_a₄` is the
fourth member of a **deliberately complete five-accessor `@[simp]` bundle** (`_a₁`…`_a₆`) generated by
hand for the `shortCurveZ` constructor. Bundle completeness/symmetry is the reason it exists even though
the `a₄` coefficient happens not to be read in the current proofs (downstream Lutz–Nagell reasoning uses
the discriminant `shortCurveZ_delta` and the vanishing coefficients, not `a₄` in isolation). Because it
is a `@[simp]` lemma, it is also available to fire automatically in any future `simp` that encounters
`(shortCurveZ _ _).a₄`. The K = 0 count does not lift it toward YES (its subject cannot go to mathlib);
it just confirms there are zero named-call sites to update if the bundle is ever folded into the def's
`simp` set.

---

### Composition check (Phase 6)

Can `shortCurveZ_a₄` be derived from mathlib (or trivially) in ≤3 chained calls?

Attempt 1: `rfl` — succeeds. `(shortCurveZ A B).a₄` reduces definitionally to the field literal `A`.
  - Mathlib decls used: none needed (definitional).
  - Result: **succeeds** (0 calls).

Attempt 2 (idiomatic inline at any future call site): `simp [shortCurveZ]` — succeeds; unfolds the local
def and reads the `a₄ := A` field directly. Needs no separate lemma.
  - Result: **succeeds** (1 simp call).

Attempt 3 (mathlib-routed): **not available** — mathlib has no statement about the `a₄` of a short-form
curve (`IsShortNF` leaves `a₄` free; there is no `a₄_of_isShortNF`). So unlike the `=0` siblings, there
is no mathlib lemma to route through; the only derivation is the definitional one above.
  - Result: n/a (no applicable mathlib lemma; reinforces that this is pure local definitional unfolding).

Conclusion: **COMPOSABLE** — trivially (`rfl`, or `simp [shortCurveZ]`). No new lemma is required, and —
unlike `curveQ_a₃` — there is no verbatim mathlib lemma that already states it, so the precise bucket is
NO-composable-from-mathlib (not NO-mathlib-has-it).

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₄`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): "`a₄ = A` in short Weierstrass form" is *definitional bookkeeping* — the
  naming dictionary between the `A,B` presentation and Tate's `aᵢ` fields; never a named result. No
  source treats a per-constructor field accessor as an object.
- Generality analysis (Phase 4): NOT a specialisation of any general mathlib statement — mathlib's
  `IsShortNF` constrains only `a₁,a₂,a₃` and leaves `a₄` free, so there is no `a₄_of_isShortNF` for this
  to specialise. Hence not YES-but-generalise-first, and not NO-mathlib-has-it.
- Mathlib search (Phase 5): the user's form is NOT in mathlib (subject `shortCurveZ` is project-local);
  and there is **no general mathlib `a₄`-of-short-form statement** either (verified: `IsShortNF` has no
  `a₄` member; no concrete mathlib constructor — `ofJ0`/`ofJ1728`/… — ships a bare `a₄` accessor `:= rfl`).
- Composition check (Phase 6): COMPOSABLE — discharged by `rfl` / `simp [shortCurveZ]` in one step.

**Rationale:**

`shortCurveZ_a₄` is a `@[simp]` glue lemma (`:= rfl`) reading off the `a₄` field of the **project-local**
definition `shortCurveZ A B := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }`, recovering the injected
parameter `A`. It cannot go to mathlib because its subject, `shortCurveZ`, is not a mathlib object:
mathlib has no concrete "short curve over ℤ from `(A,B)`" constructor, and on purpose — it models the
short form by the **`IsShortNF` typeclass** (`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean`,
`class IsShortNF` with members `a₁,a₂,a₃ = 0`). Notably, `IsShortNF` says nothing about `a₄` (it is free
data), so — unlike the `=0` siblings `shortCurveZ_a₁/_a₂/_a₃`, which shadow the existing
`a₁/a₂/a₃_of_isShortNF` — there is no general mathlib statement of which `(shortCurveZ A B).a₄ = A` is a
specialisation. The only mathlib `…_a₄ := rfl` accessors (`VariableChange.variableChange_a₄`, the
`@[simps]`-generated `map_a₄`) are for genuine algebraic operations (`C • W`, `W.map f`), not one-off
literals; and mathlib's own concrete curve constructors (`ofJ0`, `ofJ1728`, `ofJ`) deliberately ship
*derived-invariant* lemmas (`ofJ0_c₄`, `ofJ0_Δ`) but no bare `a₄`/`a₆` field accessors — confirming such
per-constructor projections sit below mathlib's lemma-granularity bar. The lemma is true and is a clean
member of the project's five-accessor `@[simp]` bundle, but it is a 0–1-call definitional unfolding of a
local def: the building block (the def itself, plus `rfl`) is already present, so the form belongs at the
(future) call site or as a local convenience bundle, not in the library.

(It is NOT `NO-mathlib-has-it`: mathlib does not have *this* statement and — for `a₄` — has no general
analogue either (contrast the sibling `curveQ_a₃`, which IS `NO-mathlib-has-it` because `curveQ = W.map …`
and mathlib's `@[simps]`-generated `map_a₃` states it verbatim in general form). And it is NOT
`YES-but-generalise-first`: there is no better-formed general statement to contribute — mathlib chose, by
design, not to name a short curve's `a₄`.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks — namely the project's own `def shortCurveZ` (whose `a₄` field is the
literal `A`) and definitional `rfl`. The exact statement is a 0–1-call definitional unfolding. There is
no mathlib lemma to *re-aim* at for `a₄` (mathlib's `IsShortNF` leaves `a₄` free), so this is squarely the
NO-composable case rather than NO-mathlib-has-it.

Mathlib building blocks / local primitives:
- `LutzNagell.LutzNagellTheorem.shortCurveZ` (the local def; field `a₄ := A`) — `ShortWeierstrass.lean:25`
- definitional `rfl`
- (general short-form API, for context only — does NOT cover `a₄`) `WeierstrassCurve.IsShortNF` —
  `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean` (`class IsShortNF`)

Composition sketch (≤3 lines):
```lean
example (A B : ℤ) : (shortCurveZ A B).a₄ = A := rfl
-- or, at any future call site, replace `shortCurveZ_a₄` in the simp set with the def itself:
--   simp only [shortCurveZ, …] -- unfolds the def, reads a₄ = A directly
```

Call sites in our project (from Phase 6.0): **K = 0** (no named uses outside the declaring file).
Refactor plan (NOTE — project-policy caveat below; do NOT mechanically apply):
There are zero named call sites to touch. If a cleaner ever wants to reduce surface area, the five
`shortCurveZ_a*` accessors can be dropped in favour of folding `shortCurveZ` itself into each relevant
`simp only […]` set (the def unfolds in place; for `a₄` this is moot today since no site reads it). But
keeping the five-accessor `@[simp]` bundle complete and symmetric is idiomatic and recommended.

Next action: **none required for mathlib.** This is a local convenience `@[simp]` accessor about a
project-local definition; it is correctly placed in the project and should NOT be upstreamed. Mathlib
deliberately does not name a short curve's `a₄`. Verdict is consistent with the sibling reports
`shortCurveZ_a₁.md` / `shortCurveZ_a₂.md` / `shortCurveZ_a₃.md` (all NO-composable-from-mathlib); `a₄`
differs only in that even the *general* fact is absent from mathlib (it reads an injected parameter rather
than `0`), which keeps it firmly in NO-composable rather than NO-mathlib-has-it.

---

## Next step

No mathlib action. Keep `shortCurveZ_a₄` as a project-local `@[simp]` accessor in the `shortCurveZ`
five-accessor bundle (or optionally, if the bundle is ever retired, inline `simp [shortCurveZ]`). Nothing
to upstream: mathlib has no concrete short-curve constructor and, by design, no `a₄`-of-short-form lemma.
