# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.algebraMap_comp_smulRing`

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task note — reasoning from source)
- decl `WeierstrassCurve.Universal.Jacobian.algebraMap_comp_smulRing`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/ZSMul.lean:420`
- namespace stack verified:  `WeierstrassCurve` (L76) → `Universal` (L86) → `Jacobian` (L395)
  ⇒ qualified name **`WeierstrassCurve.Universal.Jacobian.algebraMap_comp_smulRing`** ✓
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  ZSMul.lean proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P` in
  Jacobian coords equals `(φₙ, ωₙ, ψₙ)` evaluated at `(x,y)`, via a *universal* pointed
  Weierstrass curve over `MvPolynomial Coeff ℤ` and its coordinate ring / fraction field.

Source text:
```lean
/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl
```

---

### Statement (Phase 1)

`algebraMap_comp_smulRing` asserts a **commuting-triangle bookkeeping identity** for the three
families of division polynomials of the *universal pointed Weierstrass curve*:

Post-composing the canonical ring homomorphism `algebraMap : Universal.Ring → Universal.Field`
(the localization map `R[W] → Frac(R[W])` of the universal coordinate ring into its fraction
field) with the universal-**ring** division-polynomial triple `smulRing n = (φₙ, ωₙ, ψₙ)
mod the Weierstrass polynomial` yields exactly the universal-**field** triple
`smulField n = polyToField(φₙ, ωₙ, ψₙ)`.

In one line: `algebraMap_{R[W] → Frac R[W]} ∘ (AdjoinRoot.mk ∘ smulPoly n) = polyToField ∘ smulPoly n`.

This is **not a theorem of mathematics**; it is a Lean-internal compatibility/glue fact between
two ways of viewing the same `Fin 3 → •` tuple, true because
`polyToField := (algebraMap Universal.Ring Universal.Field).comp (AdjoinRoot.mk _)` *by definition*.

Variables / typeclasses involved (Lean side):
- `n : ℤ` — the multiplier index of the division-polynomial family.
- Implicit project-local context: `Universal.curve : WeierstrassCurve (MvPolynomial Coeff ℤ)`,
  `Universal.Ring := curve.CoordinateRing` (an `AdjoinRoot`), `Universal.Field := FractionRing Universal.Ring`,
  `polyToField : Poly →+* Universal.Field`, `smulPoly`, `smulRing`, `smulField`.

Hypotheses (Lean side): none beyond `n : ℤ`.

Conclusion (math): the localization map carries the ring-level division-polynomial triple to the
field-level one (a definitional compatibility).
Conclusion (Lean): `algebraMap Universal.Ring Universal.Field ∘ smulRing n = smulField n`
(an equality of functions `Fin 3 → Universal.Field`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `rfl`-proved compatibility lemma between two project-local `abbrev` families; not a
named theorem, not a new structure, not a `## Main results` entry (the main result is the
top-level `zsmul_eq_smulEval`).

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`ext i; fin_cases i <;> rfl`).
This is a **lemma**, so the def-oriented one-liner gate does not strictly apply — but the spirit
does: the proof is *pure definitional unfolding* over a 3-element index. Treated as a one-liner
for the verdict bias.

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|---------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | Body is `rfl`; the lemma *exposes* the defeq rather than sealing it. No `@[reducible]`/`@[irreducible]`. No downstream proof relies on it being opaque. |
| Avoid typeclass diamonds         | no       | No instance is anchored by this lemma; it is a plain functional equality. |
| Mark semantic intent / API name  | no       | No docstring; **zero** consumers in the project (see Phase 6.0). Name is not depended on. |

Conclusion: **ONE-LINER (lemma) WITHOUT-EXEMPTION** — biases the verdict toward NO.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "universal elliptic curve division polynomial coordinate ring fraction field smulRing smulField Junyan Xu" | no   | —                                | Returned SageMath generic-ring docs + division-polynomial papers; **no `smulRing`/`smulField`** anywhere — these are project-internal names. |
|  2 | WebSearch (general form)         | "division polynomials elliptic divisibility sequence universal Weierstrass curve coordinate ring AdjoinRoot Lean mathlib" | partial | The *objects* (ψₙ, φₙ, ωₙ, R[W], EDS) are standard; mathlib defines them in `DivisionPolynomial/Basic.lean` | But the **commuting-triangle glue lemma** itself appears nowhere in the literature — it is Lean bookkeeping, not mathematics. |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2; the lemma has no mathematical name — it is `algebraMap ∘ mk = polyToField`-pointwise) | n/a  | —                                | A "localization map commutes with a chosen lift" fact is folklore, never stated as a named result. |
|  4 | ChatGPT MCP                      | (unavailable this session — task note: ChatGPT MCP may be down; used WebSearch ×2 + mathlib-source + nLab/Stacks fallbacks) | n/a | — | Fallback channels below cover the standard-form question. |
|  5 | Local references                 | `ls .mathlib-quality/references/` (NagellLutz)                                                          | n/a  | (no project references dir for source PDFs of *this* fact) | The relevant "reference" is mathlib's own `DivisionPolynomial/Basic.lean`, consulted directly in Phase 5. |
|  6 | nLab                             | "coordinate ring / fraction field localization map" / "division polynomial"                            | n/a  | nLab has no division-polynomial page; localization-commutes-with-section is a triviality | Not a categorical concept worth an nLab entry. |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                | Not a categorical statement (it is a pointwise functional `rfl`). |
|  8 | Stacks Project (alg geom)        | "fraction field of coordinate ring", "localization at a point of a ring"                               | n/a  | Stacks has localization theory but no *named* lemma of this micro-shape | The fact `S⁻¹·(mk x) = algebraMap (mk x)` is below Stacks' granularity. |
|  9 | MathOverflow / MSE               | "image of division polynomials in fraction field of coordinate ring"                                   | n/a  | —                                | No question matches; the identity is definitional. |
| 10 | recent arXiv (≤5y)               | "division polynomials" universal / "Mumford coordinates" (arXiv 2412.10284), Stange 2503.15428         | partial | Confirms division polynomials over general rings + universal constructions are an active topic | None states this Lean-glue identity; they work with the polynomials, not the `algebraMap`-compatibility. |

The protocol passed: WebSearch ran 3 distinct generality levels; ChatGPT MCP recorded `n/a`
(down this session) with WebSearch×2 + direct mathlib-source + nLab + Stacks + arXiv covering the
standard-form question; local refs / nLab / nCatLab / Stacks / MathOverflow / arXiv each checked
with reasons.

### Literature summary (Phase 3)

Concept identified as: there is **no standalone mathematical concept** here. The *underlying objects*
are "the n-division polynomials `(φₙ, ωₙ, ψₙ)` of a Weierstrass curve" (Wikipedia "Division
polynomials"; mathlib `WeierstrassCurve.{ψ,φ,ω,Ψ,Φ}`) and "the coordinate ring `R[W]` and its
fraction field `Frac R[W]`" (mathlib `Affine.CoordinateRing`, `FractionRing`). The lemma is a
**Lean-internal compatibility identity** stating the fraction-field map sends the ring-triple to
the field-triple — true definitionally because `polyToField := (algebraMap _ _).comp (AdjoinRoot.mk _)`.

Sources agree on the standard form: yes (on the *objects*); the *lemma* has no literature form.
Most general standard form: n/a — the lemma is bookkeeping for a specific universal construction.
Generality dimensions where the literature varies: n/a.
Disagreement with the literature: none. The literature simply doesn't state facts at this
granularity; they are absorbed into "by definition / by construction".

If the literature returns nothing for the *lemma* (as here) that is itself a signal: the declaration
is project-internal scaffolding, not a mathlib-grade result. Phase 7 leans NO.

---

### Generality analysis — `algebraMap_comp_smulRing`

Literature-standard form (from Phase 3): n/a — no literature statement exists; the comparison
target is "the most general *mathlib-idiomatic* way to express this glue", handled in 4c.

| # | Parameter / hypothesis | Current Lean form                         | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `n : ℤ`                | index of the division-polynomial family   | n/a                      | no                  | `n` is the natural index; nothing to weaken — the lemma is `∀ n` already. |
| 2 | base ring (implicit)   | the *specific* universal ring `Universal.Ring = curve.CoordinateRing` over `MvPolynomial Coeff ℤ` | n/a | no (in this form)   | The statement is *about* the universal construction; it is not parameterised over an abstract ring. The genuinely general fact it instantiates is "`algebraMap` commutes with a chosen `RingHom` lift composed with a `Fin k`-family" — see 4c. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *within its remit* (it already quantifies over all `n : ℤ`
and there is no abstract ring to weaken to without changing what the lemma is *about* — the universal
curve is the point).
Number of weakening opportunities found: 0 (as a literature-weakening).
Proposed restatement: none on literature grounds.
Cost of restatement: n/a.

→ Proceed to 4c; the only "generalisation" available is the modern-idiom observation that this is
an instance of a trivial mathlib-level `funext`/composition pattern.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass?                                                                    | no       | —                      | No bundled-hypothesis preamble; it's a closed identity. |
|  2 | sequences/metric → filters/topology?                                                                      | no       | —                      | No analytic content. |
|  3 | construct an object → universal-property class?                                                           | no       | —                      | The "Universal curve" *is* already the relevant universal object; this lemma is just a `rfl` about its maps. |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no       | —                      | No substructure. |
|  5 | vector-space/field-specific → weaken typeclass?                                                            | partial  | The *abstract* fact `(g.comp f) ∘ (f ∘ h) `… i.e. `algebraMap` commuting with a lift, holds for any `RingHom`s — but stating it abstractly **loses the connection to the named `smulRing`/`smulField` families** the project actually uses. | None worth it — see honesty bar below. |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | —                      | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid?                                                                   | no       | The index `n : ℤ` is the division-polynomial index; generalising it is meaningless. | n/a. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no *real* organisational improvement).
One-line reason this is not a modernisation move: the only abstraction available is "factor the
identity through the generic `RingHom`-composition `rfl`", which simply **re-derives `funext` +
definitional unfolding** and severs the lemma from the concrete `smulRing`/`smulField` names it
exists to relate — i.e. it would turn a 1-line `rfl` into the *call-site* `funext`/`rfl` it already
is. No mathlib API composes better afterward. (Honesty bar: there is no downstream gain; abstracting
here would be abstraction for its own sake.)

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `lemma`** (no definitional equality or typeclass-search path introduced).

---

### Mathlib search-status: `algebraMap_comp_smulRing`

[A] Lean-Finder       "algebraMap composed with quotient map equals lift on a family"  → no hit (concept too thin / project-local names).
[B] Loogle            `algebraMap _ _ ∘ _ = _`, `⇑(algebraMap _ _) ∘ _`               → no hit for *this* family; the closest existing mathlib `rfl`-lemmas of identical *shape* are
                       `MonoidAlgebra.coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A := rfl`
                       and `Unitization.algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R := rfl`
                       (mathlib `Algebra/MonoidAlgebra/Basic.lean:123`, `Algebra/Algebra/Unitization.lean:646`).
[C] LeanSearch        "the localization map sends the ring division-polynomial triple to the field triple" → no hit (not a mathlib statement; objects are project-local).
[D] Grep mathlib src  `grep -rn "smulRing\|smulField\|Universal.Ring\|Universal.Field\|polyToField" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/`
                       → **0 hits**. Mathlib has `Affine.CoordinateRing`, `Affine.CoordinateRing.mk`,
                       `mk_ψ`, `mk_φ`, `FractionRing W.CoordinateRing` — but **no `Universal.*`
                       pointed-curve scaffolding, no `smulRing`/`smulField`/`smulPoly`, no `polyToField`.**
[E] Name pattern      `algebraMap_comp_smulRing` / `comp_smul*`  → not in mathlib (the only matches are
                       this project's own `algebraMap_comp_smulRing` and sibling `ringEval_comp_smulRing`).

Searched for both:
  - the user's current form (project-local `smulRing`/`smulField`) — **not in mathlib** (the entities don't exist there).
  - the abstract pattern (`⇑(algebraMap R S) ∘ <chosen-lift> = <field-lift>`, a `rfl`-lemma) — mathlib
    states this *per-construction* (`coe_algebraMap`, `algebraMap_eq_inl_comp`), **not** as a
    reusable general lemma over `AdjoinRoot.mk` + `FractionRing` composed with a `Fin k`-family.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the abstract-pattern search). The
lemma's subject matter (`Universal.Ring`, `Universal.Field`, `smulRing`, `smulField`, `polyToField`)
is **project-local scaffolding absent from mathlib**, so mathlib neither has this lemma nor could
"already have it" in the literal sense.

---

### Call sites — `algebraMap_comp_smulRing`

Internal use count: **K = 0** (grep over `projects/NagellLutz/**.lean`, excluding the declaring line
`ZSMul.lean:420`, returns **no other `.lean` hits**; the only matches outside the decl are in the
generated `.mathlib-quality/overview/inventory/*.md`).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| (none)           | — no call site anywhere in the project |

Inline-derivation grep (`algebraMap.*∘.*smulRing` / `algebraMap.*smulRing` outside L420): **(none)** —
the body is not re-derived inline anywhere either.

**Interpretation (per Phase 6.0.1 / 6.0.2):** K = 0, no inline re-derivation, and (Phase 2b) it is a
one-liner without exemption. This is the "dead-ish wrapper" pattern. The sibling
`ringEval_comp_smulRing` (`ZSMul.lean:557`) is the *actually-used* workhorse (5+ uses: L565, L569,
L575, L582, L621) — it has the same shape but specializes the universal polynomials to a *concrete*
curve via `ringEval`. `algebraMap_comp_smulRing` is the parallel "into the universal field" variant
that the development does not currently consume. Strong NO signal.

---

### Composition check (Phase 6)

Can `algebraMap_comp_smulRing` be derived in ≤3 chained calls?

Attempt 1: `funext fun i => by fin_cases i <;> rfl`  — i.e. exactly the existing proof, inlined.
  - Building blocks used: `funext` (or `Function.comp` defeq) + the **project-local** definitional
    facts `polyToField_apply` / `algebraMap_field_eq_comp` (`Universal.lean:110,113`,
    both `:= rfl`), which already say `polyToField = (algebraMap _ _).comp (AdjoinRoot.mk _)`.
  - Result: **succeeds** — the whole content is "`polyToField = algebraMap ∘ AdjoinRoot.mk` (a `rfl`),
    lifted pointwise over `Fin 3` by `funext`".
  - Notes: the composition uses *project-local* `rfl`-facts, not mathlib primitives. The mathlib
    primitive in play is only `funext`/`Function.comp` defeq.

Conclusion: **COMPOSABLE** — in ≤1 line, from the project's own definitions. No new lemma is needed;
if any call site ever wants this it inlines as `funext fun i => by fin_cases i <;> rfl` (or rewrites
with the existing `polyToField`/`algebraMap_field_eq_comp` `rfl`-lemmas).

Heuristic check (6b): `funext (fun i => by fin_cases i <;> rfl)` is a single `funext` over a trivial
case split on a 3-element index — the "one function call + projection/`rfl`" row → **composable**,
not a disguised proof.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.algebraMap_comp_smulRing`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): no literature statement exists; the lemma is Lean bookkeeping for the
  project's *universal-curve* construction. The underlying objects (division polynomials, coordinate
  ring, fraction field) are standard and already in mathlib, but the `smulRing`/`smulField` glue is not.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within remit; 4c found **no** real modern-idiom
  improvement (abstracting it just re-derives `funext` + `rfl`).
- Mathlib search (Phase 5): **not in mathlib** — and *cannot* be, because `Universal.Ring`,
  `Universal.Field`, `smulRing`, `smulField`, `polyToField` are project-local and absent from mathlib.
- Composition check (Phase 6): **COMPOSABLE** in ≤1 line (`funext fun i => by fin_cases i <;> rfl`,
  resting on the local `rfl`-facts `polyToField_apply` / `algebraMap_field_eq_comp`).

**Rationale:**

This is a one-line, `rfl`-proved compatibility lemma whose entire mathematical content is "the
fraction-field map `algebraMap : Universal.Ring → Universal.Field` sends the ring-level division-
polynomial triple to the field-level one" — true *by the definition* of
`polyToField := (algebraMap _ _).comp (AdjoinRoot.mk _)`. It is glue for the project's bespoke
universal-pointed-curve scaffolding, which is **not part of mathlib** (mathlib has
`Affine.CoordinateRing` and `FractionRing` of it, but no `Universal.curve` over `MvPolynomial Coeff ℤ`,
no `smulRing`/`smulField`/`polyToField`). Because mathlib lacks the very entities this lemma relates,
"NO-mathlib-has-it" is not literally accurate, and "YES-add-as-is" is wrong on two counts: (i) the
lemma is definitional pointwise-`rfl` bookkeeping, not a result worth its own mathlib name, and (ii)
it is unstatable in mathlib without first importing the entire project-local universal construction.
What mathlib *does* provide is the building block — pointwise function equality via `funext` over the
definitional `polyToField = algebraMap ∘ AdjoinRoot.mk` factorization — so the one-line composition
fully accounts for the lemma. The call-site evidence seals it: **K = 0** internal uses, no inline
re-derivation, no docstring, no defeq/diamond/API exemption (Phase 2b); the analogous *used* lemma is
the sibling `ringEval_comp_smulRing`, while this `algebraMap` variant is presently dead. It belongs
in the project (as a possibly-prunable convenience), not in mathlib.

**WHY not (refactor-actionable):**
- Mathlib has the building blocks; the lemma is a ≤1-call composition over project-local `rfl`-facts.
  Building blocks: `funext`/`Function.comp` defeq + the project's own
  `WeierstrassCurve.Universal.polyToField_apply` (`Universal.lean:110`, `:= rfl`) and
  `WeierstrassCurve.Universal.algebraMap_field_eq_comp` (`Universal.lean:113`, `:= rfl`), which
  already encode `polyToField = (algebraMap Universal.Ring Universal.Field).comp (AdjoinRoot.mk _)`.
- Mathlib's *own* `rfl`-lemmas of this exact shape (kept per-construction, never as a general lemma)
  for cross-reference: `MonoidAlgebra.coe_algebraMap` (`Mathlib/Algebra/MonoidAlgebra/Basic.lean:123`),
  `Unitization.algebraMap_eq_inl_comp` (`Mathlib/Algebra/Algebra/Unitization.lean:646`).

Mathlib building blocks:      `funext` (core); project-local `polyToField_apply`,
                              `algebraMap_field_eq_comp` (both `Universal.lean`, `:= rfl`).
Composition sketch (≤1 line):
```lean
-- at any hypothetical call site, instead of `algebraMap_comp_smulRing n`:
example (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n :=
  funext fun i => by fin_cases i <;> rfl
```
Call sites in our project (from Phase 6.0): **K = 0**.
Refactor plan: there are **no call sites to inline into**. Recommended action is therefore the
project-cleanup decision, not a mathlib move:
  1. If `algebraMap_comp_smulRing` stays genuinely unused after the development settles, **delete it**
     from `ZSMul.lean` (it is a never-consumed convenience parallel to the used `ringEval_comp_smulRing`).
  2. If a future consumer needs it, keep it as the trivial project-local `funext … rfl` above — do
     **not** upstream it: it is unstatable in mathlib without the project's `Universal.*` scaffolding,
     and even there it is definitional bookkeeping below mathlib's lemma-granularity.
Next action: leave in the project (mark for the cleanup fleet's dead-code review); do **not** PR to
mathlib.

---

## Next step

Do **not** upstream. This is project-local definitional glue with zero call sites; it composes in one
line from the project's own `rfl`-facts (`polyToField_apply` / `algebraMap_field_eq_comp`) plus
`funext`. Either delete it as an unused convenience (the used analogue is `ringEval_comp_smulRing`) or
keep it inline; in neither case does it belong in mathlib, whose library does not contain the
`Universal.Ring` / `Universal.Field` / `smulRing` / `smulField` scaffolding the lemma is about.
