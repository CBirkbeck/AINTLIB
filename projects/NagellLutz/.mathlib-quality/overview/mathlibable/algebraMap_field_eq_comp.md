# /mathlibable report — `WeierstrassCurve.Universal.algebraMap_field_eq_comp`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl read directly from source
- decl `WeierstrassCurve.Universal.algebraMap_field_eq_comp`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:113`
- kind:                      lemma (`theorem`-class; body `:= rfl`)
- has sorry:                 no
- module docstring summary:  Additions to Affine.Point + the **universal elliptic curve** over `ℤ[A₁..A₆]`; defines `Universal.Ring/Field`, `polyToField`, and the distinguished point of infinite order.

True qualified name confirmed from source: inside `namespace WeierstrassCurve` → `namespace Universal`, so
`WeierstrassCurve.Universal.algebraMap_field_eq_comp`. (Matches the parsed name.)

---

### Statement (Phase 1)

```lean
lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl
```

where
- `Universal.Field = FractionRing Universal.Ring`, `Universal.Ring = curve.CoordinateRing = AdjoinRoot P`,
- `Poly = (MvPolynomial Coeff ℤ)[X][Y]`,
- `polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk P)`,
- the RHS `algebraMap _ _` is `algebraMap (MvPolynomial Coeff ℤ) Poly`.

**Math statement.** Let `B = ℤ[A₁,A₂,A₃,A₄,A₆]` be the universal coefficient ring, `Poly = B[X][Y]`,
`Ring = Poly/⟨P⟩` the universal coordinate ring (an `AdjoinRoot`), and `Field = Frac(Ring)`. The lemma
says the structure map `B → Field` equals the composite `B → Poly → Field`, where `Poly → Field` is the
specific hand-built map `polyToField`. In other words: the canonical map from the base ring into the
universal field is the obvious tower factorization through the seven-variable polynomial ring.

Variables / typeclasses (Lean side): none free — everything is a fixed concrete object of the
universal-curve construction (`Coeff`, `curve`, `Universal.Ring`, `Universal.Field`, `polyToField`).

Hypotheses: none.

Conclusion (math): the base→field structure map factors as `polyToField ∘ (base→Poly map)`.
Conclusion (Lean): an equality of `RingHom`s `(MvPolynomial Coeff ℤ) →+* Universal.Field`, proved by `rfl`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `rfl` glue lemma recording that a hand-built composite (`polyToField`) agrees with the
structure map out of the base ring. Not a named theorem, not a new structure, not a `## Main results`
entry — it is plumbing for the `equation_point` proof.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure`, so the formal one-liner-def gate is **n/a**. But the
spirit applies strongly: the body is the single token `rfl`, i.e. the lemma asserts a *definitional*
equality. That is the canonical "this is glue, not content" signal. Carried into Phase 7.

---

### Literature search table — protocol (Phase 3)

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib IsScalarTower algebraMap_eq tower factorization algebraMap composition"       | yes  | `algebraMap R A = (algebraMap S A).comp (algebraMap R S)`      | The tower-factorization is `IsScalarTower.algebraMap_eq`; this *is* the literature/library standard form of "the lemma." |
|  2 | WebSearch (general form)         | (same query, general scalar-tower angle)                                              | yes  | basis result + `algebraMap_eq` hold for general rings, not just fields | the abstract statement is maximally general already (any `IsScalarTower R S A`) |
|  3 | WebSearch (named-after/aliases)  | "scalar tower" / "tower of algebras" structure map composition                        | yes  | "tower of algebras", `algebra_map` factorization                | classical commutative-algebra fact; no person's name attached |
|  4 | ChatGPT MCP                      | self-contained Q: is `algebraMap B Field = polyToField.comp (algebraMap B Poly)` just `IsScalarTower.algebraMap_eq`, and is the specific hand-built form library-worthy? | n/a  | —                                                              | Codex/ChatGPT MCP errored out (server down, as the task brief warned). Fell back to WebSearch + direct mathlib source reading, per instructions. |
|  5 | Local references                 | `.mathlib-quality/references/` lookup for "scalar tower" / "algebraMap"               | n/a  | (no references dir for NagellLutz)                              | dir absent — recorded n/a |
|  6 | nLab                             | "tower of algebras" / scalar restriction                                              | n/a  | —                                                              | This is elementary commutative algebra (composition of structure maps); nLab adds nothing beyond the standard statement already pinned in #1. |
|  7 | nCatLab (categorical)            | —                                                                                     | n/a  | —                                                              | Not a categorical concept beyond "composition of ring homs"; n/a. |
|  8 | Stacks Project (alg geom)        | universal Weierstrass curve / coordinate ring structure map                           | n/a  | —                                                              | The *universal elliptic curve* is alg-geom, but **this lemma** is a ring-hom factorization, not an alg-geom statement; Stacks has no lemma of this shape. n/a. |
|  9 | MathOverflow / Math.SE           | composition of algebra structure maps / scalar tower factorization                    | n/a  | —                                                              | Folklore; the named library form (#1) already settles the standard statement. |
| 10 | recent arXiv (≤5y)               | —                                                                                     | n/a  | —                                                              | No research frontier here; textbook commutative algebra. |

### Literature summary (Phase 3)

Concept identified as: **the scalar-tower factorization of structure maps** — for a tower `R → S → A`,
`algebraMap R A = (algebraMap S A) ∘ (algebraMap R S)`.
Sources agree on the standard form: **yes** — it is `IsScalarTower.algebraMap_eq` in mathlib and the
universal statement in any commutative-algebra text.
Most general standard form: holds for **any** `IsScalarTower R S A` (commutative semirings), not just
this particular `B → Poly → Field` tower.
Generality dimensions where the literature varies: none meaningful — the abstract `algebraMap_eq` is
already the maximally general statement; the project lemma is a single **concrete instantiation** of it
with `S` replaced by the hand-built `polyToField` rather than the canonical `algebraMap Poly Field`.
Disagreement with the literature: none. The project lemma is a specialised, *de-abstracted* shadow of
the standard form.

---

### Generality analysis — `WeierstrassCurve.Universal.algebraMap_field_eq_comp` (Phase 4)

Literature-standard form (Phase 3): `IsScalarTower.algebraMap_eq R S A :
algebraMap R A = (algebraMap S A).comp (algebraMap R S)`, for any `[IsScalarTower R S A]`.

| # | Parameter / hypothesis | Current Lean form                                  | Literature-standard form               | Weaker form exists? | Reason |
|---|------------------------|----------------------------------------------------|----------------------------------------|---------------------|--------|
| 1 | base ring `R`          | the concrete `MvPolynomial Coeff ℤ`                | arbitrary `CommSemiring R`             | yes                 | nothing about `ℤ[A₁..A₆]` is used; the equality is a pure tower fact |
| 2 | middle ring `S`        | the concrete `Poly = (MvPoly)[X][Y]`               | arbitrary `CommSemiring S`, `Algebra R S` | yes              | only that `R → S → A` is a tower matters |
| 3 | top object `A`         | the concrete `Universal.Field`                     | arbitrary `CommSemiring A`, `Algebra` tower | yes            | the `FractionRing (AdjoinRoot …)` structure is irrelevant to the equality |
| 4 | the map `S → A`        | the hand-built `polyToField` (a specific `def`)    | the canonical `algebraMap S A`         | n/a (de-abstraction) | this is the crux: the lemma names a *specific composite* instead of the canonical structure map |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is a single concrete instantiation of
`IsScalarTower.algebraMap_eq`, with the middle structure map hard-coded to the bespoke `polyToField`.
Number of weakening opportunities: 3 (generalise `R`, `S`, `A`) — but generalising fully **is**
`IsScalarTower.algebraMap_eq`, which already exists. So the "generalisation" is not a new mathlib lemma;
it is *reuse of an existing one*. This pushes the verdict toward NO, not toward YES-but-generalise.
Cost of restatement: n/a (the general form is already in mathlib).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation                                  | Downstream |
|----|--------------------------------------------------------------------------|----------|---------------------------------------------------------|------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                      | yes      | replace the lemma with a registered `IsScalarTower (MvPolynomial Coeff ℤ) Poly Universal.Field` instance, then use `IsScalarTower.algebraMap_eq` | the whole `algebraMap_apply`/tower API would then apply for free |
|  2 | sequences/metric → filters/topological?                                  | no       | n/a — purely algebraic ring-hom equality |  |
|  3 | construction → universal-property class?                                 | no (already) | the *general* statement is already the class lemma `IsScalarTower.algebraMap_eq` |  |
|  4 | set+closure-predicate → bundled substructure?                            | no       | n/a |  |
|  5 | field/metric-specific → weaken typeclasses?                             | yes      | the equality needs only `CommSemiring` + tower, not `Field`/`FractionRing` | matches Phase 4b |
|  6 | 1-categorical → higher-categorical?                                      | no       | n/a |  |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure?                  | no       | n/a — no numeric index |  |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — register the `IsScalarTower` instance and use the existing
`IsScalarTower.algebraMap_eq` rather than carry a bespoke `rfl` lemma. But this is *consume existing
mathlib API*, not *contribute a generalised lemma*. Real improvement: it deletes a redundant glue lemma
in favour of the canonical tower API. This confirms NO-composable / NO-mathlib-has-it territory, not a
YES-but-generalise-first contribution (the general form is not ours to add — mathlib already has it).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equality or typeclass-search path introduced).

---

### Mathlib search-status: `WeierstrassCurve.Universal.algebraMap_field_eq_comp` (Phase 5)

[A] Lean-Finder       "algebraMap equals composition tower"            no direct hit beyond the tower lemma (index stale; reasoned from source)
[B] Loogle            `algebraMap _ _ = RingHom.comp (algebraMap _ _) (algebraMap _ _)`  → `IsScalarTower.algebraMap_eq` (the general tower factorization)
[C] LeanSearch        "structure map factors through tower / scalar tower algebra map composition" → `IsScalarTower.algebraMap_eq`; `AdjoinRoot.algebraMap_eq'`
[D] Grep mathlib src  `grep -rn "algebraMap_eq" Tower.lean AdjoinRoot.lean` → two exact-shape lemmas (below)
[E] Name pattern      `algebraMap.*comp`, `Universal.*algebraMap`, `polyToField` over `Mathlib/` → **no `WeierstrassCurve.Universal` namespace exists in mathlib at all** (only a docstring mention of a "universal ring" in `DivisionPolynomial/Basic.lean:36`; no `polyToField`, no `Universal.Field/Ring`)

Building blocks found (cited by qualified name + path):
- `IsScalarTower.algebraMap_eq` — `Mathlib/Algebra/Algebra/Tower.lean:127`
  `algebraMap R A = (algebraMap S A).comp (algebraMap R S)`  (needs `[IsScalarTower R S A]`)
- `AdjoinRoot.algebraMap_eq'` — `Mathlib/RingTheory/AdjoinRoot.lean:151`
  `algebraMap S (AdjoinRoot f) = (of f).comp (algebraMap S R)`  (proved `:= rfl`)

Searched for both:
- the user's current form (concrete `B → Poly → Field` with `polyToField`) — **not in mathlib** (the
  whole universal-pointed-curve construction `polyToField/Universal.Field/Universal.Ring` is project-local;
  it does NOT exist in mathlib's `DivisionPolynomial`/`EllipticDivisibilitySequence` files despite the
  fork — those files do not define `polyToField` or this namespace).
- the literature-standard form — **in mathlib** as `IsScalarTower.algebraMap_eq` (general tower) and
  `AdjoinRoot.algebraMap_eq'` (the AdjoinRoot step).

Concluded: **not in mathlib in this concrete form**, but the **building blocks are**
(`IsScalarTower.algebraMap_eq` + `AdjoinRoot.algebraMap_eq'`); the concrete equality is a `rfl`
de-abstraction of them. The fork did NOT bring this decl in from mathlib — it is genuinely project-local
plumbing for the universal pointed curve.

---

### Call sites — `WeierstrassCurve.Universal.algebraMap_field_eq_comp` (Phase 6.0)

Internal use count: **1** (within NagellLutz, excluding the declaring file's own definition line).
Wait — corrected: the single occurrence is *inside the same file* (`Universal.lean:143`). So
external-to-file callers: **0**; in-file callers (other than the decl itself): **1**.

| Caller file:line                                   | Usage pattern                                                              |
|----------------------------------------------------|---------------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/Universal.lean:143` | `ext <;> simp [polyToField, algebraMap_field_eq_comp]` (inside `equation_point`) |

Inline-derivation grep: the *identical* lemma is independently re-stated (also `:= rfl`) in a sibling
project — `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:116` — used the same single way
(`HasseWeil/.../Universal.lean:146`). So the construction is duplicated across two projects, each using
it exactly once, in the same `simp` call. (Cross-project dedup is an AINTLIB cleanup concern, noted.)

Signal: K = 1 in-file use, body `:= rfl`, no external consumers. Per the call-site table this is the
"possibly the wrong abstraction — could be inlined" / NO-composable pattern, reinforced by the duplication.

### Composition check (Phase 6)

Can `algebraMap_field_eq_comp` be derived from mathlib in ≤3 chained calls? **Yes — it is `rfl`.**

Attempt 1: `rfl`.
  - The equality holds definitionally: `algebraMap (MvPoly) Universal.Field` unfolds (through the
    `Algebra` instances on `Field = FractionRing Ring`, `Ring = AdjoinRoot P`, `Poly = (MvPoly)[X][Y]`)
    to exactly `polyToField.comp (algebraMap (MvPoly) Poly)` because `polyToField` was *defined* as that
    composite. The project proves it with `rfl`; no lemma call is even needed.
  - Result: succeeds (0 lemma calls).

Attempt 2 (the idiomatic route, if one wanted a non-`rfl` proof): register
`[IsScalarTower (MvPolynomial Coeff ℤ) Poly Universal.Field]` (with `polyToField` as the middle map),
then `IsScalarTower.algebraMap_eq _ _ _`. ≤1 call. Alternatively, since the AdjoinRoot+FractionRing steps
are each `rfl`-tower steps (`AdjoinRoot.algebraMap_eq'`, `IsFractionRing.algebraMap`), the composite is a
2–3 lemma chain. Either way ≤3 mathlib calls.

Conclusion: **COMPOSABLE** — at the single call site the lemma can be dropped: `simp [polyToField, …]`
already unfolds the `def` and closes the same goal by `rfl`, so `algebraMap_field_eq_comp` is removable
without any new lemma. No new mathlib addition is warranted.

---

## Verdict: `WeierstrassCurve.Universal.algebraMap_field_eq_comp`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the statement is the scalar-tower factorization; standard form is
  `IsScalarTower.algebraMap_eq` (already a mathlib/literature name). Project lemma is a concrete shadow.
- Generality analysis (Phase 4): STRICTLY NARROWER than standard — a single instantiation with the
  middle map hard-coded to the bespoke `polyToField`; fully generalising it just *is* the existing
  `IsScalarTower.algebraMap_eq`.
- Mathlib search (Phase 5): not in mathlib in this concrete form (the whole `Universal.*`/`polyToField`
  construction is project-local, not inherited from the fork), but the building blocks are present
  (`IsScalarTower.algebraMap_eq` @ `Tower.lean:127`, `AdjoinRoot.algebraMap_eq'` @ `AdjoinRoot.lean:151`).
- Composition check (Phase 6): COMPOSABLE — the lemma is `:= rfl`; its single call site closes the same
  goal via `simp [polyToField, …]` with the lemma removed.

**Rationale.**
`algebraMap_field_eq_comp` is a `rfl` glue lemma: it records that the structure map `B → Universal.Field`
factors through `Poly` via the hand-built `polyToField`. Mathematically this is just the scalar-tower
factorization `algebraMap R A = (algebraMap S A).comp (algebraMap R S)`, which mathlib already provides
as `IsScalarTower.algebraMap_eq` (and `AdjoinRoot.algebraMap_eq'` for the quotient step) — both `rfl`
lemmas themselves. The project lemma is not the general statement (so it is not a YES-add); it is also not
literally `IsScalarTower.algebraMap_eq` applied verbatim, because the project never registers an
`Algebra Poly Universal.Field`/`IsScalarTower` instance with `polyToField` as the middle map — so it is not
a clean NO-mathlib-has-it citation either. What it *is*: a definitional equality removable by unfolding
`polyToField`. Its single in-file use (`simp [polyToField, algebraMap_field_eq_comp]` inside
`equation_point`) already includes `polyToField` in the simp set, so `simp [polyToField]` exposes the same
content and the named lemma is redundant. No external consumers; the identical lemma is independently
duplicated in HasseWeil's copy of the same file, used the same single way — confirming it is local
plumbing, not API.

**WHY not (refactor-actionable):**
Mathlib has the building blocks (`IsScalarTower.algebraMap_eq`, `AdjoinRoot.algebraMap_eq'`,
`IsFractionRing.algebraMap`); the project's form is a 0–1-call de-abstraction (`rfl`) of them. No new
mathlib lemma is needed — the canonical tower API covers it.

Mathlib building blocks:
- `IsScalarTower.algebraMap_eq` — `Mathlib/Algebra/Algebra/Tower.lean:127`
- `AdjoinRoot.algebraMap_eq'` — `Mathlib/RingTheory/AdjoinRoot.lean:151`
- (`IsFractionRing.algebraMap` / the `FractionRing` tower instance for the `Ring → Field` step)

Composition sketch (≤3 lines): the equality is `rfl`. Idiomatically, registering
`[IsScalarTower (MvPolynomial Coeff ℤ) Poly Universal.Field]` (middle map = `polyToField`) reduces it to
`IsScalarTower.algebraMap_eq _ _ _`; or chain `AdjoinRoot.algebraMap_eq'` with the `FractionRing` step.

Call sites in this project (Phase 6.0): K = 1 (in-file, `Universal.lean:143`), 0 external; + 1 duplicate
in HasseWeil's sibling file.

Refactor plan: at `Universal.lean:143`, delete `algebraMap_field_eq_comp` from the simp set; the existing
`simp [polyToField]` (already present in the same call) unfolds the def and closes the `ext` goal by `rfl`.
Then delete the lemma. (Cross-project: the same removal applies to the HasseWeil copy — a separate AINTLIB
cleanup ticket, since the two universal-curve files are duplicated and a shared `Common/` home or a single
canonical `IsScalarTower` instance would dedup both.)

Next action: delete `algebraMap_field_eq_comp` from NagellLutz; verify `equation_point` still closes with
`ext <;> simp [polyToField, polyToField_apply]` (or by registering the `IsScalarTower` instance and using
`IsScalarTower.algebraMap_eq`). Mirror in HasseWeil under a cross-project dedup ticket.

---

## Next step

Delete `WeierstrassCurve.Universal.algebraMap_field_eq_comp` from the project and rely on the existing
`simp [polyToField, …]` (which already unfolds the def by `rfl`) at its single call site; do not upstream —
mathlib's `IsScalarTower.algebraMap_eq` + `AdjoinRoot.algebraMap_eq'` already cover the general statement.
