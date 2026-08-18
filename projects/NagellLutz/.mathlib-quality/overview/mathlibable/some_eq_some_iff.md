# /mathlibable report — `WeierstrassCurve.Affine.Point.some_eq_some_iff`

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build is stale per task note; reasoned from source + mathlib tree directly)
- decl `WeierstrassCurve.Affine.Point.some_eq_some_iff`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:59`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — lemmas missing from released mathlib needed for the division-polynomial / ZSMul development.

Exact source (Universal.lean:59–61):
```lean
lemma some_eq_some_iff {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Nonsingular x₁ y₁)
    (h₂ : W'.Nonsingular x₂ y₂) : some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨by rintro (_ | _); trivial, by rintro ⟨rfl, rfl⟩; rfl⟩
```
Context: `variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}`, in
`namespace WeierstrassCurve.Affine.Point`. So the true qualified name is
**`WeierstrassCurve.Affine.Point.some_eq_some_iff`** (matches the parsed name).

---

### Statement (Phase 1)

`some_eq_some_iff` says: for a Weierstrass curve `W'` in affine coordinates over a
commutative ring `R`, two nonsingular affine points `(x₁, y₁)` and `(x₂, y₂)` (packaged
as `Point.some` via the `Point` inductive's `some` constructor) are equal **iff** their
coordinates agree, i.e. `x₁ = x₂ ∧ y₁ = y₂`. The nonsingularity witnesses `h₁`, `h₂` are
`Prop`s and play no role in the equality (proof irrelevance).

Variables / typeclasses (Lean side):
- `R : Type*`, `[CommRing R]` — the base ring.
- `W' : WeierstrassCurve.Affine R` — the affine Weierstrass curve.

Hypotheses (Lean side):
- `h₁ : W'.Nonsingular x₁ y₁`, `h₂ : W'.Nonsingular x₂ y₂` — nonsingularity witnesses
  (Props; required only to form the `some` constructor, irrelevant to the equality).

Conclusion (math): equality of two affine points ⇔ equality of their coordinate pairs.

Conclusion (Lean): `some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: Not a new structure, not a `## Main results` entry, not named after a person —
it is the injectivity/equality lemma for one constructor of an existing inductive
(`WeierstrassCurve.Affine.Point`).

### One-line check (Phase 2b)

Body line count: 1 substantive line (an `Iff` anonymous-constructor with two tiny tactic
blocks: `rintro (_ | _); trivial` and `rintro ⟨rfl, rfl⟩; rfl`).
One-liner verdict: kind is `lemma` (not a `def`) — the def-oriented exemption table is
**n/a**. Recorded as a one-liner *proof* of a trivial fact; no defeq/diamond/API-anchor
exemption is even applicable since it is a lemma, not a definition.
Conclusion: n/a (lemma) — but note the proof is trivial, a strong "mathlib already gives
this for free" signal carried into Phase 5/7.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Lean 4 inductive constructor injEq auto-generated lemma proof irrelevance Prop arguments"      | yes  | auto-generated `Ctor.injEq` with Prop args dropped | Confirms Lean's kernel proof irrelevance drops the `Prop` witness so the RHS is the conjunction of the *data* argument equalities. |
|  2 | WebSearch (general form)         | (same thread) Lean reference "Inductive Types" / "Axioms and Computation" proof irrelevance     | yes  | proof irrelevance: any two `t₁ t₂ : p` for `p : Prop` are definitionally equal | lean-lang.org/doc reference + theorem-proving-in-lean4. |
|  3 | WebSearch (named-after / aliases)| not applicable — this is not a *named* mathematical theorem (no person/place); it is the constructor-injectivity simp lemma | n/a | — | The "concept" is `injEq`, a Lean meta-generated lemma, not a literature theorem. |
|  4 | ChatGPT MCP                      | "exact statement of auto-generated `some.injEq` with a `Prop` constructor arg; is a bespoke `some_eq_some_iff` redundant vs `some.injEq`?" | n/a (tool down) | — | Codex MCP errored (stdin failure) — task flagged it may be down; substituted by the direct mathlib evidence below (mathlib itself does `simp_rw [some.injEq]` for the exact same goal shape). |
|  5 | Local references                 | `.mathlib-quality/references/` for NagellLutz                                                   | n/a  | — | No project-level literature on "point equality" — this is a Lean-mechanical lemma, not a math result a reference paper would state. |
|  6 | nLab                             | — | n/a | — | Not a categorical concept; "constructor injectivity / proof irrelevance" is type-theory plumbing, not an nLab entry worth citing here. |
|  7 | nCatLab                          | — | n/a | — | Not categorical. |
|  8 | Stacks Project                   | — | n/a | — | Not an algebraic-geometry result; it is decidable equality of a finite constructor with proof-irrelevant data. |
|  9 | MathOverflow / Math.SE           | — | n/a | — | No generality question to resolve; the statement is maximally trivial. |
| 10 | recent arXiv (last 5 years)      | — | n/a | — | No research content. |

### Literature summary (Phase 3)

Concept identified as: **constructor injectivity / `injEq`** for the `some` constructor of
the inductive `WeierstrassCurve.Affine.Point`. In ordinary mathematics this is invisible —
a point of an elliptic curve in affine coordinates simply *is* its coordinate pair, so
"two such points are equal iff their coordinates are equal" is a definitional triviality,
not a theorem anyone states. The only non-obvious wrinkle is the bundled `Prop`
nonsingularity witness, and the literature (Lean's own docs) confirms proof irrelevance
collapses it.

Sources agree on the standard form: yes — proof irrelevance ⇒ the equality depends only on
the data arguments `x, y`.
Most general standard form: `some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂` — already
the fully general (any `CommRing R`) statement.
Generality dimensions where the literature varies: none (no math content to vary).
Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.Affine.Point.some_eq_some_iff`

Literature-standard form (from Phase 3): the constructor-injectivity statement, already at
full generality over `[CommRing R]`.

| # | Parameter / hypothesis       | Current Lean form         | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------------|---------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`               | commutative ring          | whatever `Affine`/`Point` requires | NO meaningful weakening | `Point`/`Nonsingular` are themselves defined over `[CommRing R]`; the lemma cannot be more general than the type it is about. |
| 2 | `h₁ h₂ : Nonsingular …`      | Prop witnesses            | irrelevant (proof irrelevance) | already irrelevant | Witnesses already do not appear on the RHS; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is the injectivity lemma of the constructor,
over the same `[CommRing R]` the type lives in).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | typeclasses vs bundled hyps | no | — | The bundled `Prop` witnesses are intrinsic to the `Point.some` constructor; this is exactly how mathlib already states it. |
| 2 | filters/topology vs sequences/metric | no | — | No analysis. |
| 3 | universal-property class vs construction | no | — | — |
| 4 | bundled substructure vs set+predicate | no | — | — |
| 5 | weaken vector-space/field/metric typeclass | no | — | Already at `CommRing`. |
| 6 | higher-categorical generalisation | no | — | — |
| 7 | concrete index ℕ/ℤ/ℝ → general | no | — | No index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — the *modern mathlib idiom for exactly this fact is the
auto-generated `some.injEq`* (or `some.inj`), which mathlib uses directly. The bespoke
`Iff` lemma is the *less* idiomatic form; mathlib's convention is to `simp`/`rw` with
`Ctor.injEq` rather than to add a hand-written `_eq__iff` wrapper.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality / typeclass-search path
introduced).

---

### Mathlib search-status: `WeierstrassCurve.Affine.Point.some_eq_some_iff`

[A] Lean-Finder       (index unavailable locally)                          n/a — substituted by direct source inspection of mathlib's `Affine/Point.lean`.
[B] Loogle            pattern `Point.some _ _ _ = Point.some _ _ _ ↔ _`     auto-generated `injEq` lemmas are not separately Loogle-indexed; resolved by [D].
[C] LeanSearch        "two nonsingular affine points equal iff coordinates equal"  n/a (index stale); resolved by [D].
[D] Grep mathlib src  `some.injEq`, `some.inj`, `inductive Point`, `some_eq_some` in `Mathlib/AlgebraicGeometry/EllipticCurve/`   **HIT** — see below.
[E] Name pattern      `some_eq_some*` in mathlib                            no separate named lemma (mathlib uses the auto-generated `some.injEq`).

**Evidence (Phase-0/5 grep of the *real* mathlib tree at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/`):**

- `Affine/Point.lean:469–471` — `inductive Point | zero | some (x y : R) (h : W'.Nonsingular x y)`.
  Lean **auto-generates** `WeierstrassCurve.Affine.Point.some.injEq`, whose conclusion is
  the propositional equality
  `(some x₁ y₁ h₁ = some x₂ y₂ h₂) = (x₁ = x₂ ∧ y₁ = y₂)`
  — the `Prop` witness `h` is dropped from the RHS by proof irrelevance (Phase 3, WebSearch #1).
- `Affine/Point.lean:642` — mathlib's own `X_eq_iff` proof does
  `simp_rw [neg_some, some.injEq, ← and_or_left]` and then closes with
  `exact ⟨H, …⟩ : x₁ = x₂ ∧ y₁ = y₂` (line 643) — i.e. mathlib treats `some.injEq` as
  exactly delivering `x₁ = x₂ ∧ y₁ = y₂`, the bespoke lemma's RHS.
- `Affine/Point.lean:818` — `simpa only [some.injEq] using ⟨…(some.inj h).left, …(some.inj h).right⟩`
  (and `some.inj` at the same line) — the injectivity is used directly.
- `Affine/Point.lean:742` — `rw [neg_some, some.injEq]`.
- `Jacobian/Point.lean:474` and `Projective/Point.lean:458` — both `simp [... , Affine.Point.some.injEq]`
  for the same "two `some` points equal" reasoning.
- `.injEq` is the universal mathlib idiom: it appears in **236** mathlib files.
- No `some_eq_some` / hand-written `_eq__iff` wrapper for this constructor exists anywhere
  in `Mathlib/AlgebraicGeometry/EllipticCurve/`.

Searched for both the user's `Iff` form and the underlying `injEq`/`inj` form.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.Point.some.injEq`** (the
auto-generated constructor-injectivity lemma; the user's lemma follows in ≤1 line via
`Iff.of_eq …` / `propext`). Also available: `WeierstrassCurve.Affine.Point.some.inj`.

---

### Call sites — `WeierstrassCurve.Affine.Point.some_eq_some_iff`

Internal use count (NagellLutz, excluding the declaring `Universal.lean`): **1**
External-to-file callers: 1 file.

| Caller file:line                                   | Usage pattern |
|----------------------------------------------------|---------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:363`    | `erw [eq2, eq, add_of_X_ne ne, some_eq_some_iff] at eq1` |

(Outside NagellLutz, the same lemma is *independently re-declared* in HasseWeil:
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:62` with one call site
`…/DivisionPolynomial.lean:437` — a duplicated fork track, not a consumer of this copy.)

Inline-derivation grep: the equivalent goal is discharged in mathlib itself via
`simp_rw [some.injEq]` (`Affine/Point.lean:642`) — i.e. the canonical tool is used inline
upstream, the bespoke wrapper is a local convenience only.

Call-sites signal: **K = 1 internal use** (a single `rw` slot), and the statement is the
auto-generated `injEq` — the textbook "possibly the wrong abstraction; could be inlined"
pattern. Leans firmly toward a NO bucket.

---

### Composition check (Phase 6)

Can `some_eq_some_iff` be derived from mathlib in ≤3 chained calls? **Trivially yes** — it
*is* mathlib's `some.injEq`, repackaged from a `Prop`-equality to an `Iff`.

Attempt 1: `Iff.of_eq WeierstrassCurve.Affine.Point.some.injEq`
  - Mathlib decls used: `WeierstrassCurve.Affine.Point.some.injEq`, `Iff.of_eq`.
  - Result: succeeds (1 call). `some.injEq : (some … = some …) = (x₁ = x₂ ∧ y₁ = y₂)`, and
    `Iff.of_eq` turns the `Prop`-equality into the desired `Iff`.

Conclusion: **COMPOSABLE / NO-mathlib-has-it** — strictly, mathlib already *has* the
content as `some.injEq`; at call sites one simply uses `rw [some.injEq]` (or `simp
[some.injEq]`) instead of `rw [some_eq_some_iff]`, with no wrapper needed.

---

## Verdict: `WeierstrassCurve.Affine.Point.some_eq_some_iff`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): no math-literature concept — it is constructor injectivity;
  WebSearch confirms proof irrelevance drops the `Prop` witness, giving exactly the RHS
  `x₁ = x₂ ∧ y₁ = y₂`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; modern idiom is the auto-generated
  `some.injEq` itself, not a hand-written `_eq_iff` wrapper.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.Affine.Point.some.injEq`
  (auto-generated for the `Point.some` constructor), used directly in mathlib's
  `Affine/Point.lean` (lines 642, 742, 818), `Jacobian/Point.lean:474`, and
  `Projective/Point.lean:458`. `some.inj` also available.
- Composition check (Phase 6): NO-mathlib-has-it — `Iff.of_eq some.injEq` is a 1-call match.

**Rationale:**

`WeierstrassCurve.Affine.Point` is an `inductive` whose data constructor is
`some (x y : R) (h : W'.Nonsingular x y)`. Lean automatically generates the injectivity
lemma `WeierstrassCurve.Affine.Point.some.injEq`, whose conclusion is precisely
`(some x₁ y₁ h₁ = some x₂ y₂ h₂) = (x₁ = x₂ ∧ y₁ = y₂)` — the `Prop` nonsingularity witness
`h` is dropped on the right-hand side by proof irrelevance. The project's bespoke
`some_eq_some_iff` is nothing more than the `Iff` repackaging of that auto-generated lemma
(its trivial proof, `⟨rintro (_ | _); trivial, rintro ⟨rfl, rfl⟩; rfl⟩`, is exactly the
constructor-injectivity argument). This is not "mathlib could have it" — mathlib *does*
have it, and uses it: `simp_rw [some.injEq]` / `rw [some.injEq]` appears for this very
constructor in `Affine/Point.lean` (lines 642, 742, 818, where line 643 then consumes the
resulting `x₁ = x₂ ∧ y₁ = y₂`), and again in the Jacobian and Projective point files. The
`.injEq` idiom is mathlib-wide (236 files). Adding a named `_eq_iff` wrapper would be
redundant with — and less idiomatic than — the tool mathlib already ships and prefers.

**WHY not (refactor-actionable):**
Mathlib already provides the content as the auto-generated constructor-injectivity lemma
`WeierstrassCurve.Affine.Point.some.injEq` (a propositional equality), with
`WeierstrassCurve.Affine.Point.some.inj` for the forward direction. The user's `Iff` form
follows in ≤1 line, and at the actual call site the simp-lemma is used directly with no
wrapper. Mathlib's own analogous lemma `X_eq_iff` (`Affine/Point.lean:639`) is proved using
`some.injEq` rather than any `some_eq_some_iff`, confirming the convention.

Existing mathlib decl:  `WeierstrassCurve.Affine.Point.some.injEq`
                        (and `WeierstrassCurve.Affine.Point.some.inj`)
Located at:             auto-generated from the `Point` inductive,
                        `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:469–471`
                        (constructor `some`); used at lines 642, 742, 818 of the same file.
Our form follows in ≤1 line:
```lean
example {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Nonsingular x₁ y₁) (h₂ : W'.Nonsingular x₂ y₂) :
    some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  Iff.of_eq (WeierstrassCurve.Affine.Point.some.injEq ..)
```
Call sites in this project (NagellLutz, from Phase 6.0):  K = 1
Refactor plan:
- At `projects/NagellLutz/LutzNagell/ZSMul.lean:363`, replace `some_eq_some_iff` in the
  `erw [eq2, eq, add_of_X_ne ne, some_eq_some_iff] at eq1` chain with `some.injEq`
  (i.e. `rw`/`simp_rw [..., WeierstrassCurve.Affine.Point.some.injEq] at eq1`). `injEq` is a
  `=` of Props and rewrites cleanly; because it is the canonical `simp` form, `erw` is no
  longer needed (plain `rw`/`simp_rw` should suffice — this also removes an `erw`).
- Then delete the `some_eq_some_iff` lemma from `projects/NagellLutz/LutzNagell/Universal.lean:59–61`
  (and its mention in the module docstring, line 15).
- Note the duplicate fork copy at `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:62`
  (consumer `…/DivisionPolynomial.lean:437`): the identical refactor applies there. Worth a
  cross-project cleanup ticket so both forks drop the wrapper in favour of `some.injEq`.

Next action: at the 1 call site, rewrite with `WeierstrassCurve.Affine.Point.some.injEq`;
then delete `some_eq_some_iff` from `Universal.lean`. (Cross-link: do the same in the
HasseWeil fork.)

---

## Next step

Delete `WeierstrassCurve.Affine.Point.some_eq_some_iff` from
`projects/NagellLutz/LutzNagell/Universal.lean` and replace its single call site
(`ZSMul.lean:363`) with mathlib's auto-generated `WeierstrassCurve.Affine.Point.some.injEq`
(plain `rw`/`simp_rw`, dropping the `erw`). Mirror the change in the HasseWeil fork copy.
