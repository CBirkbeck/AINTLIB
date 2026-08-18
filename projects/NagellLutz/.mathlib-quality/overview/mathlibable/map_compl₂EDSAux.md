# /mathlibable report — `EllSequence.map_compl₂EDSAux`

> Step-9 (overview) mathlibable assessment, single declaration.
> Project: **NagellLutz** (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> This project **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
> `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so a duplicated decl may
> already be upstream. That was checked first (Phase 5).

---

### Baseline (Phase 0)

- lake build:               (not run — local build is stale per task; reasoning from source, as instructed)
- decl `EllSequence.map_compl₂EDSAux`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1421`
- **qualified name (VERIFIED):** `EllSequence.map_compl₂EDSAux`
  - The lemma sits inside `namespace EllSequence` (opened `:1356`, closed `end EllSequence` `:1431`).
    There is no other enclosing namespace in that region (the `section Map`/`section Complement`
    blocks are sections, not namespaces).
  - **Decisive cross-check:** the external consumer `DivisionPolynomialOmega.lean:112` is inside
    `namespace WeierstrassCurve` and refers to it as the **bare** `map_compl₂EDSAux` — which only
    resolves because that file does `open EllSequence` (`DivisionPolynomialOmega.lean:42`). A bare
    reference resolving under `open EllSequence` proves the lemma lives in the `EllSequence` namespace.
  - The project's own inventory independently lists it as `### lemma EllSequence.map_compl₂EDSAux`.
  - ⚠️ **Corrects a prior artifact.** An earlier version of this file claimed the name was the
    root-namespace `map_compl₂EDSAux` ("NOT `EllSequence.map_compl₂EDSAux`"). That was **wrong** — it
    missed the re-opened `namespace EllSequence` at line 1356. The correct name is
    `EllSequence.map_compl₂EDSAux`.
- kind:                      `lemma` (theorem-like; Phase 4.5 diamond/defeq analysis is **n/a**)
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised
  EDSs from initial terms; the `section Map` region proves every EDS/division-polynomial constituent
  commutes with a ring hom (`map_preNormEDS`, `map_normEDS`, `map_compl₂EDS`, …).

---

### Statement (Phase 1)

`EllSequence.map_compl₂EDSAux` states:

> For any ring homomorphism `f : R →+* S` (more precisely any `F` with
> `[FunLike F R S] [RingHomClass F R S]`), any `b c d : R`, and any `m : ℤ`,
> `f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m`.

In words: the auxiliary EDS expression `compl₂EDSAux` is **natural in the coefficient ring** — it
commutes with ring homomorphisms / base change. `compl₂EDSAux` itself is (line 1016):

```lean
def compl₂EDSAux (b c d : R) (m : ℤ) : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b
```

i.e. the **second (subtracted) summand** of the numerator of `compl₂EDS` (mathlib's `complEDS₂`).
It is the EDS-side helper that appears (a) in the reduced-invariant numerator `redInvarNum`
(`:1365`) and (b) **directly inside the definition of the `ω` division polynomial**
`WeierstrassCurve.ω` (`DivisionPolynomialOmega.lean:78`).

Lean-side parameters/typeclasses:
- `R S : Type*`, `[CommRing R] [CommRing S]` — source/target rings.
- `{F} [FunLike F R S] [RingHomClass F R S]`, `(f : F)` — a bundled-or-unbundled ring hom.
- `(b c d : R)` — the three EDS initial-coefficient parameters.
- `(m : ℤ)` — the index.

Hypotheses: none beyond the typeclasses.

Conclusion (math): `compl₂EDSAux` is functorial under ring maps.
Conclusion (Lean): `f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m`.

Proof (one line): `simp [compl₂EDSAux, apply_ite f, map_preNormEDS]` — unfold, push `f` through the
`if Even m`, and through each `preNormEDS` via mathlib's `map_preNormEDS`; `map_mul`/`map_pow` close it.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `map_*` naturality companion lemma for a `def`; not a named theorem, not a new structure,
not a `## Main results` entry. (Its *parent def* `compl₂EDSAux` is the BIG-ish object; this lemma
rides on it.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (Body is one `simp` line, but the one-liner
*definition* heuristic targets defs.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence division polynomial omega naturality base change ring homomorphism" | partial | EDS/`ωₙ` are standard; base-change "changes in a simple fashion" | Wikipedia EDS; arXiv 2102.07573, math/0404412; mathlib docs. No *named* naturality theorem. |
|  2 | WebSearch (general form)         | "elliptic curve division polynomial psi phi omega base change functorial ring homomorphism commutes" | partial | `ψ,φ,ω` standard; functoriality treated as automatic (polynomials in the coefficients) | MIT 18.783 notes6; Sage `ell_generic`; arXiv 2302.10640 (Lean group-law paper). |
|  3 | WebSearch (named-after / aliases)| "division polynomial omega_n multiplication-by-n formula functorial" (covered by #1/#2)         | partial | `ωₙ` = numerator of the `Y`-coordinate of `[n]P`; same object | The `ω` polynomial is universal in the coefficients ⇒ naturality is folklore, never a named lemma. |
|  4 | ChatGPT MCP                      | (MCP down per task; substituted with the two structured WebSearch sweeps #1–#3 + the Lean-implementation reasoning below) | n/a | — | Fallback used as the task permits. Conclusion is unaffected: the object is a Lean-implementation artifact. |
|  5 | Local references                 | `refs/NagellLutz/` / `.mathlib-quality/references/` for "omega" / "division polynomial"          | n/a  | (no references dir present for this decl) | Recorded n/a — dir absent in the worktree. |
|  6 | nLab                             | "division polynomial", "elliptic divisibility sequence"                                          | n/a  | nLab has no division-polynomial / `ωₙ` page | Not a category-theoretic concept; recorded n/a. |
|  7 | nCatLab (categorical)            | —                                                                                                | n/a  | — | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | "division polynomial", "elliptic divisibility"                                                   | n/a  | Stacks has elliptic curves but no division-polynomial `ωₙ` API | Recorded n/a — Stacks does not develop division polynomials. |
|  9 | MathOverflow / MSE               | "division polynomial omega base change" / "EDS naturality"                                       | partial | Consensus: division polynomials are defined by universal formulae, so they commute with ring maps automatically | No named theorem; treated as obvious. |
| 10 | recent arXiv (≤5 yr)             | "division polynomials arbitrary isogenies" (arXiv 2503.15428), "recurrence relation EDS" (2102.07573) | partial | Confirms `ψ,φ,ω` formalism; no isolated `compl₂EDSAux`-type helper | The specific subterm has no literature name. |

#### Literature summary (Phase 3)

- Concept identified as: the **`ω`-division-polynomial machinery** of an elliptic curve / a normalised
  EDS. `compl₂EDSAux` itself is **a single subtracted summand** of the `complEDS₂` numerator — a
  *Lean-implementation* helper with **no independent name in the mathematical literature**.
- Sources agree on the standard form: **yes** for `ψ,φ,ω`; **n/a** for `compl₂EDSAux` (it is below the
  granularity at which the literature names anything).
- Most general standard form (of the underlying fact): "division polynomials / EDS terms are given by
  universal integer-coefficient formulae, hence commute with any ring homomorphism." This is **folklore**
  — stated nowhere as a named theorem because it is immediate from the polynomial definition.
- Generality dimensions where the literature varies: base ring (field in classical treatments;
  arbitrary commutative ring in the modern/mathlib treatment — the more general one). The Lean form is
  already at the maximally general (`CommRing` + `RingHomClass`) end.
- Disagreement with the literature: none. The literature simply doesn't go to this granularity; the
  lemma is an implementation-naturality fact, not a mathematical theorem.

**Signal:** the lit search returns *no named theorem* and *no name for the object*. Per the skill, that
is itself evidence the decl is too implementation-specific to stand alone in mathlib — it only makes
sense as part of the `ωₙ` development.

---

### Generality analysis — `EllSequence.map_compl₂EDSAux` (Phase 4)

Literature-standard form (from Phase 3): "EDS/division-polynomial terms commute with ring maps,"
maximal generality = arbitrary `CommRing` + arbitrary ring hom.

| # | Parameter / hypothesis                      | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason |
|---|---------------------------------------------|------------------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R] [CommRing S]`                 | commutative rings                  | commutative ring (modern)        | NO                  | `preNormEDS`/EDS need a `CommRing`; can't drop to non-comm. Already maximal. |
| 2 | `{F} [FunLike F R S] [RingHomClass F R S]`  | any ring-hom class (bundled-or-not)| ring homomorphism                | NO                  | This is **strictly more general** than mathlib's own `map_complEDS₂`, which uses the bundled `f : R →+* S`. Already maximal. |
| 3 | `(b c d : R)` `(m : ℤ)`                      | EDS coefficients + integer index   | same                             | NO                  | Intrinsic to the object. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.** Number of weakening opportunities: 0.
Indeed it is *more* general than the mathlib sibling `map_complEDS₂` (which fixes `f : R →+* S`),
because it is stated over `[RingHomClass F R S]`. No restatement needed.

#### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Notes |
|----|--------------------------------------------------------------------------|----------|-------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | Already a clean `RingHomClass`-parametrised statement. |
|  2 | sequences/metric → filters/topology?                                     | no       | Purely algebraic naturality; no analysis. |
|  3 | construct an object where a universal-property class would characterise? | no       | It's an equation, not a construction. |
|  4 | set-with-closure → bundled substructure?                                  | no       | n/a. |
|  5 | vector-space/field-specific → weaken typeclass?                           | no       | Already `CommRing`; already maximal. |
|  6 | 1-categorical → higher-categorical?                                      | no       | n/a. |
|  7 | concrete index ℕ/ℤ/ℝ → general additive structure?                       | no       | Index is `ℤ`, intrinsic to two-sided EDS. |

Modern idiom available: **no.** The statement is already in the contemporary mathlib idiom
(`RingHomClass`, `CommRing`, `apply_ite`-style `map_*` naturality), matching — and slightly exceeding —
how mathlib states its sibling `map_complEDS₂`/`map_normEDS`/`map_preNormEDS`. Nothing to modernise.

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no new definitional equality or typeclass-search path introduced).

---

### Mathlib search-status: `EllSequence.map_compl₂EDSAux` (Phase 5)

Searched **both** the user's form and the most-general (`RingHomClass`) form.

```
[A] Lean-Finder       "ring hom commutes division polynomial omega EDS"   no hit on this object; finds map_complEDS₂ / map_normEDS (different subjects)
[B] Loogle            `?f (compl₂EDSAux ..) = compl₂EDSAux ..`-shape; `map_complEDS₂`-shape   `compl₂EDSAux` symbol absent from mathlib ⇒ no hit
[C] LeanSearch        "division polynomial omega commutes with ring homomorphism"   surfaces mathlib map_complEDS₂ (the PARENT object), not this Aux term
[D] Grep mathlib src  `grep -rn "compl₂EDSAux" .lake/packages/mathlib/`   **0 hits** (the token does not exist anywhere in mathlib)
[E] Name pattern      `map_compl₂EDSAux`, `compl₂EDSAux`, `complEDS₂Aux` over mathlib   no hit; sibling `map_complEDS₂` exists for a DIFFERENT object
```

Decisive greps:
- `grep -rn "compl₂EDSAux" .lake/packages/mathlib/` → **0 results.** The subject definition
  `compl₂EDSAux` is **not in mathlib at all**.
- `grep -rln "redInvarNum|invarDenom|redInvarDenom" Mathlib/` → **0 results**; `def invarNum`/`def invar`
  → **0 results.** The entire reduced-invariant / `ω`-EDS layer this lemma serves is **project-only**.
- Mathlib **does** have the parent object `complEDS₂` and its naturality lemma `map_complEDS₂`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`), plus the open division-polynomial
  `ωₙ` **TODO** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71,83`.

Concluded: **not in mathlib** (all 5 methods exhausted, both forms). The *subject* `compl₂EDSAux`
does not exist upstream; therefore neither can its naturality lemma. Mathlib has the **sibling**
`map_complEDS₂` for the parent object, but `compl₂EDSAux` is a *different* term (one subtracted summand
of the `complEDS₂` numerator), so `map_complEDS₂` does **not** yield `map_compl₂EDSAux`.

---

### Call sites — `EllSequence.map_compl₂EDSAux` (Phase 6.0)

Internal use count (outside the declaring file): **1**
External-to-file callers: **1 distinct file**

| Caller file:line                              | Usage pattern (one-line excerpt) |
|-----------------------------------------------|----------------------------------|
| `LutzNagell/DivisionPolynomialOmega.lean:112` | `simp_rw [ω, ← coe_mapRingHom, …, map_redInvarDenom, map_compl₂EDSAux, map_polynomial, …]` — proving `map_ω` (the ring hom commutes with the `ω` division polynomial). **Load-bearing**: `ω`'s very definition (`:78`) contains `compl₂EDSAux`, so `map_ω` cannot be proved without this rewrite. |

Plus **1 same-file consumer**: `map_redInvarNum` (`:1426`,
`simp only [redInvarNum, …, map_compl₂EDSAux, map_ofNat]`).

So the lemma has **2 real consumers** total (1 cross-file `map_ω`, 1 same-file `map_redInvarNum`),
both genuine `map_*`-pushforward proofs that need exactly this naturality step.

Inline-derivation grep (was the equivalent re-derived without `map_compl₂EDSAux`?): **(none)** — both
consumers go through the named lemma; nobody re-expands the `compl₂EDSAux` naturality by hand.

Signal: K = 1 external (+1 internal), **no inline re-derivation** → a real, used API lemma (not dead
code, not a bypassed wrapper). Within the project this is healthy. The question is purely *mathlib-fit*.

### Composition check (Phase 6)

Can `EllSequence.map_compl₂EDSAux` be obtained from **mathlib** in ≤3 chained calls **without** a new
lemma — i.e. inlined at its 2 call sites?

Attempt 1: `simp [compl₂EDSAux, apply_ite f, map_preNormEDS, map_pow, map_mul]`
- Mathlib decls used: `map_preNormEDS` (exists upstream, `EllipticDivisibilitySequence.lean:522`),
  `apply_ite`, `map_pow`, `map_mul`, `map_one` (all mathlib core).
- Result: **succeeds as a tactic** — the proof body is genuinely a `simp` over mathlib-resident
  lemmas, because `compl₂EDSAux`'s RHS is built only from `preNormEDS`, `^`, `*`, and an `if`.
- BUT this is **not a NO-composable situation**, for a structural reason: the thing being pushed `f`
  through — `compl₂EDSAux` — **is itself not in mathlib.** "Inline the composition at the call site"
  presupposes the *subject* is upstream so the call site even exists in mathlib. Here the call sites
  (`map_ω`, `map_redInvarNum`) are over **project-only** objects (`ω`, `redInvarNum`) that mathlib also
  doesn't have. There is nothing in mathlib to inline *into*.

Conclusion: **NOT-COMPOSABLE** in the sense the bucket requires. The `simp` recipe is composable *as a
proof*, but the lemma is a naturality fact about a **project-only definition**; it is meaningful only as
part of the (not-yet-upstream) `compl₂EDSAux` → `ω` development. So this is **not** a
"NO-composable-from-mathlib / inline-and-delete" case, and it is **not** "NO-mathlib-has-it" (mathlib has
the sibling, not this).

---

## Verdict: `EllSequence.map_compl₂EDSAux`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): `ψ,φ,ω` are standard, but `compl₂EDSAux`'s naturality is **folklore with
  no named theorem and no name for the object** — it is a Lean-implementation helper below literature
  granularity.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (even exceeds mathlib's sibling `map_complEDS₂`,
  using `RingHomClass` rather than a bundled `R →+* S`). No 4c modernisation available.
- Mathlib search (Phase 5): **not in mathlib**; the *subject* `compl₂EDSAux` has **0 hits** in
  `.lake/packages/mathlib/`. The whole `redInvarNum`/`invar*`/`ω`-EDS layer is project-only. Mathlib has
  the **sibling** `map_complEDS₂` (parent object) + an **open `ωₙ` TODO** (`DivisionPolynomial/Basic.lean:71,83`).
- Composition check (Phase 6): **NOT-COMPOSABLE** in the bucket sense — the `simp` proof uses mathlib
  lemmas, but there is no upstream call site to inline into because `compl₂EDSAux`, `ω`, `redInvarNum`
  are all project-only.

**Rationale.**
`map_compl₂EDSAux` is a textbook *companion `map_*` lemma whose inclusion question is inseparable from
its parent definition* `compl₂EDSAux`. It is in the right (maximally general) form, it is genuinely used
(`map_ω`, `map_redInvarNum`), and it is genuinely absent from mathlib — so it can't be NO-mathlib-has-it,
and it can't be cleanly NO-composable (there is no upstream object to inline into). On the surface that
points at YES. But a naturality lemma cannot be `YES-add-as-is` **when its subject `def` is not in
mathlib and the subject's own upstreaming is an unsettled design call.** And it is unsettled:
`compl₂EDSAux` exists only to build the project's `WeierstrassCurve.ω` (`DivisionPolynomialOmega.lean:78`),
which is precisely mathlib's **open `ωₙ` TODO** (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71,83`).
Mathlib's TODO sketches a **different** intended construction of `ωₙ` — "the image, under specialisation,
of the universal division in `ℚ[A₁,…,A₆][X,Y]`" (`Basic.lean:32–37`) — not necessarily via an EDS helper
shaped like `compl₂EDSAux`. So whether mathlib wants *this exact* helper term and *this exact* naturality
lemma, versus folding it into whatever `ωₙ` definition mathlib eventually adopts (in which case the
naturality lemma would be restated against that form, or be subsumed by `map_complEDS₂`-style lemmas),
is a **design decision for a mathlib maintainer** — exactly the judgment the skill must not make alone.

This **overturns the prior artifact's `YES-add-as-is`**. Two defects in that earlier verdict: (1) it used
the wrong qualified name (root-namespace `map_compl₂EDSAux` instead of `EllSequence.map_compl₂EDSAux`);
and (2) it fails the Phase-7 verdict gate — a `map_*` lemma for a not-yet-upstream `def` whose own
mathlibability is BORDERLINE (the parent `compl₂EDSAux` assessment is BORDERLINE, tied to the `ωₙ` TODO)
cannot be `YES-add-as-is`. The honest verdict is BORDERLINE, ride-along with the parent.

**Numbered questions for the human (≤4):**

1. **Parent first.** Will the `compl₂EDSAux` → `WeierstrassCurve.ω` development be upstreamed to
   discharge mathlib's open `ωₙ` TODO (`DivisionPolynomial/Basic.lean:71,83`)? If **no**, this naturality
   lemma stays project-local (it has no mathlib subject) → effectively NO. If **yes**, go to Q2.

2. **Definitional shape.** When `ωₙ` is upstreamed, will it be built from an EDS helper *shaped like
   `compl₂EDSAux`* (a subtracted summand of the `complEDS₂` numerator), or via mathlib's TODO-sketched
   "universal division" route (`Basic.lean:32–37`)? Only in the **former** case does
   `map_compl₂EDSAux` survive *as-is*; in the latter it is restated against the new helper (or absorbed).

3. **Granularity / `@[simp]`.** Even if `compl₂EDSAux` is upstreamed, should its naturality be a
   **standalone `@[simp]` lemma** (matching the sibling `map_complEDS₂`, which *is* `@[simp]` — note this
   project's copy is **not** tagged `@[simp]`), or just inlined into the eventual `map_ω` proof?

4. **PR grain.** If YES: confirm it ships **in one PR** with the whole helper cluster
   (`compl₂EDSAux` + its 5 `@[simp]` value lemmas + `compl₂EDSAux_mul_b` + `compl₂EDSAux_neg` +
   `map_compl₂EDSAux`), *not* as a standalone lemma PR.

**Next action:** answer Q1–Q4 (Q1 is the gate). Because this lemma's fate is bound to the parent,
**run `/mathlibable EllSequence.compl₂EDSAux` (the `def`) first** and bucket the whole `ω`-EDS helper
family in one decision against mathlib's `ωₙ` TODO; then re-run this lemma. Do **not** open a standalone
PR, and do **not** delete it (it is load-bearing for the project's `map_ω`).

---

## Next step

Run `/mathlibable EllSequence.compl₂EDSAux` (the parent `def`) and resolve its bucket against mathlib's
open `ωₙ` division-polynomial TODO; this lemma inherits that decision. If the parent is upstreamed in a
form that keeps a `compl₂EDSAux`-shaped helper, promote this to YES-add-as-is **as a `@[simp]` lemma in
the same PR**; otherwise it stays project-local.
