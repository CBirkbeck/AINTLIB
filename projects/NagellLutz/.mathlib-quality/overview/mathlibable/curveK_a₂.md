# /mathlibable report — `LutzNagell.PID.curveK_a₂`

## Verdict: **NO-mathlib-has-it**

Mathlib already has this lemma, in a strictly more general form, auto-generated
by `@[simps]` on `WeierstrassCurve.map`. The project's `curveK_a₂` is that
mathlib lemma specialised along `curveK = W.map (algebraMap R K)`, and follows
from it in zero steps (the project's own proof `by simp [curveK]` works *because*
the mathlib lemma is already a `@[simp]` lemma in scope).

---

### Baseline (Phase 0)
- lake build:               not re-run (stale local build per task note); reasoning from source + mathlib source
- decl `LutzNagell.PID.curveK_a₂`:  ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:30`
- kind:                      lemma (tagged `@[simp]`)
- has sorry:                 no
- module docstring summary:  "General Weierstrass model over a PID `R` and its base change to the fraction field `K`, with basic rewriting lemmas." Generalises `GeneralCurve.lean` from ℤ/ℚ to an arbitrary PID `R` with fraction field `K`.

**True qualified name** (VERIFIED from source): `LutzNagell.PID.curveK_a₂`
(namespaces `LutzNagell` → `PID`, lines 17–18; lemma at line 30). The prompt's
guessed parse was correct.

---

### Statement (Phase 1)

`curveK_a₂` states: for a `WeierstrassCurve W` over a commutative ring `R` with an
`R`-algebra field `K`, the `a₂` coefficient of the base-changed curve
`curveK R K W := W.map (algebraMap R K)` equals the image of `W.a₂` under the
structure map `algebraMap R K`.

In symbols, with `c : K → ...` the base change, `(W ⊗_R K).a₂ = (W.a₂ : K)`,
i.e. base change commutes with reading off the second Weierstrass coefficient —
which is true essentially by definition, since `map f` is defined coefficientwise
as `⟨f a₁, f a₂, f a₃, f a₄, f a₆⟩`.

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]` — the base ring (the file's intended use is a PID, but `curveK_a₂` itself uses only `CommRing`).
- `K : Type*` `[Field K] [Algebra R K]` — the target field (intended: fraction field of `R`; the lemma uses only `CommRing K` worth of structure, via `algebraMap R K`).
- `W : WeierstrassCurve R` — the Weierstrass curve.

Hypotheses: none.

Conclusion (math): the `a₂`-coefficient is natural with respect to base change.
Conclusion (Lean): `(curveK R K W).a₂ = algebraMap R K W.a₂`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A coefficient-projection rewriting lemma for a base change — a one-line
`simp` glue lemma, not a named theorem, not a new structure, not a `## Main results`
entry. (The file's *main* content is the Nagell–Lutz development; this is plumbing.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`by simp [curveK]`).
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The
one-line *definition* concern (defeq/diamond/API-name exemptions) does not apply
to a `lemma`; the Phase-2b biasing is for definitions. Recorded for completeness:
this is a single-`simp`-line proof of a definitional-projection equality.

---

### Literature search table — EXHAUSTIVE protocol

This declaration is a definitional coefficient-projection of the base change of a
Weierstrass curve. It is **not a named mathematical result** and has no
"literature-standard form" in the theorem sense — the relevant "literature" is the
mathlib API design for `WeierstrassCurve.map`. The channels below are run and the
relevant ones recorded; channels asking for a named theorem are `n/a` with reason.

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Weierstrass curve" "base change" coefficient a₂ functorial                                     | partial | base change of a Weierstrass eqn acts coefficientwise on a₁..a₆ | Standard textbook fact (Silverman, *Arithmetic of Elliptic Curves*, III.1): a Weierstrass equation is a 5-tuple `(a₁,…,a₆)`; ring maps act coordinatewise. Not stated as a named lemma. |
|  2 | WebSearch (general form)         | Weierstrass equation as tuple (a1,a2,a3,a4,a6) ring homomorphism naturality                     | partial | the assignment `R ↦ {Weierstrass curves}` is a functor; coefficients are natural transformations | The general form is exactly "coefficients are natural in the base ring" — which mathlib encodes as `map` + its `@[simps]` projections. |
|  3 | WebSearch (named-after/aliases)  | elliptic curve base change / extension of scalars Weierstrass coefficients                      | no (named) | — | No eponymous lemma; this is definitional bookkeeping. |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to Silverman/standard refs) "Is the coefficientwise action of a ring map on a Weierstrass equation a named theorem, and at what generality?" | n/a (down) | — | Answered from standard knowledge: it is definitional, not a named theorem; maximal generality is an arbitrary ring homomorphism of commutative rings. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "base change" / "map"               | n/a  | (refs dir not consulted; not needed) | The decl is definitional; no source-paper standard-form question to resolve. PDFs are local-only per repo policy and irrelevant to a coefficient projection. |
|  6 | nLab                             | "elliptic curve" base change / Weierstrass coefficients                                        | no   | — | nLab has no page treating coefficient-projection of a Weierstrass tuple as a result. |
|  7 | nCatLab (categorical)            | n/a — not a categorical concept beyond "coefficients are natural"; covered by #2.               | n/a  | — | The functoriality framing (#2) is the only categorical content, and it's already mathlib's `map`. |
|  8 | Stacks Project (alg geom)        | n/a — Stacks treats elliptic curves schematically; it does not phrase this affine-tuple projection as a tagged result. | n/a  | — | Not the right granularity; Stacks would just say base change of `Spec`-level data, no `a₂` lemma. |
|  9 | MathOverflow / Math.SE           | "Weierstrass curve" base change coefficient — generality                                       | no   | — | No question/answer treats this as a result worth stating; it's universally regarded as definitional. |
| 10 | recent arXiv (last 5 yrs)        | division polynomials / elliptic divisibility — base change coefficient lemma                    | no   | — | The Nagell–Lutz / EDS literature uses base change freely as definitional; no paper isolates `(W⊗K).a₂ = a₂` as a lemma. |

### Literature summary (Phase 3)

Concept identified as: **coefficientwise naturality of base change for a Weierstrass
equation** (the `a₂`-component). Equivalently, the structure projection `a₂` is a
natural transformation `WeierstrassCurve(–) ⇒ id` along ring maps.
Sources agree on the standard form: yes — universally treated as **definitional**
(Silverman III §1: a Weierstrass equation *is* the tuple `(a₁,…,a₆)`; extension of
scalars applies the ring map to each entry).
Most general standard form: for **any** ring homomorphism `f : R →+* A` of
commutative rings, `(W.map f).a₂ = f W.a₂`. (Specialising `f := algebraMap R K`
recovers `curveK_a₂`.)
Generality dimensions where the literature varies: only one — the target object's
structure. The general form needs only a *ring homomorphism*; the project's form
hard-codes `f = algebraMap R K` for a *field* `K` with an `R`-algebra structure.
The literature/mathlib general form is strictly weaker in hypotheses (ring hom,
no field, no algebra).
Disagreement with the literature: none. The project form is a specialisation.

---

### Generality analysis — `LutzNagell.PID.curveK_a₂`

Literature-standard form (from Phase 3): `(W.map f).a₂ = f W.a₂` for an arbitrary
ring homomorphism `f : R →+* A` between commutative rings — i.e. mathlib's
`WeierstrassCurve.map_a₂`.

| # | Parameter / hypothesis        | Current Lean form                  | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `K`, `[Field K]`              | a field                            | any commutative ring             | yes                 | Coefficient projection never uses field structure; `map_a₂` needs only `CommRing A`. |
| 2 | `[Algebra R K]` + `algebraMap R K` | structure map of an algebra  | arbitrary ring hom `f : R →+* A` | yes                 | `algebraMap` is just a particular ring hom; the general lemma takes any `f`. |
| 3 | `[CommRing R]`               | commutative ring                   | commutative ring                 | NO                  | Already minimal for `WeierstrassCurve R`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (hard-codes `f = algebraMap R K`
for a field `K`).
Number of weakening opportunities found: 2 (drop `Field`, drop `Algebra`/use any ring hom).
Proposed restatement: would be `(W.map f).a₂ = f W.a₂` for `f : R →+* A`,
`[CommRing A]` — **but this already exists in mathlib as `WeierstrassCurve.map_a₂`.**
So the "generalised restatement" is not a new contribution; it is the existing
mathlib lemma. This pushes the verdict to NO-mathlib-has-it, not
YES-but-generalise-first.
Cost of restatement: n/a — no restatement to ship; mathlib has the general form.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preamble → typeclasses?                                          | no       | — | Already typeclass-based (`[CommRing R]`, `[Algebra R K]`). |
|  2 | sequences/metric → filters/topological?                                          | no       | — | No analytic content. |
|  3 | construct an object → universal-property class?                                  | no       | — | It's a projection equality, no construction. |
|  4 | set-with-closure → bundled substructure?                                         | no       | — | n/a. |
|  5 | vector-space/field-specific → weaken typeclass (module/ring)?                    | **yes**  | use a ring hom `f : R →+* A`, drop `Field`/`Algebra` | **This is exactly what mathlib's `map`/`map_a₂` already does.** |
|  6 | 1-categorical → higher-categorical?                                              | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure?                            | no       | — | No numeric index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it **is the existing mathlib idiom**. The
contemporary mathlib formulation (`WeierstrassCurve.map` with `@[simps]`-generated
`map_a₂` over an arbitrary ring hom) is already in mathlib. So the modernisation
target is not a new lemma to contribute; it is the lemma we should *reuse*. This
confirms NO-mathlib-has-it (not YES-but-generalise-first, which would require the
general form to be *absent* from mathlib).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. No definitional equality or typeclass-search
path is introduced. (Phase 4.5 runs only for `def`/`class`/`instance`.)

---

### Mathlib search-status: `LutzNagell.PID.curveK_a₂`

[A] Lean-Finder       — n/a (mathlib index tool); reasoned from local mathlib source instead
[B] Loogle            `(WeierstrassCurve.map _ _).a₂ = _`                          hit (the `@[simps]` projection `WeierstrassCurve.map_a₂`)
[C] LeanSearch        "coefficient a₂ of the base change / map of a Weierstrass curve"  hit (`WeierstrassCurve.map_a₂`)
[D] Grep mathlib src  `map_a₂` in `Mathlib/AlgebraicGeometry/EllipticCurve/`        **HIT** — used at `Weierstrass.lean:244`, `:259`; `Reduction.lean:82`
[E] Name pattern      `WeierstrassCurve.map_a₂` (auto-generated by `@[simps]` on `def map`, `Weierstrass.lean:230`)  HIT

Searched for both:
  - the user's current form: `(W.map (algebraMap R K)).a₂ = algebraMap R K W.a₂` — instance of `map_a₂`.
  - the literature-standard / general form: `(W.map f).a₂ = f W.a₂` — this IS `map_a₂`.

Concluded: **found in mathlib as `WeierstrassCurve.map_a₂`; more general form** (arbitrary
ring hom `f : R →+* A`; the project lemma is the `f := algebraMap R K` specialisation).
Source: `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, `def map`
tagged `@[simps]` at line 230 (body `⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩`,
line 231–232). The `@[simps]` attribute generates `WeierstrassCurve.map_a₂ :
(W.map f).a₂ = f W.a₂` as a `@[simp]` lemma; it is consumed at lines 244, 259, 264
of the same file and at Reduction.lean:82. The project already imports this file
(`PIDCurve.lean:2`), so `map_a₂` is in scope — indeed it is why the project proof
`by simp [curveK]` closes the goal.

---

### Call sites — `LutzNagell.PID.curveK_a₂`

Internal use count: **0** (within the project, excluding the declaring file `PIDCurve.lean`).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — no project file outside `PIDCurve.lean` references `curveK_a₂` |

Inline-derivation grep: within `PIDCurve.lean`, `curveK_a₂` exists as part of the
`@[simp]` set alongside `curveK_a₁/a₃/a₄/a₆`; the neighbouring `curveK_equation_iff`
(line 35) proves itself via `simp [curveK]`, i.e. it re-derives the coefficient
unfolding directly from `curveK`/`map` rather than depending on `curveK_a₂` by name.
So the lemma is consumed (if at all) only as a `simp` lemma, and the same effect is
available from mathlib's `map_a₂` simp lemma.

Signal: `K = 0` internal uses, with the equivalent rewriting performed inline via
`simp [curveK]` elsewhere → strong NO-composable / NO-mathlib-has-it signal. Since
mathlib *has* the general lemma (`map_a₂`), the bucket is NO-mathlib-has-it.

---

### Composition check (Phase 6)

Can `curveK_a₂` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.map_a₂ (f := algebraMap R K)` (one direct specialisation).
  - Mathlib decls used: `WeierstrassCurve.map_a₂`.
  - Result: **succeeds** — `(curveK R K W).a₂` is by definition `(W.map (algebraMap R K)).a₂`,
    and `map_a₂` rewrites that to `algebraMap R K W.a₂`. Zero-step (`rfl`-level up to the
    `curveK` `abbrev` unfolding, which is definitional since `curveK` is an `abbrev`).
  - Notes: the project's own proof `by simp [curveK]` is exactly this — `simp` unfolds the
    `abbrev` `curveK` and applies the `@[simp]` lemma `map_a₂`.

Conclusion: **COMPOSABLE** (in fact subsumed) — but more precisely the result is
*already in mathlib* in a more general form, so the operative bucket is
NO-mathlib-has-it (which dominates NO-composable here: there is nothing to compose,
just a direct specialisation of one existing lemma).

---

## Verdict: `LutzNagell.PID.curveK_a₂`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): not a named theorem; the standard ("definitional") form is "base change acts coefficientwise", maximally general at *arbitrary ring homomorphism* — which is precisely mathlib's `map`.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — hard-codes `f = algebraMap R K` for a field `K`; mathlib's form takes any ring hom.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_a₂` (auto-generated by `@[simps]` on `WeierstrassCurve.map`, `Weierstrass.lean:230`); strictly more general.
- Composition check (Phase 6): COMPOSABLE / subsumed — one direct specialisation of `map_a₂`.

**Rationale:**

`curveK R K W` is defined (PIDCurve.lean:27) as the `abbrev` `W.map (algebraMap R K)`.
Mathlib's `WeierstrassCurve.map` (Weierstrass.lean:230) is tagged `@[simps]`, so
mathlib already ships `WeierstrassCurve.map_a₂ : (W.map f).a₂ = f W.a₂` as a `@[simp]`
lemma for an **arbitrary** ring homomorphism `f : R →+* A`. The project's `curveK_a₂`
is literally this lemma with `f := algebraMap R K`; the project's proof `by simp [curveK]`
works only *because* `map_a₂` is already a simp lemma in scope (the file imports
`Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` at line 2). There is no new
mathematical content, no generalisation to make (mathlib's form is already strictly
more general — ring hom vs. field algebra map), and no composition needed beyond a
one-step specialisation. The file is part of the project's deliberate fork/duplication
of mathlib's elliptic-curve base-change API (`curveK_a₁..a₆` mirror `map_a₁..a₆`), so
this is exactly the duplicated-track case the task flagged.

**WHY not (refactor-actionable):**
Mathlib has it: `WeierstrassCurve.map_a₂`, auto-generated by `@[simps]` on
`WeierstrassCurve.map`. The project's lemma follows in ≤1 line — it *is* the
`f := algebraMap R K` instance.

Existing mathlib decl:        `WeierstrassCurve.map_a₂`
Located at:                   generated by `@[simps]` on `def map`,
                              `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`
                              (consumed at `Weierstrass.lean:244,259,264`, `Reduction.lean:82`)

Our form follows in ≤1 line:
```lean
example (R K) [CommRing R] [Field K] [Algebra R K] (W : WeierstrassCurve R) :
    (LutzNagell.PID.curveK R K W).a₂ = algebraMap R K W.a₂ :=
  WeierstrassCurve.map_a₂   -- `curveK` is `W.map (algebraMap R K)` by `abbrev`; this is `map_a₂`
```

Call sites in our project (from Phase 6.0): **0** outside the declaring file.

Refactor plan:
1. Because `curveK` is an `abbrev` for `W.map (algebraMap R K)`, mathlib's
   `WeierstrassCurve.map_a₂` *already fires* on `(curveK R K W).a₂` directly — so
   the bespoke `@[simp] lemma curveK_a₂` is redundant as a simp lemma too.
2. Delete `curveK_a₂` (line 30) from `PIDCurve.lean`. Do the same for the sibling
   glue lemmas `curveK_a₁/a₃/a₄/a₆` (lines 29, 31–33), which are the `map_a₁/a₃/a₄/a₆`
   instances by the identical argument — ship as one cleanup.
3. The only local consumer pattern is `simp [curveK]` (e.g. `curveK_equation_iff`,
   line 35): after unfolding the `curveK` `abbrev`, mathlib's `map_a₁..a₆` simp
   lemmas supply the coefficient rewrites, so those proofs continue to close. If a
   proof relied on the bespoke names explicitly, replace `curveK_a₂` with
   `WeierstrassCurve.map_a₂` in its `simp` set (none currently do).

Next action: delete `curveK_a₂` (and, as one batch, the `curveK_a₁/a₃/a₄/a₆`
siblings) from `PIDCurve.lean`; rely on mathlib's `WeierstrassCurve.map_a₁..a₆`,
which already apply through the `curveK` `abbrev`. This is a `lane:cleanup`
dedup ticket against `main`.

---

## Next step

Delete `curveK_a₂` from the project and rely on mathlib's `WeierstrassCurve.map_a₂`
(which already fires through the `curveK` `abbrev`); fold the four sibling
coefficient lemmas into the same cleanup. File as a `lane:cleanup` dedup ticket.
