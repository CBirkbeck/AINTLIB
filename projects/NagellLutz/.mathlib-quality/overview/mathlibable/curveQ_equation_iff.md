# /mathlibable report — `LutzNagell.LutzNagellTheorem.curveQ_equation_iff`

> Step-9 mathlibable assessment, single declaration. Repo: AINTLIB / NagellLutz.
> Source: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:33`.
> Project context: this project forks parts of mathlib's elliptic-curve / division-polynomial
> stack and maintains duplicated `General*`/`PID*` tracks, so the prior expectation was that this
> decl may already live in mathlib. **That expectation is confirmed.**

---

## Baseline (Phase 0)

- lake build:               not re-run (environment build stale, per task note); reasoning from source
- decl `LutzNagell.LutzNagellTheorem.curveQ_equation_iff`: ✓ resolved at `GeneralCurve.lean:33`
- qualified name:           **`LutzNagell.LutzNagellTheorem.curveQ_equation_iff`** (namespaces `LutzNagell` ▸ `LutzNagellTheorem`, lines 16–17; matches the parsed name in the prompt)
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "General Weierstrass model for the generalized Lutz–Nagell theorem" — sets up `W : WeierstrassCurve ℤ`, its base change `curveQ W := W.map (algebraMap ℤ ℚ)`, and basic rewriting lemmas (equation, coefficients).

Exact source:

```lean
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

lemma curveQ_equation_iff (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveQ]
```

---

## Statement (Phase 1)

`curveQ_equation_iff` states the following:

> Let `W` be a Weierstrass curve over `ℤ`, and let `curveQ W = W.map (algebraMap ℤ ℚ)` be its
> base change to `ℚ`. For `x, y : ℚ`, the affine point `(x, y)` lies on `curveQ W` if and only if
> `y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x + a₆`, where each `aᵢ` is the integer coefficient of `W`
> viewed in `ℚ` via the canonical cast `ℤ → ℚ`.

It is the standard affine Weierstrass equation, written out explicitly, for the specific rational
curve obtained by base-changing an integral one — with the coefficients already pushed across the
ring map and presented as integer-casts `(W.aᵢ : ℚ)`.

Variables / typeclasses involved (Lean side):
- `W : WeierstrassCurve ℤ` — a Weierstrass curve with integer coefficients (fixed base ring `ℤ`).
- `x y : ℚ` — affine coordinates over `ℚ` (fixed base ring `ℚ`).

Hypotheses (Lean side): none.

Conclusion (math): membership of `(x,y)` on the base-changed curve ⇔ the explicit Weierstrass
polynomial relation with cast integer coefficients.

Conclusion (Lean):
`(curveQ W).toAffine.Equation x y ↔ y^2 + (W.a₁:ℚ)*x*y + (W.a₃:ℚ)*y = x^3 + (W.a₂:ℚ)*x^2 + (W.a₄:ℚ)*x + (W.a₆:ℚ)`

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `rw` + `simp` rewriting lemma that unfolds the `Equation` predicate for a fixed
base-changed curve; not a named theorem, not a new structure, not a `## Main results` entry. It is
plumbing for the `General*` track. (Literature width is EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — the one-liner-definition check does not apply.
(For completeness: the *proof* is two tactic lines, `rw [...]; simp [...]`; that is the
composition signal flagged in Phase 6, not a Phase-2b concern.)
One-liner verdict: n/a (kind is lemma).

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query                                                                                          | Hit? | Standard form found                                                                 | Notes |
|----|-----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)         | Weierstrass equation affine point `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆` base change rational            | yes  | $`y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6`$ — exactly                                     | LMFDB "Weierstrass model"; Stanford crypto notes; Silverman "Elementary background in elliptic curves" |
|  2 | WebSearch (general form)          | (same query, generality strand) general Weierstrass equation over a field/ring K                | yes  | identical relation over any commutative base ring with `aᵢ ∈ K`                      | Wikipedia "Elliptic curve"; the relation is ring-agnostic — `ℚ` is just one instance |
|  3 | WebSearch (named-after / aliases) | "long Weierstrass form" / "generalized Weierstrass equation" / "affine model" of an elliptic curve | yes  | same relation; "long/general Weierstrass equation" is the standard alias            | LMFDB knowledge base; casting coefficients through base change is a routine functoriality remark |
|  4 | ChatGPT MCP                       | n/a — MCP reported down for this environment (task note); substituted by extra WebSearch strands #2,#3 and by direct reading of the mathlib source (Phase 5) | n/a  | (covered by #1–#3 + mathlib source)                                                 | The "standard form + generality + historical evolution" question is fully answered by #1–#3: the long Weierstrass equation is classical and stated over an arbitrary base ring; the ℚ/base-change specialisation is not a distinct literature object |
|  5 | Local references                  | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/`                              | n/a  | directory absent                                                                    | neither `references/` nor `refs/` exists in this checkout — recorded n/a |
|  6 | nLab                              | "Weierstrass elliptic curve" affine equation                                                    | n/a  | nLab treats the moduli/stacky side, not the bare affine equation                    | the explicit affine relation is below nLab's abstraction level; no distinct standard form to find there |
|  7 | nCatLab                           | —                                                                                               | n/a  | not a categorical concept                                                            | this is a polynomial membership predicate, not a categorical construction |
|  8 | Stacks Project                    | Weierstrass equation / elliptic curve chapter                                                    | n/a  | Stacks states the long Weierstrass equation identically; base change is functorial   | confirms the relation is standard over any ring; the ℚ-specialisation is not a separate Stacks object |
|  9 | MathOverflow / Math.StackExchange | base change of Weierstrass equation coefficients to ℚ                                            | n/a  | routine; folklore "apply the ring hom to each coefficient"                           | no MO thread needed — `map` of a Weierstrass curve applies the ring hom coefficientwise (mathlib's `def map`) |
| 10 | recent arXiv (last 5 years)       | Weierstrass model base change                                                                    | yes  | e.g. arXiv:2310.11768 (Weierstrass curves over `ℤ_n`), arXiv:1812.10415 (Selmer/Mordell–Weil) use the identical affine relation | confirms the form is the contemporary standard; no newer/more-general affine relation exists |

**Protocol pass check:** WebSearch ran ≥3 distinct queries at different generality levels (#1 specific,
#2 general-ring, #3 named-after/aliases). ChatGPT MCP recorded n/a with reason (down in this env) and
explicitly substituted by additional WebSearch strands + direct mathlib-source reading, which fully
cover the "standard form + generality" question. Local refs checked (absent → n/a). nLab / Stacks /
MathOverflow / arXiv each checked with a one-line reason.

### Literature summary (Phase 3)

Concept identified as: the **(long / generalized) affine Weierstrass equation** of an elliptic
curve, `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.
Sources agree on the standard form: **yes** — LMFDB, Wikipedia, Stanford, Silverman, Stacks all state
exactly this relation.
Most general standard form: the relation holds over **any commutative base ring** with `aᵢ` in that
ring; base change is the coefficientwise application of a ring homomorphism (here `ℤ → ℚ`).
Generality dimensions where the literature varies:
  - base ring: from a specific field/ring (`ℚ`) up to an arbitrary commutative ring — the most
    general is "arbitrary commutative ring", and the literature default is exactly that.
  - source of the coefficients: a curve given directly over the base, vs. a curve base-changed from
    a sub-ring — the literature treats the latter as a one-line functoriality remark, not a new fact.
Disagreement with the literature: **none.** The user's form is the literature form, fixed to
`base ring = ℚ` and `curve = map of an integral curve`.

---

## Generality analysis — `curveQ_equation_iff`

Literature-standard form (from Phase 3): the affine Weierstrass equation over an **arbitrary
commutative ring**, i.e. mathlib's `WeierstrassCurve.Affine.equation_iff`.

| # | Parameter / hypothesis              | Current Lean form                       | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|-----------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | base ring of the curve              | `ℚ` (the curve `curveQ W : WeierstrassCurve ℚ`) | arbitrary `[CommRing R]`               | **yes**             | the relation `equation_iff` holds verbatim over any commutative ring; `ℚ` is an arbitrary specialisation. Mathlib already states the general form. |
| 2 | the curve itself                    | `curveQ W = W.map (algebraMap ℤ ℚ)` — a base change of an integral curve | an arbitrary curve over the base ring  | **yes**             | nothing in the statement needs the `ℚ`-curve to be `map`ped from `ℤ`; mathlib's `equation_iff` takes any `W : WeierstrassCurve R`. The `map` here only serves to rewrite `(curveQ W).aᵢ` to `(W.aᵢ : ℚ)`, the cosmetic coefficient presentation. |
| 3 | coefficient presentation            | `(W.aᵢ : ℚ)` (integer-cast)             | `(curveQ W).aᵢ` (curve's own coeffs)   | n/a (cosmetic)      | the cast form is purely a display choice; `WeierstrassCurve.map_aᵢ` (auto-`@[simp]`) and the project's own `curveQ_aᵢ` simp lemmas bridge `(curveQ W).aᵢ = (W.aᵢ : ℚ)` in one `simp`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (two specialisation axes: base ring fixed to
`ℚ`, curve fixed to a `ℤ→ℚ` base change).
Number of weakening opportunities found: 2 (axes 1 and 2).
Proposed restatement (if STRICTLY NARROWER): the maximally general form is **already in mathlib** as
`WeierstrassCurve.Affine.equation_iff (W : WeierstrassCurve R) (x y : R)`. There is nothing to restate
into the project — the general statement exists upstream. Hence this is a `NO-mathlib-has-it` case
(mathlib has the strictly-more-general form), **not** a `YES-but-generalise-first`.
Cost of restatement: n/a — no new declaration; the consumer should call the existing mathlib lemma
(plus the coefficient simp lemmas) directly.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                    | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                              | no       | —                      | the base ring is already a typeclass parameter in mathlib's `equation_iff` |
|  2 | sequences/metric → filters/topological?                                                                      | no       | —                      | purely algebraic; no topology |
|  3 | construct an object → universal-property class?                                                             | no       | —                      | this is a membership predicate, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | —                      | no substructure here |
|  5 | vector-space/field-specific → module/ring typeclass weakening?                                              | **yes**  | state over `[CommRing R]` rather than `ℚ` — but mathlib's `equation_iff` already does exactly this | the general lemma composes with every base ring, including the `ℤ`-curve and any other base change |
|  6 | 1-categorical → higher/∞-categorical?                                                                       | no       | —                      | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                            | no (re: index); the analogous "concrete base ring → arbitrary ring" point is row 5 | —          | covered by row 5 |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it is **already realised in mathlib** — the contemporary
mathlib-idiomatic form is `WeierstrassCurve.Affine.equation_iff` over `[CommRing R]`. The project
lemma is the un-idiomatic specialisation (fixed `ℚ`, fixed `map`). Because the modern form is the
existing upstream lemma, this does **not** push the verdict toward `YES-but-generalise-first` (there
is no new general lemma to ship); it reinforces `NO-mathlib-has-it`.
Real mathematical improvement: none beyond what mathlib already provides.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `curveQ_equation_iff`

[A] Lean-Finder       n/a (index queries not run in this env) — superseded by direct mathlib-source reading below
[B] Loogle            type-pattern `WeierstrassCurve.Affine.Equation _ _ ↔ _` / `_ .Equation _ _ ↔ _ = _`  →  hits: `equation_iff`, `equation_iff'`
[C] LeanSearch        natural-language "Weierstrass curve affine equation iff polynomial" → hit: `WeierstrassCurve.Affine.equation_iff`
[D] Grep mathlib src  `equation_iff`, `Equation.map`, `map_a₁`, `@[simps] def map`, `curveQ` over `.lake/packages/mathlib/` → see below
[E] Name pattern      `curveQ` / `curveQ_equation_iff` over mathlib src → **no hits** (project-only name, as expected)

Direct mathlib-source findings (the load-bearing evidence):

- **`WeierstrassCurve.Affine.equation_iff`** — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`:
  ```lean
  lemma equation_iff (x y : R) : W.Equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    rw [equation_iff', sub_eq_zero]
  ```
  General over any `[CommRing R]`. This is **exactly** the project statement with `R := ℚ`,
  `W := curveQ W`, before the cosmetic coefficient rewrite. (Used by `rw [WeierstrassCurve.Affine.equation_iff]`
  in the project proof — the project lemma literally opens by calling this.)
- **`WeierstrassCurve.map_a₁ … map_a₆`** — auto-generated `@[simp]` lemmas from `@[simps] def map`
  (`Mathlib/.../Weierstrass.lean:230`): `(W.map f).aᵢ = f (W.aᵢ)`. With `f = algebraMap ℤ ℚ` these
  turn `(curveQ W).aᵢ` into `(W.aᵢ : ℚ)` — exactly what the project's `simp [curveQ]` does.
- **`WeierstrassCurve.Affine.Equation.map` / `…map_iff`** — `Affine/Basic.lean:275–281`: the
  base-change interaction `(W.map f).Equation (f x) (f y) ↔ W.Equation x y` for injective `f`.
- **`curveQ` / `curveQ_equation_iff`** — `[E]` name search over mathlib: **no hits** (confirmed
  project-only; the prompt's "may already be in mathlib" warning refers to the *general* form, which
  is `equation_iff`, not to this exact name).

Searched for both:
  - the user's current form (`curveQ`-specialised, ℚ, cast coefficients) → not present verbatim (it is a project specialisation);
  - the literature-standard form (general ring) → **present as `WeierstrassCurve.Affine.equation_iff`**.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.equation_iff`; strictly more general form
(our lemma is the `R := ℚ`, `W := W.map (algebraMap ℤ ℚ)` specialisation, with coefficients rewritten
by the existing `map_aᵢ` simp lemmas).**

---

## Call sites — `curveQ_equation_iff`

Internal use count: **5** (within NagellLutz, excluding the declaring file `GeneralCurve.lean`).
External-to-file callers: **2 distinct files** (`GeneralDiscriminant.lean`, `GeneralPrimeOrder.lean`).

| Caller file:line                                                   | Usage pattern (one-line excerpt)                                   |
|--------------------------------------------------------------------|--------------------------------------------------------------------|
| `LutzNagellTheorem/GeneralDiscriminant.lean:56`                    | `have hQ := (curveQ_equation_iff W x y).mp hpt.left; … linarith`   |
| `LutzNagellTheorem/GeneralPrimeOrder.lean:108`                     | `((curveQ_equation_iff W x y).mp hns.left) hp h`                   |
| `LutzNagellTheorem/GeneralPrimeOrder.lean:139`                     | `((curveQ_equation_iff W x y).mp hns.left) (by decide) h`          |
| `LutzNagellTheorem/GeneralPrimeOrder.lean:142`                     | `((curveQ_equation_iff W x y).mp hns.left) hx₀⟩`                   |
| `LutzNagellTheorem/GeneralPrimeOrder.lean:157`                     | `((curveQ_equation_iff W x y).mp hns.left) hx₀⟩`                   |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
  - (none found) — every consumer goes through `curveQ_equation_iff`; the `.mp` direction is always used.

Signal reading: `K = 5` internal uses across 2 files is a genuine in-project API (would normally lean
YES). But the parent (`equation_iff`) is in mathlib in a strictly more general form, so the re-aim
rule applies: this is a thin, ℚ-specialised convenience wrapper, and the consumers should call the
mathlib lemma plus the coefficient simp lemmas instead. The 5 call sites are the refactor surface.

---

## Composition check (Phase 6)

Can `curveQ_equation_iff` be derived from mathlib in ≤3 chained calls? **Yes — it already is.**

Attempt 1 (the actual project proof, verbatim):
```lean
rw [WeierstrassCurve.Affine.equation_iff]   -- general-ring iff, instantiated at R := ℚ, W := curveQ W
simp [curveQ]                               -- fires map_a₁..map_a₆ (and curveQ_aᵢ) to cast coefficients
```
  - Mathlib decls used: `WeierstrassCurve.Affine.equation_iff`, `WeierstrassCurve.map_a₁..map_a₆`
    (auto-`@[simp]`), plus `Int.cast`/`eq_intCast` ring-hom simp facts.
  - Result: **succeeds** (this is the existing proof; 2 tactic steps).
  - Notes: the entire content of the lemma is "`equation_iff` specialised + coefficients pushed through
    `map`". No new mathematics.

Conclusion: **COMPOSABLE** — and, more strongly, it is a direct specialisation of a single mathlib
lemma (`equation_iff`) with a cosmetic `simp`. Because mathlib has the *general statement itself*
(not merely building blocks), the primary bucket is `NO-mathlib-has-it`; the composition sketch is
the refactor recipe for inlining at the 5 call sites.

---

## Verdict: `LutzNagell.LutzNagellTheorem.curveQ_equation_iff`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the long Weierstrass equation `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆` is the
  universal standard form (LMFDB, Wikipedia, Stanford, Silverman, Stacks), stated over an arbitrary
  base ring; the ℚ/base-change instance is not a distinct literature object.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — two specialisation axes
  (base ring fixed `ℚ`; curve fixed to a `ℤ→ℚ` `map`). The general form is the upstream lemma.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.Affine.equation_iff`** (general
  ring); the project lemma is its `R:=ℚ`, `W:=curveQ W` specialisation, coefficients rewritten by the
  existing `WeierstrassCurve.map_aᵢ` `@[simp]` lemmas.
- Composition check (Phase 6): **COMPOSABLE** (≤2 lines; it is literally the existing proof).

**Rationale:**

Mathlib already contains this result in strictly greater generality. `WeierstrassCurve.Affine.equation_iff`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`) states, for any `[CommRing R]` and
any `W : WeierstrassCurve R`, exactly `W.Equation x y ↔ y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. The
project lemma is that statement specialised to `R = ℚ` and `W = curveQ W = W.map (algebraMap ℤ ℚ)`,
with the only extra content being that the coefficients `(curveQ W).aᵢ` are displayed as the integer
casts `(W.aᵢ : ℚ)` — a rewrite the auto-generated `@[simps]` lemmas `WeierstrassCurve.map_aᵢ` (and the
project's own `curveQ_aᵢ`) discharge in a single `simp`. The proof body is the proof of this fact:
`rw [WeierstrassCurve.Affine.equation_iff]; simp [curveQ]`. There is no new mathematics, and the
specialisation does not even need its own name — call sites can `rw [WeierstrassCurve.Affine.equation_iff]`
(then `simp [curveQ]`) directly. This is precisely the "duplicated General track forks mathlib"
situation the project context flagged: the General-track `curveQ` plumbing re-expresses an existing
mathlib lemma at a fixed base ring.

**WHY not (refactor-actionable):**
Mathlib already has it. The exact decl is **`WeierstrassCurve.Affine.equation_iff`**, located at
**`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`**. Our form follows in ≤1 line
(modulo the cosmetic coefficient cast, handled by `simp`):

```lean
-- our statement, derived directly:
example (W : WeierstrassCurve ℤ) (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]; simp [curveQ]
```

Existing mathlib decl:  `WeierstrassCurve.Affine.equation_iff`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`
Supporting mathlib decls (for the coefficient rewrite): `WeierstrassCurve.map_a₁ … map_a₆`
                        (auto-`@[simp]` from `@[simps] def map`, `Mathlib/.../Weierstrass.lean:230`).

Call sites in our project (from Phase 6.0): **K = 5** (1 in `GeneralDiscriminant.lean`, 4 in
`GeneralPrimeOrder.lean`).

Refactor plan: this lemma is **owned by the NagellLutz producer** and lives on the `General*` track;
the cleanest disposition is one of:
  1. **Inline + delete.** At each of the 5 call sites, replace `(curveQ_equation_iff W x y).mp h`
     with `((WeierstrassCurve.Affine.equation_iff x y).mp h)` after a local `simp [curveQ]` (or
     `simp only [curveQ_a₁, curveQ_a₃, …]`) to normalise `(curveQ W).aᵢ` to `(W.aᵢ : ℚ)`. Note the
     argument-order difference: the mathlib lemma is `W.equation_iff x y` (curve via dot notation,
     coordinates positional), whereas the wrapper threads `W` explicitly as `curveQ_equation_iff W x y`.
  2. **Keep as a one-line local convenience but mark it as such** (acceptable under AINTLIB's
     WIP-tolerant `main`, but it must NOT be proposed to mathlib): the 5 consumers all use the `.mp`
     direction with the cast-coefficient RHS, so a private/`local` helper is defensible for ergonomics.
     This is a project-policy call, not a mathlib contribution.
Either way: **do not** open a mathlib PR for `curveQ_equation_iff` — mathlib has the general lemma.

Next action: do **not** submit to mathlib. On the dev branch, optionally inline the 5 call sites onto
`WeierstrassCurve.Affine.equation_iff` (+ `simp [curveQ]`) and delete the wrapper; or retain it as an
explicitly-local convenience. No upstreaming.

---

## Next step

Do not submit `curveQ_equation_iff` to mathlib: it is the `R := ℚ`, `W := W.map (algebraMap ℤ ℚ)`
specialisation of the existing `WeierstrassCurve.Affine.equation_iff`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:156`), with coefficients rewritten by the
existing `WeierstrassCurve.map_aᵢ` simp lemmas. Inline at the 5 call sites
(`GeneralDiscriminant.lean:56`; `GeneralPrimeOrder.lean:108,139,142,157`) via
`rw [WeierstrassCurve.Affine.equation_iff]; simp [curveQ]` and delete, or keep it as an explicitly
project-local convenience — but not as a mathlib contribution.

---

### Sources (Phase 3 literature)
- [LMFDB — Weierstrass equation / model](https://www.lmfdb.org/knowledge/show/ec.weierstrass_coeffs)
- [Elliptic curve — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_curve)
- [Elliptic Curves — The Weierstrass Form (Stanford)](https://crypto.stanford.edu/pbc/notes/elliptic/weier.html)
- [Silverman — Elementary background in elliptic curves (arXiv:math/9708216)](https://arxiv.org/pdf/math/9708216)
- [Weierstrass curves over ℤ_n (arXiv:2310.11768)](https://arxiv.org/pdf/2310.11768)
