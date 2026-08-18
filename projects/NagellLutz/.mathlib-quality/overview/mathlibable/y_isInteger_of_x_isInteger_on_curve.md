# /mathlibable report — `LutzNagell.PID.y_isInteger_of_x_isInteger_on_curve`

> **Verdict (TL;DR): NO-composable-from-mathlib.** The reusable mathematical content
> is exactly `isInteger_of_is_root_of_monic` (Mathlib/RingTheory/Polynomial/RationalRoot.lean:115),
> which mathlib already has *with the identical typeclasses*. The theorem is bespoke
> glue that specialises that lemma to the Weierstrass equation by building the monic
> quadratic `X² + c₁X + c₀` that `y` satisfies. The only thing mathlib is genuinely
> missing here is the **Nagell–Lutz development as a whole** — this `y`-from-`x`
> helper would ship *with* that, not as a standalone library lemma.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoning from source statement, which elaborates in the integrated tree.
- decl `LutzNagell.PID.y_isInteger_of_x_isInteger_on_curve`: ✓ resolved at projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:37
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Prime-order torsion integrality for Weierstrass curves over UFDs" — generalises `GeneralPrimeOrder.lean` (ℤ/ℚ) to a UFD `R` with fraction field `K`.

Verified qualified name: **`LutzNagell.PID.y_isInteger_of_x_isInteger_on_curve`** (namespace `LutzNagell.PID`, matches the parsed name in the task).

---

### Statement (Phase 1)

`y_isInteger_of_x_isInteger_on_curve` is a theorem stating: let `W` be a Weierstrass
curve with coefficients `a₁,…,a₆ ∈ R`, where `R` is an integral domain that is a UFD
with fraction field `K`. If a point `(x, y) ∈ K × K` lies on the curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, and the first coordinate `x` is integral
(`x = ι x₀` for some `x₀ ∈ R`), then the second coordinate `y` is also integral
(`y ∈ R`, i.e. `IsLocalization.IsInteger R y`).

Mathematically: on a Weierstrass curve over an integrally-closed base, an integral
`x`-coordinate forces an integral `y`-coordinate, because `y` is then a root of the
*monic* quadratic `T² + (a₁x₀ + a₃)T − (x₀³ + a₂x₀² + a₄x₀ + a₆) ∈ R[T]`, and a UFD
is integrally closed in its fraction field, so a fraction-field root of a monic
`R`-polynomial lies in `R`. This is the standard "`y` is integral once `x` is" step of
the Nagell–Lutz theorem.

Variables / typeclasses involved (Lean side):
- `R : Type*` `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — the base ring (a UFD).
- `K : Type*` `[Field K] [Algebra R K] [IsFractionRing R K]` — the fraction field. (`[DecidableEq K]` is `omit`-ted.)
- `W : WeierstrassCurve R` — the curve; its coefficients `a₁,a₃,a₂,a₄,a₆` are elements of `R`.

Hypotheses (Lean side):
- `hcurve : y² + ι a₁·x·y + ι a₃·y = x³ + ι a₂·x² + ι a₄·x + ι a₆` — `(x,y)` is on the affine curve (`ι = algebraMap R K`).
- `hx : ι x₀ = x` — the `x`-coordinate is integral, witnessed by `x₀ ∈ R`.

Conclusion (math): `y ∈ R` (the `y`-coordinate is integral).

Conclusion (Lean): `IsLocalization.IsInteger R y`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — the "integral `y` from integral `x`" step. Not a named
theorem on its own (Nagell–Lutz is the named result; this is one of its steps), not a
new structure, not listed as a standalone main goal independent of the overall
integrality theorem. It is consumed three times internally to finish off integrality
once `x` is known integral.

(Note: literature width was run EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **n/a**. The body
is a genuine ~15-line proof (monic-quadratic construction + `linear_combination` +
degree/`Monic` bookkeeping + one mathlib call), not a one-liner.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz … torsion point integral coordinates y-coordinate integer proof Weierstrass"             | yes  | If `P=(x,y)` of finite order has integer `x`, then `y` is an integer (and `y²` or `y` constrained by the discriminant) | Wikipedia, PlanetMath, Harvard "Nagell-Lutz, quickly" — universally a textbook step |
|  2 | WebSearch (general form)         | "root of monic polynomial integrally closed domain implies element integral fraction field"           | yes  | `A` integrally closed, `K=Frac A`: a `K`-root of a monic `A[X]` lies in `A` | Wikipedia "Integrally closed domain"; Stacks 0DCK; Stanford/Brandeis notes. The exact engine of the proof. |
|  3 | WebSearch (named-after / source) | "Silverman arithmetic elliptic curves Nagell-Lutz … if x integral then y integral monic quadratic root" | yes  | quadratic with one integral root + integral coeffs ⟹ other root integral (sum of roots `−b/a ∈ R`) | Silverman & Tate, *Rational Points on Elliptic Curves*; this is precisely the `y`-step |
|  4 | ChatGPT MCP                      | (MCP down per task brief — substituted by an extra targeted WebSearch on the integrally-closed engine, row 2) | n/a  | —                                | Fallback used as the brief permits; rows 1–3 already pin the standard form unambiguously |
|  5 | Local references                 | `ls .mathlib-quality/references/` (NagellLutz project)                                                 | n/a  | (directory absent)               | No references dir for this project — recorded n/a |
|  6 | nLab                             | "Nagell-Lutz theorem" / "integrally closed domain"                                                     | n/a  | —                                | Not a categorical concept; nLab has no dedicated Nagell-Lutz page. The integrally-closed engine is bog-standard commutative algebra, fully covered by row 2 sources. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "monic polynomial integrally closed fraction field" → tag 0DCK area; "integral closure"               | yes  | integral closure / integrally-closed characterisation (the algebra engine) | Stacks covers the commutative-algebra engine (integral closure). It does **not** carry the Nagell–Lutz arithmetic statement itself. |
|  9 | MathOverflow / Math.StackExchange| "Nagell-Lutz why is y an integer when x is" (general knowledge)                                         | yes  | same as #1/#3 — monic quadratic in `y`, integral closure | Standard Q&A folklore; consistent with the texts. |
| 10 | recent arXiv (last 5 years)      | "Nagell-Lutz" + torsion integrality (e.g. arXiv math/0011066 Tate-normal-form torsion)                 | yes  | uses the same integrality step as a black box | Confirms it is settled classical background, not a research-frontier statement. |

### Literature summary (Phase 3)

Concept identified as: the **"`y` is integral once `x` is integral"** step of the
**Nagell–Lutz theorem** (Silverman & Tate, *Rational Points on Elliptic Curves*;
Harvard "Nagell-Lutz, quickly"). Its engine is the standard commutative-algebra fact
**"a root in `Frac(A)` of a monic polynomial over an integrally-closed domain `A` lies
in `A`"**.

Sources agree on the standard form: **yes.** Every source proves `y ∈ R` by observing
`y` satisfies the monic quadratic obtained from the Weierstrass equation (with `x`
substituted as an element of `R`), then invokes integral closure. The Lean statement
matches this exactly.

Most general standard form: for the *engine*, `A` integrally closed with `K = Frac A`
(strictly weaker than UFD). For the *arithmetic wrapper*, the statement is curve- and
fraction-field-specific and not separately "generalised" in the literature — it is a
lemma inside Nagell–Lutz, classically stated over `ℤ ⊂ ℚ` and routinely run over any
integrally-closed base.

Generality dimensions where the literature varies:
  - base ring: literature engine wants only **integrally closed** (`A`); the Lean form
    uses **UFD** (`UniqueFactorizationMonoid R`), which is strictly stronger but is the
    typeclass `isInteger_of_is_root_of_monic` itself is stated over — so the Lean form
    is *exactly as general as the mathlib lemma it calls*. Not a defect of this decl.
  - field: any fraction field `K` (general); matches Lean.

Disagreement with the literature: **none.** The Lean statement is the textbook step.

---

## PHASE 4 — Generality analysis

### Generality analysis — `y_isInteger_of_x_isInteger_on_curve`

Literature-standard form (engine): `A` integrally closed, `K = Frac A`, `r ∈ K` a root
of a monic `A[X]` ⟹ `r ∈ A`. Applied to the monic quadratic in `y` from the curve.

| # | Parameter / hypothesis              | Current Lean form            | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened   |
|---|-------------------------------------|------------------------------|-----------------------------------|---------------------|------------------------------------|
| 1 | `[UniqueFactorizationMonoid R]`     | UFD base                     | integrally-closed base            | yes (in principle)  | The proof only needs `R` integrally closed in `K`. But the *only* mathlib lemma that finishes it directly (`isInteger_of_is_root_of_monic`) is itself stated over a UFD, so weakening here would require re-deriving against `IsIntegrallyClosed.isIntegral_iff` instead. The narrowing is **inherited from the mathlib API this calls** — not a flaw to fix in this project. |
| 2 | `[IsDomain R]`                      | integral domain             | integral domain                   | NO                  | Needed for fraction field + integral closure; standard. |
| 3 | `[IsFractionRing R K]`              | `K = Frac R`                 | `K = Frac A`                      | NO                  | Exactly the standard hypothesis. |
| 4 | `hcurve` (curve equation)           | affine Weierstrass equation  | the curve equation                | NO                  | This is what produces the monic quadratic; intrinsic. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *relative to the mathlib lemma it composes
with.* (It could be stated over an integrally-closed base instead of a UFD, but only by
swapping `isInteger_of_is_root_of_monic` for `IsIntegrallyClosed.isIntegral_iff`; the
UFD hypothesis here is the same one mathlib uses for the integral-root theorem, so the
specialisation is API-inherited, not a project-side over-restriction.)

Number of weakening opportunities found: 1 (UFD → integrally-closed), inherited from
the chosen mathlib lemma; not material to the verdict.

Cost of restatement: would be CHEAP-to-MODERATE, but **irrelevant** — this decl is not
going to mathlib on its own (see Phase 7), so the generalisation target is moot.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                           | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses?                                                          | no       | already fully typeclass-driven (`CommRing`/`IsDomain`/`UFM`/`IsFractionRing`) | — |
|  2 | sequences/metric → filters/topology?                                                               | no       | purely algebraic; no analysis | — |
|  3 | construction → universal-property class?                                                            | no       | it's a theorem, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                  | no       | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaker typeclass (module/(semi)ring)?                          | partial  | UFD → integrally-closed (row 1, Phase 4a) | would compose with `IsIntegrallyClosed.isIntegral_iff` instead — but see Phase 7; moot for a non-shipped helper |
|  6 | 1-categorical → higher-categorical?                                                                 | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                                                    | no       | already over an abstract `R` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the one partial — UFD→integrally-closed — is a
generality tweak inherited from the mathlib lemma, not a Bourbaki-2.0 reorganisation,
and is irrelevant because the decl is not a standalone mathlib candidate). The
statement is already in modern, fully-typeclassed mathlib style.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** No definitional equality or typeclass-search
path introduced.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `y_isInteger_of_x_isInteger_on_curve`

[A] Lean-Finder       "y integral from x integral Weierstrass curve point"  → no direct hit (no Nagell-Lutz in mathlib)
[B] Loogle            `IsLocalization.IsInteger _ _` ⊕ `WeierstrassCurve`; `Monic _ → aeval _ _ = 0 → IsInteger _ _` → engine hit only (see [D])
[C] LeanSearch        "second coordinate of a point on a Weierstrass curve is integral when the first is" → no curve-specific hit
[D] Grep mathlib src  `Nagell|Lutz` in `Mathlib/AlgebraicGeometry/EllipticCurve/` → **none** (the `Nagell`/`Lutz`-named files are FieldTheory/Galois, unrelated). `isInteger_of_is_root_of_monic` → **HIT**, Mathlib/RingTheory/Polynomial/RationalRoot.lean:115. `IsInteger`/`integral` in `EllipticCurve/` → only `Reduction.lean`, `DivisionPolynomial/Degree.lean`, `Affine/Point.lean`, none about coordinate integrality of torsion/affine points.
[E] Name pattern      `isInteger_of_*`, `*_of_x_isInteger_*`, `*on_curve*` over mathlib → only the generic root-theorem family (`isInteger_of_is_root_of_monic`, `isInteger_of_isUnit_den`, `RationalRootTheorem.*`); nothing Weierstrass-specific.

Searched for both:
  - the user's current form (Weierstrass `y`-from-`x`): **not in mathlib** — mathlib
    has **no Nagell–Lutz / coordinate-integrality material** for Weierstrass curves at all.
  - the literature-standard *engine* (monic root over UFD ⟹ integer): **in mathlib**,
    `isInteger_of_is_root_of_monic` (RationalRoot.lean:115), stated over
    `[CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [IsFractionRing A K]` — the
    *exact* typeclasses this theorem uses. This lemma is literally the last line of the
    proof (`exact isInteger_of_is_root_of_monic hmonic hroot`).

Concluded: **found the building block** (`isInteger_of_is_root_of_monic`, plus the
`Monic`-construction primitives `Polynomial.Monic.add_of_left`, `monic_X_pow`,
`degree_C_mul_X_le`, `degree_C_le`, `degree_add_eq_left_of_degree_lt`); the
curve-specific wrapper is **not** in mathlib (mathlib has no Nagell–Lutz).

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `y_isInteger_of_x_isInteger_on_curve`

Internal use count: **3** (within the NagellLutz project, excluding the declaring decl).
External-to-file callers: 1 distinct file (PIDIntegralMultiple.lean); plus 2 uses later
in the declaring file.

| Caller file:line                                                      | Usage pattern (one-line excerpt)                                     |
|-----------------------------------------------------------------------|----------------------------------------------------------------------|
| PIDPrimeOrder.lean:170 (`integrality_of_order_four_squarefree`)       | `⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W (… curveK_equation_iff …) hx₀⟩` |
| PIDPrimeOrder.lean:210 (`prime_order_integrality_squarefree`)         | `⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W (… curveK_equation_iff …) hx₀⟩` |
| PIDIntegralMultiple.lean:89                                           | `⟨⟨x₀, hx₀⟩, y_isInteger_of_x_isInteger_on_curve W …⟩`               |

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?):
  - (none) — the three sites all *use* the helper; no inline re-derivation of "build the
    monic quadratic in `y` and apply the root theorem" was found. So it is a real
    internal API node, not dead code.

Call-sites signal: K = 3 internal uses, no inline re-derivation → leans toward a YES-*
bucket *if it were a general-purpose statement*. But the consumers are all
Nagell–Lutz-internal integrality finishers (order-4, odd-prime, integral-multiple
torsion), i.e. the helper is internal plumbing for one theorem, not a library primitive
other developments would reach for. The signal is "genuine project API node", not
"missing mathlib primitive".

### Composition check (Phase 6)

Can `y_isInteger_of_x_isInteger_on_curve` be derived from mathlib in ≤3 chained calls?

Attempt 1 (direct one-liner): `exact isInteger_of_is_root_of_monic hmonic hroot`
  - Mathlib decls used: `isInteger_of_is_root_of_monic`.
  - Result: **partial** — the final call is a single mathlib invocation, but it needs
    two locally-built inputs: `hroot` (that `y` is a root of `X²+C c₁ X+C c₀`) and
    `hmonic` (that the quadratic is monic).
  - Notes: `hroot` is one `simp` + one `linear_combination hcurve` (a genuine algebraic
    step, but mechanical). `hmonic` is degree bookkeeping via mathlib's `Monic.add_of_left`
    / `monic_X_pow` / `degree_C_mul_X_le` / `degree_add_eq_left_of_degree_lt` — ~8 lines,
    all mathlib primitives, no new ideas.

Attempt 2 (can the monic-quadratic step be a single mathlib call?): there is no mathlib
lemma "the `y`-coordinate of a Weierstrass point is a root of a monic quadratic", so the
construction of `X²+C c₁ X+C c₀` and the `linear_combination` proof must be written out.
  - Result: this pushes the derivation just past a literal 3-call inline — it's ~15 lines.

Conclusion: **COMPOSABLE** (in substance) — every step is a mathlib primitive
(`isInteger_of_is_root_of_monic` + the `Monic`/`degree` lemma family + `linear_combination`
on the hypothesis). The proof is slightly longer than a 3-call chain because it must
*name and prove monic* the Weierstrass quadratic, but it introduces **no mathematics
mathlib lacks**: the content is entirely "curve equation ⟹ monic quadratic in `y`" (algebra)
+ "monic root over a UFD ⟹ integer" (`isInteger_of_is_root_of_monic`). No new lemma is
warranted; it is curve-specific glue around an existing mathlib theorem.

---

## Verdict: `LutzNagell.PID.y_isInteger_of_x_isInteger_on_curve`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): standard textbook "`y` integral once `x` integral" step of
  Nagell–Lutz (Silverman & Tate; Harvard note); its engine is the classical
  "monic root over an integrally-closed domain ⟹ integral" — both are settled classical
  background, not research-level statements.
- Generality analysis (Phase 4): MAXIMALLY GENERAL relative to the mathlib lemma it calls
  (the UFD hypothesis is inherited from `isInteger_of_is_root_of_monic`); no modern-idiom
  reorganisation available.
- Mathlib search (Phase 5): the building block `isInteger_of_is_root_of_monic`
  (Mathlib/RingTheory/Polynomial/RationalRoot.lean:115) is in mathlib *with the identical
  typeclasses*; mathlib has **no** Nagell–Lutz / Weierstrass-coordinate-integrality material.
- Composition check (Phase 6): COMPOSABLE — the proof is `isInteger_of_is_root_of_monic`
  applied to the monic quadratic `X²+C c₁ X+C c₀` built from the curve equation (one
  `linear_combination`) with monic-ness from mathlib's `Monic`/`degree` primitives.

**Rationale:**

The mathematically reusable content of this theorem is **already in mathlib in full**:
`isInteger_of_is_root_of_monic` is the integral-root theorem over a UFD, and it is
literally the final line of this proof. Everything the project adds is *curve-specific
glue*: it observes that the Weierstrass equation, after substituting an integral `x = ι x₀`,
exhibits `y` as a root of the monic quadratic `T² + (a₁x₀+a₃)T − (x₀³+a₂x₀²+a₄x₀+a₆)` over
`R`, and then hands that to the mathlib lemma. The "build a monic quadratic from the curve
equation" half is pure algebra (`linear_combination hcurve` plus mathlib's
`Monic.add_of_left` / `monic_X_pow` / `degree_*` bookkeeping) — it produces no result of
independent library value. So mathlib has the building blocks; the statement is glue around
them, slightly longer than a 3-call inline only because the monic quadratic must be named
and proven monic.

The one thing mathlib genuinely lacks is **Nagell–Lutz itself** — there is no
coordinate-integrality material for Weierstrass curves anywhere in
`Mathlib/AlgebraicGeometry/EllipticCurve/`. This `y`-from-`x` helper is a *step inside* that
development. The right way for it to reach mathlib is **as part of a Nagell–Lutz
contribution**, packaged with the `x`-integrality results it serves — not as a standalone
lemma. As an isolated decl, it is NO-composable: the engine is `isInteger_of_is_root_of_monic`,
and the remainder is the curve-equation algebra that belongs with the theorem it finishes.

WHY not (refactor-actionable):
  - Mathlib has the building blocks. The load-bearing primitive is
    `isInteger_of_is_root_of_monic` (the integral-root theorem over a UFD). The rest of the
    proof is the monic-quadratic construction, which is *specific to the Weierstrass
    equation* and carries no reusable mathematical content on its own. No new mathlib lemma
    is warranted; the right home for this reasoning is inside a future mathlib Nagell–Lutz
    file, alongside the `x`-integrality theorems.
  - This is NOT a "delete and inline at call sites" within the AINTLIB project. Locally the
    helper is a legitimate API node (3 internal consumers, no inline re-derivation) and
    should stay as-is. The NO-composable verdict is about **mathlib**: relative to mathlib,
    this is curve glue over `isInteger_of_is_root_of_monic`, not a missing primitive.

Mathlib building blocks:
  - `isInteger_of_is_root_of_monic`  — Mathlib/RingTheory/Polynomial/RationalRoot.lean:115
    (over `[CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [IsFractionRing A K]`)
  - `Polynomial.Monic.add_of_left`, `Polynomial.monic_X_pow`, `Polynomial.degree_C_mul_X_le`,
    `Polynomial.degree_C_le`, `Polynomial.degree_add_eq_left_of_degree_lt` — the `Monic`/degree
    bookkeeping (all in Mathlib/Algebra/Polynomial/…).
  - `linear_combination` (tactic) for the root identity from `hcurve`.

Composition sketch (the actual proof, condensed — this is what an inlined derivation is):
```lean
example {x y : K} {x₀ : R}
    (hcurve : y^2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x^3 + algebraMap R K W.a₂ * x^2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    (hx : algebraMap R K x₀ = x) : IsLocalization.IsInteger R y := by
  set c₁ : R := W.a₁ * x₀ + W.a₃
  set c₀ : R := -(x₀^3 + W.a₂ * x₀^2 + W.a₄ * x₀ + W.a₆)
  have hroot : aeval y (X^2 + C c₁ * X + C c₀ : R[X]) = 0 := by
    simp only [map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C, c₁, c₀]
    have hc := hcurve; rw [← hx] at hc; linear_combination hc
  have hmonic : (X^2 + C c₁ * X + C c₀ : R[X]).Monic := by
    apply Polynomial.Monic.add_of_left
    · exact .add_of_left (monic_X_pow 2)
        (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))
    · exact degree_C_le.trans_lt (by
        rw [degree_add_eq_left_of_degree_lt
          (degree_C_mul_X_le c₁ |>.trans_lt (by norm_num [degree_X_pow]))]
        norm_num [degree_X_pow])
  exact isInteger_of_is_root_of_monic hmonic hroot   -- the single mathlib call
```
(This is exactly the present proof — it *is* the composition; nothing mathlib-shaped is
missing from it.)

Call sites in our project (from Phase 6.0): K = 3 (PIDPrimeOrder.lean:170, :210;
PIDIntegralMultiple.lean:89).
Refactor plan (mathlib-facing, not AINTLIB-facing): **do not delete this from AINTLIB.**
It is correct project plumbing and should remain. When/if Nagell–Lutz is contributed to
mathlib, this `y`-from-`x` step ships *inside that PR* (e.g. `Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean`),
co-located with the `x`-integrality theorems (`isInteger_of_root_squarefree_leading_coeff`,
`x_isInteger_of_odd_prime_torsion_squarefree`, etc.), reusing
`isInteger_of_is_root_of_monic` exactly as it does now. It is not a separable standalone
mathlib lemma.

Next action (mathlib): keep the helper in AINTLIB unchanged; treat it as part of the
Nagell–Lutz package for any future upstreaming, not as an individual contribution. No
standalone mathlib PR for this decl.

---

## Next step

Keep `y_isInteger_of_x_isInteger_on_curve` in the AINTLIB NagellLutz project as-is (it is
sound internal API with 3 consumers). For mathlib purposes it is **NO-composable-from-mathlib**:
the engine `isInteger_of_is_root_of_monic` already exists; the remainder is Weierstrass-equation
glue. It would only reach mathlib bundled inside a full Nagell–Lutz contribution, not as a
standalone lemma.
