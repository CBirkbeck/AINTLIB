# /mathlibable report — `LutzNagell.LutzNagellTheorem.y_integral_of_x_integral_on_general_curve`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task instructions; reasoning from source).
- decl `LutzNagell.LutzNagellTheorem.y_integral_of_x_integral_on_general_curve`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:31`
- qualified name:           `LutzNagell.LutzNagellTheorem.y_integral_of_x_integral_on_general_curve`
                            (VERIFIED: file opens `namespace LutzNagell` / `namespace LutzNagellTheorem`; base name as parsed.)
- kind:                     theorem
- has sorry:                no
- module docstring summary: "Prime-order and order-4 torsion integrality for general Weierstrass curves."

---

### Statement (Phase 1)

`y_integral_of_x_integral_on_general_curve` states: let `W` be a Weierstrass curve with integer
coefficients `a₁,…,a₆ ∈ ℤ`, and let `(x, y) ∈ ℚ²` be a point on the affine Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. If the `x`-coordinate is an integer (`∃ x₀ ∈ ℤ, x₀ = x`),
then the `y`-coordinate is an integer (`∃ y₀ ∈ ℤ, y₀ = y`).

Mathematically: `y` is a root of the **monic** quadratic
`Y² + (a₁x₀ + a₃)Y − (x₀³ + a₂x₀² + a₄x₀ + a₆) ∈ ℤ[Y]`, so since `ℤ` is integrally closed in its
fraction field `ℚ`, `y ∈ ℤ`. This is the standard "vertical step" in the proof of the Nagell–Lutz
theorem (Silverman, *Arithmetic of Elliptic Curves* VIII.7; Alpoge, *Nagell–Lutz, quickly*).

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — the integral Weierstrass curve (coefficients `W.aᵢ : ℤ`).

Hypotheses (Lean side):
- `{x y : ℚ}` — affine coordinates, implicit.
- `hcurve : y^2 + a₁·x·y + a₃·y = x^3 + a₂·x^2 + a₄·x + a₆` (coefficients cast `ℤ → ℚ`) — the point lies on the curve.
- `{x₀ : ℤ}`, `hx : (x₀ : ℚ) = x` — the x-coordinate is integral.

Conclusion (math): `y ∈ ℤ`.
Conclusion (Lean): `∃ y₀ : ℤ, (y₀ : ℚ) = y`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: helper lemma — the "y integral from x integral" sub-step of Nagell–Lutz; not a `def`/structure,
not the project's headline result, not itself a named theorem (it is one ingredient of the named
Nagell–Lutz theorem). It feeds `integrality_of_order_four_general` and `prime_order_integrality_general`.

(Literature width run at full EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` → n/a. (Body is ~12 lines: build the monic quadratic, verify the root with `nlinarith`,
prove `Monic`, apply `isInteger_of_is_root_of_monic`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz … if x-coordinate is integer then y-coordinate is integer Weierstrass monic polynomial"   | yes  | y root of monic quadratic over ℤ ⇒ y ∈ ℤ                         | Wikipedia, Silverman; the standard "vertical" sub-step |
|  2 | WebSearch (general form)         | (same search surfaced) Alpoge "Nagell-Lutz, quickly"; Silverman AEC VIII                                 | yes  | general statement: ℤ integrally closed ⇒ root of monic poly is integral | the content is integral-closedness of a UFD/Dedekind ring |
|  3 | WebSearch (named-after/aliases)  | "Nagell-Lutz theorem proof" (Wikipedia / planetmath / Harvard Alpoge notes / Notre Dame Lecture 3)      | yes  | torsion ⇒ integral coords; this lemma is the y-from-x half       | universally stated as a one-line consequence of x∈ℤ |
|  4 | ChatGPT MCP                      | (MCP down per task env; substituted by reading Silverman-style proofs surfaced in #1–#3)                 | n/a  | —                                                                | env: ChatGPT MCP unavailable; covered by #1–#3 + mathlib source |
|  5 | Local references                 | `.mathlib-quality/references/` and `refs/` for "Nagell"/"integral"                                       | n/a  | neither directory exists                                         | dirs absent — recorded n/a |
|  6 | nLab                             | "Nagell-Lutz" / "integral closure" relevance                                                            | n/a  | not an nLab-style categorical concept                            | the underlying lemma (integral closure) is in mathlib already |
|  7 | nCatLab                          | —                                                                                                       | n/a  | not a categorical concept                                       | — |
|  8 | Stacks Project                   | integrally closed domain / root of monic                                                                | n/a (relevant tag exists) | "integrally closed = every root in K of a monic poly over A is in A" | exactly the principle; mathlib's `IsIntegrallyClosed` already encodes it |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz x integer ⇒ y integer                                                                       | yes  | folklore one-liner: substitute, get monic quadratic in y         | confirms triviality given x∈ℤ |
| 10 | recent arXiv (last 5 yrs)        | Nagell-Lutz integrality                                                                                  | n/a  | classical 1930s result; no recent reformulation                  | nothing newer than the standard statement |

### Literature summary (Phase 3)

Concept identified as: the **y-from-x integrality step of the Nagell–Lutz theorem** — i.e. once the
x-coordinate of a curve point is an integer, the y-coordinate is a root of a monic quadratic over ℤ,
hence integral because ℤ is integrally closed in ℚ.
Sources agree on the standard form: yes. Every reference (Silverman, Alpoge, Wikipedia, planetmath)
treats it as an immediate consequence of x ∈ ℤ via the monic quadratic in y.
Most general standard form: "Let `A` be an integrally closed domain (e.g. a UFD/Dedekind/PID) with
fraction field `K`; if `x ∈ A` then the point's `y ∈ K` is integral over `A`, hence in `A`." The ℤ/ℚ
statement is the classical special case.
Generality dimensions where the literature varies:
  - base ring: ℤ → any integrally closed domain / UFD / Dedekind domain (general elliptic-curves-over-`R` theory; e.g. Silverman AEC over a Dedekind ring).
  - the actual driver is `isInteger_of_is_root_of_monic` / `IsIntegrallyClosed`, which is ring-theory, not elliptic-curve-specific.
Disagreement with the literature: none — the Lean statement is the textbook ℤ/ℚ form.

---

### Generality analysis — `y_integral_of_x_integral_on_general_curve`

Literature-standard form (from Phase 3): root of a monic polynomial over an integrally closed domain
lies in the ring; applied to the Weierstrass quadratic in y over `R = ℤ`, `K = ℚ`.

| # | Parameter / hypothesis              | Current Lean form          | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|----------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`            | curve over ℤ               | curve over any UFD / int. closed `R` | YES             | proof uses only that `R = ℤ` is integrally closed in `K = ℚ`; nothing ℤ-specific |
| 2 | `{x y : ℚ}`                         | coords in ℚ                | coords in `K = Frac R`            | YES                 | the field ℚ is only used as `Frac ℤ`; any `IsFractionRing R K` works |
| 3 | `(hcurve : … = …)` over ℚ           | curve equation over ℚ      | curve equation over `K`           | YES                 | algebraic identity holds over any commutative ring |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD.
Number of weakening opportunities found: 3 (base ring ℤ → UFD/integrally-closed; field ℚ → `Frac R`; equation over ℚ → over `K`).
Proposed restatement: **already exists in this project, verbatim.**
`LutzNagell.PID.y_isInteger_of_x_isInteger_on_curve`
(`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:37`), with signature

```lean
variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

theorem y_isInteger_of_x_isInteger_on_curve
    {x y : K}
    (hcurve : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {x₀ : R} (hx : algebraMap R K x₀ = x) :
    IsLocalization.IsInteger R y
```

The `ℚ`-specific decl under assessment is the `R = ℤ, K = ℚ` specialization of this (ℤ is a
`UniqueFactorizationMonoid`, and `Rat.isFractionRing : IsFractionRing ℤ ℚ` exists —
`Mathlib/RingTheory/Localization/FractionRing.lean:65`). Both proofs are byte-for-byte the same shape
(build the monic quadratic with `c₁ = a₁x₀ + a₃`, `c₀ = -(x₀³ + a₂x₀² + a₄x₀ + a₆)`, then
`isInteger_of_is_root_of_monic`).

Cost of restatement: CHEAP — the general form is already proved; the ℚ-version is a specialization.
(But note: the project keeps the General*/PID* tracks deliberately split, so this duplication is
intentional within the project; the relevant point for mathlib is that mathlib would never want the
ℚ-only specialization.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                          | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|-------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                         | no       | already typeclass-driven (`WeierstrassCurve`)   | — |
|  2 | sequences/metric → filters/topological?                                                          | no       | no analytic content                             | — |
|  3 | construct an object where a universal-property class fits?                                         | no       | it's a propositional integrality statement      | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | no substructure here                            | — |
|  5 | vector-space/metric/field-specific → weaken typeclass to module/ring?                              | yes      | base ℤ → integrally-closed domain / UFD with `IsFractionRing R K` | precisely the PID-track form above (`isInteger_of_is_root_of_monic` lives at this generality) |
|  6 | 1-categorical → higher-categorical?                                                               | no       | n/a                                              | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/monoid?                                              | yes      | ℤ → general base ring (same as row 5)            | unifies with elliptic-curves-over-`R` API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — generalise the base ring ℤ to an integrally-closed domain / UFD with
`IsFractionRing R K`. This is exactly the project's own `PID.y_isInteger_of_x_isInteger_on_curve`.
Real mathematical improvement: yes (the integrality argument never uses anything about ℤ beyond integral
closedness), BUT — critically — even the generalised form is **not a mathlib candidate**: its entire
non-curve content is `isInteger_of_is_root_of_monic`, which mathlib already has. So the modernisation
target is "use the existing mathlib lemma + curve-specific glue", not "add a new mathlib lemma".

---

### Diamond / defeq risk — `y_integral_of_x_integral_on_general_curve`

n/a — declaration kind is `theorem`.

---

### Mathlib search-status: `y_integral_of_x_integral_on_general_curve`

[A] Lean-Finder       "y integral from x integral on Weierstrass curve" / "root of monic ⇒ integer"  no hits for the curve form; the ring lemma is `isInteger_of_is_root_of_monic`
[B] Loogle            `IsInteger _ _`, `Monic _ → aeval _ _ = 0 → IsInteger _ _`                       hit: `isInteger_of_is_root_of_monic` (the building block); no Weierstrass-specific hit
[C] LeanSearch        "if x integer and point on elliptic curve then y integer"                        no hit (no Nagell–Lutz in mathlib)
[D] Grep mathlib src  `Nagell`, `y_integral`, `y_isInteger`, `den_dvd_of_is_root` in EllipticCurve/ + NumberTheory/  no Nagell–Lutz anywhere; no Weierstrass integral-coordinate lemma
[E] Name pattern      `isInteger_of_is_root_of_monic`, `IsIntegrallyClosed`, `integer_of_integral`     building blocks present (`Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`, `:135`)

Searched for both:
  - the user's current ℚ/ℤ form — **not in mathlib** (no Nagell–Lutz, no Weierstrass integral-y lemma);
  - the literature-standard general form — the *ring-theoretic core* IS in mathlib:
    `RationalRootTheorem.isInteger_of_is_root_of_monic` (root of a monic poly over a UFD lies in the ring)
    and `UniqueFactorizationMonoid.integer_of_integral` / `IsIntegrallyClosed`. The curve-specific
    wrapper is not, and should not be (it's just substitution into the equation).

Concluded: "found building blocks (`RationalRootTheorem.isInteger_of_is_root_of_monic`,
`Polynomial.Monic.add_of_left`, `degree_C_mul_X_le`, `monic_X_pow`); composition would yield our form."
The Weierstrass-specific statement is **not** in mathlib and is not a general-purpose lemma mathlib would host.

---

### Call sites — `y_integral_of_x_integral_on_general_curve`

Internal use count: 2 (within the project, excluding the declaring lines)
External-to-file callers: 0 distinct files (both uses are in the **same** file, `GeneralPrimeOrder.lean`)

| Caller file:line                         | Usage pattern (one-line excerpt)                                                |
|------------------------------------------|----------------------------------------------------------------------------------|
| GeneralPrimeOrder.lean:141               | `⟨⟨x.num, hx₀⟩, y_integral_of_x_integral_on_general_curve W … hx₀⟩` (order-4)   |
| GeneralPrimeOrder.lean:156               | `⟨⟨x₀, hx₀⟩, y_integral_of_x_integral_on_general_curve W … hx₀⟩` (odd prime)    |

Inline-derivation grep (equivalent re-derived elsewhere?):
  - `PID.y_isInteger_of_x_isInteger_on_curve` (PIDPrimeOrder.lean:37) — the **more general** twin, used 3×
    (PIDPrimeOrder.lean:170,210; PIDIntegralMultiple.lean:89). Same monic-quadratic + `isInteger_of_is_root_of_monic`
    argument over a general UFD. This is the deliberate General/PID track split, not accidental duplication.

Signal: 2 internal uses, both in the declaring file, with a strictly-more-general project twin already
proving the same fact. Composability signal leans NO-composable (it's a curve-specific wrapper around a
mathlib lemma, re-derivable in ≤3 calls).

---

### Composition check (Phase 6)

Can `y_integral_of_x_integral_on_general_curve` be derived from mathlib in ≤3 chained calls?

Attempt 1: build the monic quadratic `q := X^2 + C (a₁x₀+a₃) * X + C (-(x₀³+a₂x₀²+a₄x₀+a₆)) : ℤ[X]`;
  (i) `hroot : aeval y q = 0` is the curve equation rearranged (the existing proof discharges it with
      `push_cast; nlinarith`); (ii) `hmonic : q.Monic` via `Polynomial.Monic.add_of_left (monic_X_pow 2) …`;
  (iii) apply `RationalRootTheorem.isInteger_of_is_root_of_monic hmonic hroot` to get `IsInteger ℤ y`,
  then unwrap `RingHom.mem_rangeS` to `∃ y₀ : ℤ, (y₀:ℚ) = y`.
  - Mathlib decls used: `isInteger_of_is_root_of_monic`, `Polynomial.Monic.add_of_left`, `monic_X_pow`,
    `degree_C_mul_X_le`, `RingHom.mem_rangeS`.
  - Result: succeeds — this IS the existing proof body.
  - Notes: the single load-bearing mathlib call is `isInteger_of_is_root_of_monic`. The remaining lines
    are (a) the `Monic` proof — pure boilerplate over `ℤ[X]` — and (b) the `nlinarith` that checks the
    root condition, which is just the curve equation. None of this is new mathematics; it is substitution.

Conclusion: COMPOSABLE — the user's statement is a ≤3-mathlib-call composition (monic-quadratic
construction + `isInteger_of_is_root_of_monic`), with the only non-boilerplate step being a one-line
`nlinarith` that re-expresses the Weierstrass equation. No new mathlib lemma is warranted.

---

## Verdict: `LutzNagell.LutzNagellTheorem.y_integral_of_x_integral_on_general_curve`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the y-from-x step of Nagell–Lutz; universally a one-line consequence of
  x ∈ ℤ via a monic quadratic in y — i.e. integral-closedness of ℤ, which is ring theory mathlib already has.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (ℤ/ℚ specialization); the general form
  is `PID.y_isInteger_of_x_isInteger_on_curve`, already in the project — but even it reduces to a mathlib lemma.
- Mathlib search (Phase 5): the user's curve form is NOT in mathlib; the **building block**
  `RationalRootTheorem.isInteger_of_is_root_of_monic` IS (`Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`).
- Composition check (Phase 6): COMPOSABLE — monic-quadratic construction + `isInteger_of_is_root_of_monic`,
  ≤3 calls; the only non-boilerplate is a `nlinarith` re-expressing the curve equation.

**Rationale:**

The mathematical content here is entirely the **rational/integral root theorem** — "a root in ℚ of a
monic polynomial over ℤ is an integer" — which mathlib provides as
`RationalRootTheorem.isInteger_of_is_root_of_monic` (and more abstractly via `IsIntegrallyClosed`, with
ℤ-as-integrally-closed coming free from `UniqueFactorizationMonoid.instIsIntegrallyClosed`). Everything
this theorem adds beyond that lemma is Weierstrass-equation-specific glue: assemble the monic quadratic
`Y² + (a₁x₀+a₃)Y − (x₀³+a₂x₀²+a₄x₀+a₆)`, observe (via `nlinarith`) that `y` is a root once `x = x₀ ∈ ℤ`,
and apply the lemma. That is substitution into a fixed equation, not a reusable theorem. It is also
narrowly ℚ/ℤ-specific: the project itself already carries the correct general statement,
`PID.y_isInteger_of_x_isInteger_on_curve`, over an arbitrary UFD with a fraction field — and even that
general version is just the same `isInteger_of_is_root_of_monic` call. Mathlib would not host either:
the abstract ingredient is already there, and the curve-specific wrapper belongs inline at its call sites
(here, the two Nagell–Lutz integrality proofs), exactly as it is used.

**WHY not (refactor-actionable):**
Mathlib has the building block; the user's form is a 1–3-mathlib-call composition. There is no missing
mathlib API — `isInteger_of_is_root_of_monic` is the whole engine. The wrapper exists only to package
the Weierstrass quadratic, which is local to the Nagell–Lutz development.

Mathlib building blocks:
- `RationalRootTheorem.isInteger_of_is_root_of_monic` — `Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`
- `Polynomial.Monic.add_of_left`, `Polynomial.monic_X_pow`, `Polynomial.degree_C_mul_X_le` — `Mathlib/Algebra/Polynomial/Monic.lean`, `Mathlib/Algebra/Polynomial/Degree/*`
- `RingHom.mem_rangeS` (to convert `IsInteger ℤ y` to `∃ y₀ : ℤ, (y₀:ℚ) = y`)

Composition sketch (≤3 lines, mirrors the existing proof):
```lean
example (W : WeierstrassCurve ℤ) {x y : ℚ}
    (hcurve : y^2 + (W.a₁:ℚ)*x*y + (W.a₃:ℚ)*y = x^3 + (W.a₂:ℚ)*x^2 + (W.a₄:ℚ)*x + (W.a₆:ℚ))
    {x₀ : ℤ} (hx : (x₀:ℚ) = x) : ∃ y₀ : ℤ, (y₀:ℚ) = y :=
  -- set c₁ := W.a₁*x₀+W.a₃, c₀ := -(x₀^3+W.a₂*x₀^2+W.a₄*x₀+W.a₆); q := X^2 + C c₁*X + C c₀
  -- hroot : aeval y q = 0   (by push_cast/nlinarith from hcurve, hx)
  -- hmonic : q.Monic        (Monic.add_of_left (monic_X_pow 2) …)
  -- RingHom.mem_rangeS.mp (isInteger_of_is_root_of_monic hmonic hroot)
  sorry
```

Call sites in our project (from Phase 6.0): 2 (both in `GeneralPrimeOrder.lean`:141, :156).

Refactor plan (note: this is a NON-`main` producer-branch project; the General/PID split is intentional,
so deletion is a *project* call, not a fleet cleanup action):
- Option A (mathlib-perspective answer): do NOT upstream. There is nothing for mathlib here beyond the
  existing `isInteger_of_is_root_of_monic`. If the project ever wants this de-duplicated, the wrapper
  can be inlined at the two call sites (lines 141 and 156) using the composition sketch above, or simply
  replaced by `PID.y_isInteger_of_x_isInteger_on_curve` instantiated at `R = ℤ, K = ℚ` (then convert
  `IsInteger ℤ y` ↦ `∃ y₀ : ℤ, (y₀:ℚ) = y` via `RingHom.mem_rangeS`/`IsFractionRing` — one line).
- Argument-flow note: callers pass `W`, `hcurve` (from `curveQ_equation_iff`), `hx`; an inlined version
  keeps the same arguments. The PID twin returns `IsLocalization.IsInteger R y` rather than the existential,
  so a call-site replacement needs the one-line `mem_rangeS` unwrap that this decl already performs.

Next action: no mathlib PR. (For the project: optionally inline the composition at the 2 call sites in
`GeneralPrimeOrder.lean`, or specialise `PID.y_isInteger_of_x_isInteger_on_curve` to ℤ/ℚ — a producer-branch
dedup decision, out of scope for mathlib upstreaming.)

---

## Next step

No mathlib contribution. The result is a ≤3-call composition over the existing mathlib lemma
`RationalRootTheorem.isInteger_of_is_root_of_monic`; if de-duplication is desired within the project,
inline it at the two call sites in `GeneralPrimeOrder.lean` or specialise the more-general
`PID.y_isInteger_of_x_isInteger_on_curve`.
