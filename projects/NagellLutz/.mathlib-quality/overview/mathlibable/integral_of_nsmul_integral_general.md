# /mathlibable report — `LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoned from source + mathlib `.lake/packages/mathlib`
- decl `LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean:82` (theorem head; `:= by`-proof body opens at line 88 — the `:98` in the task brief points into the body)
- kind:                      theorem
- has sorry:                 no
- true qualified name:       `LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general` (file opens `namespace LutzNagell` then `namespace LutzNagellTheorem`) — matches the task brief's parsed name
- module docstring summary:  "Integral multiple implies integral point (general Weierstrass curves)": if `n • P` has integral affine coordinates on a general Weierstrass curve over ℚ with integral coefficients, then `P` already has integral affine coordinates. The docstring explicitly states this is the `R = ℤ`, `K = ℚ` specialisation of the `LutzNagell.PID` lemmas, with `IsLocalization.IsInteger ℤ x` unfolded to `∃ x₀ : ℤ, (x₀ : ℚ) = x`, and that `curveQ W` is definitionally `PID.curveK ℤ ℚ W`.

---

### Statement (Phase 1)

`integral_of_nsmul_integral_general` is a theorem stating the following:

Let `W : WeierstrassCurve ℤ` be a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
with `aᵢ ∈ ℤ`, and let `curveQ W` be its base change to ℚ. Let `P = (x, y)` be a nonsingular affine
point on `curveQ W`, and `n` a nonzero integer such that `n • P = P' = (x', y')` is also a nonsingular
affine point. If `P'` has integral affine coordinates (`x', y' ∈ ℤ`), then `P` has integral affine
coordinates (`x, y ∈ ℤ`). This is the **integral-descent step** of the Nagell–Lutz theorem: integrality
of a nonzero multiple forces integrality of the point.

Variables / typeclasses involved (Lean side):
- `(W : WeierstrassCurve ℤ)` — an integral Weierstrass curve (the file's section variable).
- `{x y : ℚ}` — the affine coordinates of `P`, a priori only rational.
- `{n : ℤ}` — the multiplier.
- `{x' y' : ℚ}` — the affine coordinates of `P' = n • P`.

Hypotheses (Lean side):
- `(hns : (curveQ W).toAffine.Nonsingular x y)` — `P` is a nonsingular point.
- `(hn : n ≠ 0)` — nonzero multiplier.
- `(hns' : (curveQ W).toAffine.Nonsingular x' y')` — `P'` is nonsingular.
- `(hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')` — `n • P = P'`.
- `(hx' : ∃ x₀ : ℤ, (x₀ : ℚ) = x')` — `x'` is integral.
- `(hy' : ∃ y₀ : ℤ, (y₀ : ℚ) = y')` — `y'` is integral (passed to `PID.isInteger_of_nsmul_isInteger`, where the corresponding parameter `_hy'` is unused; `y`-integrality of `P` is re-derived from `x`-integrality via the curve equation).

Conclusion (math): `x ∈ ℤ` and `y ∈ ℤ`.

Conclusion (Lean): `(∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`.

Proof shape (4 lines): the entire body is a wrapper — it calls `PID.isInteger_of_nsmul_isInteger W …`
(re-casting `n ≠ 0` to `(n : ℤ) ≠ 0` via `exact_mod_cast`, and converting each `∃ x₀ : ℤ, (x₀ : ℚ) = ·`
hypothesis to `IsLocalization.IsInteger ℤ ·` via the local lemma `isInteger_int_iff`), then converts the
two resulting `IsLocalization.IsInteger ℤ` conclusions back to the `∃ cast` form, again via
`isInteger_int_iff`. **All mathematical content is delegated to the PID lemma.**

---

### Size classification (Phase 2a)

Verdict: BIG (borderline) — it is a structural step of a **named theorem** (Nagell–Lutz). On its own it
is a `theorem` (not a new structure), but it is one of the load-bearing lemmas of a person-named result,
so by the skill's "named after a person" criterion it is treated as BIG.
Reason: integral-descent step of the Nagell–Lutz theorem; the two call sites (`GeneralMain.lean:74, 102`)
are inside the helper lemmas feeding the ℤ/ℚ Nagell–Lutz main theorem `lutz_nagell_integrality_general`.

(Literature width run EXHAUSTIVE regardless of BIG/SMALL.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-line check is n/a. (Body is ≈4 substantive lines of
`exact_mod_cast`/`isInteger_int_iff` plumbing over one delegated `PID.isInteger_of_nsmul_isInteger` call.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem proof if n*P integral point then P integral elliptic curve division polynomial monic" | yes  | x(n·P) = φₙ/ψₙ²; `numₙ(x,y)` monic in x; "if n·(x,y) integral then x,y ∈ ℤ" | Wikipedia, Harvard "Nagell-Lutz, quickly" (Alpoge), MIT 18.782 Lec #24, arXiv:1108.3051, arXiv:0802.2651 — all give the monic-numerator descent route |
|  2 | WebSearch (general form)         | "elliptic curve multiplication by n x-coordinate phi_n psi_n^2 division polynomial integrally closed integral point descent" | yes  | x(nP) = φₙ/ψₙ², φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁; [n]P = (φ/ψ², ω/ψ³) | Wikipedia "Elliptic curve point multiplication"; arXiv:1108.3051 (explicit valuations of division polynomials); gₙ=gcd(φₙ,ψₙ²) ∣ Δ-power |
|  3 | WebSearch (named-after / aliases / generalisation)| "Nagell-Lutz theorem generalization number fields imaginary quadratic ring of integers Dedekind domain" | yes  | same descent lemma, base ring = ring of integers `𝒪_K` of a number field | arXiv:2509.07524 "Nagell-Lutz for Imaginary Quadratic Fields"; Wikipedia: "generalizes to arbitrary number fields and more general cubic equations"; Anqi Li p-adic notes — confirms ℤ/ℚ is a specialisation, not the ceiling |
|  4 | ChatGPT MCP                      | (intended) "Is this descent lemma ℤ/ℚ-specific or naturally over a UFD/integrally-closed domain? Is ℤ/ℚ a pure specialisation of the UFD form?" | n/a  | —                                | MCP server down per task brief. Substituted by the literature (rows 1–3, 9, 10) + the project's own sorry-free UFD twin `PID.isInteger_of_nsmul_isInteger`, which answers the generality question empirically (the ℤ/ℚ theorem's proof *is* a one-line call to the UFD one). |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/` for "Nagell" / "division polynomial" | n/a  | (no references dir)                | `projects/NagellLutz/.mathlib-quality/references/` absent; `refs/` absent. Recorded n/a. |
|  6 | nLab                             | "Nagell-Lutz theorem" / "elliptic curve torsion"                                                       | n/a  | —                                | nLab has no Nagell–Lutz page; the descent lemma is an arithmetic, not categorical, statement. n/a — not a categorical concept. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "elliptic curve torsion integral point"                                                                | n/a  | —                                | Stacks treats the foundational scheme-theory of elliptic curves but not the arithmetic of rational torsion / Nagell–Lutz. n/a. |
|  9 | MathOverflow / Math.StackExchange| "Nagell-Lutz nP integral implies P integral division polynomial generality"                            | yes  | confirms standard route; threads note the argument needs only an integrally-closed / DVR base | MO/MSE threads on Nagell–Lutz proofs reproduce the monic-numerator + bounded-denominator argument |
| 10 | recent arXiv (last 5 years)      | "Nagell-Lutz theorem imaginary quadratic / number field generalization"                                | yes  | arXiv:2509.07524 (2025) "Nagell–Lutz Theorem for Imaginary Quadratic Fields and class groups"; arXiv:1108.3051 | the theorem is actively GENERALISED beyond ℤ/ℚ — number fields, class number one — i.e. ℤ/ℚ is a specialisation, not the natural ceiling |

Protocol pass: WebSearch ran 3 distinct queries at different generality levels (specific descent form / general
φₙ-ψₙ² multiplication form / named-after-and-generalisation) ✓; ChatGPT MCP attempted but server down, documented
with a substitute ✓; local refs checked (absent → n/a) ✓; nLab checked ✓; Stacks/nCatLab/MO/arXiv each checked or
n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: the **integral-descent step of the Nagell–Lutz theorem** — "if `n • P` is an
integral point then `P` is integral" — proved via the multiplication-by-`n` x-coordinate formula
`x([n]P) = φₙ(P)/ψₙ(P)²` (mathlib names: `Φₙ`/`ΨSqₙ`), with `Φₙ` monic in x and `deg Φₙ > deg ΨSqₙ`,
reducing `x`-integrality to the integral-root theorem for monic integer polynomials.

Sources agree on the standard form: yes. Every treatment (Silverman AEC VIII; Washington; the MIT 18.782
lecture; Alpoge's "Nagell-Lutz, quickly"; Wikipedia; the EDS / explicit-valuation literature
arXiv:1108.3051, arXiv:0802.2651) uses the same division-polynomial denominator route.

Most general standard form: the argument needs only that the base ring is **integrally closed in its
fraction field** (so a fraction-field element that is a root of a monic polynomial over the ring lies in
the ring). It is stated over ℤ/ℚ for the classical Nagell–Lutz, and the literature (arXiv:2509.07524;
p-adic notes; Wikipedia's "arbitrary number fields") generalises it to rings of integers of number fields /
DVRs. The project itself proves the **UFD** version (`R` a `UniqueFactorizationMonoid`, `K = Frac R`),
which is the mathlib-natural generality because mathlib's integral-root theorem
`isInteger_of_is_root_of_monic` is stated exactly there (UFD `A` with `IsFractionRing A K`).

Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → ring of integers of a number field → general integrally closed / DVR / UFD.
    Most general standard = integrally closed domain; mathlib-natural realisation = UFD.
  - integrality predicate: "`∈ ℤ`" → "in the image of `algebraMap R K`" = `IsLocalization.IsInteger R`.

Disagreement with the literature: none. The Lean statement is the literal ℤ/ℚ instance of the standard
lemma.

---

### Generality analysis — `integral_of_nsmul_integral_general`

Literature-standard form (from Phase 3): the same lemma over an integrally closed domain `R` with fraction
field `K`. Mathlib-natural realisation: `R` a UFD, `K = Frac R`, integrality = `IsLocalization.IsInteger R`.

| # | Parameter / hypothesis                | Current Lean form                         | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|-------------------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | base ring of the curve `W`            | `WeierstrassCurve ℤ`                       | `WeierstrassCurve R`, `R` UFD/integrally closed | YES             | Proof uses only `Φ`/`ΨSq ∈ R[X]`, `Φ` monic, and the integral-root theorem — all available over any UFD. |
| 2 | coordinate field                      | `ℚ` (`curveQ W`)                           | `K = Frac R`                              | YES                 | Nothing uses ℚ specifically; only `IsFractionRing R K`. `curveQ W` is *definitionally* `curveK ℤ ℚ W` (both are `W.map (algebraMap _ _)`; `algebraMap ℤ ℚ = Int.castRingHom ℚ` by `algebraMap_int_eq`). |
| 3 | integrality predicate                 | `∃ x₀ : ℤ, (x₀ : ℚ) = x`                   | `IsLocalization.IsInteger R x` (`∈ range (algebraMap R K)`) | YES   | The `∃ cast` predicate is literally `IsInteger ℤ` over ℚ unfolded — proved by the file's own one-line `isInteger_int_iff`. |
| 4 | `n ≠ 0`                               | `(n : ℤ), n ≠ 0`                           | `n ≠ 0` in ℤ AND `(n : R) ≠ 0`            | NO (essential)      | Both forms are essential to `natDegree_ΨSq` / monicity; the PID twin carries `n ≠ 0` and `(n:R) ≠ 0` separately. (Over ℤ the second follows from the first by `exact_mod_cast`.) |

**This generalisation is not hypothetical — the project has already done it.**
`LutzNagell.PID.isInteger_of_nsmul_isInteger`
(`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:80`, namespace `LutzNagell.PID`)
is the verbatim UFD-general form: `{R} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`,
`{K} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]`, `W : WeierstrassCurve R`, conclusion
`IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`. The target theorem's *entire proof* is a
one-line call to it. The project's own `/overview` duplications analysis
(`analysis/05-duplications.md`) records this `General` decl — and every other line of the General track —
as **"special-case of PID"**.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `R := ℤ`, `K := ℚ` instance of the
UFD-general lemma the project already proves sorry-free).
Number of weakening opportunities found: 3 (base ring, coordinate field, integrality predicate).
Proposed restatement: exactly the existing `LutzNagell.PID.isInteger_of_nsmul_isInteger`:

```lean
theorem isInteger_of_nsmul_isInteger
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') (_hy' : IsLocalization.IsInteger R y') :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y
```

Cost of restatement: CHEAP — the UFD form already exists, sorry-free, in the same project. For a mathlib PR
the work is selecting the UFD form (and its support: `curveK`, `x_coord_nsmul_eq`, `monic_Φ_sub_smul_ΨSq`,
`x_isInteger_of_nsmul_x_isInteger`, `y_isInteger_of_x_isInteger_on_curve`), not re-deriving anything. The
unused `_hy'` parameter should be dropped on the way in.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | already typeclass-driven (`Nonsingular`, `IsFractionRing`) | — |
|  2 | sequences/metric → filters/topological?                                                                  | no       | purely algebraic; no topology/limits | — |
|  3 | construct an object → universal-property class?                                                          | no       | it is a Prop, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | n/a | — |
|  5 | vector-space/metric/field-specific → weaken via typeclass hierarchy?                                      | **YES**  | ℤ → UFD `R`, ℚ → `Frac R`, `∃ cast` → `IsLocalization.IsInteger R` | full `IsFractionRing`/`IsInteger`/`IsIntegrallyClosed` API; reuse for rings of integers of number fields, DVRs, `k[t]` |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/monoid?                                                       | partial  | the multiplier `n` is correctly `ℤ` (the `ℤ`-action on the point group); the thing to generalise is the *base ring*, covered by row 5 | — |
|  8 | concrete-object proof betrays an abstract form (named identifier vanishes after first unfolding)?         | partial  | the body is a pure wrapper around the UFD lemma — there is no ℤ/ℚ-specific reasoning at all; the "abstract form" IS the PID lemma it calls | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it coincides with the literature-weakening: state over a UFD `R` with
`K = Frac R`, integrality via `IsLocalization.IsInteger R`.
  - Proposed mathlib-idiomatic restatement: the `isInteger_of_nsmul_isInteger` signature above.
  - Cost: CHEAP (already proved in-project; the ℤ/ℚ theorem is a one-line specialisation of it).
  - Mathlib downstream this enables: the result then applies to any UFD base — ℤ (classical Nagell–Lutz),
    `ℤ[i]` and other rings of integers of number fields (arXiv:2509.07524 territory), `k[t]` (function-field
    elliptic curves / EDS over function fields), and any DVR — without re-proving. Composes with mathlib's
    `IsLocalization.IsInteger` / `IsFractionRing` / `IsIntegrallyClosed` API.
  - Real mathematical improvement (not "looks cooler"): removes a pure specialisation; the ℤ/ℚ statement adds
    **zero** number-theoretic content over the UFD one (its proof is literally `PID.isInteger_of_nsmul_isInteger …`
    plus predicate-unfolding). The project itself encodes this by deriving the entire General track as
    special-cases of the PID track.

---

### Diamond / defeq risk — `integral_of_nsmul_integral_general`

n/a — declaration kind is `theorem` (Phase 4.5 skipped; theorems introduce no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `integral_of_nsmul_integral_general`

[A] Lean-Finder       — (index unavailable in this environment)                                  n/a: reasoned from grep over `.lake/packages/mathlib`
[B] Loogle            `WeierstrassCurve.Φ`/`ΨSq` ↔ `Affine.Point` smul; integral-multiple        no hits — mathlib never relates `n • P` (group op) to `Φ`/`ΨSq`
[C] LeanSearch        "if n times a point on an elliptic curve is integral then the point is integral"  no hits
[D] Grep mathlib src  `Nagell`, `Lutz`, `nsmul.*[Ii]nteger`, `[Ii]nteger.*nsmul`, `torsion.*integ` in `Mathlib/`  no relevant hits
[E] Name pattern      `integral_of_nsmul`, `isInteger_of_nsmul`, division-poly smul formula        no hits in mathlib

Detailed grep evidence (this run, over `.lake/packages/mathlib`):
- `grep -rli "nagell\|lutz" Mathlib/` → the only "Lutz" hit is the *author* Patrick Lutz (FieldTheory/AbelRuffini
  copyright header) and "Nagell" matches nothing relevant. **Nagell–Lutz is not in mathlib.**
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` define `Φ`, `ΨSq`, `ψ`,
  `preΨ` and their degrees — but `grep "smul\|nsmul\|zsmul"` over those two files returns **0 hits**. Mathlib
  has the division polynomials and the `Affine.Point` group law **separately**; it does NOT have the bridge
  `x(n • P) · ΨSqₙ(x) = Φₙ(x)`. That bridge is precisely the project's `x_coord_nsmul_eq` / `x_coord_nsmul_eq_general`
  (a ≈21-line Jacobian-coordinate proof) on which this descent lemma rests.
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` has no `addOrderOf`/`torsion`/`IsInteger`
  content for points.
- The only mathlib building block actually used: `Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`
  `isInteger_of_is_root_of_monic` (**integral root theorem**), stated over a UFD `A` with `IsFractionRing A K` —
  exactly the generality of the project's PID track.

Searched for both: the user's ℤ/ℚ form AND the literature-standard UFD form. Neither is in mathlib.

Concluded: **not in mathlib** (all methods exhausted, both the ℤ/ℚ form and the UFD-general form). Mathlib
has only the final building block (`isInteger_of_is_root_of_monic`); the elliptic-curve-specific content (the
smul→division-polynomial formula and the descent lemma built on it) is absent.

---

### Call sites — `integral_of_nsmul_integral_general` (Phase 6.0)

Internal use count: **2** (within the project, excluding the declaring file).
External-to-file callers: 1 distinct file (`GeneralMain.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| GeneralMain.lean:74            | `exact integral_of_nsmul_integral_general W hpt`          |
| GeneralMain.lean:102           | `exact integral_of_nsmul_integral_general W hpt`          |

Both call sites are inside the helper lemmas of `lutz_nagell_integrality_general` (the ℤ/ℚ Nagell–Lutz main
theorem). So this is a live, load-bearing descent step — NOT dead code.

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?):
  - The PID track re-derives the SAME mathematics in greater generality
    (`LutzNagell.PID.isInteger_of_nsmul_isInteger`, `PIDIntegralMultiple.lean:80`), used by the PID-track main
    theorems in `PIDMain.lean`. This is the "re-derivation": the General and PID tracks are parallel, the PID
    one strictly more general, and **the target theorem's own proof body already calls the PID lemma** — so it
    is less a re-derivation than a thin ℤ/ℚ adapter over it.

Composability signal: K = 2 internal uses, no inline re-derivation *within the General track* → it is a real
API node for the ℤ/ℚ track. But the *existence of the strictly-more-general PID twin* (which the target's own
body delegates to) is the dominant signal for the verdict.

---

### Composition check (Phase 6)

Can `integral_of_nsmul_integral_general` be derived from mathlib in ≤3 chained calls?

Attempt 1: `isInteger_of_is_root_of_monic` (mathlib) applied to `Φₙ − C x' · ΨSqₙ`.
  - Mathlib decls used: `isInteger_of_is_root_of_monic`.
  - Result: **fails as a standalone composition** — it needs, as a hypothesis, that `x` is a root of that
    monic polynomial, i.e. `x' · ΨSqₙ(x) = Φₙ(x)`. That equation is the multiplication-by-`n` x-coordinate
    formula, which is NOT in mathlib (no smul↔division-polynomial bridge). Producing it requires the ≈21-line
    `x_coord_nsmul_eq` (Jacobian coordinates, `X_eq_of_equiv`, `zsmul_eq_smulEval`, the evalEval→Φ/ΨSq
    conversions). Plus monicity (`monic_Φ_sub_smul_ΨSq`) and the `y`-from-`x` step
    (`y_isInteger_of_x_isInteger_on_curve`).
  - Notes: this is a genuine multi-lemma development, not a 1–3 call composition.

(Note: the target theorem *is* a ≤3-call composition of the **in-project** `PID.isInteger_of_nsmul_isInteger`
plus `isInteger_int_iff`. But composability is judged against **mathlib**, not against the project's own
not-yet-upstreamed lemmas. The mathlib building blocks alone do not give it.)

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The substantive content (smul→`Φ`/`ΨSq` formula) is
missing from mathlib; only the final integral-root step is a mathlib one-liner.

---

## Verdict: `LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): standard integral-descent step of Nagell–Lutz; stated over ℤ/ℚ classically and
  actively generalised to number-field rings of integers / DVRs (arXiv:2509.07524; Wikipedia "arbitrary number
  fields"). Natural ceiling = integrally closed domain; mathlib-natural realisation = UFD.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 weakenings (base ring ℤ→UFD, field
  ℚ→Frac R, predicate `∃ cast`→`IsInteger R`). The general form is already proved in-project as
  `LutzNagell.PID.isInteger_of_nsmul_isInteger`, and the target's own proof body delegates to it.
- Mathlib search (Phase 5): **not in mathlib** in either form; the smul→division-polynomial bridge is absent,
  only `isInteger_of_is_root_of_monic` exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the missing piece is the multiplication-by-n
  x-coordinate formula, a real ~21-line lemma).

**Rationale (1–2 paragraphs):**

This declaration is a genuine, missing-from-mathlib result — the integral-descent step of Nagell–Lutz — but
the form sent to mathlib should NOT be the ℤ/ℚ one. The proof uses ℚ and ℤ nowhere essentially: it needs
`Φₙ`/`ΨSqₙ ∈ R[X]`, `Φₙ` monic, and the integral-root theorem `isInteger_of_is_root_of_monic`, all of which
mathlib already provides over an arbitrary UFD with its fraction field. The project itself proves exactly this
UFD-general version (`LutzNagell.PID.isInteger_of_nsmul_isInteger`, sorry-free) and the target theorem's
entire body is a one-line call to it (the rest is `isInteger_int_iff` predicate-unfolding); the project's own
`/overview` duplications pass classifies `integral_of_nsmul_integral_general` as a "special-case of PID". So
the ℤ/ℚ statement adds no number-theoretic content over the UFD statement — it is a pure specialisation
(`R := ℤ`, `K := ℚ`; `curveQ W` is definitionally `curveK ℤ ℚ W`). The Phase 4b STRICTLY-NARROWER finding (and
the matching Phase 4c typeclass-weakening row 5) means the verdict gate forbids YES-add-as-is and selects
YES-but-generalise-first.

The contribution worth upstreaming is the whole development the descent rests on — most importantly the
multiplication-by-`n` x-coordinate identity `x(n • P) · ΨSqₙ(x) = Φₙ(x)` connecting the `Affine.Point` group
law to mathlib's division polynomials, which mathlib conspicuously lacks (it has the polynomials and the point
group, but not the bridge). Upstreaming should be done at UFD generality, in which form it unlocks Nagell–Lutz
over rings of integers of number fields, over DVRs, and over function-field bases (EDS), not just over ℚ.

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the user's ℤ/ℚ form strictly narrower than the integrally-closed / UFD
    standard form (the literature states and generalises Nagell–Lutz to number-field rings of integers).
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c row 5 — replace the field/ring-specific (ℤ, ℚ, `∃ cast`) data by the
    typeclass-driven (`UniqueFactorizationMonoid R`, `IsFractionRing R K`, `IsLocalization.IsInteger R`) form.

**Proposed restatement** (already exists, sorry-free, as `LutzNagell.PID.isInteger_of_nsmul_isInteger`):

```lean
theorem isInteger_of_nsmul_isInteger
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') (_hy' : IsLocalization.IsInteger R y') :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y
```

Estimated cost of regeneralisation: **CHEAP** — the UFD form is already proved in the project; for mathlib the
effort is selecting the UFD form (plus its support: `curveK`, `x_coord_nsmul_eq`, `monic_Φ_sub_smul_ΨSq`,
`x_isInteger_of_nsmul_x_isInteger`, `y_isInteger_of_x_isInteger_on_curve`) over the ℤ/ℚ duplicate. The unused
`_hy'` hypothesis should be dropped on the way in. EXPENSIVE-cost considerations do not arise.

Mathlib downstream this enables (MODERN-IDIOM):
  - Applies over any UFD base, not just ℤ: rings of integers of number fields (`ℤ[i]`, …), DVRs, and `k[t]`
    (function-field elliptic curves / EDS over function fields). The ℚ result is the `R := ℤ` instance.
  - The supporting smul↔division-polynomial bridge (`x_coord_nsmul_eq`) is itself net-new mathlib API: the
    canonical link between `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial` and the `Affine.Point`
    group law, currently absent. Torsion / height / EDS results would build on it.
  - Composes with mathlib's `IsLocalization.IsInteger`, `IsFractionRing`, `IsIntegrallyClosed` API.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Point.lean` (new) for
the smul-formula bridge, with the descent lemma either there or in a `.../NagellLutz.lean`.

PR grouping: ship the descent lemma together with its prerequisites as one coherent contribution — the
smul-formula bridge `x_coord_nsmul_eq`, the monic-polynomial lemma `monic_Φ_sub_smul_ΨSq`, the x-step
`x_isInteger_of_nsmul_x_isInteger`, the y-step `y_isInteger_of_x_isInteger_on_curve`, and the packaged
`isInteger_of_nsmul_isInteger`. (Their `General*` ℤ/ℚ twins are *not* separate contributions — they are the
`R := ℤ` specialisations and should not be upstreamed.)

Pre-PR checklist before opening:
  - [ ] `/generalise LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general` — tension the ℤ/ℚ form
        against both the literature-standard integrally-closed form and the in-project UFD twin; confirm UFD is
        the right ceiling and no further weakening (e.g. straight to `IsIntegrallyClosed`) is cheap.
  - [ ] `/cleanup` the PID-track files — full audit + diff gates — before the mathlib PR.
  - [ ] Pick a mathlib reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits.

Next action: run `/generalise LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general` (it will
tension the ℤ/ℚ form against both the literature-standard integrally-closed form and the in-project UFD twin)
before opening a PR. Within AINTLIB, the cleanup-side action is to treat the General track as the
specialisation it is (the PID track already subsumes it) — see `analysis/05-duplications.md`. For the mathlib
PR, ship the UFD form (`isInteger_of_nsmul_isInteger`) together with its smul-formula bridge.

---

## Next step

Run `/generalise LutzNagell.LutzNagellTheorem.integral_of_nsmul_integral_general`, then upstream the
**UFD-general** form (`LutzNagell.PID.isInteger_of_nsmul_isInteger`) plus the missing
`x(n • P) · ΨSqₙ(x) = Φₙ(x)` division-polynomial bridge — not the ℤ/ℚ specialisation.
