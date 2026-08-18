# /mathlibable report — `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`

## Verdict (one line)

**YES-but-generalise-first** — the discriminant-divisibility half of the
Nagell–Lutz theorem is a famous named result genuinely absent from mathlib, and
this is the right (general-Weierstrass, PID) generality; but it must be restated
against mathlib's own division-polynomial / point API (this project forks those)
and mathlib's integral-point idiom before upstreaming.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source.
- decl `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:401`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lutz–Nagell theorem over a PID `R` (char 0) with
  fraction field `K`: integrality of torsion coordinates + the κ₀²∣4Δ
  discriminant bound; specialises to number fields with class number 1.
- namespace:                 `LutzNagell.PID` (file: `namespace LutzNagell` →
  `namespace PID`). Qualified name as given is correct.

---

### Statement (Phase 1)

`lutz_nagell_pid_discriminant_of_torsion` is **the discriminant-divisibility half
of the Nagell–Lutz theorem**, stated for a general Weierstrass curve over a PID.

In prose: Let `R` be a characteristic-zero principal ideal domain with fraction
field `K`, and `W : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` a Weierstrass curve
over `R`. Let `P = (x, y)` be a nonsingular point on the base-changed curve over
`K`, assumed to be a torsion point (`IsOfFinAddOrder`) whose every prime order
divisor `p` is squarefree in `R` (`Squarefree (p : R)` — the "unramified"
hypothesis, automatic when `R = ℤ`). Suppose `P` has *integral* coordinates,
i.e. `x = x₀`, `y = y₀` for `x₀, y₀ ∈ R`. Write `κ₀ := 2y₀ + a₁x₀ + a₃` (the
evaluation of the 2-torsion / ψ₂ quantity at `P`). Then **either `κ₀ = 0`
(equivalently `2P = O`, the order-2 case) or `κ₀² ∣ 4Δ`**, where `Δ` is the
discriminant of `W`.

Variables / typeclasses (Lean side):
- `R` : `CommRing`, `IsDomain`, `IsPrincipalIdealRing`, `CharZero` — the PID.
- `K` : `Field`, `DecidableEq`, `Algebra R K`, `IsFractionRing R K` — fraction field.
- `W : WeierstrassCurve R` — the curve.

Hypotheses (Lean side):
- `hpt : (curveK R K W).toAffine.Nonsingular x y` — `P` nonsingular on `W ⊗ K`.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — `P` is torsion.
- `hsf_all : ∀ p, p.Prime → p ∣ addOrderOf P → Squarefree (p : R)` — unramified.
- `hx : algebraMap R K x₀ = x`, `hy : algebraMap R K y₀ = y` — integral coords.

Conclusion (math): `κ₀ = 0  ∨  κ₀² ∣ 4Δ`.
Conclusion (Lean): `(2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ`.

Note: this is the *generalised* half of Nagell–Lutz. The classical statement is
phrased over `ℤ`; the project's `Δ`-divisibility for short Weierstrass
(`y₀² ∣ 4a₄³+27a₆²`) is the downstream `lutz_nagell_cubicDisc_discriminant`,
which is `lutz_nagell_pid_discriminant_of_torsion` specialised to `a₁=a₃=0`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem named after people (Nagell, Trygve; Lutz, Élisabeth — 1935/1937)
and a `## Main results` entry of the project. Guaranteed to be in the literature.

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check is n/a.
(Body is a 6-line proof: `by_cases` on κ₀ = 0, then a 3-lemma composition.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Nagell-Lutz theorem … y divides discriminant statement" | yes | If `P=(x,y)` is rational of finite order then `y=0` (order 2) or `y ∣ D`, hence `y² ∣ D` | Wikipedia, HandWiki, PlanetMath all agree; `D` = discriminant |
| 2 | WebSearch (general form) | "…general Weierstrass equation … 2y+a1x+a3 … number field PID generalization" | yes | General Weierstrass `y²+a₁xy+a₃y=…`: torsion ⇒ integral coords, or order 2 with `x=m/4, y=n/8`; generalises to number fields | confirms the general-Weierstrass version and the κ₀ = 2y+a₁x+a₃ role (the order-2 / 2-division quantity) |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2; "Lutz–Nagell", "Nagell-Lutz, quickly" Alpöge) | yes | same theorem; Alpöge's note gives the modern division-polynomial proof | name order varies (Nagell–Lutz = Lutz–Nagell) |
| 4 | ChatGPT MCP | — | n/a | — | MCP available but not needed: three independent reference channels (Wikipedia + Silverman-style notes + PlanetMath) already pin the exact standard form and its generality. Recorded n/a to avoid redundant external call; the standard form is not in doubt. |
| 5 | Local references | grep `.mathlib-quality/references/` | n/a | (dir absent for NagellLutz) | no references dir; project uses `refs/` (gitignored, not present locally) |
| 6 | nLab | "Nagell-Lutz" / "elliptic curve torsion" | n/a — not an nLab topic | — | nLab has no Nagell–Lutz page; arithmetic-of-EC results are out of nLab's categorical scope |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | "Nagell-Lutz" / EC torsion integrality | n/a | — | Stacks is scheme-theoretic foundations; no Nagell–Lutz / explicit torsion-integrality result |
| 9 | MathOverflow / MSE | "Nagell-Lutz general Weierstrass discriminant" | yes | reproduces the Silverman VIII.7 statement and proof sketch via reduction mod p / formal group | standard textbook material, not research-level |
| 10 | recent arXiv | "Nagell-Lutz p-adic / number field" | yes | Anqi Li (p-adic Nagell–Lutz), Tate-normal-form torsion computation (math/0011066) | modern treatments via formal groups / p-adic; same theorem, same generality target |

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (a.k.a. Lutz–Nagell), specifically
its *discriminant-divisibility* conclusion. Canonical reference: Silverman, *The
Arithmetic of Elliptic Curves*, VIII.7 (Cor. 7.2 / the "y² ∣ Δ" corollary);
Trygve Nagell (1935), Élisabeth Lutz (1937).

Sources agree on the standard form: **yes.** For a Weierstrass equation with
coefficients in a ring `R` (classically `ℤ`), a torsion point with integral
coordinates satisfies `y = 0` or `(2y+a₁x+a₃)² ∣ Δ` (short form: `y² ∣ Δ` /
`y² ∣ 4A³+27B²`). The quantity `2y+a₁x+a₃` is exactly `ψ₂(P)` (the partial
derivative `∂F/∂y`); `2P = O ⟺ ψ₂(P)=0`, which is why the disjunction splits on it.

Most general standard form: torsion + integral-coordinates ⇒ `κ₀=0 ∨ κ₀²∣Δ`, over
any ring where "torsion points are integral" holds — Silverman proves it for `ℤ`;
the standard generalisation is to a number field's ring of integers (Dedekind),
and via the same formal-group / reduction argument to a PID with a residue-field
condition at each prime (the project's `Squarefree (p:R)` = "unramified" hypothesis).

Generality dimensions where the literature varies:
  - **base ring**: `ℤ` (classical) → ring of integers `𝓞_K` of a number field →
    PID with the squarefree/unramified condition. The project takes the PID form,
    which is at-or-above the standard generalisation level.
  - **`4Δ` vs `Δ`**: classical short form gives `y²∣Δ`; over a general ring the
    clean integral statement carries a factor of `4` (`κ₀²∣4Δ`) because `κ₀²` is
    the *square* `ψ₂²` and the elimination introduces the 4. This `4` is standard
    and expected (it disappears when `2` is a unit), not an artefact.

Disagreement with the literature: **none.** The Lean form is the textbook
statement at the textbook generality (general Weierstrass, integral torsion point),
generalised in the base ring to a PID — a recognised generalisation direction.

---

### Generality analysis — `lutz_nagell_pid_discriminant_of_torsion`

Literature-standard form (Phase 3): torsion point with integral coordinates on a
general Weierstrass curve ⇒ `κ₀ = 0 ∨ κ₀² ∣ 4Δ`, base ring `ℤ`/`𝓞_K`/PID(+unram).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[IsPrincipalIdealRing R] [IsDomain R]` | PID | `ℤ` (classical) / Dedekind `𝓞_K` | NO (weaker would need new math) | PID is *already more general* than the classical `ℤ` and matches the standard "class-number-1 / PID" generalisation. Going to Dedekind is a genuine generalisation (localise-at-each-prime), not a free weakening — out of scope here. |
| 2 | `[CharZero R]` | char 0 | char 0 (classical; char ≠ 2,3 in some treatments) | partially | Some helper lemmas already `omit [CharZero R]`. Char 0 is the standard setting; weakening to "2,3 not zero-divisors" is plausible but is real work, not mechanical. |
| 3 | `hsf_all : Squarefree (p:R)` for `p ∣ ord` | squarefree (unramified) at torsion primes | implicit/automatic over `ℤ`; the "good reduction"/unramified condition over general `R` | NO | This is the correct, minimal hypothesis making the formal-group argument run over a general PID. Automatic for `R=ℤ`. Not removable. |
| 4 | integral coords `hx,hy` (`algebraMap R K x₀ = x`) | explicit integrality hyp | "torsion ⇒ integral" is a *theorem* (the other half) | — | Here integrality is taken as hypothesis; the project proves integrality separately (`lutz_nagell_integrality_pid`). Standard to separate the two halves. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (along the standard axes — already at
the PID level, the general Weierstrass equation, the κ₀² ∣ 4Δ conclusion).
Number of *free* weakening opportunities found: 0 (Dedekind / low-char are real
generalisations, not mechanical weakenings).

So Phase 4b does **not** by itself force "generalise-first". The generalise-first
verdict instead comes from Phase 4c / Phase 5: the statement is bound to this
project's *forked* API rather than mathlib's, and must be re-expressed against
mathlib idioms before it can land.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" preambles → typeclasses? | partial | The `Squarefree (p:R)` family could become a `[ … unramified … ]`-style hypothesis bundle, but mathlib has no such class yet | would need a new mathlib notion of "unramified base for EC integrality" |
| 2 | sequences/metric → filters/topological? | no | finite-order + divisibility; no limiting notion | — |
| 3 | construct object → universal property? | no | a divisibility statement, nothing to characterise universally | — |
| 4 | set+closure-predicate → bundled substructure? | no | — | — |
| 5 | field/metric-specific → weaken typeclasses? | **yes (the key one)** | state integrality via mathlib's localization-integrality idiom and `WeierstrassCurve.Affine.Point` torsion directly, rather than the project's `curveK`/`IsFractionRing.den` machinery | composes with all of mathlib's `WeierstrassCurve`/`Affine.Point` API |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index ℤ/ℝ → general algebraic structure? | already done | the base is already a general PID `R`, not `ℤ` | this *is* the generalisation; good |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but as repackaging against mathlib's API, not a
mathematical change.** The mathematical statement is already in the right modern
form (general curve, PID base, `addOrderOf`/`IsOfFinAddOrder` on
`WeierstrassCurve.Affine.Point`, `WeierstrassCurve.Δ`). What is *not*
mathlib-idiomatic is the surrounding scaffolding the statement leans on:
  - `curveK R K W` — the project's own "base change to the fraction field" wrapper;
  - the project's *forked* `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`
    and `Mathlib.NumberTheory.EllipticDivisibilitySequence` (the task brief notes the
    fork; `Ψ₂Sq`, `Ψ₃`, `Φ`, `preΨ` etc. are used pervasively in the supporting lemmas);
  - integrality expressed via `IsFractionRing.den`/`IsLocalization.IsInteger`.

  - Cost: **MODERATE-to-EXPENSIVE** — the statement line is fine, but everything it
    is *proved from* (the `kappa_sq_dvd_four_Psi3_of_torsion` chain, `x_coord_nsmul_eq`,
    `lutz_nagell_integrality_pid`) rests on the forked division-polynomial layer.
    Upstreaming requires either landing that layer in mathlib first or rebuilding
    the proof on mathlib's existing `DivisionPolynomial` API.
  - Mathlib downstream this enables: a *canonical* Nagell–Lutz API
    (`WeierstrassCurve.Affine.Point` torsion ⇒ integrality ⇒ `κ₀²∣4Δ`), which is the
    natural home for the `y²∣Δ` torsion-search algorithm used throughout computational
    number theory; nothing in mathlib currently lets a user bound torsion coordinates.
  - Real mathematical improvement: it removes the project's reliance on a *fork* of
    mathlib files — the whole point of upstreaming is to retire that fork.

---

### Mathlib search-status: `lutz_nagell_pid_discriminant_of_torsion`

[A] Lean-Finder       n/a (mathlib index search unavailable offline; used grep + reasoning)
[B] Loogle            n/a (offline) — type pattern would be
                      `WeierstrassCurve.Δ`, `IsOfFinAddOrder`, `Dvd` on a point quantity; none co-occur in mathlib (confirmed by grep [D])
[C] LeanSearch        n/a (offline)
[D] Grep mathlib src  searched `.lake/packages/mathlib/`:
      - `nagell`/`lutz` → only **Patrick Lutz** (field theory, Galois) — unrelated person.
      - `addOrderOf`/`IsOfFinAddOrder` inside `EllipticCurve/` → **zero theorems**
        (only appears via transitive imports, never as a result about EC points).
      - `IsInteger`/`integral.point` in `EllipticCurve/` → **none**.
      - `dvd … Δ` / `… ∣ 4*Δ` across all of mathlib → **none** (only an unrelated
        `WellApproximable` hit). The only `Δ`-divisibility-adjacent fact is
        `twoTorsionPolynomial_discr = 16*W.Δ` (Weierstrass.lean:308) — about the
        2-division polynomial's discriminant, NOT a torsion-point coordinate bound.
      - `torsionOrder` hits → `NumberField.torsionOrder` (roots of unity in `𝓞_K`),
        entirely unrelated to EC points.
[E] Name pattern      grep for the qualified name in mathlib → none.

Searched for both:
  - user's form (κ₀² ∣ 4Δ from torsion) — not in mathlib;
  - literature-standard form (`y²∣Δ`, EC torsion integrality) — not in mathlib, at
    any generality. Mathlib has `WeierstrassCurve.Δ`, the `twoTorsionPolynomial`,
    division polynomials (`Ψ`, `Φ`, `ψ`), and `Affine.Point` as an `AddCommGroup`,
    but **no theory of the order/torsion of those points and no integrality result**.

Concluded: **not in mathlib** (all available methods exhausted, both forms).
Mathlib has the *ingredients* (curve, Δ, division polynomials, the point group)
but neither the Nagell–Lutz statement nor the torsion-integrality scaffolding it
needs. The building blocks do NOT compose in ≤3 calls (see Phase 6).

---

### Call sites — `lutz_nagell_pid_discriminant_of_torsion`

Internal use count: **2** (both inside the NagellLutz project).
External-to-file callers: 1 distinct file (the number-field wrapper), plus 1 use
in the same file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/PIDMain.lean:433` | `rcases lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy with hκ \| hdvd` (inside `lutz_nagell_cubicDisc_discriminant`) |
| `…/PIDMain.lean:546` | `PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy` (inside `lutz_nagell_number_field_discriminant`) |

Inline-derivation grep (equivalent re-derived elsewhere without using it): none.
The two callers genuinely consume it (the cubic-discriminant specialisation and
the number-field wrapper). This is real API with downstream consumers, supporting
a YES-family verdict.

---

### Composition check (Phase 6)

Can `lutz_nagell_pid_discriminant_of_torsion` be derived from **mathlib** in ≤3
chained calls?

Attempt 1: compose from mathlib's EC API directly.
  - Mathlib decls available: `WeierstrassCurve.Δ`, `WeierstrassCurve.Ψ₂Sq`/`Ψ₃`,
    `WeierstrassCurve.twoTorsionPolynomial`, `Affine.Point` group structure.
  - Result: **fails.** There is no mathlib lemma relating `addOrderOf` of an
    `Affine.Point` to its coordinates, no integrality result, and no
    `κ₀² ∣ 4Δ` building block. The proof here is ~200 lines of bespoke development
    (`kappa_sq_dvd_four_delta`, the Bézout identity `bezout_identity`,
    `kappa_sq_dvd_four_Psi3_of_torsion`, the `x_coord_nsmul_eq` 2-descent, and
    `lutz_nagell_integrality_pid`). None of this exists in mathlib.

Conclusion: **NOT-COMPOSABLE.** Mathlib lacks the intermediate theory entirely; this
is a substantial new development, not a 1–3 call composition.

---

## Verdict: `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): identified as the discriminant-divisibility half of
  the **Nagell–Lutz theorem** (Silverman AEC VIII.7); the Lean form is the textbook
  general-Weierstrass statement, generalised in the base ring to a PID — a
  recognised generalisation direction. No disagreement with the literature.
- Generality analysis (Phase 4): MAXIMALLY GENERAL along the standard axes (PID
  base, general Weierstrass, `κ₀²∣4Δ`). Phase 4c: the *statement* is modern, but it
  is bound to the project's forked division-polynomial API and a non-idiomatic
  integrality encoding (`IsFractionRing.den`), which should be reconciled with
  mathlib before upstreaming.
- Mathlib search (Phase 5): **not in mathlib** in any form; mathlib has `Δ` and
  division polynomials but no EC-torsion-order theory and no integrality/divisibility
  result. (`twoTorsionPolynomial_discr = 16Δ` is the closest, and is unrelated.)
- Composition check (Phase 6): **NOT-COMPOSABLE** (≈200 lines of bespoke theory).

**Rationale:**

This is a genuinely missing, famous, named theorem — the Nagell–Lutz discriminant
bound — and mathlib has *nothing* like it: no order/torsion theory for
`WeierstrassCurve.Affine.Point`, no integrality of torsion coordinates, no
coordinate-divides-discriminant statement. The mathematical content is exactly
mathlib-shaped (general Weierstrass curve, arbitrary PID base, the standard `κ₀`
quantity, `WeierstrassCurve.Δ`), and it has real internal consumers. So the answer
is firmly on the YES side, not NO.

It is **generalise-first rather than add-as-is** because the declaration, while
mathematically at the right generality, is built on a *fork* of two mathlib files
(`…DivisionPolynomial.*` and `…EllipticDivisibilitySequence`, per the project brief
and the pervasive `Ψ₂Sq`/`Ψ₃`/`preΨ` usage in its supporting lemmas) and expresses
integrality through `IsFractionRing.den`/`IsLocalization.IsInteger` and a bespoke
`curveK` base-change wrapper rather than mathlib's own idioms. Upstreaming must
first (a) reconcile/retire that division-polynomial fork against mathlib's
`DivisionPolynomial` API, and (b) restate integrality and the point-torsion
hypotheses in mathlib-canonical form. The mathematical theorem does not change; its
*plumbing* must be made mathlib-native. This is the Phase-4c MODERN-IDIOM trigger
(row 5: replace project-local scaffolding with mathlib's typeclass/API idioms), so
the verdict gate routes it to YES-but-generalise-first.

Reason for the generalisation:
  - MODERN-IDIOM (Bourbaki 2.0): restate against mathlib's `WeierstrassCurve` /
    `Affine.Point` / `DivisionPolynomial` API and mathlib's integral-point idiom,
    eliminating the project's fork of mathlib files. (Not a LITERATURE-WEAKENING:
    Phase 4b found no free weakening; the base is already a general PID.)

Proposed restatement (sketch — the statement stays the same; the *dependencies*
become mathlib-native):
```lean
-- Upstream target (schematic): same theorem, but
--   * `(curveK R K W)`  →  mathlib's base-change `W.baseChange K` / `W.map (algebraMap R K)`
--   * forked `Ψ₂Sq`,`Ψ₃`,`preΨ`  →  mathlib `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial`
--   * `IsFractionRing.den`/`IsLocalization.IsInteger`  →  mathlib integral-point API
theorem WeierstrassCurve.nagellLutz_dvd_discr
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K}
    (hpt : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some hpt))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (.some hpt) → Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  sorry -- proof rebuilt on mathlib's DivisionPolynomial API (or after that layer lands)
```
Estimated cost of regeneralisation: **MODERATE-to-EXPENSIVE** — the statement is
cheap to restate, but the proof rests on the project's forked division-polynomial
layer and 2-descent (`x_coord_nsmul_eq`, `lutz_nagell_integrality_pid`). The honest
path is to first upstream that supporting layer (much of which is itself a
fork/extension of mathlib), then this capstone lands cheaply on top.
Note: EXPENSIVE does not downgrade the verdict — getting the mathlib-native form is
the point.

Mathlib downstream this enables (MODERN-IDIOM evidence):
  - A canonical `WeierstrassCurve.Affine.Point` **torsion-integrality + Nagell–Lutz**
    API — currently mathlib cannot state, let alone bound, an EC torsion point's
    coordinates. This is the foundation of the standard finite-order-point search
    algorithm and of any formalised torsion-subgroup computation over `ℚ`/number fields.
  - Retires the project's fork of `…DivisionPolynomial.*` /
    `…EllipticDivisibilitySequence` (the explicit reason the fork exists).
  - The short-Weierstrass corollary (`y²∣4a₄³+27a₆²`) and the number-field wrapper
    (`lutz_nagell_number_field_discriminant`) become mathlib corollaries.

Next action: run `/generalise LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`
(tensioning against mathlib's `WeierstrassCurve`/`DivisionPolynomial` API and the
fork-retirement target) before opening a PR. The PR is necessarily *grouped*: the
supporting division-polynomial/integrality layer is the prerequisite, and this
theorem is the capstone of that upstreaming effort, not a standalone one-liner.

---

## Next step

Run `/generalise` on this declaration to restate it against mathlib's native
`WeierstrassCurve` / `Affine.Point` / `DivisionPolynomial` API (retiring the
project's fork of those files) and mathlib's integral-point idiom, then upstream as
the capstone of a grouped Nagell–Lutz PR series — the torsion-integrality +
division-polynomial supporting layer must land first, after which this `κ₀²∣4Δ`
theorem follows cheaply.
