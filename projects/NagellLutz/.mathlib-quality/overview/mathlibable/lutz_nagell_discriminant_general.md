# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general`

> Step-9 (overview) full mathlibable assessment, single declaration.
> Local Lean build stale per task brief; reasoned from source. Lean-index tools
> (loogle/leansearch) and ChatGPT MCP were unavailable/down (as the brief warned) —
> Phase 5 used exhaustive grep-over-mathlib + grep-over-project; Phase 3 used
> WebSearch ×4 + primary sources. All conclusive.
>
> NOTE: this supersedes an earlier draft that returned `YES-add-as-is`. That draft
> grepped only mathlib and missed the **in-project PID/number-field generalization**
> that the task brief explicitly flagged ("duplicated General*/PID* tracks -- so this
> decl may ALREADY be in mathlib. Check those mathlib files first."). The corrected
> verdict is `YES-but-generalise-first` — see Phases 4/6/7.

---

### Baseline (Phase 0)
- lake build:               not run (environment: local build stale per brief; reasoned from source)
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:187`
- kind:                     theorem
- has sorry:                no
- module docstring summary: "General discriminant divisibility for Weierstrass curves" — for a
  nonzero torsion point `(x₀,y₀) ∈ ℤ²` on a general Weierstrass curve, with `κ₀ = 2y₀+a₁x₀+a₃`,
  either `κ₀ = 0` or `κ₀² | 4Δ`. THE main result of the file.

Qualified name VERIFIED from source: `namespace LutzNagell` → `namespace LutzNagellTheorem`
(file lines 27–28) ⇒ `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general`. ✓
(matches the parsed name in the brief.)

---

### Statement (Phase 1)

`lutz_nagell_discriminant_general` is the **discriminant-divisibility half of the Nagell–Lutz
theorem** for a *general (long) Weierstrass equation*, stated over ℤ/ℚ.

Let `W` be a Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ`,
base-changed to ℚ (`curveQ W`). Let `P = (x,y)` be a nonsingular torsion point on `W/ℚ` with
integral coordinates `x = x₀, y = y₀` (`x₀,y₀ ∈ ℤ`). Set `κ₀ := 2y₀ + a₁x₀ + a₃`. Then either
`κ₀ = 0` (the point is 2-torsion) or `κ₀² ∣ 4Δ`.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ`.

Hypotheses (Lean side):
- `hpt : (curveQ W).toAffine.Nonsingular x y`, where `curveQ W := W.map (algebraMap ℤ ℚ)`
  (`GeneralCurve.lean:24`).
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)`.
- `hx : (x₀ : ℚ) = x`, `hy : (y₀ : ℚ) = y`.

Conclusion (Lean): `(2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨ (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ`.

**Key identification.** `κ₀ = 2y₀ + a₁x₀ + a₃` is exactly mathlib's 2-division polynomial
`ψ₂ := 2Y + a₁X + a₃` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`)
evaluated at `P`; `κ₀² = 4x₀³+b₂x₀²+2b₄x₀+b₆` is mathlib's `Ψ₂Sq`. The statement is in the
mathlib division-polynomial idiom.

**Proof shape (source lines 193–202).** `by_cases κ₀ = 0`; in the nonzero case it delegates
**entirely** to `PID.lutz_nagell_pid_discriminant (R := ℤ)`, feeding the curve equation and the
ℚ/ℤ Ψ₃-divisibility `kappa_sq_dvd_four_Psi3`. The decl is a **thin ℤ/ℚ wrapper over the project's
own PID API** — see Phase 6.

---

### Size classification (Phase 2a)

Verdict: **BIG** — named theorem (Nagell–Lutz, 1935/1937) and the sole `## Main results` entry of
its file. (Literature width EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`. (Proof is ~10 lines of delegation, not a one-liner.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem … torsion point y² divides discriminant statement"                                 | yes  | `y=0` or `y²∣Δ`; torsion ⇒ integral coords | Wikipedia, HandWiki, Silverman; canonical named theorem |
|  2 | WebSearch (general form)         | "Lutz-Nagell … general Weierstrass … 2y+a₁x+a₃ squared divides discriminant"                             | yes  | long form: order-2 ⇔ `2y+a₁x+a₃=0`; else `y²∣D`; order-2 coords `x=m/4,y=n/8` | Wikipedia "Generalization" paragraph confirms the long-Weierstrass form |
|  3 | WebSearch (named-after / proof)  | "Silverman arithmetic elliptic curves Nagell-Lutz proof division polynomial torsion"                    | yes  | Silverman *AEC* VIII; `y²∣Δ` short form | + arXiv 2509.07524 (Nagell-Lutz for imaginary quadratic fields, **2025**) |
|  4 | WebSearch (generalization dir.)  | "nLab Nagell-Lutz / torsion points elliptic curve integral coordinates"                                 | yes  | confirms `y²∣4A³+27B²`; generalizations to rings of integers | AIMS essay, Li REU, arXiv 2509.07524 — the active generalization is to **number fields / `𝓞 K`** |
|  5 | ChatGPT MCP                      | 3-part query: standard generality / ℤ-squarefree triviality / PID-vs-Dedekind                           | n/a  | — | **MCP down** (Codex exec stdin failure), as brief warned. Fallback channels 1–4 + grep are conclusive. |
|  6 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                                    | n/a  | (absent) | no references dir for this project; PDFs are local-only/gitignored. Recorded n/a. |
|  7 | nLab                             | Nagell-Lutz / torsion points elliptic curve                                                             | no   | (no nLab page) | arithmetic/Diophantine result, not categorical. |
|  8 | nCatLab                          | —                                                                                                       | n/a  | — | not categorical. |
|  9 | Stacks Project                   | —                                                                                                       | n/a  | — | Stacks has EC generalities but not this torsion/discriminant divisibility. |
| 10 | MathOverflow / Math.SE           | (surfaced within #1–4: PlanetMath, course PDFs, teahouse)                                                | yes  | consistent with #1–4 | no disagreement across sources. |
| 11 | recent arXiv (last 5 yrs)        | (via #3,#4)                                                                                              | yes  | generalizations to number fields | arXiv 2509.07524 (2025), math/0011066 (Tate form). ℚ base case is classical. |

### Literature summary (Phase 3)

Concept: **Nagell–Lutz theorem** (Nagell 1935; Lutz 1937), discriminant-divisibility half, long
Weierstrass model. Sources agree on the standard form (**yes**): short form `y₀=0 ∨ y₀²∣Δ`; long
form replaces `y₀=0` by `κ₀ = ψ₂(P) = 2y₀+a₁x₀+a₃ = 0` and `y₀²∣Δ` by `κ₀²∣4Δ`. The Lean
statement is the faithful long-form ℤ/ℚ rendering.
Most general standard form: classical is **ℤ/ℚ**; the literature's *generalization* (active, arXiv
2509.07524, 2025) goes to **number fields / rings of integers `𝓞 K`** — i.e. exactly the PID /
`𝓞 K` direction this project already implements.
Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → `𝓞 K` / Dedekind / PID (active research).
  - model: short → long Weierstrass (both standard; long is the general one).
Disagreement with the literature: none.

---

## PHASE 4 — Generality analysis

Literature-standard form: classical statement over ℤ/ℚ; the **modern, maximally-general** form
(active literature + mathlib idiom) is over a char-0 PID `R` with fraction field `K` (subsuming
`𝓞 K`), with an unramified-prime hypothesis. **That form already exists in this very project** as
`PID.lutz_nagell_pid_discriminant_of_torsion` (`PIDMain.lean:401`).

### Generality status table

| # | Parameter / hypothesis              | Current Lean form        | Literature-standard / modern form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|--------------------------|-------------------------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`            | curve over **ℤ**         | curve over char-0 PID `R` (`𝓞 K` for number fields) | **yes**             | the project *already* proves the `R`-general version; ℤ is the specialization `R := ℤ` |
| 2 | coords `x y : ℚ`, `x₀ y₀ : ℤ`       | fraction field **ℚ**     | fraction field `K = Frac R`                     | **yes**             | `ℚ = Frac ℤ`; PID version uses `IsFractionRing R K`; `curveQ W` is defeq `curveK ℤ ℚ W` |
| 3 | (implicit) "every prime squarefree" | free over ℤ              | `hsf_all : ∀ p∣ord, Squarefree (p:R)`           | n/a (ℤ side)        | over ℤ automatic via `Irreducible.squarefree` (mathlib `Algebra/Squarefree/Basic.lean:65`); the general form must hypothesize it (it can genuinely fail at ramified primes) |
| 4 | `htor`, `hx`, `hy`, `hpt`           | identical to PID version | identical                                       | —                   | structurally the same |
| 5 | conclusion `κ₀² ∣ 4Δ`               | identical                | identical (`PIDMain.lean:407-408`)              | —                   | the two conclusions are **textually identical** |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**. It is the `R = ℤ, K = ℚ` specialization
of a strictly more general statement that (a) matches the modern literature's generalization
direction and (b) **is already proven in this project**.
Number of weakening opportunities: 2 (base ring ℤ→PID; fraction field ℚ→`Frac R`).
Proposed restatement: **none to author** — the general form exists as
`PID.lutz_nagell_pid_discriminant_of_torsion` (`PIDMain.lean:401`), re-exported for number fields
of class number 1 as `NumberField.lutz_nagell_number_field_discriminant` (`PIDMain.lean:533`).
Cost of restatement: **CHEAP** — the general theorem is proven and sorry-free; the ℤ case is a
≤2-line corollary. (Indeed the target's proof *already* calls `PID.lutz_nagell_pid_discriminant`.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                            | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                  | no       | — | already typeclass-driven (`WeierstrassCurve`, `IsFractionRing`) |
|  2 | sequences/metric → filters/topological?                                              | no       | — | purely arithmetic |
|  3 | construct an object → universal-property class?                                      | no       | — | it is a `Prop`, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                   | no       | — | n/a |
|  5 | field/metric/vector-space-specific → weaken typeclass hierarchy (PID/`Frac R`)?      | **yes**  | state over char-0 PID `R`, `K = Frac R` | the existing PID form; recovers ℤ/ℚ AND `𝓞 K`/number fields uniformly |
|  6 | 1-categorical → higher-categorical?                                                  | no       | — | n/a |
|  7 | concrete index (ℤ) → arbitrary group/monoid/ordered structure (here: ground ring)?   | **yes**  | base ring ℤ → general PID | unifies ℤ/ℚ and `𝓞 K` Nagell-Lutz under one statement |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (rows 5,7) — the PID/`Frac R` form. It is **not a new target to
author**: the project already contains it. The modern form *is* the existing general theorem; the
assessed decl is its ℤ/ℚ specialization.
Real mathematical improvement: the general form covers number fields of class number 1
(`lutz_nagell_number_field_discriminant`), matching the active literature (arXiv 2509.07524, 2025),
which the ℤ-only form cannot.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem`.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `lutz_nagell_discriminant_general`

[A] Lean-Finder        n/a — index tool unavailable in this environment.
[B] Loogle             n/a — lean_loogle unavailable; compensated by exhaustive grep [D].
[C] LeanSearch         n/a — lean_leansearch unavailable.
[D] Grep mathlib src   **EXHAUSTIVE — decisive.** `grep -rln "Nagell\|nagell\|lutz\|discriminant_general\|pid_discriminant"` over `.lake/packages/mathlib/Mathlib/` → **0 hits**. `IsOfFinAddOrder`/torsion + `Δ`-divisibility across `AlgebraicGeometry/EllipticCurve/` → none tying torsion points to integrality or Δ. No Mordell/Siegel/integral-point machinery for EC either.
[E] Name pattern       n/a (lean_local_search unavailable); grep substitutes — no `lutz`/`nagell` decl names in mathlib.

Searched for both:
  - the user's current form (ℤ/ℚ long-Weierstrass `κ₀²∣4Δ`) — **not present**.
  - the literature-standard / general form (PID `κ₀²∣4Δ`; short `y₀²∣Δ`; Nagell–Lutz in any guise)
    — **not present**.

Mathlib **does** have the infrastructure (`WeierstrassCurve.Δ`, `ψ₂`/`Ψ₂Sq`/`Ψ₃`/`Φ`,
`Affine.Point` group law, `IsFractionRing`, division polynomials in
`Mathlib/.../DivisionPolynomial/`, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`), but
**no Nagell–Lutz theorem** and **no torsion ⇒ discriminant-divisibility result**, in any generality.

Concluded: **not in mathlib** (both forms exhausted). Mathlib lacks Nagell–Lutz entirely. (This
rules out `NO-mathlib-has-it`.)

---

## PHASE 6 — Composition check (+ call-sites signal)

### 6.0. Call sites — `lutz_nagell_discriminant_general`

Internal use count: **1** (outside the declaring file).
External-to-file callers: 1 distinct file.

| Caller file:line  | Usage pattern (one-line excerpt)                                                                 |
|-------------------|--------------------------------------------------------------------------------------------------|
| `Main.lean:53`    | `rcases lutz_nagell_discriminant_general (shortCurveZ A B) hpt htor hx hy with hκ ∣ hdvd` — proves the short-Weierstrass `lutz_nagell_discriminant` (`y₀=0 ∨ y₀²∣Δ`) |

(Also used at `GeneralDiscriminant.lean:222` — same file — inside the combined `lutz_nagell_general`.)

Inline-derivation grep — **the same statement is independently proven, MORE GENERALLY, elsewhere in
the project**: `PID.lutz_nagell_pid_discriminant_of_torsion` (`PIDMain.lean:401`, identical
conclusion over a char-0 PID), re-exported as `NumberField.lutz_nagell_number_field_discriminant`
(`PIDMain.lean:533`). The `General*` ℤ/ℚ track **parallels** the `PID*` track; this decl is the
ℤ/ℚ shadow of the PID theorem (and its *proof already delegates* to `PID.lutz_nagell_pid_discriminant`).

### Composition check (Phase 6)

Can `lutz_nagell_discriminant_general` be derived in ≤3 chained calls?

Attempt 1 — from mathlib primitives: **fails.** Mathlib has the definitions (`ψ₂`, `Ψ₂Sq`, `Δ`,
`Affine.Point`, EDS) but **no theorem** relating a torsion point to `Δ`; nothing to chain.

Attempt 2 — from the project's own PID API (the decisive route; `curveQ W` is **defeq**
`curveK ℤ ℚ W`, both `= W.map (algebraMap ℤ ℚ)`):
```lean
example {W : WeierstrassCurve ℤ} {x y : ℚ}
    (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    {x₀ y₀ : ℤ} (hx : (x₀:ℚ) = x) (hy : (y₀:ℚ) = y) :
    (2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ :=
  PID.lutz_nagell_pid_discriminant_of_torsion (R := ℤ) (K := ℚ) W hpt htor
    (fun p hp _ => hp.prime_int.irreducible.squarefree)  -- every prime in ℤ is squarefree
    (by exact_mod_cast hx) (by exact_mod_cast hy)
```
  - Building blocks: `PID.lutz_nagell_pid_discriminant_of_torsion` (project),
    `Irreducible.squarefree` (mathlib, `Algebra/Squarefree/Basic.lean:65`).
  - Result: **succeeds** — 1 call to the general theorem + a one-liner discharging `hsf_all` over ℤ.
  - Caveat: composes from a **PROJECT** decl, not a mathlib decl. Mathlib has *neither* form. So
    this is **not** `NO-composable-from-mathlib` (that bucket means "inline from mathlib and delete";
    here deleting would lose the theorem entirely). It is *redundancy within the project*.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks Nagell–Lutz). It **is** a ≤2-line
specialization of the project's own more-general PID theorem.

---

## PHASE 7 — Verdict

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz is a classical named theorem; the long-Weierstrass
  `κ₀²∣4Δ` form is standard; the *active* generalization (arXiv 2509.07524, 2025) is to number
  fields / rings of integers — the PID/`𝓞 K` direction.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the assessed decl is the
  `R = ℤ, K = ℚ` specialization of a strictly more general statement (rows 1,2; modern-idiom rows
  5,7) that the project already proves.
- Mathlib search (Phase 5): **not in mathlib** in any form — mathlib has the EC/division-polynomial/
  EDS infrastructure but no Nagell–Lutz theorem (rules out NO-mathlib-has-it).
- Composition check (Phase 6): COMPOSABLE from the project's own
  `PID.lutz_nagell_pid_discriminant_of_torsion` in ≤2 lines (since `curveQ W` is defeq `curveK ℤ ℚ W`);
  NOT composable from mathlib (rules out NO-composable-from-mathlib).

**Rationale.**
Mathlib genuinely lacks Nagell–Lutz, so the *result* is a real contribution — this is not
`NO-mathlib-has-it`. But the assessed declaration is stated at the **wrong generality**: it is the
ℤ/ℚ specialization, whereas the project itself already proves the maximally-general form
`PID.lutz_nagell_pid_discriminant_of_torsion` (over a char-0 PID `R` with fraction field `K` and an
unramified-prime hypothesis), with the conclusion **textually identical** to the target, and
re-exports it for number fields of class number 1 as `lutz_nagell_number_field_discriminant`. The
target's own proof even *delegates* to `PID.lutz_nagell_pid_discriminant`. The general form matches
exactly the direction the modern literature generalizes Nagell–Lutz (rings of integers / `𝓞 K`,
arXiv 2509.07524, 2025). Mathlib's iron rule — add the most general form — means the PID/`𝓞 K`
statement is what should go upstream, not the ℤ/ℚ corollary. The ℤ case then follows in ≤2 lines
because `curveQ W = W.map (algebraMap ℤ ℚ)` is definitionally `curveK ℤ ℚ W`, and over ℤ the
squarefree-prime hypothesis is discharged for free (`Irreducible.squarefree`).

This is `YES-but-generalise-first` rather than `NO-composable-from-mathlib` because the thing it
composes from is a **project** theorem, not a mathlib primitive — mathlib has *neither* form, so
"inline and delete" would lose the result. The correct upstreaming action is to PR the general
(PID and/or number-field) statement, with the ℤ/ℚ and short-Weierstrass forms as thin corollaries.

**Reason for the generalisation:** both apply —
  - LITERATURE-WEAKENING: Phase 4b found the ℤ/ℚ form strictly narrower than the PID/`𝓞 K` form the
    project already proves and the 2025 literature uses.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c rows 5 & 7 — generalize the ground ring ℤ to an arbitrary
    char-0 PID with `K = Frac R`.

**Proposed restatement (already exists in-project — upstream THIS, not the ℤ version):**
```lean
-- PIDMain.lean:401 — the form to take to mathlib
theorem lutz_nagell_pid_discriminant_of_torsion
    {R K} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) → Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    (2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ
```
Then `lutz_nagell_discriminant_general` (ℤ/ℚ) becomes the ≤2-line corollary in Phase 6 Attempt 2.

Estimated cost of regeneralisation: **CHEAP** — the general proof is already proven and sorry-free;
only the ℤ corollary needs re-deriving (and it already routes through the PID lemma today).

Mathlib downstream this enables (the real improvement):
  - One Nagell–Lutz discriminant statement covering ℤ/ℚ, all char-0 PIDs, AND number fields of
    class number 1 (`𝓞 K`) — matching arXiv 2509.07524 (2025).
  - Composes with mathlib's `IsFractionRing` / `NumberField` / `IsPrincipalIdealRing` API so the
    `𝓞 K` instance is free; the ℤ/ℚ form is a corollary, not a parallel proof.

**Next action:** run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general` (it
will tension the ℤ/ℚ form against the already-proven PID/`𝓞 K` form). Upstream the **general**
theorem (`lutz_nagell_pid_discriminant_of_torsion`, and/or the `𝓞 K` re-export) to a new file under
`Mathlib/NumberTheory/EllipticCurve/` or `Mathlib/AlgebraicGeometry/EllipticCurve/`, with ℤ/ℚ and
short-Weierstrass as corollaries. This assessment applies to the whole Nagell–Lutz cluster: the
`General*` ℤ/ℚ track and the `PID*` track are parallel — PR the `PID*` (general) track and reduce
`General*` to corollaries.

---

## Next step

Run `/generalise` on this decl, then open the mathlib PR against the **general** PID / number-field
statement (`lutz_nagell_pid_discriminant_of_torsion` / `lutz_nagell_number_field_discriminant`),
keeping `lutz_nagell_discriminant_general` (ℤ/ℚ) and `lutz_nagell_discriminant` (short Weierstrass)
as ≤2-line corollaries.
