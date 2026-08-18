# /mathlibable report — `LutzNagell.PID.den_no_simple_prime_factor_of_on_curve`

## Baseline (Phase 0)
- lake build:               not run (local build stale, per task; mathlib MCP index unavailable
  in this env — reasoned from source + grep over the vendored mathlib clone, which is
  authoritative for "is it in mathlib").
- mathlib pin:              `.lake/packages/mathlib` @ `09b373db6e247a35cfa5e44578c09a20e7c97271`
  (2026-06-21).
- decl `LutzNagell.PID.den_no_simple_prime_factor_of_on_curve`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDDenominators.lean:87`.
- namespace: confirmed `namespace LutzNagell` (l.19) → `namespace PID` (l.20), closed
  `end PID` (l.188) / `end LutzNagell` (l.189). Qualified name
  **`LutzNagell.PID.den_no_simple_prime_factor_of_on_curve`** verified from source.
- kind:                      theorem.
- has sorry:                 no (full ~75-line proof, lines 94–170).
- module docstring summary:  "Denominators on general Weierstrass curves over UFDs — if a prime
  `q` divides `den_R(x)` exactly once for `(x, y)` on the curve, contradiction." This decl is the
  file's **sole `## Main results` entry** (PIDDenominators.lean l.15).

## Statement (Phase 1)

Let `R` be a UFD (`CommRing R`, `IsDomain R`, `UniqueFactorizationMonoid R`) with fraction field
`K` (`Field K`, `Algebra R K`, `IsFractionRing R K`). Let `W : WeierstrassCurve R` be the general
(long) Weierstrass model `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, `aᵢ ∈ R`. Suppose `(x, y) ∈ K²`
satisfies the curve equation (`heq`). Let `q : R` be `Prime`. If `q ∣ (IsFractionRing.den R x : R)`
(`hqd`) but `¬ q² ∣ (IsFractionRing.den R x : R)` (`hq2`) — i.e. `q` divides the ring-theoretic
denominator of the x-coordinate **exactly once** — then `False`.

Equivalently (contrapositive, quantified): every prime factor of `den_R(x)` for a point on a
Weierstrass curve over a UFD has multiplicity ≥ 2 — the denominator of the x-coordinate is
*powerful / squarefull*. This is the classical "den(x) is a perfect square (= c²), den(y) a perfect
cube (= c³)" structure, and is the integrality core of the Nagell–Lutz theorem.

Conclusion (Lean): `False`.

**Proof body (substantive, ~75 lines):** write `x = α/d`, `y = γ/e` in reduced form (`num`/`den`,
coprime since `R` UFD). Clear denominators to an equation in `R` (private helper
`clearing_denominators`). Since `q ∣ d` but `q² ∤ d`, write `d = q·u` with `q ∤ u`; coprimality of
`α, d` gives `q ∤ α`, hence `q ∤ S := α³ + a₂α²d + a₄αd² + a₆d³` (private helper
`not_dvd_sum_of_not_dvd_cube`). Then a **three-round q-adic descent**:
round 1 — `q ∣ LHS = e²·S`, so `q ∣ e²`, so `q ∣ e`, write `e = q·e₁`;
round 2 — substitute, divide by `q²`, get `q ∣ e₁²·S`, so `q ∣ e₁`, write `e₁ = q·e₂`;
round 3 — substitute, divide by `q`, get `q ∣ γ²u³`, and since `q ∤ u`, `q ∣ γ`.
Finally `q ∣ γ` and `q ∣ e` contradict `IsRelPrime γ e`. (`q.not_unit (hcop_y …)`.)

## Size classification (Phase 2a)

Verdict: **LARGE / substantive**.
Reason: it IS the file's sole `## Main results` headline. ~75 lines of genuine, irreducible
arithmetic (the three-round descent). It is the load-bearing engine behind the project's
`den_powerful_of_on_curve` (PIDMain l.71, a one-line `by_contra` restatement of THIS decl) and
`den_not_prime_of_on_curve` (PIDDenominators l.176, the `q = den x` corollary). It is the
formal core of a classical named theorem (Nagell–Lutz integrality). Literature width run
EXHAUSTIVE.

## Relationship to its in-project siblings (decisive context)

There are three statements of the same fact in this project; THIS decl is the engine, the other
two are cosmetic repackagings of it:

| Decl | Location | Form | Relationship |
|------|----------|------|--------------|
| **`den_no_simple_prime_factor_of_on_curve`** (this) | PIDDenominators l.87 | `q∣den ∧ q²∤den → False` | the ~75-line arithmetic **engine** |
| `den_powerful_of_on_curve` | PIDMain l.71 | `∀ q, Prime q → q∣den → q²∣den` | `fun _ hq hqd ↦ by_contra fun h ↦ den_no_simple_prime_factor_of_on_curve W heq hq hqd h` — **one-line `by_contra` wrapper** over this decl |
| `den_not_prime_of_on_curve` | PIDDenominators l.176 | `Prime (den) → False` | `q := den x`, `dvd_rfl`, trivial `¬q²∣q` witness — **thin corollary** (assessed separately, verdict NO-composable) |

The sibling `/mathlibable` report on the *corollary* `den_not_prime_of_on_curve`
(`…/mathlibable/den_not_prime_of_on_curve.md`) reached **NO-composable-from-mathlib** and
explicitly deferred the YES case to THIS decl, stating: *"The parent
`den_no_simple_prime_factor_of_on_curve` is a substantive, genuinely-absent-from-mathlib result …
If/when the parent is upstreamed, run `/mathlibable` on it — that is where the YES case lives."*
This report is that follow-up; it confirms the YES (with a reformulation rider).

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query / action                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz proof denominator x-coordinate perfect square torsion integral Silverman"                  | yes  | "denominator of `x` is `d²`, of `y` is `d³`; for any prime the denominators of torsion pts are coprime to it ⟹ integral" | Wikipedia, Harvard (Alpoge "Nagell-Lutz, quickly"), UMich REU (Li), UChicago REU (Galperin), PlanetMath; **Silverman AEC Cor. VIII.7.2** named explicitly |
|  2 | WebSearch (general/source form)  | "powerful/squarefull denominator x-coordinate Weierstrass every prime divides twice integral points reduction" | partial | confirms it is a specialised arithmetic-geometry fact behind integral-points; Cremona ch.3, Dummit notes ch.7 | The exact "squarefull denominator" phrasing is below the resolution of survey hits; it is the standard *intermediate lemma*, packaged via valuations/formal groups in sources |
|  3 | WebSearch (Lean/formalisation)   | "Lean mathlib Nagell-Lutz elliptic curve denominator IsFractionRing"                                    | yes (neg.) | mathlib has `num/den_dvd_of_is_root` (rational root thm) and `IsFractionRing` num/den API; **no** Nagell–Lutz formalisation found | "1000 theorems in Lean" list + Zulip "thoughts on elliptic curves" confirm NL is not yet upstream |
|  4 | ChatGPT MCP                      | self-contained NL-integrality query (Silverman VII/VIII)                                                | n/a (down) | — | MCP Codex bridge errored in this env (per task note); substituted with two extra source-text WebSearches at differing generality (rows 1,2) |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/` → only `overview/`, no `references/`                          | n/a  | — | directory absent; recorded n/a |
|  6 | nLab                             | "Nagell-Lutz" / "elliptic curve torsion integral"                                                       | n/a  | nLab has no NL / integral-torsion page | elementary arithmetic-geometry; not nLab-shaped |
|  7 | Stacks Project                   | "elliptic curve torsion integral" / "Nagell"                                                            | n/a  | no NL material | Stacks is scheme-theoretic foundations; this Diophantine result is out of scope |
|  8 | MathOverflow / MSE               | (via #1/#2 result sets) "denominator x-coordinate torsion point square"                                  | yes  | confirms `c²`/`c³` denominator structure as the standard mechanism | matches this decl's per-prime engine exactly |
|  9 | recent arXiv (last 5 years)      | "Nagell-Lutz" → arXiv:2509.07524                                                                        | yes  | Nagell–Lutz over imaginary quadratic fields; same integrality core, generalised base ring | modern generalisation keeps the result at the full-integrality grain; our UFD form is in that spirit |

Protocol pass check: WebSearch ≥3 distinct queries at different generality ✓ (1,2,3); ChatGPT MCP
standard-form query substituted (down) and documented ✓; local refs checked (absent → n/a) ✓; nLab
✓ (n/a, reason); Stacks / MathOverflow / arXiv each checked or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept: the **integrality (powerful-denominator) core of the Nagell–Lutz theorem** — for a point
on a Weierstrass curve, the x-coordinate denominator is a perfect square (each prime divides it ≥
twice); equivalently `v_q(x) < 0 ⟹ v_q(x)` even, the `x = a/c²`, `y = b/c³` scaling. Standard
sources: **Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), Cor. VIII.7.2** plus the
reduction / formal-group machinery of §IV, §VII; **Silverman–Tate, *Rational Points on Elliptic
Curves*, Ch. II**; course notes (Cremona ch.3, Dummit ch.7, REU notes). Sources agree on the
standard fact. Literature usually states the **full integrality theorem** and proves it via this
exact squarefull-denominator step (the per-prime engine), but only the *headline* theorem gets a
name; the engine is the universally-used mechanism, not separately christened. Modern generality:
ℤ (classical) → ring of integers of a number field (arXiv:2509.07524) → DVR / local field
(Silverman). Disagreement with literature: none; the math is standard. The project's UFD base ring
**meets or exceeds** the classical ℤ form.

## Generality analysis

Literature-standard form: the integrality theorem / its squarefull-denominator step over ℤ
(classical), DVR (Silverman), or `𝒪_F` (modern). This decl is stated over a **general UFD**, which
is the right mathlib generality for a num/den statement.

| # | Parameter / hypothesis                        | Current Lean form                                   | Literature-standard | Weaker form exists? | Reason |
|---|-----------------------------------------------|-----------------------------------------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` | UFD | ℤ classically; DVR/`𝒪_F` modern | **already ≥ standard** | `IsFractionRing.num`/`den` and `num_den_reduced` (Mathlib/RingTheory/Localization/NumDen.lean l.33) require **exactly** `[CommRing][IsDomain][UniqueFactorizationMonoid]`. Cannot be weakened below UFD without losing num/den. Optimal. |
| 2 | `W : WeierstrassCurve R`, long equation `a₁..a₆` | general (long) Weierstrass model | often short form `y²=x³+Ax+B` in textbooks | already **more** general | The long model with all `aᵢ` subsumes the short form; no weakening wanted. Good. |
| 3 | `heq` : `(x,y)` on the curve                   | bivariate curve relation in `K`                     | same                | n/a                 | exactly the on-curve hypothesis. |
| 4 | `q : R` `Prime`, `q∣den`, `¬q²∣den`           | per-prime "exactly once" hypotheses, conclusion `False` | usually `∀ prime, q∣den ⟹ q²∣den` (positive) | reformulation, not weakening | **The one idiom point — see Phase 4c.** mathlib prefers the positive contrapositive; the project already has it (`den_powerful_of_on_curve`). |

### Generality verdict (Phase 4b)

Hypotheses are at **optimal generality** (UFD is forced by `num`/`den`; long Weierstrass model is
already maximal). **Zero hypothesis-weakening opportunities.** The current form is *more* general
than the classical ℤ literature form. The only adjustment is a **statement-shape reformulation**
(Phase 4c), not a weakening.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | `...→ False` engine → positive contrapositive? | **yes** | State the public lemma as `∀ q, Prime q → q ∣ den_R(x) → q² ∣ den_R(x)` (i.e. the `den_powerful_of_on_curve` shape), keeping this `→ False` form as the `private` engine. mathlib idiom strongly prefers positive divisibility statements over `→ False`. | the powerful-denominator form is what every consumer (integrality theorem) actually wants |
|  2 | "let R be a UFD" preamble → typeclasses? | no | already typeclass-based (`UniqueFactorizationMonoid`, `IsFractionRing`) | — |
|  3 | concrete index (ℤ) → general ring? | already done | base ring is a general UFD, not ℤ | — |
|  4 | valuation phrasing? | optional | could *additionally* be expressed via `multiplicity`/`emultiplicity q (den …) ≥ 2`, but the plain `q²∣den` form is cleaner and matches mathlib's divisibility idiom | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, a reformulation** — ship the **positive contrapositive**
(`q∣den → q²∣den`, the powerful-denominator statement the project already wrote at PIDMain l.71)
as the public mathlib lemma, with this `→ False` decl retained as the private proof engine. This is
a presentation change, not a hypothesis weakening — hence the **YES-but-generalise-first** bucket
(generalise = reformulate to mathlib's idiom + land alongside the headline integrality theorem).

## Diamond / defeq risk — n/a

Declaration kind is `theorem` (Prop-valued); introduces no instances or definitional equalities.

## Mathlib search-status

[A] Lean-Finder / LeanSearch — mathlib MCP index unavailable in this env; substituted with grep
    over the vendored mathlib source (authoritative) + reasoning. NL search "denominator of
    x-coordinate of point on Weierstrass curve is powerful / Nagell-Lutz integrality" — no upstream
    development exists to hit.
[B] Loogle — type patterns `WeierstrassCurve _ → … → False` and
    `Prime _ → _ ∣ IsFractionRing.den _ _ → _² ∣ IsFractionRing.den _ _`: no plausible hit; mathlib
    has no Weierstrass-point ⟹ denominator-multiplicity lemma (confirmed by src grep).
[D] **Grep mathlib src** (decisive): `grep -rn "den_no_simple_prime|den_powerful|NagellLutz|Nagell|Lutz"`
    over `.lake/packages/mathlib/Mathlib` → **0 hits**. No `*nagell*`/`*lutz*` files.
    Surveyed `Mathlib/AlgebraicGeometry/EllipticCurve/` incl. `Reduction.lean`, `Weierstrass.lean`,
    `Affine/Point.lean`: mathlib has **reduction-theory scaffolding** (`IsIntegral`, `IsMinimal`,
    `reduction`, `IsGoodReduction`, over a DVR/`ValuationRing`) but **no point-integrality, no
    powerful-denominator, no torsion-integrality, no valuation-of-den result**. The Weierstrass +
    `IsFractionRing` grep co-hits (Reduction.lean, Affine/Point.lean) are unrelated uses.
[E] Closest composable primitive — `Mathlib/RingTheory/Polynomial/RationalRoot.lean`:
    `den_dvd_of_is_root` (`den A r ∣ p.leadingCoeff` for `r` a root of univariate `p ∈ A[X]`) and
    `num/den_dvd_of_is_root`, `isInteger_of_is_root_of_monic`. These bound den by a *fixed divisor*
    and require a *univariate* root; they say **nothing about multiplicity/powerfulness** and do
    not apply to the bivariate on-curve relation. Not the same statement (see Phase 6).

Concluded: **not in mathlib** (all methods exhausted; literature-standard form also absent). No
Nagell–Lutz development exists upstream — only the reduction scaffolding that *would consume* this.

## Call sites

`den_no_simple_prime_factor_of_on_curve` is consumed within the project by:
- `den_powerful_of_on_curve` (PIDMain l.71) — the positive ∀-form restatement.
- `den_not_prime_of_on_curve` (PIDDenominators l.176) — the `q = den x` corollary.
Both are thin wrappers; the substantive arithmetic lives entirely in THIS decl. The
powerful/not-prime forms then feed the project's integrality chain
(`integrality_of_*`, `lutz_nagell_integrality_pid`, PIDMain). So K ≥ 2 distinct in-project
consumers, all routing the real work through this engine — a genuine reusable core, not a
single-use convenience.

## Composition check (Phase 6)

Can `den_no_simple_prime_factor_of_on_curve` be derived in ≤3 chained calls from results **mathlib
has**? → **No.**

- The proof is the irreducible three-round q-adic descent (~75 lines). Its only non-glue
  dependencies are two **project-local private helpers** in the same file:
  `clearing_denominators` (PIDDenominators l.49) and `not_dvd_sum_of_not_dvd_cube` (l.30) — neither
  is in mathlib. The remainder is generic `ring`/`linear_combination`/`Prime.dvd_or_dvd`/
  `IsRelPrime` glue.
- The nearest mathlib primitive, `den_dvd_of_is_root`, is **not composable into this**: it bounds
  `den` by `leadingCoeff` of a *univariate* polynomial and yields no multiplicity information; the
  x-coordinate here is given by the *bivariate* curve relation (you would first have to eliminate
  `y`, and even then get only "den ∣ const", never "every prime divides den twice").
- There is no mathlib lemma about the multiplicity / squarefull structure of `IsFractionRing.den`
  (grep over `Mathlib/RingTheory/Localization/` → none).

Conclusion: **NOT composable from mathlib** in ≤3 calls (or any bounded number) — this is original,
load-bearing arithmetic content.

## Verdict

**Category:** `YES-but-generalise-first`

**Evidence:**
- **Literature (Phase 3):** classical — the squarefull/`c²`-`c³`-denominator integrality core of
  Nagell–Lutz (Silverman AEC Cor. VIII.7.2 + §IV/§VII; Silverman–Tate Ch. II). A genuinely
  important, universally-used result; mathlib wants Nagell–Lutz.
- **Mathlib search (Phase 5):** not in mathlib, and neither is any Nagell–Lutz / point-integrality
  development — mathlib has only DVR reduction scaffolding (`EllipticCurve/Reduction.lean`).
- **Generality (Phase 4):** hypotheses are at **optimal** generality (general UFD — forced by, and
  matching, mathlib's `IsFractionRing.num`/`den` API; general long Weierstrass model). Exceeds the
  classical ℤ form. **Zero hypothesis-weakening opportunities.**
- **Composition (Phase 6):** **NOT** composable from mathlib — ~75 lines of irreducible q-adic
  descent over two project-private helpers; the nearest primitive (`den_dvd_of_is_root`) is a
  different statement.
- **Reuse:** ≥2 distinct in-project consumers route their real work through this engine.

**Rationale:**

This is the substantive theorem the file is built around — the formal heart of Nagell–Lutz
integrality, stated at the right (UFD, long-Weierstrass) generality, genuinely absent from mathlib,
and not composable from mathlib primitives. It belongs in mathlib. The single reason it is
**YES-but-generalise-first** rather than YES-add-as-is is **statement shape**: it is phrased as a
per-prime engine `q∣den ∧ q²∤den → False`, whereas mathlib idiom wants the **positive
contrapositive** `∀ q, Prime q → q ∣ den_R(x) → q² ∣ den_R(x)` (the *powerful-denominator* lemma) —
which the project itself already wrote as `den_powerful_of_on_curve` (PIDMain l.71, a one-line
`by_contra` over this decl). The recommended mathlib shape is: keep this `→ False` lemma `private`
as the proof engine, and expose the powerful-denominator contrapositive as the public result,
landed in `Mathlib/AlgebraicGeometry/EllipticCurve/` alongside the headline Nagell–Lutz integrality
theorem this development is heading toward. "Generalise" here means **reformulate to idiom + ship
with its consumer**, not weaken any hypothesis (there is nothing to weaken).

**WHAT to generalise / reformulate before PR:**
1. Public statement: `∀ q : R, Prime q → q ∣ (den R x : R) → q² ∣ (den R x : R)` (positive); retain
   the current `→ False` form as the `private` engine. (Optionally also offer the
   `multiplicity`/`emultiplicity ≥ 2` phrasing.)
2. Package with the corollaries (`den_not_prime`, the integral-point / `c²`,`c³` structure) and the
   target Nagell–Lutz integrality theorem, so mathlib gets a coherent unit rather than a bare engine.
3. Names: under the `WeierstrassCurve` namespace, e.g. `WeierstrassCurve.sq_dvd_den_of_…` /
   `…den_isPowerful…`, not the project-internal `LutzNagell.PID.*`.

**Building blocks:** project-private `clearing_denominators`, `not_dvd_sum_of_not_dvd_cube`
(PIDDenominators l.49, l.30) — would move to mathlib with the theorem. Mathlib glue used:
`Prime.dvd_or_dvd`, `Prime.dvd_of_dvd_pow`, `IsRelPrime` (`num_den_reduced`),
`mul_left_cancel₀`, `IsFractionRing.{num,den,mk'_num_den',injective}`,
`mem_nonZeroDivisors_iff_ne_zero`, `ring`/`linear_combination`.

---

## Next step

Upstream the **powerful-denominator** form to mathlib (positive contrapositive
`q∣den → q²∣den`), with this `→ False` lemma as its private engine, under the `WeierstrassCurve`
namespace and `Mathlib/AlgebraicGeometry/EllipticCurve/`, ideally together with the corollaries
and the Nagell–Lutz integrality theorem. The companion decls `den_powerful_of_on_curve` (PIDMain)
and `den_not_prime_of_on_curve` (corollary; assessed NO-composable separately) become the
restatement and the thin corollary of this core.
