# /mathlibable report — `LutzNagell.LutzNagellTheorem.x_integral_of_odd_prime_torsion_general`

## Verdict: BORDERLINE-needs-human

One-line: a genuine, non-trivially-composable proof **step** of the Nagell–Lutz theorem
(itself absent from mathlib) whose `ℤ`-form is the *less* general of two duplicated tracks
in the project. Belongs upstream only *as part of* a Nagell–Lutz PR, at the PID generality —
the open question is grouping/which-track, not mathematical worth.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — statement
  elaborates per file structure; mathlib pin `09b373db6e24` confirmed in `lakefile.toml`).
- decl `LutzNagell.LutzNagellTheorem.x_integral_of_odd_prime_torsion_general`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:80` (signature; the line
  `:83` in the task points at the `htors` hypothesis of this same theorem).
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Prime-order and order-4 torsion integrality for general Weierstrass
  curves" — if `P ≠ 0` has odd prime order or order 4 on a general integral Weierstrass curve,
  `P` has integral affine coordinates.

Qualified name **VERIFIED** from source: file declares `namespace LutzNagell` (line 19) then
`namespace LutzNagellTheorem` (line 20), closed by `end LutzNagellTheorem` (205) / `end LutzNagell`
(206). Base name `x_integral_of_odd_prime_torsion_general` ⇒ full name
`LutzNagell.LutzNagellTheorem.x_integral_of_odd_prime_torsion_general`. ✓ (matches the parsed name).

---

### Statement (Phase 1)

`x_integral_of_odd_prime_torsion_general` states: let `W` be a Weierstrass curve with **integer**
coefficients `aᵢ ∈ ℤ`, and let `P = (x, y)` be a nonsingular rational affine point on its base
change `curveQ W` to `ℚ`. If `p` is an odd prime and `p • P = 0` in the (Jacobian) point group,
then the x-coordinate `x ∈ ℚ` is in fact an **integer** (`∃ x₀ : ℤ, (x₀ : ℚ) = x`).

This is one half (the x-coordinate half, odd-prime case) of the integrality clause of the
**Nagell–Lutz theorem**: a nonzero torsion point on an integral-model elliptic curve has integral
coordinates.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — a Weierstrass curve over `ℤ` (general 5-coefficient model, not short form).

Hypotheses (Lean side):
- `hns : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point of the curve over `ℚ`.
- `hp : p.Prime`, `hodd : p ≠ 2` — `p` is an odd prime.
- `htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0` — `p`-torsion.

Conclusion (math): `x ∈ ℤ`.
Conclusion (Lean): `∃ x₀ : ℤ, (x₀ : ℚ) = x`.

Proof shape (from source, lines 86–109): (1) `p • P = 0 ⟹ ψ_p(x,y) = 0`
(`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`); (2) for odd `p`, `ψ_p` evaluates to the univariate
`preΨ_p(x)` (`evalEval_ψ_odd`); (3) base-change `map_preΨ` + `eval_map` turn this into
`aeval x (W.preΨ p) = 0` over `ℤ`; (4) **rational root theorem** `den_dvd_of_is_root` ⟹
`x.den ∣ leadingCoeff (preΨ_p)`; (5) `leadingCoeff_preΨ` ⟹ that leading coeff is `p` (odd case),
so `x.den ∣ p`; (6) `x.den` is `1` or `p`; (7) the project lemma
`den_ne_prime_of_on_general_curve` rules out `x.den = p` (a point on an integral curve cannot have
denominator exactly a prime), leaving `x.den = 1`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline) — not itself a named theorem, but a *constituent step of* a
person-named theorem (Nagell–Lutz). It lives under the file's "Odd prime torsion: x integral"
section and is the engine of `prime_order_integrality_general`, a primary project goal.
Reason: step of a named theorem ⇒ guaranteed near the literature.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)
Kind is `theorem`, not a `def` — one-line check **n/a**. (For the record the proof body is ~24
substantive lines with four non-trivial `have` steps; nowhere near a one-liner.)

---

### Literature search table (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "Nagell-Lutz theorem torsion point integral coordinates elliptic curve division polynomial proof" | yes | NL: nonzero torsion pt of `y²=x³+Ax+B`, `A,B∈ℤ`, has `x,y∈ℤ`; further `y=0` or `y²∣4A³+27B²` | Wikipedia (dedicated page), Silverman AEC, Alpoge "Nagell-Lutz, quickly" (Harvard), AIMS essay, Li/Galperin REU notes, unizg §15.3 |
| 2 | WebSearch (mechanism) | "torsion point x-coordinate denominator divides n division polynomial leading coefficient rational root theorem elliptic curve" | yes | roots of `ψ_n` are x-coords of n-torsion; division polys give denominators of `[n]`; torsion ⟹ bounded denominators | Galperin REU, arXiv 1108.3051 (explicit valuations of division polys), confirms the exact proof strategy used here |
| 3 | ChatGPT MCP | — | n/a | — | `mcp__chatgpt-math__ask_chatgpt_math` is loadable but task flags it may be down; the two web channels already pin the standard form unambiguously (Nagell–Lutz is textbook), so a second opinion is not load-bearing. Recorded n/a with reason. |
| 4 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | — | no `references/` directory under the project's `.mathlib-quality/` (only `overview/`); per-project ref PDFs are gitignored & live in `refs/NagellLutz/` which is absent in this checkout. |
| 5 | nLab | "Nagell-Lutz" / "elliptic curve torsion integral" | no | — | nLab has no Nagell–Lutz / torsion-integrality page; not a category-theoretic concept. |
| 6 | nCatLab | — | n/a | — | not a categorical concept (concrete diophantine statement). |
| 7 | Stacks Project | — | n/a | — | not in Stacks' scope (no explicit elliptic-curve torsion arithmetic of this kind). |
| 8 | MathOverflow / MSE | (covered via WebSearch #1–2 result sets) | yes | same NL statement + coprime/bounded-denominator argument | standard textbook lemma; many expository write-ups surfaced (REU papers, course notes). |
| 9 | recent arXiv (≤5 yr) | "Nagell-Lutz" / "division polynomial valuations" (#1, #2 result sets) | yes | arXiv 2509.07524 (NL over imaginary quadratic fields, 2025), 1108.3051 (valuations of division polys) | confirms it's a classical, *named* result actively generalised; the ℚ statement is textbook. |

### Literature summary (Phase 3)

Concept identified as: the **x-coordinate / odd-prime case of the integrality half of the
Nagell–Lutz theorem**, proved by the standard "division polynomial + rational root" argument.
Sources agree on the standard form: **yes** — the proof step ("for `n`-torsion, `x.den ∣` the
leading coefficient of the `n`-th division polynomial, hence — when `n` is an odd prime so the
leading coeff is `n` — `x.den ∈ {1, n}`, and a curve-equation argument kills `den = n`") is exactly
the textbook route (Silverman AEC VIII; Cremona Ch.3; Alpoge "Nagell-Lutz, quickly").
Most general standard form: the **full Nagell–Lutz integrality statement** — *every* nonzero
torsion point (any order, both coordinates) on an integral model has integral coordinates (plus
the `y² ∣ Δ` refinement). The present decl is the **odd-prime, x-coordinate fragment** of that.
Generality dimensions where the literature varies:
  - torsion order: literature states it for arbitrary order; here split into odd-prime / order-2 /
    order-4 fragments (the project handles 2 and 4 in sibling lemmas in the same file). The split is
    forced by the leading coefficient of `preΨ_n` differing (`n` for odd `n`, `n/2` for even `n`).
  - coordinate: literature does both `x` and `y`; here `x` only (`y` is the sibling
    `y_integral_of_x_integral_on_general_curve`).
  - base: classically over `ℚ`; recent arXiv work pushes to number fields. This decl is over `ℚ`/`ℤ`;
    the project's PID track pushes to a general PID with fraction field.
Disagreement with the literature: **none** — it is a faithful fragment of the standard proof.

---

### Generality analysis (Phase 4)

Literature-standard form: full Nagell–Lutz integrality (all torsion orders, both coords).

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `W : WeierstrassCurve ℤ` | integer-coeff general Weierstrass model | integral model over `ℤ` (or a DVR / PID) | **yes (realised)** | The project's **PID track** (`PIDPrimeOrder.lean`) already generalises base ring `ℤ → R` a PID with fraction field `K`. The strictly more general form exists *in the project itself* (`x_isInteger_of_odd_prime_torsion_squarefree`, `PIDPrimeOrder.lean:113`). |
| 2 | `hp : p.Prime`, `hodd : p ≠ 2` | odd prime order | any torsion order | yes (in principle) | Full NL is for all orders; the project deliberately splits into odd-prime / 2 / 4 fragments because the leading-coeff value of `preΨ_n` differs (`n` odd vs `n/2` even). |
| 3 | conclusion: `x` integral | x-coordinate only | both coordinates | yes | `y` handled separately (`y_integral_of_x_integral_on_general_curve`); `prime_order_integrality_general` combines them. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (one fragment — odd prime, x-coord, base
`ℤ`). Number of weakening opportunities: ~3, but they are **deliberate decomposition**, not
accidental over-specialisation. The "right" mathlib object is the *assembled* Nagell–Lutz theorem,
not this fragment in isolation. Notably the project **already carries the more general (PID) form**
of this very step (`x_isInteger_of_odd_prime_torsion_squarefree` resting on
`isInteger_of_root_squarefree_leading_coeff`, `PIDPrimeOrder.lean:82`), making this `ℤ`-specialised
copy the *less* general of the two duplicated tracks.

Proposed restatement: not a single-lemma rewrite — the natural upstream artifact is a **Nagell–Lutz
file** whose public face is `prime_order_integrality` (+ order-2/4), with this step as a private/
internal helper, stated at PID generality. Cost of restatement: **MODERATE–EXPENSIVE** (requires
upstreaming the surrounding torsion → `ψ=0` bridge and the denominator lemmas too). Cost does *not*
drive the verdict (per gate).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | bundled-hyp → typeclass? | no | hypotheses already minimal (`Prime`, `≠ 2`, a torsion equation); nothing to classify. |
| 2 | sequences/metric → filters? | no | purely algebraic; no limits. |
| 3 | construction → universal property? | no | a divisibility/integrality statement, not a construction. |
| 4 | set+closure → bundled substructure? | no | n/a. |
| 5 | field/vector-space → weaker typeclass? | **yes (mild)** | base `ℤ` → PID/DVR (or `IsIntegrallyClosed` + `IsFractionRing`); **the project's PID track already does exactly this** (`isInteger_of_root_squarefree_leading_coeff`). The `ℤ` form here is the specialisation. |
| 6 | 1-categorical → higher? | no | n/a. |
| 7 | concrete index → general monoid/group? | partial | `p` an odd prime is intrinsic to the leading-coeff value (`leadingCoeff_preΨ` is `p` exactly when `p` is odd); not a free index to generalise. |

Modern idiom available: **yes, mild** — state over a PID (or `IsIntegrallyClosed` + `IsFractionRing`)
rather than `ℤ`. The downstream benefit (works for any integral model, not just `ℤ`) is real and is
*already realised in the project's PID track*. This pushes the verdict toward "if upstreamed, prefer
the PID-general form" — but the packaging question (fragment vs whole NL, and which of the two
parallel tracks is the canonical one) dominates, hence BORDERLINE rather than a clean
YES-but-generalise-first.

---

### Mathlib search-status (Phase 5)

Index MCP tools (loogle / leansearch / lean_local_search) are **not loadable** in this environment
(deferred-tool list exposes `WebSearch`, the Google/Gmail MCPs, `LSP`, etc., but no loogle/leansearch
handle). Substituted direct source grep over the pinned mathlib (`.lake/packages/mathlib`, rev
`09b373db6e24`).

[A] Lean-Finder       n/a — index tool unavailable in env.
[B] Loogle            n/a — index tool unavailable; substituted [D].
[C] LeanSearch        n/a — index tool unavailable; substituted [D].
[D] Grep mathlib src  `grep -rni "nagell\|lutz" Mathlib/` over the *entire* library → the only
                      "Lutz" hits are **Patrick Lutz** (Galois-theory author: AbelRuffini, KummerExtension,
                      Solvable, …); **zero** matches for "nagell" / the torsion-integrality theorem.
                      `grep "torsion" .../EllipticCurve/**` → only `twoTorsionPolynomial` (the 2-torsion
                      polynomial def + its discriminant lemma), **no integrality theorem**.
[E] Name pattern      grep decl heads for `x_integral`/`prime_order`/`torsion.*integ` in mathlib → none.

Searched for both: the user's current form (odd-prime x-integral) **and** the literature-standard
form (full Nagell–Lutz / any torsion ⟹ integral). Neither is in mathlib.

What mathlib *does* have (the building blocks, all confirmed present in this checkout):
- `Mathlib.RingTheory.Polynomial.RationalRoot.den_dvd_of_is_root` (`RationalRoot.lean:89`) — rational
  root theorem (`aeval r p = 0 ⟹ den ∣ p.leadingCoeff`). Used directly.
- `Mathlib.RingTheory.Polynomial.RationalRoot.isInteger_of_is_root_of_monic` (`:115`) — used by the
  sibling `y_integral_*`.
- `WeierstrassCurve.leadingCoeff_preΨ`
  (`DivisionPolynomial/Degree.lean:310`, `= if Even n then n/2 else n`), plus `preΨ`, `map_preΨ`,
  `leadingCoeff_preΨ₄` (`Degree.lean:145`, `= 2`) — `…/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`.
- `WeierstrassCurve` Affine + Jacobian Point groups — `…/EllipticCurve/{Affine,Jacobian}/Point.lean`.
- `Mathlib.NumberTheory.EllipticDivisibilitySequence` — the EDS / `ψ` recurrence.
- `Mathlib.RingTheory.Localization.Rat` (`Rat.isFractionRingDen`, identifies `x.den` with the
  ring-theoretic denominator).

Concluded: **not in mathlib** (all available methods exhausted, both the user's form and the
literature-standard form). Mathlib has every primitive but not the assembled torsion-integrality
result, and not the Nagell–Lutz theorem.

> NOTE on the fork: the project forks `DivisionPolynomial.*` and `EllipticDivisibilitySequence` into
> `projects/NagellLutz/LutzNagell/`. This decl is **not** a forked-mathlib decl — it is genuinely new
> project content built *on top of* the (forked copy of the) mathlib division-polynomial API. The
> upstream `leadingCoeff_preΨ` etc. exist; `x_integral_of_odd_prime_torsion_general` does not. So this
> is **not** a "mathlib already has it via the fork" case.

---

### Composition check (Phase 6)

#### Call sites (Phase 6.0)
Internal use count: **1** (excluding the declaring file's own declaration line).
External-to-file callers: 0.

| Caller file:line | Usage |
|------------------|-------|
| `GeneralPrimeOrder.lean:155` (same file) | `obtain ⟨x₀, hx₀⟩ := x_integral_of_odd_prime_torsion_general W hns hp hodd htors` — inside `prime_order_integrality_general` |

Inline-derivation grep: the PID track re-derives the *same idea* at a more general typeclass level
(`x_isInteger_of_odd_prime_torsion_squarefree`, `PIDPrimeOrder.lean:113`) — a parallel duplicated
implementation, **not** a consumer of this decl. So this is a **single-use internal step** with a
more-general twin elsewhere in the project. By the call-sites heuristic (K = 1, twin re-derivation),
this leans away from "standalone API" and toward "internal helper of a bigger theorem".

#### Composition attempt (Phase 6a)

Can it be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: `den_dvd_of_is_root … |> …` — fails. To even *reach* `aeval x (W.preΨ p) = 0` you must
first prove `p • P = 0 ⟹ ψ_p(x,y) = 0` (the torsion → division-polynomial bridge,
`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, itself a multi-step lemma about the Jacobian point
group), then `evalEval_ψ_odd` to drop to the univariate `preΨ`, then `map_preΨ`/`eval_map` to land
over `ℤ`. That is already ≥3 non-trivial steps *before* the rational-root call.

Attempt 2: after the rational root theorem gives `x.den ∣ p`, closing the goal needs the
**project-specific** `den_ne_prime_of_on_general_curve` (`GeneralDenominators.lean:42`, an honest
lemma: a point on an integral curve cannot have denominator exactly a prime — it delegates to the
UFD valuation lemma `PID.den_not_prime_of_on_curve`). Mathlib has no analogue. This is reasoning,
not composition.

Conclusion: **NOT-COMPOSABLE** — the proof is a genuine ~24-line argument chaining four non-trivial
`have`s plus a project-only dependency, not a 1–3 mathlib-call inline.

---

## Verdict: `LutzNagell.LutzNagellTheorem.x_integral_of_odd_prime_torsion_general`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): a faithful **fragment** (odd-prime, x-coordinate, base `ℤ`) of the
  **Nagell–Lutz theorem** — a classical, person-named result (Wikipedia, Silverman AEC, Alpoge).
  Not in mathlib in any form (`grep nagell Mathlib/` = 0 hits; only Patrick-Lutz authorship hits).
- Generality (Phase 4): **STRICTLY NARROWER THAN STANDARD** — and the project itself already carries
  a strictly more general (PID) twin of this step (`PIDPrimeOrder.lean:113`).
- Mathlib search (Phase 5): **not in mathlib**; all building blocks present
  (`den_dvd_of_is_root`, `leadingCoeff_preΨ`, the Point groups), the assembled result absent.
- Composition (Phase 6): **NOT-COMPOSABLE** (multi-step proof + project-only dependency); K = 1
  internal use, with a more-general duplicate twin.

**Rationale.**
Mathematically this is exactly the right kind of content for mathlib — a load-bearing step of the
Nagell–Lutz theorem, proved the textbook way (division-polynomial leading coefficient + rational
root theorem + a coprime-denominator argument), and mathlib conspicuously lacks Nagell–Lutz entirely
despite owning every primitive. So it is **not** NO-mathlib-has-it (mathlib doesn't have it, and the
fork doesn't change that — the fork only re-supplies the division-polynomial *primitives*), and
**not** NO-composable (the proof is a real multi-step argument with a project-specific dependency,
nowhere near a ≤3-call inline). On those grounds the instinct is YES.

But it does **not** clear a clean YES bucket, for three reasons, each a judgment call only the
maintainer can make. (1) **Packaging** — the natural upstream artifact is a *Nagell–Lutz file*
exposing `prime_order_integrality` (with order-2/4 companions), in which this decl is a private
helper, not a public API lemma; shipping this fragment alone, named
`x_integral_of_odd_prime_torsion_general`, is not how mathlib would carve it. (2) **Generality /
duplication** — the project maintains parallel **General (`ℤ`)** and **PID** tracks, and the PID
track already states the strictly more general form
(`isInteger_of_root_squarefree_leading_coeff` ⟶ `x_isInteger_of_odd_prime_torsion_squarefree`,
`prime_order_integrality_squarefree`); upstream should take the general one, so this `ℤ` copy is
arguably redundant before it ever reaches a PR. (3) **Scope of the PR** — this step is inseparable
from its dependencies (`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`,
`den_ne_prime_of_on_general_curve`, `evalEval_ψ_odd`), so the real decision is "should AINTLIB
upstream its Nagell–Lutz development, and at what generality / on which API surface?", not "is this
one lemma good?". That is a roadmap/taste call, hence BORDERLINE.

Cost is **not** the reason for BORDERLINE here (per the gate) — the reason is genuine packaging +
generality-track + which-form judgment that the skill cannot settle alone.

**Numbered questions for the human (≤5):**
1. Does AINTLIB intend to **upstream the Nagell–Lutz theorem to mathlib** as a unit? If yes, this
   decl goes in as an internal step of that PR (not as a standalone lemma) — confirm that framing.
2. Between the **General (`ℤ`)** and **PID** tracks, should the upstream version be the **PID-general**
   one (`x_isInteger_of_odd_prime_torsion_squarefree` / `prime_order_integrality_squarefree`)?
   If yes, this `ℤ`-specialised copy is **dropped in favour of the twin** before any PR.
3. Is the public face of the eventual PR the *combined* `prime_order_integrality` (x **and** y, all
   small orders), with `x_integral_of_odd_prime_torsion_general` demoted to a `private`/section-local
   helper? (mathlib would likely not want the bare x-only odd-prime fragment as a named API lemma.)
4. Should the upstream statement be phrased against mathlib's existing `WeierstrassCurve` /
   `EllipticCurve` **Point group + `Reduction.IsIntegral` model** API (rather than the project's
   `curveQ`/`Jacobian.Point.fromAffine` scaffolding)? This affects whether the decl as-written is
   PR-ready or needs restating on the mathlib API surface first.
5. Given the bundled dependencies (`evalEval_ψ_*`, `den_ne_prime_*`) and that the project **forks**
   `DivisionPolynomial.*`/`EllipticDivisibilitySequence`, is a Nagell–Lutz contribution on the
   **mathlib roadmap** at all right now, or should this stay AINTLIB-internal for the foreseeable future?

**Next action:** human answers Q1–Q5. If "upstream NL, PID-general, combined statement on the mathlib
Point API" → re-run `/mathlibable` on the *assembled* `prime_order_integrality_squarefree` (PID track)
as the real candidate, treating this fragment as an internal helper. If "stay internal" → no mathlib
action; optionally `/generalise` to deduplicate the General vs PID tracks within AINTLIB.
