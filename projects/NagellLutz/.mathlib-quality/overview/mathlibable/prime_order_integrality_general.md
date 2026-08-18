# /mathlibable report — `LutzNagell.LutzNagellTheorem.prime_order_integrality_general`

## Verdict: BORDERLINE-needs-human

One-line: the **odd-prime full-integrality assembly** of the Nagell–Lutz theorem (absent from
mathlib at any generality). Mathematically YES, but it is an intermediate assembly mathlib would
likely fold into the headline `prime_order_integrality`, and a strictly more general **PID twin**
already exists in-project. The call is packaging + which-track, not mathematical worth.

_Assessment date: 2026-06-21. Mathlib pin: `d90090f` (Lean v4.31.0-rc2), read directly from
`.lake/packages/mathlib`. Local Lean build stale per task brief — reasoned from source; the
declaration elaborates by inspection (qualified name verified from the namespace blocks)._

---

### Baseline (Phase 0)
- lake build:               ~ not run (environment build stale per task note; reasoned from source)
- decl `LutzNagell.LutzNagellTheorem.prime_order_integrality_general`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:149`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Prime-order and order-4 torsion integrality for general Weierstrass
  curves" — if `P ≠ 0` has odd prime order or order 4 on a general integral Weierstrass curve, `P`
  has integral affine coordinates.

Qualified name **VERIFIED** from source: the file opens `namespace LutzNagell` (line 19) then
`namespace LutzNagellTheorem` (line 20), closed by `end LutzNagellTheorem` / `end LutzNagell`
(lines 205–206). Base name `prime_order_integrality_general` (line 149) ⇒ full name
`LutzNagell.LutzNagellTheorem.prime_order_integrality_general`. ✓ (matches the parsed name).

---

### Statement (Phase 1)

`prime_order_integrality_general` states: let `W` be a Weierstrass curve with **integer**
coefficients `aᵢ ∈ ℤ`, and let `P = (x, y)` be a nonsingular rational affine point on the base
change `curveQ W` to `ℚ`. If `p` is an **odd prime** and `p • P = 0` in the (Jacobian) point group
(and `P ≠ 0`), then **both** coordinates are integers: `∃ x₀ : ℤ, x₀ = x` and `∃ y₀ : ℤ, y₀ = y`.

This is the **odd-prime case of the (full, two-coordinate) integrality clause of the Nagell–Lutz
theorem**: a nonzero point of odd prime order on an integral-model elliptic curve has integral
coordinates. It is the assembly that combines the x-coordinate fragment with the y-from-x fragment.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — a Weierstrass curve over `ℤ` (general 5-coefficient model).

Hypotheses (Lean side):
- `hns : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point over `ℚ`.
- `hp : p.Prime`, `hodd : p ≠ 2` — `p` is an odd prime.
- `htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0` — `p`-torsion.
- `_hne : … ≠ 0` — `P ≠ 0` (**unused** in the body; carried for the caller's interface).

Conclusion (math): `x ∈ ℤ ∧ y ∈ ℤ`.
Conclusion (Lean): `(∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`.

Proof shape (source lines 155–157): a **two-call composition of project lemmas** —
`obtain ⟨x₀, hx₀⟩ := x_integral_of_odd_prime_torsion_general W hns hp hodd htors` (the x-half),
then `y_integral_of_x_integral_on_general_curve W ((curveQ_equation_iff …).mp hns.left) hx₀` (the
y-from-x half). Both callees are project lemmas, not mathlib decls. The body never uses `_hne`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline) — not itself a person-named theorem, but the odd-prime *assembly*
of the integrality half of the **Nagell–Lutz** theorem and a primary project goal (it is the
odd-prime branch consumed by `lutz_nagell_integrality_general`, a `## Main results` entry).
Reason: assembly of a person-named theorem ⇒ guaranteed near the literature.

(Literature width is EXHAUSTIVE regardless. Recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def` — one-line check **n/a**. (For the record the body is a 2-line
composition of two non-trivial project lemmas; the *content* lives in the callees, not here. This
"thin assembly over deep callees" shape is the crux of the verdict below — see Phase 6.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

This decl is the odd-prime assembly of the same Nagell–Lutz integrality result whose literature
was swept in full for the two parent fragments (`x_integral_of_odd_prime_torsion_general`,
`y_integral_of_x_integral_on_general_curve`) and the headline (`lutz_nagell_integrality_general`)
during the 2026-06-18 overview pass. The standard form is pinned and unambiguous; the table below
re-confirms it for the assembled odd-prime statement.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "Nagell-Lutz theorem torsion point integral coordinates elliptic curve" | yes | nonzero torsion pt of integral model has `x,y ∈ ℤ` | Wikipedia "Nagell–Lutz theorem"; Silverman AEC VIII.7; Cassels LMSST; Alpoge "Nagell–Lutz, quickly" |
| 2 | WebSearch (mechanism / prime order) | "prime order torsion point both coordinates integral division polynomial rational root" | yes | for `n`-torsion `x.den ∣ leadingCoeff ψₙ`; odd prime ⇒ `x,y ∈ ℤ` | exactly the route used; x then y from the curve equation |
| 3 | WebSearch (named/source/aliases) | "Lutz Nagell integrality points finite order Weierstrass equation y integral from x" | yes | y integral once x integral (root of a monic quadratic over ℤ) | Silverman AEC; Cremona Ch.3; standard "complete the y" step |
| 4 | ChatGPT MCP | "Standard statement & generality of the Nagell–Lutz integrality clause for a point of odd prime order; is the natural unit the full theorem or the per-order fragment?" | n/a | — | `mcp__chatgpt-math__ask_chatgpt_math` flagged possibly-down per task; web channels #1–3 already pin the form unambiguously, so not load-bearing. Recorded n/a. |
| 5 | Local references | grep `.mathlib-quality/references/` for "nagell"/"lutz"/"torsion" | n/a | — | no `references/` directory under the project's `.mathlib-quality/` (only `overview/`). Recorded n/a. |
| 6 | nLab | "Nagell-Lutz theorem" / "division polynomial" | no | — | nLab has no Nagell–Lutz / torsion-integrality page; not a category-theoretic concept. |
| 7 | nCatLab | — | n/a | — | not a categorical concept. |
| 8 | Stacks Project | "elliptic curve torsion integral" | n/a | — | not in Stacks' scope (no explicit elliptic-curve torsion-integrality arithmetic). |
| 9 | MathOverflow / MSE | (covered via #1–#3 result sets) | yes | same NL statement; "complete the y-coordinate via the integral monic in y" | standard textbook lemma; many expository write-ups (REU notes, unizg). |
| 10 | recent arXiv (≤5y) | "Nagell-Lutz division polynomial number field" | yes | arXiv 2509.07524 (NL over imaginary quadratic fields), 1108.3051 (valuations of division polynomials) | confirms classical, named, actively generalised; the ℚ statement is textbook. |

### Literature summary (Phase 3)

Concept identified as: the **odd-prime, two-coordinate case of the integrality half of the
Nagell–Lutz theorem**. The x-coordinate is forced integral by the division-polynomial + rational
root argument (odd prime ⇒ `leadingCoeff(preΨ_p) = p`, and a point on an integral curve cannot have
denominator a prime); the y-coordinate is then integral because it is a root of the **monic**
quadratic `Y² + (a₁x₀+a₃)Y − (x₀³+a₂x₀²+a₄x₀+a₆) ∈ ℤ[Y]`.
Sources agree on the standard form: **yes**. Both halves are textbook (Silverman AEC VIII; Cassels
LMSST; Cremona Ch.3; Alpoge).
Most general standard form: the **full Nagell–Lutz integrality statement** — *every* nonzero torsion
point (any order, both coordinates) on an integral model has integral coordinates (Cassels'
valuation-theoretic proof holds over any Dedekind/PID base / number field). The present decl is the
**odd-prime, base-`ℤ`** slice of that, assembled across both coordinates.
Generality dimensions where the literature varies:
  - torsion order: literature does all orders; here the file splits odd-prime / order-2 / order-4
    (leading-coeff value of `preΨ_n` differs: `n` odd vs `n/2` even, and `4` for `Ψ₂²`).
  - base: classically over `ℚ`; recent arXiv pushes to number fields / PIDs. This decl is over `ℤ`;
    the project's PID track does the general base.
Disagreement with the literature: **none** — a faithful slice of the standard proof.

---

### Generality analysis (Phase 4)

Literature-standard form: full Nagell–Lutz integrality (all torsion orders, both coords, general
Dedekind/PID base).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ` | integer-coeff general Weierstrass model | integral model over a PID / Dedekind domain `R` with `Frac R = K` | **yes** | The project's **PID track** already states exactly this: `prime_order_integrality_squarefree` (`PIDPrimeOrder.lean:202`) over any `[IsPrincipalIdealRing R] [CharZero R]` with a `Squarefree (p:R)` hypothesis. So a strictly more general form **exists in-project**; the `ℤ` form here is its specialisation. |
| 2 | `hp : p.Prime`, `hodd : p ≠ 2` | odd prime order | any torsion order | yes (in principle) | Full NL is for all orders; the file deliberately splits odd-prime / 2 / 4 because the leading coefficient of the relevant division polynomial differs by case. Not accidental over-specialisation. |
| 3 | conclusion: `x ∧ y` integral | both coords, odd-prime case | both coords, all orders | yes | order-2 / order-4 handled by sibling lemmas (`bounded_den_of_order_two_general`, `integrality_of_order_four_general`); `lutz_nagell_integrality_general` assembles all cases. |
| 4 | `_hne : … ≠ 0` | unused hypothesis | (not needed) | n/a | the body never uses `_hne`; it is interface ballast for the caller. A maximally-clean upstream statement would drop it. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the odd-prime, base-`ℤ` slice, with
one redundant hypothesis (`_hne`). Number of weakening opportunities: ~2 substantive (base ring;
order-case) + 1 cosmetic (drop `_hne`). These are **deliberate decomposition**, not accidental
over-specialisation — the "right" mathlib object is the *assembled* `prime_order_integrality` (all
orders) over the *general base*, of which this is the odd-prime ℤ-slice.

Crucially, the project **already carries the strictly more general form** of this very assembly:
`prime_order_integrality_squarefree` (PID track, `PIDPrimeOrder.lean:202`), making this `ℤ` copy the
*less* general of two duplicated tracks.

Proposed restatement: not a single-lemma rewrite. The natural upstream artifact is the **assembled
odd-prime branch over a PID** — which already exists as `prime_order_integrality_squarefree` — folded
into the headline NL theorem. Cost of restatement: **CHEAP** (the general form is already proven;
the ℤ form is recovered by `R := ℤ`, `Squarefree (p:ℤ)` automatic for primes). The dominating
question is packaging (standalone-named assembly vs. private branch of the headline), not cost.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
|  1 | bundled-hyp → typeclass? | no | hypotheses already minimal (`Prime`, `≠ 2`, a torsion equation); nothing to classify. The one move is *dropping* the unused `_hne`. |
|  2 | sequences/metric → filters? | no | purely algebraic; no limits or topology. |
|  3 | construction → universal property? | no | an integrality statement, not a construction. |
|  4 | set+closure → bundled substructure? | no | n/a. |
|  5 | field/vector-space → weaker typeclass? | **yes (mild)** | base `ℤ`/`ℚ` → PID `R` / `Frac R` via `IsFractionRing` + `IsLocalization.IsInteger`. **The project's PID track already realises this** (`prime_order_integrality_squarefree`). |
|  6 | 1-categorical → higher? | no | n/a. |
|  7 | concrete index → general monoid/group? | partial | `p` an odd prime is intrinsic to the leading-coeff value (`= p`); not a free index to generalise. |

Modern idiom available: **yes, mild** — state over a PID rather than `ℤ`, with the integrality
conclusion in mathlib's canonical `IsLocalization.IsInteger R` vocabulary. The downstream benefit
(every integral model, every number field) is real and **already realised in-project**. This pushes
toward "if upstreamed, prefer the PID-general assembly", but — exactly as for the two parent
fragments — the packaging question (standalone-named odd-prime assembly vs. a private branch of the
headline `prime_order_integrality`) dominates, so the verdict is **BORDERLINE** rather than a clean
YES-but-generalise-first. (Real improvement, not abstraction-for-its-own-sake: the PID form composes
with the whole `WeierstrassCurve`-over-a-`CommRing` API and yields number-field torsion corollaries
the ℤ form blocks.)

---

### Mathlib search-status (Phase 5)

Index MCP tools (Loogle / LeanSearch / Lean-Finder) were **not available** in this environment
(only `LSP`, `WebSearch`, and the possibly-down ChatGPT MCP loaded as deferred tools). Substituted
direct source grep over the pinned mathlib (`.lake/packages/mathlib`, rev `d90090f`).

[A] Lean-Finder       n/a — index tool unavailable in env.
[B] Loogle            n/a — index tool unavailable; substituted [D].
[C] LeanSearch        n/a — index tool unavailable; substituted [D].
[D] Grep mathlib src  `grep -rni "nagell" Mathlib/` over the **entire** library → **zero matches**.
                      `grep -rniE "theorem.*(integ|IsInteger).*torsion|torsion.*integ"` over
                      `Mathlib/AlgebraicGeometry/EllipticCurve/**` → **no hit**. No
                      `prime_order`/`x_integral`/`…_general` torsion-integrality decl anywhere.
[E] Name pattern      grep decl heads for `prime_order`/`integrality`/`torsion_general` in mathlib → none.

Searched for both: the user's current form (odd-prime, two-coordinate, base `ℤ`) **and** the
literature-standard form (full Nagell–Lutz / any torsion ⟹ integral, general base). **Neither** is
in mathlib.

What mathlib *does* have (the building blocks — all confirmed present at rev `d90090f`):
- `Mathlib.RingTheory.Polynomial.RationalRoot.den_dvd_of_is_root` (rational root theorem) and
  `isInteger_of_is_root_of_monic` (integral root theorem — used by the **y-half** callee). Present
  at `RationalRoot.lean:89` / `:115`.
- `WeierstrassCurve.preΨ`, `WeierstrassCurve.leadingCoeff_preΨ` (`= if Even n then n/2 else n`),
  `map_preΨ`, `natDegree_preΨ` — `…/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`
  (`leadingCoeff_preΨ` documented at `Degree.lean:34`).
- `WeierstrassCurve` Affine/Jacobian Point group — `…/EllipticCurve/{Affine,Jacobian/*}`.
- `Mathlib.NumberTheory.EllipticDivisibilitySequence` — the EDS / `ψ` recurrence.

Concluded: **not in mathlib** (all available methods exhausted, both the user's form and the
literature-standard form). Mathlib owns every primitive but neither the assembled odd-prime
integrality result nor the Nagell–Lutz theorem.

> NOTE on the fork: the project forks `DivisionPolynomial.*` and `EllipticDivisibilitySequence` into
> `projects/NagellLutz/LutzNagell/`. This decl is **not** a forked-mathlib decl — it is genuinely new
> project content built on top of the (forked) division-polynomial API. The upstream
> `leadingCoeff_preΨ` etc. exist; `prime_order_integrality_general` does not, in any namespace.

---

### Composition check (Phase 6)

#### Call sites (Phase 6.0)

Internal use count: **1** (excluding the declaring file's own declaration line).
External-to-file callers: **0**. External-to-project callers: **0**.

```
grep -rn "prime_order_integrality_general" projects/ --include="*.lean" | grep -v GeneralPrimeOrder.lean
→ projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:72
```

| Caller file:line | Usage pattern |
|------------------|---------------|
| `GeneralMain.lean:72` | `obtain ⟨hx'_int, hy'_int⟩ := prime_order_integrality_general W hns' hp hodd (nsmul_eq_zero_affine_to_jac W …) hne_jac` — inside the private `integrality_of_prime_dvd_order`, which reduces a point whose order is divisible by `p` to a point of exact order `p`. |

Inline-derivation grep: the **PID track** re-derives the same assembly at a more general typeclass
level — `prime_order_integrality_squarefree` (`PIDPrimeOrder.lean:202`), itself composing
`x_isInteger_of_odd_prime_torsion_squarefree` + a y-from-x step. A parallel **duplicated
implementation**, not a consumer. So this is a **single-use internal assembly with a more-general
twin** elsewhere in the project. By the call-sites heuristic (K = 1, twin re-derivation), this leans
away from "standalone API" and toward "internal step of a bigger theorem".

#### Composition attempt (Phase 6a)

Can `prime_order_integrality_general` be derived **from mathlib** in ≤3 chained calls? **No.**

Attempt 1 — chain mathlib's rational/integral root theorems directly. Fails. The decl's own body is
a 2-call composition, but **of two project lemmas**, not mathlib primitives:
- the x-half (`x_integral_of_odd_prime_torsion_general`) is itself a ~30-line argument routing
  through the project's torsion→division-polynomial bridge
  (`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`), `evalEval_ψ_odd`, `map_preΨ`/`eval_map`, the
  rational root theorem, `leadingCoeff_preΨ`, and the project-only `den_ne_prime_of_on_general_curve`
  (a point on an integral curve cannot have denominator a prime — proved via the curve equation in
  `GeneralDenominators.lean`). Mathlib has no analogue of that last lemma.
- the y-half (`y_integral_of_x_integral_on_general_curve`) builds the monic quadratic in `Y` and
  calls mathlib's `isInteger_of_is_root_of_monic` — that *single* step is mathlib-composable, but it
  is only the second of two, and it depends on the x-half's output.

Attempt 2 — accept the body as the composition and ask whether the two callees are mathlib. They are
**not**: both are project decls (`GeneralPrimeOrder.lean:80` and `:31`) resting on ~880 lines of
`General*` infrastructure plus the forked division-polynomial/EDS development. Substituting them does
not reduce to ≤3 mathlib calls; it expands into the full proof.

Conclusion: **NOT-COMPOSABLE** from mathlib. The thin 2-line body is composition *of project
lemmas*, and those lemmas are genuine multi-step arguments with project-only dependencies, not
mathlib primitives. (Contrast a true NO-composable: there the ≤3 calls are *all mathlib*. Here only
the y-half's final call is.)

---

## Verdict: `LutzNagell.LutzNagellTheorem.prime_order_integrality_general`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the **odd-prime, two-coordinate slice of the integrality half of the
  Nagell–Lutz theorem** — a classical, person-named result. Not in mathlib in any form
  (`grep -rni nagell Mathlib/` = 0 hits); all building blocks present.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — odd-prime, base `ℤ`, plus a
  redundant `_hne`; the project already carries a strictly more general **PID twin**
  (`prime_order_integrality_squarefree`).
- Mathlib search (Phase 5): **not in mathlib** at any generality; every primitive present, the
  assembled result and Nagell–Lutz itself absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the 2-line body composes two
  non-trivial *project* lemmas resting on ~880 lines of project infra + a project-only
  denominator lemma); K = 1 internal use, with a more-general duplicate twin.

**Rationale.**
Mathematically this is exactly the right kind of content for mathlib: it is the odd-prime branch of
the integrality conclusion of the **Nagell–Lutz theorem**, proved the textbook way (x integral via
the division-polynomial leading coefficient + rational root theorem + the coprime-denominator
argument; y integral as the root of a monic quadratic over ℤ), and mathlib conspicuously lacks
Nagell–Lutz **entirely** despite owning every primitive. So it is **not** NO-mathlib-has-it (mathlib
doesn't), and **not** NO-composable-from-mathlib: although the *body* is two lines, the composition
is of two deep **project** lemmas, not of mathlib primitives — inlining it at the one call site would
paste the full ~30-line x-half (with its project-only `den_ne_prime_of_on_general_curve` dependency),
which is precisely what NO-composable is meant to exclude. On those grounds the instinct is YES.

It does **not** clear a clean YES bucket for two judgment-call reasons the maintainer must settle —
the same two that put both of its parent fragments and the headline theorem in the human-decision
lane. (1) **Packaging / grain.** `prime_order_integrality_general` is an *intermediate assembly*: the
odd-prime branch consumed by the headline `lutz_nagell_integrality_general` (itself
YES-but-generalise-first). Mathlib would most likely expose a single `prime_order_integrality`
(merging x, y, and quite possibly the order-2/4 branches) and demote this odd-prime-only assembly to
a `private`/section-local step, dropping the unused `_hne` hypothesis. Shipping it standalone under
this name is not how mathlib would carve the API. (2) **Generality track.** The project maintains
parallel **General (`ℤ`)** and **PID** tracks, and the PID track already states the strictly more
general form of this exact assembly (`prime_order_integrality_squarefree`, `PIDPrimeOrder.lean:202`);
per mathlib's iron rule the upstreaming unit should be the PID/number-field statement, so this `ℤ`
copy is arguably redundant before it ever reaches a PR. Both points are roadmap/taste calls — "should
AINTLIB upstream its Nagell–Lutz development, at what grain, and from which track?" — not a
mathematical-worth call, and (per the gate) **not** a cost-driven downgrade: the general form is
already proven, so generalising is free. Hence BORDERLINE.

This verdict is consistent with the sibling assessments: the x-half
(`x_integral_of_odd_prime_torsion_general`) is BORDERLINE for the same reasons, the y-half
(`y_integral_of_x_integral_on_general_curve`) is NO-composable, and the headline assembly
(`lutz_nagell_integrality_general`) is YES-but-generalise-first. `prime_order_integrality_general`
sits one level below the headline and is governed by the same packaging + which-track judgment.

**Numbered questions for the human (≤5):**
1. Does AINTLIB intend to **upstream the Nagell–Lutz theorem to mathlib** as a unit? If yes, this
   odd-prime assembly goes in as an internal step of that PR, not as a standalone named lemma —
   confirm that framing.
2. Should the upstream version come from the **PID track** (`prime_order_integrality_squarefree`,
   the strictly more general form already proven in-project) rather than this `ℤ`-specialised copy?
   If yes, this decl is **dropped in favour of the twin** before any PR (ℚ recovered as a corollary).
3. Is the public face of the eventual PR a single `prime_order_integrality` merging the **x and y**
   coordinates (and probably the **order-2 / order-4** branches too), with the bare odd-prime-only
   assembly demoted to a `private`/section-local helper? (mathlib would likely not want the
   odd-prime-only two-coordinate slice as a named API lemma.) And should the unused `_hne` be dropped?
4. Should the upstream statement be phrased against mathlib's existing `WeierstrassCurve` /
   `EllipticCurve` **Point group + `Reduction.IsIntegral` model** API rather than the project's
   `curveQ` / `Jacobian.Point.fromAffine` scaffolding? This decides whether the decl is PR-ready or
   needs restating on the mathlib surface first.
5. Given the bundled dependencies (`x_integral_of_odd_prime_torsion_general`,
   `y_integral_of_x_integral_on_general_curve`, the torsion→ψ bridge, `den_ne_prime_of_on_general_curve`),
   is a Nagell–Lutz contribution on the **mathlib roadmap** at all right now, or should this stay
   AINTLIB-internal for the foreseeable future?

**Next action:** human answers Q1–Q5. If "upstream NL, PID-general, single combined
`prime_order_integrality` on the mathlib Point API" → the real candidate is the **headline**
`lutz_nagell_integrality_*` (PID track) — run `/mathlibable` / `/generalise` there and treat this
odd-prime assembly as an internal helper folded into the combined statement. If "stay internal" → no
mathlib action; optionally `/generalise` to deduplicate the General (`ℤ`) vs PID tracks within
AINTLIB (this `ℤ` copy vs. `prime_order_integrality_squarefree`).

---

## Next step

Human answers Q1–Q5. If the intent is to upstream Nagell–Lutz at PID generality with a single
combined `prime_order_integrality`, re-run the assessment on the **headline** assembly and demote
this odd-prime decl to an internal helper; otherwise keep it AINTLIB-internal and consider
`/generalise` to merge the General/PID duplicate tracks.
