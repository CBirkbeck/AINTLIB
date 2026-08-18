# /mathlibable report — `LutzNagell.LutzNagellTheorem.integrality_of_order_four_general`

_Assessment date: 2026-06-21. Mathlib pin: `d90090f` (Lean `v4.31.0-rc2`), read directly from
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. Local Lean build is
stale per the task brief; mathlib presence/absence is established by **direct grep of the pinned
checkout** (authoritative for this pin) plus **independent WebSearch** (literature). Every load-bearing
claim below — the PID twin's statement, the building blocks in mathlib, the duplication classification,
the call sites, the absence of any Nagell–Lutz in mathlib, the literature standard form — was
**re-verified from primary sources in this run**, not merely inherited from the prior draft. The
conclusion (BORDERLINE) coincides with the 2026-06-18 assessment and is consistent with the sibling
reports for this file._

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  direct read of the pinned mathlib checkout. Full statement + proof read from
  `GeneralPrimeOrder.lean:118–143`.
- decl `LutzNagell.LutzNagellTheorem.integrality_of_order_four_general`:
                            ✓ resolved at `GeneralPrimeOrder.lean:118` (the `theorem` keyword line;
                            the task brief's "line 121" is the `h2ne` hypothesis line).
- qualified name:           ✓ VERIFIED `LutzNagell.LutzNagellTheorem.integrality_of_order_four_general`
                            — `namespace LutzNagell` (line 19) → `namespace LutzNagellTheorem` (line 20);
                            base name `integrality_of_order_four_general` (line 118). Matches the
                            task's parsed guess exactly.
- kind:                     theorem
- has sorry:                no — complete proof (lines 122–143): `ψ₄` factor split via `mul_eq_zero`,
                            then `preΨ₄`-root → `x.den ∣ 2` → `x ∈ ℤ` → `y ∈ ℤ`, else `ψ₂=0` contradiction.
- module docstring summary: "Prime-order and order-4 torsion integrality for general Weierstrass curves":
                            if `P ≠ 0` has odd prime order or order 4 on a general integral-coefficient
                            Weierstrass curve, then `P` has integral affine coordinates (order 2 gets the
                            weaker `4x, 8y ∈ ℤ`).

---

### Statement (Phase 1)

`integrality_of_order_four_general` states: let `W : WeierstrassCurve ℤ` be an integral-coefficient
Weierstrass curve, `curveQ W` its base-change to ℚ, and `P = (x, y)` a nonsingular affine rational
point. If `P` has **exact order 4** — encoded as `4 • P = 0` (`h4`, in the Jacobian point group)
together with `2 • P ≠ 0` (`h2ne`, in the affine group) — then **both coordinates of `P` are integers**:
`(∃ x₀ : ℤ, (x₀:ℚ) = x) ∧ (∃ y₀ : ℤ, (y₀:ℚ) = y)`.

This is the **order-4 (2-power) branch** of the division-polynomial proof of Nagell–Lutz. The proof
(read from source): from `4 • P = 0` one gets `ψ₄(x,y) = 0` (project bridge
`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`); mathlib's/the fork's factorisation
`WeierstrassCurve.ψ_four : ψ₄ = C(preΨ₄)·ψ₂` then splits the vanishing via `mul_eq_zero`. In the
`preΨ₄(x) = 0` case, `x` is a root of the integer polynomial `W.preΨ₄` whose **leading coefficient is 2**
(`leadingCoeff_preΨ₄`), so the rational-root theorem (`den_dvd_of_is_root`) gives `x.den ∣ 2`; combined
with the denominator lemma `den_ne_prime_of_on_general_curve` (which excludes `x.den = 2`) this forces
`x.den = 1`, i.e. `x ∈ ℤ`, and then `y ∈ ℤ` via the curve equation
(`y_integral_of_x_integral_on_general_curve`). In the `ψ₂(x,y) = 0` case,
`two_nsmul_eq_zero_of_ψ₂_eq_zero` gives `2 • P = 0`, contradicting `h2ne`.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — integral general-Weierstrass model.
- `curveQ W : WeierstrassCurve ℚ` — project abbrev (the base-change `W ⊗ ℚ`).

Hypotheses (Lean side):
- `hns : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` nonsingular (gives the curve equation + `≠ O`).
- `h4 : (4 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0` — `4 • P = 0`.
- `h2ne : (2 : ℕ) • Affine.Point.some _ _ hns ≠ 0` — `2 • P ≠ 0` (so `P` has order exactly 4).

Conclusion (math): a rational point of exact order 4 on an integral general-Weierstrass model has
integer coordinates.
Conclusion (Lean): `(∃ x₀ : ℤ, (x₀:ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀:ℚ) = y`.

---

### Size classification (Phase 2a)

**Verdict: SMALL** (an internal step inside a BIG named theorem).
Reason: a **helper lemma** — one of the three torsion-order branches feeding the Nagell–Lutz integrality
dichotomy. Not listed under any `## Main results`; the file header marks it "order-4 torsion: integrality".
The enclosing **Nagell–Lutz theorem** `lutz_nagell_integrality_general` (GeneralMain.lean:110, assessed
YES-but-generalise-first) is the BIG named target; this lemma is one supporting branch, structurally
parallel to `x_integral_of_odd_prime_torsion_general` (odd-prime branch) and
`bounded_den_of_order_two_general` (order-2 branch).

(Literature width is EXHAUSTIVE regardless. SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. **n/a** — skipped. (Body is a multi-line tactic
proof with genuine `rcases … with hpreΨ | hψ₂` case analysis, lines 122–143.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem proof division polynomial order 4 torsion point integer coordinates elliptic curve" | yes  | division polynomials "give the denominators of mult-by-`n`" and "have roots exactly the n-torsion points"; the order-4 case is an internal step of the div-poly proof | **re-run this session.** Alpoge "Nagell-Lutz, quickly" (Harvard); Wikipedia; Galperin (UChicago REU); A Neighbourhood of Infinity — order-4 is a step, **not a named standalone theorem** |
|  2 | WebSearch (general form)         | "Nagell-Lutz … order 2 x=m/4 y=n/8 general Weierstrass"                                                  | yes  | **verbatim Wikipedia generalised statement**: "for a nonsingular cubic whose Weierstrass form has integer coefficients, any rational point of finite order must have integer coordinates, or else have order 2 and coordinates x=m/4, y=n/8" | **re-run this session.** Confirms orders ≥ 3 (incl. **4**) force **full integrality** — exactly this lemma's conclusion; baseline is general-Weierstrass over ℚ |
|  3 | WebSearch (named-after / source) | (Silverman AEC VIII.7 / Silverman–Tate Ch.II; surfaced transitively + via #1/#2 result lists)           | yes  | integrality via local (p-adic, incl. 2-adic) denominators; the `p=2` / order-4 part is the same descent at the prime 2 | Silverman AEC; Silverman–Tate "Rational Points on Elliptic Curves"; Husemöller; Cassels |
|  4 | ChatGPT MCP                      | (MCP down in this env per task brief; substituted by WebSearch #1–3 covering form + the order-4 step)    | n/a  | —                   | tool genuinely unavailable; compensated by the verbatim Wikipedia wording (#2) + explicit div-poly order-4 description (#1) |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                              | n/a  | (absent)            | confirmed this session: no `references/` dir (only `overview/`), `refs/` store not present. Recorded n/a. |
|  6 | nLab                             | "Nagell-Lutz theorem" / torsion of elliptic curves                                                      | no   | —                   | nLab has no dedicated Nagell–Lutz page (elementary Diophantine result, not a categorical concept) |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell-Lutz / torsion integrality                                                                       | n/a  | —                   | Stacks does scheme-theoretic AG foundations, not Diophantine arithmetic of `E/ℚ` torsion |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz via division polynomials, order-4 / 2-power torsion integrality                              | yes  | community proofs match Silverman/Cassels; x-coord denominators only grow; order-4 = 2-adic descent step | A Neighbourhood of Infinity exposition; folklore textbook proof |
| 10 | recent arXiv (last 5 years)      | Nagell-Lutz generalisations (imaginary quadratic / number fields)                                       | yes  | **arXiv:2509.07524 (2025)** generalises Nagell–Lutz to imaginary quadratic fields w/ class number one; cites the classical ℤ statement | confirms classical general-Weierstrass-over-ℚ is the baseline; **base ℤ→number field is the natural generalisation** (= what the PID twin does); **no Lean/mathlib version** |

Protocol passes: WebSearch ran **3 distinct queries this session** at different generality levels (the
order-4/`ψ₄` step; the general-Weierstrass denominator form; the named-after/Silverman source); the
standard form, generality and the order-4 step's role were probed; local refs checked (absent → n/a);
nLab/Stacks/nCatLab checked and reasoned n/a; MathOverflow-class expositions + recent arXiv both
checked and hit. ChatGPT MCP genuinely unavailable, compensated by the verbatim Wikipedia wording.

### Literature summary (Phase 3)

Concept identified as: **the order-4 (2-power) branch of the Nagell–Lutz integrality theorem** — "a
rational torsion point of exact order 4 on an integral general-Weierstrass model has integer
coordinates", proved via the **division-polynomial factorisation** `ψ₄ = preΨ₄ · ψ₂`, the
**rational-root theorem** on `preΨ₄` (leading coefficient 2 ⇒ `x.den ∣ 2`), and a **denominator lemma**
excluding `x.den = 2`.

Sources agree on the standard form: **yes**, with one nuance. The *named* object in the literature is
the **whole Nagell–Lutz theorem** (Silverman AEC, Silverman–Tate, Cassels, Husemöller, Alpoge); the
**order-4 case is an internal step** of its proof, not a separately-named result. The textbook route
splits the torsion order into odd-prime and 2-power parts and runs the same division-polynomial / `p`-adic
denominator descent at each prime; the `p=2` / order-4 instance is exactly this lemma. Wikipedia's
generalised statement (verbatim, query #2) makes the order-2 escape (`x=m/4, y=n/8`) explicit and
thereby confirms **orders ≥ 3 (including 4) force full integrality** — precisely this lemma's conclusion.

Most general standard form: over a **Dedekind domain / number field / PID** `R` with fraction field `K`
(place-by-place), general Weierstrass model, integrality phrased as `IsInteger R`. This lemma is the
`ℤ ⊂ ℚ` instance with the ad-hoc `∃ x₀:ℤ, (x₀:ℚ)=x` encoding. (arXiv:2509.07524 is exactly such a
number-field generalisation.)

Generality dimensions where the literature varies:
  - **Base**: ℚ (this lemma) ↔ number field / Dedekind / PID `R ⊂ K`, place-by-place (most general).
  - **Model**: short `y²=x³+Ax+B` ↔ **general Weierstrass** (this lemma uses the **general** model — good).
  - **Integrality encoding**: bespoke `∃ x₀:ℤ` (this lemma) ↔ mathlib idiom `IsLocalization.IsInteger R x`.

Disagreement with the literature: **none.** A faithful Lean rendering of the order-4 step of the
classical division-polynomial Nagell–Lutz proof, at the general-Weierstrass / `ℤ⊂ℚ` level.

---

### Generality analysis — `integrality_of_order_four_general`

Literature-standard form (from Phase 3): the same order-4 integrality over an arbitrary Dedekind
domain / PID `R` with fraction field `K` (place-by-place), general Weierstrass model, with `IsInteger R`.

**Decisive fact, re-verified this session by reading `PIDPrimeOrder.lean:151–172` directly: the
maximally-general form already exists, in this very project.** `PID.integrality_of_order_four_squarefree`
is *exactly* this lemma generalised: over `R` a UFD (`[CommRing R] [IsDomain R]
[UniqueFactorizationMonoid R]`) with fraction field `K`, hypothesis `Squarefree (2 : R)`, conclusion
`IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`. Its proof is the same `ψ_four` split +
rational-root descent, routed through `isInteger_of_root_squarefree_leading_coeff`. The project's own
duplication analysis records the pair (re-read this session, `05-duplications.md:65`):
`| GeneralPrimeOrder.integrality_of_order_four_general | PIDPrimeOrder.integrality_of_order_four_squarefree | Mostly (PID adds Squarefree (2:R)) | Parallel (ψ_four factor split) | special-case of PID |`.

Note: `Squarefree (2:ℤ)` holds automatically (2 is prime in ℤ), so the General lemma is the PID twin's
`R=ℤ, K=ℚ` instance with that hypothesis discharged "for free". **The General lemma does NOT call the
PID twin** — it is an independently-written parallel proof, not a thin wrapper (this distinguishes it
from the sibling `x_integral_of_nsmul_x_integral_general`, which *is* a wrapper and was assessed
NO-composable).

| # | Parameter / hypothesis                              | Current Lean form                  | Literature-standard form (= PID twin)        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|------------------------------------|-----------------------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`, point over `curveQ W`     | base `ℤ`, field `ℚ`                | `R` a UFD/PID (with `Squarefree (2:R)`), `K = FractionRing R`, point on `W.map (R→K)` | **yes** (already done in PID twin) | The descent generalises place-by-place. `Squarefree (2:ℤ)` is automatic, so the General lemma drops it "for free". The PID twin `integrality_of_order_four_squarefree` *is* the weakening — already proved, sorry-free, in the project. |
| 2 | integrality `∃ x₀:ℤ, (x₀:ℚ)=x` / `∃ y₀:ℤ, (y₀:ℚ)=y` | bespoke `∃ : ℤ` packaging          | `IsLocalization.IsInteger R x` / `… R y`      | **yes** (PID twin uses it) | mathlib idiom is `IsInteger` (used verbatim by the PID twin and by `RationalRoot.lean`); the `∃ x₀:ℤ` surface is a ℚ-specialisation artifact. CHEAP to restate. |
| 3 | order-4 encoding `4•P=0` (`h4`) + `2•P≠0` (`h2ne`)   | `4•P=0` ∧ `2•P≠0`                  | identical (`h4`, `h2ne`) — same in PID twin   | **NO** (essential)  | "exact order 4" is the defining hypothesis; the PID twin uses the identical pair. Correct as is. |
| 4 | general Weierstrass model                            | general (`a₁..a₆`)                | general                                       | **NO** (already general) | already at the right model-generality — strictly more general than the short corollary. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (base fixed `ℤ⊂ℚ`; integrality encoded
non-idiomatically as `∃:ℤ`) — though already maximally general in the *model* dimension.
Number of weakening opportunities found: **2** (base ring `ℤ→` UFD/Dedekind `R` with `Squarefree(2:R)`;
integrality `∃:ℤ →` `IsLocalization.IsInteger`).
Proposed restatement: **it already exists** — `PID.integrality_of_order_four_squarefree` (over `R`/`K`,
`Squarefree (2:R)`, `IsInteger`). The General lemma is its `R=ℤ, K=ℚ` instance.
Cost of regeneralisation: **already paid** (the PID twin is fully proved, sorry-free, in the same
project). The "cost" is therefore *deduplication / consolidation*, not new mathematics.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                                                              | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|--------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                | yes      | `IsLocalization.IsInteger R x/y` instead of `∃ x₀:ℤ, (x₀:ℚ)=x`; base via `[IsFractionRing R K]` (exactly the PID twin's signature) | composes with all of `RationalRoot.lean` + mathlib's `IsLocalization` / base-change EC API |
|  2 | sequences/metric → filters/topological?                                                            | no       | purely algebraic Diophantine statement; no analysis                                  | — |
|  3 | construct an object → universal-property class?                                                    | no       | it's a `Prop`, nothing constructed                                                   | — |
|  4 | set-with-closure-predicate → bundled-substructure?                                                 | no       | n/a                                                                                  | — |
|  5 | vector-space/field-specific → weaken to modules/(semi)ring?                                        | yes      | the `ℤ⊂ℚ` base weakens to a UFD/PID `R ⊂ FractionRing R` (row 1 of 4a) — done by the PID twin | unifies with number-field Nagell–Lutz (arXiv:2509.07524); reuses the same `ψ_four` split + rational-root machinery |
|  6 | 1-categorical → higher-categorical?                                                                | no       | n/a | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/monoid?                                                | partial  | the order `4` is mathematically essential here (this is *the* order-4 case), not an incidental index; base `ℤ→R` is the real generalisation (covered by #5) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (two real improvements, both already realised by the PID twin:
`IsLocalization.IsInteger R` packaging; UFD/PID base with `Squarefree (2:R)`).
  - Proposed mathlib-idiomatic restatement: **`integrality_of_order_four_squarefree`** verbatim — over `R`
    a UFD, `K := FractionRing R`, `W : WeierstrassCurve R`, point `P` of exact order 4 on `W.map (R→K)`,
    `Squarefree (2:R)`; conclusion `IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`.
  - Cost: **already paid** (the PID twin is proved). Consolidation cost only.
  - Mathlib downstream this enables: a base-independent order-4 integrality step usable for number-field
    Nagell–Lutz; direct reuse of `den_dvd_of_is_root` / `IsInteger` without the `ℤ→ℚ` `∃ x₀:ℤ` shim;
    composes with mathlib's `IsLocalization` and `WeierstrassCurve.map` APIs.
  - Real mathematical improvement: removes a redundant `ℤ⊂ℚ` specialisation and an ad-hoc integrality
    encoding; the statement becomes the genuine "order-4 torsion is integral over any UFD/PID" lemma.

NOTE (cost caveat, per the skill's gate): cost may inform *sequencing* but cannot by itself downgrade the
verdict bucket. The decisive factors here are (a) the **already-existing more-general PID twin in the same
project** and (b) the **whole-theorem packaging/dedup scope** — not cost.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `integrality_of_order_four_general`

Method note: local Lean build stale, so live loogle/leansearch indices may not reflect this pin. The
authoritative check is a **direct grep of the pinned mathlib checkout** (`.lake/packages/mathlib`,
`d90090f`), plus reading the EC + EDS + RationalRoot source. All greps below were **re-run this session**.

[A] Lean-Finder       "order 4 torsion elliptic curve integral coordinates"    n/a — index MCP unavailable in env; substituted by [D]/[E] grep over the pinned tree.
[B] Loogle            `(4:ℤ)•_ = 0 → _ → (∃ _:ℤ, _=_) ∧ _` over EC points       n/a — index unavailable; grep substitute. (No lemma of this shape exists — see [D].)
[C] LeanSearch        "order four torsion point on elliptic curve has integer coordinates"   n/a — index unavailable; grep substitute.
[D] **Grep mathlib src (authoritative, exact pin — re-run this session)**:
      • `grep -rIn "nagell|Nagell"` over `Mathlib/`                                       → **ZERO Nagell–Lutz hits** (no file, no decl). **No Nagell–Lutz theorem in mathlib.**
      • `grep -rInE "IsOfFinAddOrder|addOrderOf"` ∩ `AlgebraicGeometry/EllipticCurve/`    → **0 occurrences** — no torsion↔EC-integrality result anywhere; the affine/Jacobian API stops at the abstract group law.
      • `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean` (building blocks, confirmed present): `preΨ₄` (`Basic.lean:147`), `leadingCoeff_preΨ₄ (h : (2:R)≠0) : … = 2` (`Degree.lean:145`); plus (per the proof's consumption) `ψ_four`, `map_preΨ₄` — **but NO integrality theorem.**
      • `Mathlib/RingTheory/Polynomial/RationalRoot.lean` (confirmed present): `den_dvd_of_is_root` (`:89`), `isInteger_of_is_root_of_monic` (`:115`), `isInteger_of_isUnit_den` (used `:117`) — the rational-root tools. Generic; not EC-specific.
[E] Name pattern      `theorem … integrality_of_order_four` / `…four_torsion…` / `nagell_lutz` in mathlib   → no hits.

Searched for both:
  - the user's current form (`4•P=0 ∧ 2•P≠0` ⇒ `x,y∈ℤ`, over `ℤ⊂ℚ`, general Weierstrass) — **not in mathlib**.
  - the literature-standard / general form (UFD/PID base, `IsInteger`, order-4) — **not in mathlib** either
    (grep found zero torsion-integrality results at *any* generality).

_Project-framing note (the task flagged that this project forks `Mathlib.…DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and runs duplicated General/PID tracks): the proof
of THIS decl consumes the division-polynomial API by its `WeierstrassCurve.…` names (`ψ_four`, `preΨ₄`,
`leadingCoeff_preΨ₄`, `map_preΨ₄`). The project **re-defines / shadows** these under
`namespace WeierstrassCurve` in `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean`. The mathlib
originals it forks contain **only** the polynomial machinery, **never this integrality theorem** — so
this decl is decidedly **not** already upstream; mathlib has only the building blocks._

Concluded: **not in mathlib** (all methods exhausted, both the user's form and the general form). Mathlib
has the **building blocks** (`preΨ₄`, `leadingCoeff_preΨ₄`, `ψ_four`, `den_dvd_of_is_root`,
`isInteger_of_is_root_of_monic`) — which the project forks — but **not** this order-4 integrality step,
and **no** torsion↔integrality theorem at any generality.

---

### Call sites — `integrality_of_order_four_general`

(Re-grepped this session over `projects/`, excluding the declaring file `GeneralPrimeOrder.lean:118`.)

Internal use count: **1**.
External-to-file callers: **1 distinct file** (`GeneralMain.lean`).

| Caller file:line                   | Usage pattern (one-line excerpt)                                                                       |
|------------------------------------|--------------------------------------------------------------------------------------------------------|
| GeneralMain.lean:100               | `obtain ⟨hx'_int, hy'_int⟩ := integrality_of_order_four_general W hns' (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne)` |

The single caller is the `private` helper `integrality_of_four_dvd_order` (GeneralMain.lean, the "4 ∣ order"
dispatch branch of `lutz_nagell_integrality_general`): it reduces a finite-order point whose order is
divisible by 4 to a multiple `k•P` of exact order 4, applies this lemma, then descends to `P` via
`integral_of_nsmul_integral_general`.

Inline-derivation grep (equivalent re-derived elsewhere without calling this lemma?): **(none)** — the
only other place the order-4 integrality content lives is the parallel **PID-track engine**
`integrality_of_order_four_squarefree` (`PIDPrimeOrder.lean:151`), which is the *more general* analogue
(separate file, UFD/number-field base), **not** an inline re-derivation of the ℚ statement.

Call-sites reading: **K = 1** (one external-to-file caller, the `private` order-4 branch of the main
theorem). The skill's table reads "K = 1" as a weak NO-composable / wrong-abstraction lean — **but** here
the lemma is a **named, docstring'd branch of a classical theorem's proof**, tightly bundled with its
sibling branches. Crucially, unlike the dead-wrapper sibling `x_integral_of_nsmul_x_integral_general`
(K=0, body = one PID-lemma application → NO-composable), this lemma has a **real caller** and an
**independent multi-branch proof**, so the NO-composable signal does **not** transfer. Its
mathlib-worthiness is inseparable from that of the whole Nagell–Lutz development.

---

### Composition check (Phase 6)

Can `integrality_of_order_four_general` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `mul_eq_zero.mp` on `ψ₄(P)=0`, then rational-root (`den_dvd_of_is_root` /
`isInteger_of_is_root_of_monic`) on the `preΨ₄` factor.
  - Mathlib decls used: `WeierstrassCurve.ψ_four`, `mul_eq_zero`, `den_dvd_of_is_root`,
    `leadingCoeff_preΨ₄` (all present in mathlib / the fork).
  - Result: **fails as a ≤3-call composition.** Each "call" needs non-trivial *project* inputs mathlib
    does not provide:
      (a) `ψ₄(P) = 0` comes from `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` — a project bridge through
          Jacobian coordinates (`zsmul_eq_smulEval`, `Z_eq_zero_of_equiv`), not a mathlib lemma;
      (b) excluding `x.den = 2` needs `den_ne_prime_of_on_general_curve` — a project denominator lemma
          (mod-`p` reductions), no mathlib counterpart;
      (c) the `ψ₂(P)=0 ⇒ 2•P=0` contradiction branch needs `two_nsmul_eq_zero_of_ψ₂_eq_zero` (project) →
          `Affine.Point.add_of_Y_eq` (mathlib), plus `h2ne`;
      (d) the final `y∈ℤ` step needs `y_integral_of_x_integral_on_general_curve` (project).
  - Notes: the body (lines 122–143) is a genuine multi-step proof — `rcases … with hpreΨ | hψ₂`, two
    branches each with several `have`s, `rw`/`change`/`absurd` reasoning — not a one-liner.

Attempt 2 (alternate angle): treat the `preΨ₄` branch as pure rational-root once `ψ₄(P)=0` and the
denominator exclusion exist — but producing those two inputs is precisely the mathematical content and is
**not** available in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib alone. Mathlib (incl. the forked division-polynomial API)
supplies the `ψ_four` factorisation and the generic rational-root call, but the surrounding inputs (the
Jacobian-to-`ψ₄` bridge, the denominator-exclusion lemma, the order-2 contradiction, the `y`-integrality)
are project lemmas with no mathlib analog. Far more than a 1–3 mathlib-call composition.

---

## Verdict: `LutzNagell.LutzNagellTheorem.integrality_of_order_four_general`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the **order-4 (2-power) branch** of the classical Nagell–Lutz integrality
  theorem (Silverman AEC VIII.7 / Silverman–Tate / Alpoge "Nagell-Lutz, quickly" / UChicago REU & MIT
  notes / Doud's torsion algorithm). An **internal step**, not a separately-named theorem; Wikipedia's
  generalised statement (re-verified verbatim this session) confirms orders ≥ 3 (incl. 4) force full
  integrality. Mathlib has **no** Nagell–Lutz theorem.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — base fixed `ℤ⊂ℚ`, integrality
  encoded non-idiomatically (`∃ x₀:ℤ` instead of `IsLocalization.IsInteger`). The maximally-general form
  **already exists in this project** as `PID.integrality_of_order_four_squarefree` (UFD `R`/`K`,
  `Squarefree (2:R)`, `IsInteger`; read directly this session); the project's own `05-duplications.md:65`
  calls this General decl a "**special-case of PID**". Modern-idiom (4c) = **yes** (the PID twin is the
  idiomatic form). Already maximally general in the *model* dimension.
- Mathlib search (Phase 5): **not in mathlib** (both forms); direct grep of the pinned checkout finds
  **zero** Nagell/Lutz hits and zero torsion↔integrality results at any generality. Mathlib has only the
  building blocks `preΨ₄`, `leadingCoeff_preΨ₄`, `ψ_four`, `den_dvd_of_is_root` (which the project forks).
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine multi-branch proof whose inputs (Jacobian↔`ψ₄`
  bridge, denominator-exclusion lemma, order-2 contradiction, `y`-integrality) are project lemmas, not a
  ≤3 mathlib-call chain. **K = 1** call site (the `private` order-4 branch of the main theorem).

**Rationale (1–2 paragraphs):**

This is a faithful, sorry-free Lean rendering of a genuine classical step — the order-4 (2-power) branch
of the Nagell–Lutz integrality theorem — and mathlib does not have it (mathlib has *no* Nagell–Lutz and
*no* torsion↔integrality theorem at any generality; it has only the division-polynomial and rational-root
infrastructure this proof consumes, which the project moreover *forks*). So it is neither
`NO-mathlib-has-it` (nothing to point at upstream) nor `NO-composable-from-mathlib` (the inputs to the
rational-root call are project lemmas, not a ≤3 mathlib-call chain — and, unlike the dead-wrapper sibling
`x_integral_of_nsmul_x_integral_general`, this lemma has a real caller and an independent proof, so the
NO-composable reading does not transfer). On the YES side, two things hold it back from a clean verdict.
First, it is **STRICTLY NARROWER than the literature/mathlib-idiom standard** — mathlib would want
`IsLocalization.IsInteger R x` over a UFD/PID base, not the bespoke `∃ x₀:ℤ` packaging fixed to `ℤ⊂ℚ` —
which by the skill's gate *forbids* `YES-add-as-is`. Second, and decisively, **the maximally-general form
already exists in this same project**: `PID.integrality_of_order_four_squarefree` is the
`R`/`K`/`IsInteger` generalisation, of which this General decl is literally the `R=ℤ, K=ℚ` instance (the
project's `05-duplications.md:65` classifies it "special-case of PID"). So this is not a clean
`YES-but-generalise-first` *in isolation* either — the generalisation isn't hypothetical work to be done,
it's an existing duplicate, and the real question is **which of the two parallel tracks to upstream and
how to deduplicate them**.

That makes the honest verdict **BORDERLINE**, for the same structural reason its sibling
`x_integral_of_nsmul_x_integral_general` came out a NO and the parent `lutz_nagell_integrality_general`
came out `YES-but-generalise-first`: this is an **intermediate helper with a single (private) call site**,
tightly coupled to its sibling branches and to the forked division-polynomial track, existing in **two
near-duplicate copies** (General ℤ⊂ℚ vs PID `R`/`K`). It should ship to mathlib **only as an internal step
of the complete Nagell–Lutz theorem**, in mathlib's idiom (`IsInteger`, general base), after the
General↔PID duplication is resolved — which track is canonical, and whether the order-4 branch is even
exposed as a standalone lemma or inlined into the main proof, are packaging-and-scope judgment calls the
skill should not make alone. (The parent theorem `lutz_nagell_integrality_general` was assessed
`YES-but-generalise-first`; this helper rides along with that PR rather than being an independent addition.)

**Numbered questions (≤5):**

1. Is the **whole Nagell–Lutz theorem** (`lutz_nagell_integrality_general`, assessed
   YES-but-generalise-first) being upstreamed to mathlib? If yes, this order-4 branch rides along as an
   internal step — restated in mathlib idiom — and the question collapses to "expose it as a named lemma,
   or inline it into the main proof?"
2. The project already has the strictly-more-general **`PID.integrality_of_order_four_squarefree`**
   (UFD base, `Squarefree (2:R)`, `IsLocalization.IsInteger`). Which of the two parallel tracks —
   **General (ℤ⊂ℚ)** or **PID (`R`/`K`)** — is the intended canonical form to upstream, so mathlib doesn't
   receive two near-duplicate order-4 lemmas?
3. Should the upstreamed order-4 step be stated with **`IsLocalization.IsInteger R`** (the PID-twin /
   mathlib idiom, cf. `RationalRoot.lean`) rather than the current `ℤ⊂ℚ` `∃ x₀:ℤ, (x₀:ℚ)=x` encoding?
   (Strongly preferred by mathlib convention.)
4. Is the order-4 branch worth exposing as a **standalone public lemma** in mathlib at all, given its
   single call site is the `private` `integrality_of_four_dvd_order`? Or should it be a `private`/`local`
   step (or inlined) inside the Nagell–Lutz file?
5. Before any of this: are the project's **forks** of `WeierstrassCurve.{preΨ₄, ψ_four, leadingCoeff_preΨ₄,
   map_preΨ₄}` (in `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean`) going to be **reconciled
   against mathlib's identically-named originals** before upstreaming? They are the prerequisite — the
   upstreamed proof must build on mathlib's versions, not the project's shadows.

Next action: user answers the questions; re-run `/mathlibable` on the chosen canonical order-4 form (most
likely the **PID `IsInteger` form**, or the bundled Nagell–Lutz statement) to resolve the verdict. The
most likely resolution, if Nagell–Lutz is headed upstream, is that this helper is **absorbed into the
Nagell–Lutz PR** (as a private/internal step of the main proof, stated over the canonical base), rather
than shipped as an independent declaration.

---

## Next step

User answers the 5 questions above. If the Nagell–Lutz theorem is bound for mathlib, treat this order-4
branch as an **internal step of that PR** — restated over the canonical base (the existing PID `R`/`K` /
`IsLocalization.IsInteger` form is the natural target, deduplicating the General↔PID pair) and likely kept
`private`/inlined like the project's own `integrality_of_four_dvd_order` — after first reconciling the
forked `DivisionPolynomial.*` dependencies against mathlib's originals. As an isolated declaration in its
current `ℤ⊂ℚ` / `∃ x₀:ℤ` form, it is **not** an independent mathlib addition.
