# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant`

_Step-9 mathlibable assessment (AINTLIB /overview), single declaration._

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source.
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean:48`
- kind:                      theorem
- has sorry:                 no (decl body and its whole dependency chain — `lutz_nagell_discriminant_general`,
  `PID.lutz_nagell_pid_discriminant`, `PIDMain.lean` — grep clean for `sorry`/`admit`)
- module docstring summary:  Main.lean assembles the Lutz–Nagell theorem (Thm 1.1 of "Nagell–Lutz, quickly")
  for the short Weierstrass curve `y² = x³ + Ax + B` over ℚ from the two halves: integrality + discriminant divisibility.

---

### Statement (Phase 1)

`lutz_nagell_discriminant` is **Part 2 of the Nagell–Lutz theorem, specialised to the short
Weierstrass model**:

> Let `A, B ∈ ℤ` and let `E : y² = x³ + Ax + B` over ℚ have nonzero discriminant
> `Δ = -16·(4A³ + 27B²)`. If `(x, y)` is a nonzero rational point of finite (additive) order on `E`,
> and `x = x₀`, `y = y₀` with `x₀, y₀ ∈ ℤ` (integrality is the *hypothesis* here — supplied by Part 1),
> then either `y₀ = 0` or `y₀² ∣ Δ`.

Variables / typeclasses (Lean side):
- `A B : ℤ` — the curve coefficients (short Weierstrass, so `a₁ = a₂ = a₃ = 0`, `a₄ = A`, `a₆ = B`).
- `x y : ℚ` — the (rational) coordinates of the point.
- `x₀ y₀ : ℤ` — integer witnesses for the coordinates.

Hypotheses (Lean side):
- `hΔ : (shortCurveZ A B).Δ ≠ 0` — nonsingularity / elliptic.
- `hpt : (shortCurveQ A B).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion.
- `hx : (x₀ : ℚ) = x`, `hy : (y₀ : ℚ) = y` — integrality of the coordinates (output of Part 1).

Conclusion (math): `y₀ = 0 ∨ y₀² ∣ Δ`.
Conclusion (Lean): `y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ`.

Proof body (7 lines): invoke `lutz_nagell_discriminant_general (shortCurveZ A B) …`, which yields
`κ₀ = 0 ∨ κ₀² ∣ 4Δ` with `κ₀ = 2y₀ + a₁x₀ + a₃`; specialise `a₁ = a₃ = 0` (so `κ₀ = 2y₀`), then
peel the factor `4` from `4y₀² ∣ 4Δ` via `mul_dvd_mul_iff_left`. This decl is a **thin
specialisation wrapper** around the general theorem one file over.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named-after-people theorem (Nagell–Lutz) and a stated main result of the project
(part 2 of Thm 1.1). Named theorems are essentially guaranteed to be in/near the literature.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line def check is **n/a**. (For the record
the proof is 7 lines, a pure specialisation of a sibling theorem.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem … torsion points integer coordinates y² divides discriminant"     | yes  | `(x,y)` torsion ⇒ `x,y ∈ ℤ` and `y = 0` or `y ∣ D` (⇒ `y² ∣ D`) | Wikipedia, NumberAnalytics guide, UChicago REU (Galperin), HandWiki — unanimous |
|  2 | WebSearch (general form)         | "Nagell-Lutz" theorem statement general Weierstrass curve discriminant divisibility     | yes  | Stated for the **integer cubic** `y² = x³+ax²+bx+c` with `D = -4a³c+a²b²+18abc-4b³-27c²`; generalises to full Weierstrass `y²+a₁xy+a₃y=x³+…`, order-2 points have `x=m/4, y=n/8` | This is *strictly more general* than the short form `y²=x³+Ax+B` |
|  3 | WebSearch (formalisation / aliases)| Nagell-Lutz theorem Lean 4 mathlib formalization elliptic curve torsion formalized     | no   | — | No public Lean/mathlib formalisation found. Source paper "Nagell–Lutz, quickly" (Alpöge, Harvard) surfaced — exactly the project's cited Thm 1.1. Also a 2025 arXiv extension to imaginary quadratic fields. |
|  4 | ChatGPT MCP                      | (server down per task note — fallback)                                                  | n/a  | — | Substituted by extra WebSearch (#3) + WebFetch of Wikipedia for the exact statement & generality. |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                  | n/a  | — | Neither directory exists in this checkout. |
|  6 | nLab                             | Nagell–Lutz / elliptic curve torsion                                                    | n/a  | — | Not an nLab-style categorical topic; arithmetic of elliptic curves is covered by the textbook sources above. |
|  7 | nCatLab                          | —                                                                                       | n/a  | — | Not a categorical concept. |
|  8 | Stacks Project                   | —                                                                                       | n/a  | — | Stacks does scheme-theoretic AG, not the Diophantine arithmetic of rational torsion; no entry. |
|  9 | MathOverflow / MSE               | (folded into WebSearch) Nagell-Lutz torsion integrality                                 | yes  | same form as #1–2 | Surya-Teja blog, ND/MIT 18.783 problem sets, p-adic notes (Anqi Li) all restate it; standard. |
| 10 | recent arXiv (≤5 yrs)            | Nagell-Lutz formalization / generalisations                                             | yes  | arXiv 2509.07524 (imag. quad. fields), arXiv 2302.10640 (group law formalisation) | Confirms the *group law* is formalised (it's in mathlib) but Nagell–Lutz itself is not. |

### Literature summary (Phase 3)

Concept identified as: **the Nagell–Lutz theorem** (Nagell 1935 / Lutz 1937).
Sources agree on the standard form: **yes** — universally stated.
Most general standard form (textbook): for `E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ`,
every finite-order rational point either has integer coordinates with `y = 0` or `y² ∣ Δ`, or has
order 2 with `x = m/4, y = n/8`. The most commonly *quoted* form is the integer cubic
`y² = x³ + ax² + bx + c`.
Generality dimensions where the literature varies:
  - **Curve model**: short `y² = x³ + Ax + B`  ⊊  monic integer cubic `y² = x³ + ax² + bx + c`
    ⊊  full Weierstrass `y² + a₁xy + a₃y = x³ + …`. The literature's headline is the *middle/most-general*;
    the short form is a teaching specialisation. **`lutz_nagell_discriminant` is the narrowest model.**
  - **Conclusion strength**: literature gives `y ∣ D` (stronger) and notes `⇒ y² ∣ D`; the Lean decl
    proves the `y² ∣ Δ` half (the general theorem it calls actually proves the sharper `κ₀² ∣ 4Δ`).
Disagreement with the literature: none on content. The Lean form is correct but stated at a
**narrower curve-model generality** than the literature standard.

---

### Generality analysis — `lutz_nagell_discriminant` (Phase 4)

Literature-standard form (from Phase 3): general Weierstrass curve over ℤ (or at least the monic
integer cubic), `κ₀ = 2y₀ + a₁x₀ + a₃`, conclusion `κ₀ = 0 ∨ κ₀² ∣ 4Δ` (sharper) ⇒ short-form `y₀² ∣ Δ`.

| # | Parameter / hypothesis            | Current Lean form                              | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | curve `shortCurveZ A B`           | short Weierstrass `a₁=a₂=a₃=0, a₄=A, a₆=B`     | general `WeierstrassCurve ℤ` (any `aᵢ`)   | **yes**             | The project **already** proves the general version: `lutz_nagell_discriminant_general (W : WeierstrassCurve ℤ)` in `GeneralDiscriminant.lean:187`. This short decl is its 7-line specialisation. The weakening is *already done one layer up*. |
| 2 | conclusion `y₀² ∣ Δ`              | `y₀ = 0 ∨ y₀² ∣ Δ`                            | `κ₀ = 0 ∨ κ₀² ∣ 4Δ` (general), `y ∣ D` (textbook) | yes (sharper exists) | The general theorem already yields the sharper `κ₀² ∣ 4Δ`; the short form discards the factor 4. The textbook `y ∣ D` is sharper still but the `y² ∣ Δ` form is the standard "useful" statement. |
| 3 | `hΔ ≠ 0`, `Nonsingular`, `IsOfFinAddOrder`, integrality hyps | as written | same | no | These are exactly the right hypotheses; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (curve-model axis).
Number of weakening opportunities found: 1 substantive (curve model), already realised in-project.
Proposed restatement: there is nothing new to *prove* — the general form already exists as
`lutz_nagell_discriminant_general` / `lutz_nagell_general` in `GeneralDiscriminant.lean`. The mathlib
contribution is **the general theorem (+ its supporting API), not this short-Weierstrass wrapper.**
Cost of restatement: **CHEAP** — the general statement is already proved; "generalising" here means
*choosing the general decl as the upstream target* and dropping/inlining the short wrapper.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" → typeclass? | no | already a bundled `WeierstrassCurve ℤ` | — |
| 2 | sequences/metric → filters? | no | discrete arithmetic statement | — |
| 3 | construction → universal property? | no | it is a theorem, not a construction | — |
| 4 | set+closure → bundled substructure? | no | n/a | — |
| 5 | field/metric-specific → weaker typeclass? | **partially** | the general theorem is over `WeierstrassCurve ℤ` with point over ℚ; mathlib-idiomatically one might phrase torsion-integrality over a Dedekind/number-field base, but ℤ→ℚ is the canonical Nagell–Lutz setting and the right first target | full Nagell–Lutz API; later number-field generalisation (cf. arXiv 2509.07524) |
| 6 | 1-categorical → higher? | no | n/a | — |
| 7 | concrete index → general algebraic structure? | **yes (curve model)** | replace short model by general `WeierstrassCurve ℤ` — *already done in-project* | torsion-integrality for **every** integral Weierstrass curve, not just `y²=x³+Ax+B` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (the general-Weierstrass form), and it coincides with the
literature-standard generalisation — so the "generalise first" target is unambiguous.
  - Proposed mathlib-idiomatic target: `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general`
    (and the combined `lutz_nagell_general`) over `W : WeierstrassCurve ℤ`.
  - Cost: CHEAP (already proved).
  - Mathlib downstream: gives the discriminant-divisibility half for arbitrary integral Weierstrass
    curves; specialises in one line to the short model and to the monic integer cubic.
  - Real mathematical improvement: it is the form the textbooks state and the form every downstream
    application (torsion computation for a curve not handed to you in short form) actually needs.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or instances introduced).

---

### Mathlib search-status: `lutz_nagell_discriminant` (Phase 5)

Five-method search (lean_loogle / lean_leansearch MCP **not available** in this environment — task
note; substituted by exhaustive `grep` over `.lake/packages/mathlib/`, the source of truth, plus the
web formalisation search from Phase 3):

[A] Lean-Finder       n/a: MCP unavailable here → substituted by [D] grep + Phase-3 web search ("…formalized")
[B] Loogle            n/a: MCP unavailable here → substituted by [D] grep over mathlib source for the type shape
[C] LeanSearch        n/a: MCP unavailable here → substituted by Phase-3 NL web search
[D] Grep mathlib src  Terms: `nagell`, `lutz`, `IsOfFinAddOrder` (in EC files), `dvd.*[Dd]iscriminant`,
                      `torsion.*integ`, `torsion.*finite`/`Mordell` (EC dir), `divides the discriminant`.
                      → **no hits** for any torsion-integrality / discriminant-divisibility / Nagell–Lutz
                      result. Only "Lutz" hits are *Patrick Lutz* (Galois theory, unrelated). Only EC
                      torsion content is `WeierstrassCurve.twoTorsionPolynomial` (the 2-torsion *polynomial*,
                      `Weierstrass.lean:305`) and the group law `Affine.Point.instAddCommGroup`
                      (`Affine/Point.lean`). DivisionPolynomial files mention "torsion point" only as a
                      file *tag*, not a theorem. `torsion_int`/`isTorsion_iff_isTorsion_int`
                      (`Algebra/Module/Torsion/Basic.lean`) are module torsion — unrelated.
[E] Name pattern      `(theorem|lemma|def)\s+\w*(nagell|lutz|torsionInt|integralTorsion)` over all of
                      mathlib → no relevant hits.

Searched for both:
  - the user's short-Weierstrass form — not present.
  - the literature-standard general form (general Weierstrass torsion-integrality) — also not present.

Concluded: **not in mathlib** (all available methods exhausted, both forms). Mathlib's elliptic-curve
arithmetic currently stops at the group law on nonsingular points and the 2-torsion polynomial; there
is **no theory of finite-order points, torsion integrality, torsion finiteness, Mordell, or
Nagell–Lutz**. This is a genuine gap.

---

### Call sites — `lutz_nagell_discriminant` (Phase 6.0)

Internal use count: **1** (within the project, excluding the declaring file's own statement line).
External-to-file callers: **0** distinct files (used only inside `Main.lean`; no consumer in HasseWeil
or any other project).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Main.lean:72`   | `… hy, lutz_nagell_discriminant A B hΔ hpt htor hx hy⟩` — the *only* call; feeds the headline `lutz_nagell` |

Inline-derivation grep (was the equivalent re-derived elsewhere?): (none) — but the *general* form
`lutz_nagell_discriminant_general` is the thing actually doing the work, called once here.

Signal read: K = 1 internal use, no external consumers. Per the call-sites heuristic this is the
"possibly the wrong abstraction — could be inlined / leans NO-composable" pattern. Combined with the
Phase-4 finding that it is a strict specialisation of a sibling that *already exists*, the short-form
decl is a convenience wrapper, not the upstreamable object.

### Composition check (Phase 6)

Can `lutz_nagell_discriminant` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: from mathlib alone — **fails**. The result it specialises (`lutz_nagell_discriminant_general`)
is *project* code, not mathlib; there is no mathlib primitive for torsion-point discriminant divisibility
to compose from. (From *project* code it is a 7-line specialisation, but the composition check is
against **mathlib**.)

Conclusion: **NOT-COMPOSABLE from mathlib.** (It *is* a cheap specialisation of the project's own
general theorem — which is the real upstreaming candidate.)

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz is a canonical named theorem, universally stated for the
  *general* (or monic-cubic) integer Weierstrass curve; the short model `y²=x³+Ax+B` is a teaching
  specialisation. No Lean/mathlib formalisation exists.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** on the curve-model axis. The
  literature-standard general form is already proved in-project as `lutz_nagell_discriminant_general`.
- Mathlib search (Phase 5): **not in mathlib** in any form; mathlib's EC arithmetic has no torsion
  integrality / discriminant divisibility (only the group law + 2-torsion polynomial).
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (it composes only from project code).

**Rationale:**

The Nagell–Lutz theorem is exactly the kind of named, classical, genuinely-missing result mathlib
wants — mathlib's elliptic-curve arithmetic currently stops at the affine group law and the 2-torsion
polynomial, with no notion of torsion-point integrality or discriminant divisibility at all. So a
"YES" of some flavour is correct, and the NO buckets are excluded (nothing in mathlib to point at;
nothing composable from mathlib primitives).

But **`lutz_nagell_discriminant` itself is the wrong granularity to upstream.** It is the short-model
specialisation `a₁=a₃=0`, and its 7-line proof simply calls the project's own general theorem
`lutz_nagell_discriminant_general` (over an arbitrary `WeierstrassCurve ℤ`) and strips a factor of 4.
The literature states Nagell–Lutz for the general/monic-cubic curve; the general form already exists
right next door; and this short wrapper has a single internal call site and no external consumers.
Per the Bourbaki-2.0 rule (add the most general form that makes sense) the upstreaming target is the
**general** statement — `lutz_nagell_discriminant_general` and the combined `lutz_nagell_general` —
with the short-form `lutz_nagell_discriminant` / `lutz_nagell` retained, if at all, only as a one-line
`example`-style corollary. Hence YES-**but-generalise-first**: the generalisation is on the
curve-model axis, the target is already proved, and the cost is CHEAP.

**Reason for the generalisation:** LITERATURE-WEAKENING (Phase 4b: the user's form is strictly
narrower than the literature-standard general Weierstrass form) — *and* the general form is the one
the project already proved, so this is a packaging/target choice, not new mathematics.

**Proposed restatement (already exists in-project — upstream this instead):**
```lean
-- projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:187
theorem lutz_nagell_discriminant_general (W : WeierstrassCurve ℤ)
    {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ
-- together with the combined `lutz_nagell_general` (integrality + this).
-- The short-form `lutz_nagell_discriminant` becomes a ≤2-line corollary (or is inlined into `lutz_nagell`).
```
Estimated cost of regeneralisation: **CHEAP** (the general theorem is already proved, sorry-free).
Note: EXPENSIVE would not downgrade the verdict anyway; here it is genuinely cheap.

Mathlib downstream this enables:
- Torsion-point integrality/discriminant divisibility for **every** integral Weierstrass curve, not
  just the short model — the first piece of an elliptic-curve *torsion* theory in mathlib (currently
  absent), composing with the existing `Affine.Point` group law and `twoTorsionPolynomial`.
- One-line specialisations to the short model and to the monic integer cubic; a natural hook for the
  later number-field generalisation (cf. arXiv 2509.07524).

**Caveat for the human (sequencing, not a verdict change):** the *whole* general track —
`lutz_nagell_discriminant_general`, `lutz_nagell_general`, and the supporting `General*`/`PID*` files
plus the forked `DivisionPolynomial.*` / `EllipticDivisibilitySequence` — is one coherent upstreaming
unit. This assessment is about the **target/granularity** of the short-form discriminant decl;
the actual PR is the general theorem with its API, gated through `/generalise` + `/cleanup` +
`/pre-submit`. The short-form decl is best kept as a corollary or inlined.

---

## Next step

Run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant` (it will tension the short
form against the literature-standard general Weierstrass form from Phase 3 and against the in-project
`lutz_nagell_discriminant_general`). Outcome: target the **general** theorem (`lutz_nagell_discriminant_general`
/ `lutz_nagell_general`) for upstreaming and demote the short-form decl to a one-line corollary (or
inline it into `lutz_nagell`), then proceed via `/cleanup` + `/pre-submit` on the general statement.
