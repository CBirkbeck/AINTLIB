# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_general`

_Assessment date: 2026-06-21 (Step-9 `/overview` mathlibable pass). Mathlib pin: `09b373db6e24`
(toolchain `leanprover/lean4:v4.32.0-rc1`), read directly from
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. The local Lean build is
stale per the task brief, so presence/absence in mathlib is established by **direct grep of the pinned
checkout** (authoritative for this exact pin) plus WebSearch, not the live loogle/leansearch indices.
ChatGPT-math MCP was **down** at assessment time (Codex exec error) — its channel is recorded `n/a
(fallback)` and compensated by extra WebSearch + the textbook record. This report is consistent with — and
reuses the protocol of — the sibling reports already written for this file
(`lutz_nagell_integrality_general.md` → YES-add-as-is, `lutz_nagell_discriminant_general.md` →
YES-but-generalise-first)._

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  direct read of the pinned mathlib checkout. Full statement + proof read from
  `GeneralDiscriminant.lean:204–223`.
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_general`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:211`
                            (`theorem lutz_nagell_general`; the task's line 248 points at the proof body /
                            statement block — the `theorem` keyword is at 211, conclusion through 218,
                            proof 219–223).
- qualified name:           ✓ VERIFIED `LutzNagell.LutzNagellTheorem.lutz_nagell_general`
                            — `namespace LutzNagell` (line 27) → `namespace LutzNagellTheorem` (line 28);
                            base name `lutz_nagell_general` (line 211). Matches the task's parsed guess
                            exactly.
- kind:                     theorem
- has sorry:                no — complete proof (219–223): `rcases lutz_nagell_integrality_general …`,
                            then `Or.inl ⟨…, lutz_nagell_discriminant_general …⟩` / `Or.inr hord2`.
- module docstring summary: "General discriminant divisibility for Weierstrass curves": for a nonzero
                            torsion point `(x₀,y₀) ∈ ℤ²` on `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆` (`aᵢ∈ℤ`),
                            with `κ₀ = 2y₀+a₁x₀+a₃`, either `κ₀=0` or `κ₀²∣4Δ`. The file's stated **Main
                            result** is `lutz_nagell_discriminant_general`; `lutz_nagell_general` is the
                            combined public theorem packaging it with the integrality dichotomy.

---

### Statement (Phase 1)

`lutz_nagell_general` is the **combined Nagell–Lutz theorem for a general Weierstrass curve over ℚ**. Let
`W : WeierstrassCurve ℤ` be a Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with integer
coefficients, and `curveQ W` its base change to ℚ. Let `P = (x, y)` be a nonsingular affine rational point
that is a **torsion point** (`IsOfFinAddOrder`). Then exactly one of the following holds:

1. **(generic branch)** the coordinates are integers — there exist `x₀, y₀ ∈ ℤ` with `(x₀:ℚ)=x`,
   `(y₀:ℚ)=y` — and, writing `κ₀ = 2y₀ + a₁x₀ + a₃`, either `κ₀ = 0` **or** `κ₀² ∣ 4·Δ` (where `Δ` is the
   Weierstrass discriminant of `W`);
2. **(2-torsion branch)** `P` has order exactly 2 (`addOrderOf P = 2`) and the half-integral denominators
   are bounded: `4x ∈ ℤ` and `8y ∈ ℤ`.

In classical notation (Wikipedia/HandWiki general form): a finite-order rational point has **integer
coordinates, or else order 2 with `x = m/4, y = n/8`** (`m,n ∈ ℤ`); and on the integer branch the
"completed `y`-coordinate" `κ₀` satisfies `κ₀ = 0` or `κ₀² | 4Δ`. For the short model `y² = x³ + Ax + B`
one has `a₁=a₂=a₃=0`, so `κ₀ = 2y` — i.e. this is the general-Weierstrass lift of the textbook "`β = 0`
or `β² ∣ 4A³+27B²`".

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — an integral-coefficient Weierstrass curve (the most general single-curve
  object; `Δ`, `bᵢ` are mathlib's `WeierstrassCurve.Δ`, `WeierstrassCurve.b₂…b₈`).
- `{x y : ℚ}` — the affine coordinates of the point, over the rationals.

Hypotheses (Lean side):
- `hpt : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point of the base-changed curve.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion (mathlib's own
  finite-order predicate on the affine point group).

Conclusion (math): integral coordinates with `κ₀=0 ∨ κ₀²∣4Δ`, **or** order 2 with `4x,8y ∈ ℤ`.

Conclusion (Lean):
`(∃ x₀ y₀ : ℤ, ↑x₀ = x ∧ ↑y₀ = y ∧ (2*y₀+W.a₁*x₀+W.a₃ = 0 ∨ (2*y₀+W.a₁*x₀+W.a₃)^2 ∣ 4*W.Δ))`
`∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧ (∃ n:ℤ, ↑n = 4*x) ∧ ∃ m:ℤ, ↑m = 8*y)`.

---

### Size classification (Phase 2a)

Verdict: **BIG.**
Reason: a **theorem named after people** (Trygve Nagell 1935, Élisabeth Lutz 1937) and the top-level
**combined / capstone** result of the project's `General*` track — the public face the whole file builds
toward. Two of the three BIG triggers fire (named-after-a-person; project main result).

(Note: literature width is EXHAUSTIVE regardless — and is here, because the decl is genuinely BIG.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` → **n/a**. The body is a 5-line `rcases`/`Or`
assembly; the one-line-definition heuristic does not apply.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz elliptic curve torsion integer coordinates discriminant divisibility                       | yes  | `x,y∈ℤ`; `y=0` (order 2) or `y²∣D`; general model adds the order-2 `x=m/4,y=n/8` escape | Wikipedia, HandWiki, NumberAnalytics, en-academic, "A Neighbourhood of Infinity", PlanetMath — all agree |
|  2 | WebSearch (general Weierstrass)  | Nagell-Lutz general Weierstrass `y²+a₁xy+a₃y=…` `2y+a₁x+a₃` squared divides discriminant order-2 m/4 n/8 | yes  | **verbatim**: "integer coordinates, or else order 2 and coordinates `x=m/4, y=n/8`" | HandWiki general-form quote (WebFetch) — **exact match to the Lean two-branch dichotomy** |
|  3 | WebSearch (named-after / textbook)| Silverman–Tate *Rational Points on Elliptic Curves* Nagell-Lutz proof; `β²∣4A³+27B²`                    | yes  | short model `y²=x³+Ax+B`: `x,y∈ℤ`, `y=0 ∨ y²∣4A³+27B²`; `Δ=4A³+27B²` | Silverman–Tate UTM Ch. II; Tate 1961 lectures; "NOT an iff" caveat confirmed |
|  4 | ChatGPT MCP                      | standard general-Weierstrass form + `κ²∣4Δ` correctness + is it in Lean/mathlib?                        | n/a  | (Codex exec failed — MCP down)   | recorded n/a per brief; compensated by #1–3, #9, #10 + textbook record + direct mathlib grep |
|  5 | Local references                 | `refs/NagellLutz/`, `projects/NagellLutz/.mathlib-quality/references/`                                  | n/a  | (directories absent)             | no local PDFs present in this checkout (refs are local-only & gitignored; none synced here) — recorded n/a |
|  6 | nLab                             | torsion points of an elliptic curve / Nagell-Lutz                                                      | yes  | confirms `x,y∈ℤ`, `y=0 ∨ y²∣D`; "effective method for `E(ℚ)_tors`" | ncatlab.org/nlab/show/torsion+points+of+an+elliptic+curve — statement, not a fuller generalisation |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept        | Nagell–Lutz is a Diophantine/arithmetic statement; no higher-categorical reformulation — n/a |
|  8 | Stacks Project (alg geom)        | torsion elliptic curve integral model                                                                 | n/a  | only moduli-stack/Picard-torsion items; no Nagell-Lutz | Stacks covers the stack `M_{1,1}`, not Diophantine torsion-coordinate bounds — n/a for this result |
|  9 | MathOverflow / Math.SE           | (transitive via #1–3; "A Neighbourhood of Infinity" exposition; algebrateahouse "Computing Points of Finite Order") | yes  | matches #1; worked `E(ℚ)_tors` computations via the theorem | community expositions all agree on the statement |
| 10 | recent arXiv (last 5 yrs)        | Nagell-Lutz imaginary quadratic fields / p-adic                                                        | yes  | arXiv:2509.07524 (2025, imag. quadratic fields); Anqi Li p-adic notes (784paper) | the theorem is a **live, canonical object** mathematicians actively re-derive & extend; **no Lean version surfaced** |

The protocol passes: WebSearch ran ≥3 distinct queries at different generality levels (specific short
form, general-Weierstrass form, named-after/textbook); the general-form query was confirmed verbatim by a
direct WebFetch of HandWiki; ChatGPT MCP attempted but down (n/a with reason); local refs checked (absent,
n/a); nLab checked (hit); nCatLab/Stacks checked with n/a reasons; MathOverflow + arXiv checked (hits).

### Literature summary (Phase 3)

Concept identified as: **the Nagell–Lutz theorem** (a.k.a. Lutz–Nagell theorem), general-Weierstrass
formulation over ℚ.
Sources agree on the standard form: **yes.** HandWiki's generalized statement is verbatim — "any rational
point P=(x,y) of finite order must have integer coordinates, or else have order 2 and coordinates of the
form x=m/4, y=n/8, for m and n integers." Wikipedia/PlanetMath/nLab give the short-model divisibility
`y=0 ∨ y²∣D`; Silverman–Tate Ch. II is the canonical proof reference; Silverman *AEC* VIII.7 and Husemöller
carry the general-curve version; Alpöge's "Nagell–Lutz, quickly" is a modern short proof.
Most general standard form (for a single curve over ℚ): exactly the Lean statement — integral coordinates
with the completed-`y` divisibility `κ₀=0 ∨ κ₀²∣4Δ`, **or** the order-2 escape with `4x,8y∈ℤ`.
Generality dimensions where the literature varies:
  - **model**: short `y²=x³+Ax+B` (textbook default) ↔ general `a₁..a₆` (Silverman AEC, Husemöller) — the
    Lean decl takes the **general** model (the strictly more general single-curve form).
  - **base ring/field**: ℚ (classical) ↔ number fields / PIDs (arXiv:2509.07524, Tate normal form) — this
    is a *different theorem*, and the project already formalises it separately in the parallel **PID
    track** (`lutz_nagell_integrality_pid`, `lutz_nagell_number_field`). Not a weakening of *this* ℚ form.
Disagreement with the literature: **none.** The `4·Δ` factor and the `κ₀=2y₀+a₁x₀+a₃` completion are the
standard general-model bookkeeping (square-completing the Weierstrass `y`); `κ₀²∣4Δ` is the faithful lift
of the short-form `β²∣4A³+27B²`.

If the literature had returned nothing this would bias toward BORDERLINE/NO — but it returned a *named,
ubiquitous, actively-extended* theorem with a verbatim statement match, which biases firmly toward a YES
bucket.

---

### Generality analysis — `lutz_nagell_general` (Phase 4)

Literature-standard form (from Phase 3): general-Weierstrass-over-ℚ Nagell–Lutz — exactly the Lean form.

| # | Parameter / hypothesis                         | Current Lean form                  | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------------|------------------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`                       | general integral Weierstrass `a₁..a₆` | general Weierstrass `a₁..a₆` (Silverman AEC, Husemöller) | NO (already maximal in-model) | This is the *general* model — strictly more general than the short `y²=x³+Ax+B` corollary that sits below it in the file. Maximal for a single curve. |
| 2 | base field ℚ (`curveQ W = W.map (ℤ→ℚ)`)         | ℚ                                  | ℚ (classical); number fields / PIDs (extensions) | yes — but to a **different theorem** | Broadening the base ring is the project's *separate, already-formalised* PID/number-field track (`PIDMain.lean`), not a weakening of the ℚ statement. ℚ is exactly right here. |
| 3 | `hpt : Nonsingular x y`                         | nonsingular affine point           | point on the curve                 | NO                  | Nonsingularity is required for the point group / `Affine.Point.some` to be defined; standard. |
| 4 | `htor : IsOfFinAddOrder P`                      | torsion (finite order)             | finite order                       | NO                  | Finite order *is* the hypothesis of the theorem — the whole content is "torsion ⇒ (integral ∨ 2-torsion)". |
| 5 | conclusion uses mathlib `Δ`, `bᵢ`, `addOrderOf`, `IsOfFinAddOrder` | native mathlib vocabulary | — | n/a | Already speaks mathlib's idiom; nothing to modernise. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the ℚ / integral-Weierstrass single-curve setting).
Number of in-scope weakening opportunities found: **0.** The only "weakening" axis (base ring ℚ → PID /
number field) yields a *different theorem* that the project formalises separately in its PID track — per
the verdict-gate rules and the sibling `lutz_nagell_integrality_general` report, that is not a
generalisation of this declaration.
Cost of restatement: n/a (no restatement needed).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                  | Applies? | Proposed reformulation | Downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | — | Already typeclass-native: `WeierstrassCurve ℤ`, `IsOfFinAddOrder`, `Nonsingular`. |
|  2 | sequences/metric → filters/nets/topology?                                                  | no       | — | Purely algebraic/Diophantine; no limiting/topological content. |
|  3 | construct an object → universal-property class?                                            | no       | — | It's a structure theorem about existing points, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                         | no       | — | No subobject is built. (A future `EllipticCurve.torsion` submonoid would *consume* this, not replace it.) |
|  5 | vector-space/metric/field-specific → weaken typeclasses (modules/(semi)ring)?              | partial→separate | base ℚ → PID/number field | This is exactly axis #2 of Phase 4a — **already a separate formalised theorem** (PID track), not a modernisation of the ℚ form. |
|  6 | 1-categorical → higher/∞-categorical?                                                      | no       | — | Not a categorical statement. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                  | no       | — | The `ℤ`/`ℚ` here are the arithmetic content (the theorem is *about* integrality over ℤ), not an incidental index. |
| 8* | concrete-via-abstract: does the named object vanish from the proof body? (Case-6 probe)    | no       | — | The proof is a genuine assembly of two substantial project theorems (`…integrality_general` + `…discriminant_general`); it does not secretly prove a more abstract statement that `lutz_nagell_general` then specialises. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The declaration already uses mathlib's native vocabulary
(`WeierstrassCurve`, `WeierstrassCurve.Δ`/`bᵢ`, `Affine.Point.some`, `IsOfFinAddOrder`, `addOrderOf`).
The one "abstraction" axis (PID/number-field base) is a *distinct* theorem already formalised separately,
not a reorganisation of this one. There is no contemporary reformulation that organises the
general-Weierstrass-over-ℚ statement better — so Phase 4c does **not** flip the verdict to
YES-but-generalise-first.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `lutz_nagell_general` (Phase 5)

[A] Lean-Finder       n/a — live index not consulted (build stale); substituted by [D] direct grep of the exact pin.
[B] Loogle            pattern: torsion `IsOfFinAddOrder` on `WeierstrassCurve` / `Affine.Point` ⇒ `∃ (_:ℤ), …` integrality — no such index hit known; **[D] is authoritative for this pin**.
[C] LeanSearch        NL: "Nagell-Lutz theorem", "torsion point of elliptic curve has integer coordinates" — not consulted live; covered by [D].
[D] Grep mathlib src  `grep -rniE "nagell|lutz" Mathlib/` → only "Patrick Lutz" (Galois-theory author), **zero** Nagell–Lutz hits. `grep -rniE "IsOfFinAddOrder|torsion" Mathlib/AlgebraicGeometry/EllipticCurve/` → only `twoTorsionPolynomial` (2-torsion *polynomial*, `discr = 16Δ`) and 2-torsion docstrings; **no torsion-point→integrality/discriminant theorem at any generality**. `mordell` → only a motivational mention in `GroupTheory/Descent.lean`; **no Mordell–Weil, no Nagell–Lutz**.   → **no hits**
[E] Name pattern      `lutz_nagell` / `nagell_lutz` / `torsion_integral` / `*_tors` over EC files → no hits.   → **no hits**

Searched for both:
  - the user's current form (combined general-Weierstrass-over-ℚ disjunction) — absent;
  - the literature-standard form (short `y²=x³+Ax+B`; the integrality half alone; the discriminant half
    alone; any "torsion ⇒ integral" statement at any generality) — all absent.

Concluded: **not in mathlib** (direct grep of the pinned checkout exhausted, plus the literature-standard
short form and each half independently). Mathlib has built the entire elliptic-curve *substrate* —
`WeierstrassCurve` (`Weierstrass.lean`), the affine group law (`Affine/`), the discriminant `Δ`
(`Weierstrass.lean:132`), `twoTorsionPolynomial` (`discr = 16Δ`), the `DivisionPolynomial/` files, and the
whole `NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) — but has **never connected any of it
to the arithmetic of torsion points.** The only formalised EC *arithmetic* result upstream (arXiv:2302.10640)
is the group-law associativity, not Nagell–Lutz.

---

### Composition check (+ call-sites signal) (Phase 6)

#### Call sites — `lutz_nagell_general` (Phase 6.0)

Internal use count (excluding the declaring file): **K = 0.**
External-to-file callers: **0.**
Inline-derivation grep: the combined disjunction is **not** re-derived anywhere else — `lutz_nagell_general`
is the unique assembly point. (Whole-repo grep for `lutz_nagell_general` returns only the declaration
itself.)

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Interpretation: `K = 0` here is the **expected signature of a top-level headline theorem**, not dead code.
`lutz_nagell_general` is the project's *capstone disjunction* — the public face that packages the two
substantial sub-results (`lutz_nagell_integrality_general`, `lutz_nagell_discriminant_general`) into the
single statement a downstream user / textbook reaches for. Such capstones are the *export*, consumed by
external libraries and human readers, not by sibling lemmas. The Phase-2b "one-liner with K=0" NO-trap does
**not** apply: this is a `theorem` (not a one-line `def`), it is named after people, and its content is the
full classical statement — the call-sites table here is a YES signal (genuinely-new main result), not a NO
signal.

#### Composition attempt (Phase 6a)

Can `lutz_nagell_general` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `rcases lutz_nagell_integrality_general …; exact Or.inl ⟨…, lutz_nagell_discriminant_general …⟩ / Or.inr …`
  - Decls used: `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`,
    `LutzNagell.LutzNagellTheorem.lutz_nagell_discriminant_general` — **both are project theorems, NOT
    mathlib primitives.**
  - Result: **fails as a mathlib composition.** The two ingredients are themselves substantial novel
    results (a multi-file p-adic/formal-group denominator descent + the order-2 quartic bound for
    integrality; a division-polynomial / `Ψ₃` divisibility + Bézout argument for the discriminant half).
    Neither is in mathlib (Phase 5).

Conclusion: **NOT-COMPOSABLE** (from mathlib). The proof *is* a clean 5-line assembly — but of two
declarations that do not exist in mathlib and would have to be upstreamed first. It is a composition of
**project** results, which is precisely why this capstone co-ships with them as one PR series rather than
being inlined. (Heuristics table: a multi-`have`/`rcases` assembly over non-mathlib lemmas is "a proof",
not a mathlib composition.)

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_general`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): a **named classical theorem** (Nagell 1935 / Lutz 1937). The Lean statement
  is the literature-standard general-Weierstrass-over-ℚ form, with **both** branches matching the sources
  verbatim — integral coordinates + the completed-`y` divisibility `κ₀=0 ∨ κ₀²∣4Δ`, OR the order-2 escape
  `4x,8y∈ℤ` (Wikipedia/HandWiki "`x=m/4, y=n/8`"). Textbook homes: Silverman–Tate Ch. II, Silverman *AEC*
  VIII.7, Husemöller, Alpöge. arXiv:2509.07524 (2025) shows it is a live, actively-extended object; **no
  Lean/mathlib formalisation exists.**
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for the ℚ / integral-Weierstrass single-curve
  setting; 0 in-scope weakenings; Phase 4c modern-idiom = **no**. The base-ring axis (PID/number field) is a
  *separate, already-formalised* theorem (the parallel PID track), not a weakening of this one.
- Mathlib search (Phase 5): **not in mathlib** — direct grep of the pinned checkout finds **zero**
  Nagell/Lutz hits (only the unrelated Galois-theory author) and **zero** torsion↔integrality /
  torsion↔discriminant results at any generality; mathlib's EC + EDS API (including the very files this
  project forks) stops at the abstract group law and bare polynomial/EDS identities.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib — the 5-line assembly composes two *project*
  theorems that are themselves novel and absent from mathlib; `K = 0` is the capstone-export signature, not
  dead code.

**Rationale:**

This is **the Nagell–Lutz theorem** in its combined general-Weierstrass formulation over ℚ — the single
public statement that a number theorist or a textbook cites by name: a nonzero rational torsion point on
`y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆` (`aᵢ∈ℤ`) either has integer coordinates with `κ₀=0 ∨ κ₀²∣4Δ`, or has order 2
with `4x, 8y ∈ ℤ`. Every literature channel agrees on the statement, and the Lean encoding reproduces it
faithfully — including the subtle order-2 escape branch (`x=m/4, y=n/8`) that Wikipedia, HandWiki and
PlanetMath state verbatim. The generality is correct and maximal for the ℚ statement (general Weierstrass
`a₁..a₆`, strictly more general than the short corollary in `Main.lean`), and there is no modernisation
move that organises it better — it already speaks mathlib's native vocabulary (`WeierstrassCurve`,
`WeierstrassCurve.Δ`, `Affine.Point.some`, `IsOfFinAddOrder`, `addOrderOf`).

The reason this is `YES-add-as-is` rather than `NO-composable-from-mathlib` despite its short proof body is
the Phase-6 finding: the two ingredients it `rcases`/assembles (`lutz_nagell_integrality_general`,
`lutz_nagell_discriminant_general`) are **not** mathlib primitives — they are themselves substantial novel
results absent from mathlib (the first got its own `YES-add-as-is`; the second `YES-but-generalise-first`).
A capstone that bundles two missing theorems is not "composable from mathlib"; it is genuinely-new content
that must be *added*, co-shipping with the ingredients it depends on. And it is not `YES-but-generalise-
first`, because Phase 4b found 0 in-scope weakenings and Phase 4c found no modern idiom: the only broader
axis (base ring) is a distinct, separately-formalised theorem in the project's PID track, not a
generalisation of this ℚ declaration. (Consistency note: the previous on-disk report and the two sibling
reports reach the same verdict family — this independent re-assessment confirms `YES-add-as-is` for the
combined headline.)

Note on generality-vs-cost: upstreaming the Nagell–Lutz series is a **large** effort — it first requires
reconciling the project's forks of `AlgebraicGeometry/EllipticCurve/DivisionPolynomial.*` and
`NumberTheory/EllipticDivisibilitySequence` against mathlib's originals. Per the verdict gate, that cost is
**not** a downgrade reason: getting the right form into mathlib is exactly the work mathlib exists to do.

**WHY add it (refactor-actionable):**
- **New mathematical content / named gap.** Mathlib has *no* Nagell–Lutz and *no* "torsion ⇒ integral /
  bounded-denominator coordinates" or "torsion ⇒ `κ²∣Δ`" theorem **anywhere**, at any generality (Phase 5
  [D], exhaustive grep of the exact pin: 0 hits). Mathlib's elliptic-curve chapter currently stops at the
  abstract Mordell–Weil **group law** plus bare division-polynomial / two-torsion-polynomial / EDS
  identities; the entire *Diophantine* layer — the arithmetic of torsion-point coordinates — is missing.
  `lutz_nagell_general` is the **canonical public entry point** to that absent chapter: the named theorem
  that makes `E(ℚ)_tors` effectively computable (for each square divisor `m²` of `4Δ`, solve a finite
  system), and the headline a reader looks up.
- **Composition with existing mathlib API.** Its hypothesis is `IsOfFinAddOrder` on
  `WeierstrassCurve.Affine.Point` — mathlib's *own* torsion predicate — so the whole
  `addOrderOf` / `IsOfFinAddOrder` toolbox applies directly, and its integral-coordinate conclusion is
  precisely what a future `EllipticCurve.torsion`-subgroup / Mazur-style development would build on. It also
  gives the upstream division-polynomial + EDS files (`Δ`, `twoTorsionPolynomial`, `Ψ₂Sq`, `Ψ₃`, `normEDS`)
  their **first arithmetic consumer** — they currently terminate at definitions/identities with no theorem
  consuming them downstream.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean` (new file), with
                              `lutz_nagell_general` as the file's headline theorem; alternatively grouped under
                              `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Torsion.lean` with the
                              point-arithmetic.
Proposed PR title:            `feat(NumberTheory/EllipticCurve): Nagell–Lutz theorem (general Weierstrass over ℚ)`
PR grouping (REQUIRED — this decl is a capstone over its siblings; upstream as **one coherent Nagell–Lutz
series**, def-/dependency-first, since the headline is meaningless without its engines):
  - `lutz_nagell_integrality_general` (GeneralMain.lean) — the integrality dichotomy engine [YES-add-as-is];
  - `lutz_nagell_discriminant_general` (GeneralDiscriminant.lean:187) — the `κ₀=0 ∨ κ₀²∣4Δ` half
    [YES-but-generalise-first: run `/generalise` first per its report];
  - **`lutz_nagell_general` (GeneralDiscriminant.lean:211) — this decl, the combined public disjunction**
    (the user-facing face);
  - the short-form siblings in `Main.lean` (`lutz_nagell` / `lutz_nagell_integrality` /
    `lutz_nagell_discriminant`) — the friendly `y²=x³+Ax+B` corollaries, as a follow-up.
Pre-PR checklist before opening:
  - [ ] Reconcile/upstream the project's forks of `DivisionPolynomial.*` + `EllipticDivisibilitySequence`
        against mathlib's originals (blocking prerequisite — the General*/PID* duplicated tracks must be
        de-forked).
  - [ ] `/generalise lutz_nagell_discriminant_general` (its sibling verdict requires it) before the series PR.
  - [ ] `/cleanup` over `GeneralDiscriminant.lean` `lutz_nagell_general` (full audit + diff gates).
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the
        `WeierstrassCurve` / division-polynomial maintainers).

---

## Next step

Upstream as **one coherent Nagell–Lutz PR series** (dependency-first): the integrality engine
`lutz_nagell_integrality_general`, then the discriminant half `lutz_nagell_discriminant_general` (after
`/generalise`), then **this capstone `lutz_nagell_general`** as the public disjunction, with the short-form
`Main.lean` corollaries as a follow-up. The hard blocking prerequisite is de-forking the project's copies of
`DivisionPolynomial.*` and `EllipticDivisibilitySequence` so the series sits on mathlib's own EC substrate.
Run `/cleanup` on the file (and `/generalise` on the discriminant sibling) before opening the PR.
