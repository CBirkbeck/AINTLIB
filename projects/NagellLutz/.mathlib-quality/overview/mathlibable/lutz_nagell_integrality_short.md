# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_short`

### Baseline (Phase 0)
- lake build:               ~ not run (environment build is stale; reasoned from source per task note)
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_short`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:153`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Generalized Lutz–Nagell integrality theorem, with a short-Weierstrass specialisation collapsing the order-2 branch to full integrality.

Qualified name VERIFIED from source: namespaces `LutzNagell` (line 20) + `LutzNagellTheorem` (line 21); theorem `lutz_nagell_integrality_short` (line 153). Parsed name in the task (`...LutzNagellTheorem.lutz_nagell_integrality_short`) is correct.

---

### Statement (Phase 1)

`lutz_nagell_integrality_short` is a theorem stating the **integrality half of the Nagell–Lutz theorem for short Weierstrass curves over ℚ**:

Let `A, B ∈ ℤ` and let `E : y² = x³ + Ax + B` be the short Weierstrass curve over ℚ (base-changed from ℤ). If `(x, y) ∈ ℚ²` is a nonsingular affine point that is **nonzero and of finite additive order** in the elliptic-curve group, then `x ∈ ℤ` and `y ∈ ℤ` (formally: `∃ x₀ : ℤ, (x₀ : ℚ) = x` and `∃ y₀ : ℤ, (y₀ : ℚ) = y`).

This is precisely conjunct (1) of the classical Nagell–Lutz theorem, specialised to the short model.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the curve coefficients (short model `y² = x³ + Ax + B`).
- `x y : ℚ` — the affine coordinates of the point.

Hypotheses (Lean side):
- `hpt : (shortCurveQ A B).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point on the curve (encodes both the curve equation and nonsingularity at the point).
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is of finite order in the Mordell–Weil group (the nonzero point `.some` is automatically ≠ 0).

Conclusion (math): the coordinates of a nonzero rational torsion point on `y² = x³ + Ax + B` are integers.

Conclusion (Lean): `(∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`.

Proof shape (from source, lines 157–187): invoke the general-Weierstrass version `lutz_nagell_integrality_general` on `shortCurveZ A B`; in the integral branch return directly; in the order-2 branch use `a₁ = a₃ = 0 ⇒ ψ₂ = 2y`, so order 2 forces `y = 0`, whence `x` is a root of the monic `X³ + AX + B ∈ ℤ[X]` and is integral by `isInteger_of_is_root_of_monic`. Several hundred lines of project + forked-mathlib machinery sit underneath (`GeneralMain`, `GeneralPrimeOrder`, `GeneralIntegralMultiple`, division polynomials, EDS).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem named after people (Nagell–Lutz / Lutz–Nagell) and a primary project result (the file's `## Main results` and the project name itself). Guaranteed to be in the classical literature.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a multi-line tactic proof, lines 157–187.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found                              | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz short Weierstrass `y²=x³+Ax+B` torsion integral coordinates proof             | yes  | `(α,β)` torsion ⇒ `α,β ∈ ℤ`, and `β=0` or `β²∣4A³+27B²` | Wikipedia, HandWiki, Alpöge, Anqi Li, multiple lecture notes |
|  2 | WebSearch (general form)         | Nagell-Lutz integer coordinates torsion points statement (general)                        | yes  | torsion ⇒ integral coords + `y∣D`; finite torsion subgroup | Wikipedia: also general Weierstrass `a₁..a₆` form |
|  3 | WebSearch (named-after/aliases)  | Silverman–Tate "Rational Points on Elliptic Curves" Nagell-Lutz points of finite order    | yes  | `(x,y)≠O` finite order ⇒ `x,y ∈ ℤ`; then `y=0` or `y²∣D` | Standard UTM textbook; the canonical reference for this exact statement |
|  4 | ChatGPT MCP                      | (asked for standard form, generality, whether nonsingularity needed for integrality half) | n/a  | —                                                | **Codex command failed** (MCP down, as task warned); fell back to refs below |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`               | n/a  | (directory absent)                               | no references dir and no `refs/NagellLutz` symlink store present |
|  6 | nLab                             | Nagell-Lutz theorem                                                                        | n/a  | —                                                | nLab has no dedicated Nagell-Lutz entry (elementary Diophantine result, not a categorical concept); recorded n/a |
|  7 | nCatLab (if categorical)         | —                                                                                         | n/a  | —                                                | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell-Lutz / torsion integrality                                                         | n/a  | —                                                | Stacks covers scheme-theoretic AG foundations, not classical Diophantine torsion statements; recorded n/a |
|  9 | MathOverflow / Math.StackExchange| Nagell-Lutz statement / discriminant hypothesis                                           | yes  | confirms standard form; integrality is conjunct (1) | via aggregated search results; consistent with #1–#3 |
| 10 | recent arXiv (last 5 years)      | Nagell-Lutz imaginary quadratic / p-adic; formalization Lean mathlib                       | yes  | arXiv 2509.07524 (number-field generalisation); Li p-adic notes; **no Lean formalisation found** | confirms the result is actively generalised AND not yet in mathlib/Lean |

Primary references located:
- **E. Lutz** (1937) and **T. Nagell** (1935) — original papers (cited in the project's `Main.lean`).
- **Silverman & Tate, *Rational Points on Elliptic Curves*** (UTM) — the canonical textbook statement.
- **Silverman, *The Arithmetic of Elliptic Curves*** (GTM 106), VIII.7 — the modern reference.
- **L. Alpöge, "Nagell–Lutz, quickly"** — Theorem 1.1; *explicitly cited by the project* (`Main.lean` docstring) as the formalisation target.

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (a.k.a. Lutz–Nagell), integrality part, short Weierstrass form.
Sources agree on the standard form: **yes**. Every source states: for `y² = x³ + Ax + B`, `A,B ∈ ℤ`, a nonzero finite-order rational point has `x, y ∈ ℤ` (and then `y = 0` or `y² ∣ 4A³+27B²`).
Most general standard form: the **general Weierstrass** statement `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ` — a nonzero finite-order point either has integer coordinates or has order 2 with `x = m/4, y = n/8` (Wikipedia's "generalized form"). Over number fields (arXiv 2509.07524) is a strictly further generalisation.
Generality dimensions where the literature varies:
  - curve model: short (`a₁=a₂=a₃=0`) ⊂ general Weierstrass (`a₁..a₆`) — the most general over ℚ is the `a₁..a₆` form.
  - base field: ℚ ⊂ number fields / `p`-adic local statements.
Disagreement with the literature: **none**. The Lean statement (short model, ℚ, finite-order nonzero point ⇒ integral coords) matches the textbook conjunct (1) exactly.

Note on the nonsingularity / discriminant hypothesis: the Lean `_short` theorem assumes `Nonsingular` *at the point* (via `hpt`) but does **not** assume the global discriminant `Δ ≠ 0`. This is mathematically correct and is a (mild) strength: the integrality half does not need `Δ ≠ 0` (only the `y² ∣ Δ` divisibility half consumes a nonsingular/elliptic hypothesis). The sibling `lutz_nagell_integrality` (`Main.lean:35`) carries a redundant `hΔ` purely for uniform packaging and discards it, calling `_short` — direct evidence that `_short` is the load-bearing, hypothesis-minimal form.

---

### Generality analysis — `lutz_nagell_integrality_short`

Literature-standard form (from Phase 3): short-Weierstrass integrality is itself a standard named statement; the strictly-more-general standard form is the general-Weierstrass `a₁..a₆` version.

| # | Parameter / hypothesis                          | Current Lean form              | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------------------|--------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | curve = `shortCurveQ A B` (`a₁=a₂=a₃=0`)         | short Weierstrass over ℚ       | general Weierstrass `a₁..a₆`/ℤ    | yes (more general)  | The general form is **already proved** in this very file as `lutz_nagell_integrality_general` (line 110); `_short` is its deliberate specialisation. |
| 2 | base ring ℤ → ℚ (`A B : ℤ`, point in ℚ)         | integers / rationals           | number fields, `p`-adic           | yes (more general)  | Number-field version exists in the project too (`lutz_nagell_number_field`, `PIDMain.lean:499`); separate result, not a weakening of *this* one. |
| 3 | `hpt : Nonsingular x y` (pointwise)             | nonsingular at the point       | nonsingular at the point          | NO                  | needed to form the group point and run the reduction; standard. |
| 4 | `htor : IsOfFinAddOrder …`                      | finite order                   | finite order (= torsion)          | NO                  | this is the defining hypothesis of the theorem. |
| (— )| global `Δ ≠ 0`                                 | **absent**                     | usually stated (for the full thm) | already weaker      | `_short` omits `Δ≠0` for the integrality half — correctly weaker than the bundled textbook statement. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in curve-model and base-ring dimensions) — *but* the strictly-more-general forms already exist as sibling theorems in the same project (`lutz_nagell_integrality_general`, `lutz_nagell_number_field`). So the "narrowness" is not a missing-generality defect; it is a standard, separately-citable specialisation.
Number of weakening opportunities found: 2 (curve model, base ring), **both already realised elsewhere in the project**.
Proposed restatement: none needed — the general form is `lutz_nagell_integrality_general` (already present and itself a YES candidate).
Cost of restatement: n/a.

This is the canonical "ship the general lemma AND its named specialisation" situation: short-Weierstrass Nagell–Lutz is the form every textbook states, so it earns its own name even though the `a₁..a₆` version subsumes it.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | —                      | hypotheses are already minimal (two: Nonsingular, IsOfFinAddOrder) |
|  2 | sequences/metric → filters/topological?                                                     | no       | —                      | no limiting/topological content |
|  3 | construction → universal-property class?                                                    | no       | —                      | it's a theorem, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                          | partial  | could phrase via the torsion subgroup `E(ℚ)tors` being integral-valued | mathlib has no `E(ℚ)` torsion-subgroup-as-bundled-object API for this yet; minor, not blocking |
|  5 | vector-space/field-specific → weaken typeclass?                                             | no       | —                      | base is ℤ/ℚ intrinsically (Nagell–Lutz is about ℚ-rational torsion) |
|  6 | 1-categorical → higher-categorical?                                                         | no       | —                      | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                              | no       | —                      | the "ℤ/ℚ" here is the mathematical content, not an incidental index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (only a marginal row-4 nicety about packaging the conclusion as "the torsion subgroup is integral", which mathlib lacks API for and which is not a real organisational improvement over the explicit `∃ x₀ : ℤ` form used throughout the project).
One-line reason: the statement is already a minimal-hypothesis, idiomatic mathlib statement (`WeierstrassCurve.Affine`, `IsOfFinAddOrder`, integrality via `∃ : ℤ`).

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem`. (No definitional equalities or instances introduced.)

---

### Mathlib search-status: `lutz_nagell_integrality_short`

[A] Lean-Finder       — tool not available in this environment        n/a: substituted by [D] grep over the actual mathlib source tree (authoritative for presence)
[B] Loogle            — tool not available in this environment        n/a: substituted by [D]
[C] LeanSearch        — tool not available in this environment        n/a: substituted by [D] + WebSearch "formalization Lean mathlib Nagell-Lutz" (no hit)
[D] Grep mathlib src  `nagell`, `lutz`, `torsion`, `IsOfFinAddOrder`, `∃ x₀ : ℤ`, `isInteger`+`Nonsingular` over `.lake/packages/mathlib/Mathlib`   **no hits** for a torsion-integrality / Nagell–Lutz theorem
[E] Name pattern      `theorem … nagell/lutz/integrality` over mathlib   no hits

Detail of [D]:
- `grep -rni "nagell|lutz"` in mathlib → **only the unrelated mathematician Patrick Lutz** (Galois theory, `Data/Bracket.lean`, etc.). No Nagell–Lutz theorem.
- `Mathlib/AlgebraicGeometry/EllipticCurve/` → has `twoTorsionPolynomial`, division polynomials, EDS, Jacobian/Projective formulas — the **machinery**, but no theorem concluding a torsion point has integer coordinates. `IsOfFinAddOrder` appears nowhere under `AlgebraicGeometry/`.
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (the files this project FORKS) → contain only EDS / division-polynomial definitions; the strings "torsion point" appear solely in docstrings describing what division polynomials compute, **not** an integrality theorem.

Searched for both:
  - the user's current form (short-Weierstrass torsion integrality) — not found.
  - the literature-standard general form (general-Weierstrass / number-field torsion integrality) — not found.

Concluded: **not in mathlib** (grep over the source tree exhausted, including the specific forked files and the general-Weierstrass form; corroborated by WebSearch finding no Lean/mathlib formalisation of Nagell–Lutz).

---

### Call sites — `lutz_nagell_integrality_short`

Internal use count: **1** (within the project, excluding the declaring file `GeneralMain.lean:153`).
External-to-file callers: 1 distinct file.

| Caller file:line   | Usage pattern (one-line excerpt)                          |
|--------------------|-----------------------------------------------------------|
| Main.lean:39       | `lutz_nagell_integrality_short A B hpt htor` (body of the public wrapper `lutz_nagell_integrality`, which adds a discarded `hΔ`) |

Inline-derivation grep: (none) — no other file re-derives short-Weierstrass torsion integrality without calling this theorem. The general engine `lutz_nagell_integrality_general` (line 110) is the only other place the integrality content lives, and `_short` is its sanctioned specialisation. The public-facing `lutz_nagell` bundles this with the discriminant half.

Composability signal: K=1 internal use, but the single consumer is the *public API wrapper* `lutz_nagell_integrality`/`lutz_nagell` — i.e. this theorem IS the integrality result the project exports, not an incidental helper. Combined with "named classical theorem, not in mathlib", this points to a YES bucket (the low count reflects that it's a top-level deliverable, not a reused utility).

---

### Composition check (Phase 6)

Can `lutz_nagell_integrality_short` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: any direct mathlib API for torsion-point integrality?
  - Mathlib decls used: — (none exist; see Phase 5)
  - Result: **fails** — mathlib has no torsion-integrality theorem to chain to.

Attempt 2: build it from mathlib primitives (division polynomials + EDS + valuation argument)?
  - Mathlib decls used: `twoTorsionPolynomial`, `WeierstrassCurve.DivisionPolynomial.*`, `IsEllDivSequence`, p-adic valuations …
  - Result: **fails** — this is the *entire Nagell–Lutz proof* (formal subgroup at `p`, denominators are `p`-adic, reduction mod `p`), which the project spends hundreds of lines and a whole forked DivisionPolynomial track to carry out. Not a 1–3 call composition.

Conclusion: **NOT-COMPOSABLE**. The proof is a substantial development (the project's `General*`/`PID*` tracks), not a short composition of existing mathlib lemmas.

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_short`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): classical, named (Nagell–Lutz), standard textbook statement (Silverman–Tate; Silverman GTM 106 VIII.7; Alpöge Thm 1.1, *explicitly the project's cited target*). The short-Weierstrass integrality `x,y ∈ ℤ` is the universally-stated conjunct (1).
- Generality analysis (Phase 4): STRICTLY NARROWER than the general-Weierstrass form — but that more general form **already exists in the project** (`lutz_nagell_integrality_general`), and short-Weierstrass Nagell–Lutz is itself a standard, separately-citable named statement. No modern-idiom improvement (Phase 4c = no).
- Mathlib search (Phase 5): **not in mathlib** (all methods exhausted incl. the forked files and the general form; no Lean formalisation exists anywhere).
- Composition check (Phase 6): **NOT-COMPOSABLE** (the proof is a full development).

**Rationale:**

This is a flagship classical theorem of the arithmetic of elliptic curves, named after Nagell and Lutz, and mathlib does not have it in any form — confirmed by grepping the whole mathlib tree (the only "Lutz" is the unrelated Galois-theory author) and the specific forked files (`EllipticDivisibilitySequence.lean`, `DivisionPolynomial/Basic.lean`), which carry only the division-polynomial/EDS machinery, plus a WebSearch confirming no Lean/mathlib formalisation exists. The Lean statement matches the standard textbook form exactly (short Weierstrass `y²=x³+Ax+B`, `A,B∈ℤ`, nonzero finite-order rational point ⇒ integral coordinates) and is in fact *hypothesis-minimal*: it omits the global `Δ≠0` that the integrality half does not need (the sibling `lutz_nagell_integrality` adds and discards `hΔ`). It is not derivable from mathlib by any short composition — it is the conclusion of the project's entire `General*` development.

The one subtlety is generality: the general-Weierstrass version `lutz_nagell_integrality_general` (same file, line 110) strictly subsumes it. Under mathlib's "most general form" rule that *might* suggest YES-but-generalise-first. It does not here, for two reasons: (1) the more general form **already exists and would be upstreamed alongside** — there is nothing to "generalise first"; and (2) short-Weierstrass Nagell–Lutz is the form every textbook names and that downstream users reach for, so mathlib should carry it as a named specialisation regardless. Hence **add-as-is** (as part of a small PR family with the general version), not generalise-first.

**WHY add it (refactor-actionable):**
- New mathematical content: the integrality of rational torsion-point coordinates on an elliptic curve over ℚ — a named classical theorem entirely **absent from mathlib**. The concrete gap: mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/` has `twoTorsionPolynomial`, the `DivisionPolynomial` directory, and `NumberTheory/EllipticDivisibilitySequence.lean` — i.e. exactly the *inputs* to Nagell–Lutz — but **no theorem that consumes them to bound torsion-point denominators**. `IsOfFinAddOrder` does not occur anywhere under `AlgebraicGeometry/`. Nagell–Lutz is the natural capstone these files are building toward, and it is the standard effective tool for computing `E(ℚ)_tors`.
- How it composes with mathlib: it connects mathlib's existing `WeierstrassCurve.Affine.Point` group law + `IsOfFinAddOrder` torsion API to integrality (`∃ x₀ : ℤ`), unlocking downstream torsion-subgroup computations (the effective Nagell–Lutz search) and giving a target for the division-polynomial machinery that currently terminates at definitions.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean` (new file; or `Mathlib/AlgebraicGeometry/EllipticCurve/Torsion.lean`).
Proposed PR title:            `feat(NumberTheory/EllipticCurve): the Nagell–Lutz integrality theorem`
PR grouping:                  Ship together with the engine `lutz_nagell_integrality_general` (GeneralMain.lean:110) and the discriminant-divisibility half (`lutz_nagell_discriminant_general`, `lutz_nagell` in Main.lean) as one coherent "Nagell–Lutz" PR family. The substantial forked-mathlib prerequisites (the project's `DivisionPolynomial*`, `EvalBridge`, EDS forks, `General*` track) must be upstreamed first or in the same series — this is a large multi-PR upstreaming effort, not a single drop-in lemma. (Cost is large but does not change the verdict: per the gate, "too expensive" is not a downgrade reason.)
Pre-PR checklist before opening:
  - [ ] `/generalise lutz_nagell_integrality_short` — confirm no further easy weakening (expected: none; the general form already exists).
  - [ ] `/cleanup GeneralMain.lean lutz_nagell_integrality_short` — full audit + diff gates.
  - [ ] First reconcile the project's forks of `DivisionPolynomial.*` / `EllipticDivisibilitySequence` against current mathlib (the FORK is the real upstreaming blocker).
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the elliptic-curve / division-polynomial maintainers).

---

## Next step

Run `/generalise lutz_nagell_integrality_short` (expected: no further weakening — the general-Weierstrass form already exists as `lutz_nagell_integrality_general`), then `/cleanup` the file, then plan the Nagell–Lutz PR family — gated on first reconciling the project's DivisionPolynomial/EDS forks with upstream mathlib.
