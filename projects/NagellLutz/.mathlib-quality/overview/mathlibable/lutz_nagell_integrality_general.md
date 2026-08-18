# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`

> Run date: 2026-06-21. Mode A (single declaration), full 8-phase workflow.
> Environment notes: local `lake build` stale (not re-run; reasoning from source).
> ChatGPT MCP **down** (Codex exec failed on both attempts) — compensated with
> WebFetch(Wikipedia) + 4× WebSearch at differing generality. Mathlib search
> tools (loogle / leansearch MCP) **not available** in this environment; Phase 5
> method [D] (authoritative grep over the vendored mathlib source tree at
> `.lake/packages/mathlib/`) + structural scan of the EllipticCurve directory
> substituted, which is conclusive for an *absence* verdict.
> (Supersedes the 2026-06-18 run; same verdict, evidence refreshed.)

---

### Baseline (Phase 0)
- lake build:               ~ not re-run (stale); decl elaborates per source + CLAUDE.md (main builds green)
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:110`
- parsed/VERIFIED qualified name: `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`
  (namespaces `namespace LutzNagell` L20 + `namespace LutzNagellTheorem` L21 — prompt's guess CONFIRMED)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Generalized Lutz–Nagell integrality theorem for a general
  Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ ℤ`.

---

### Statement (Phase 1)

`lutz_nagell_integrality_general` is a **theorem** (the general-Weierstrass form of the
**Nagell–Lutz theorem**) stating: let `W` be a Weierstrass curve over `ℤ` (coefficients
`a₁,a₂,a₃,a₄,a₆ ∈ ℤ`), and let `P = (x, y)` be a nonsingular **rational** affine point on
the base-changed curve `curveQ W` over `ℚ`. If `P` has finite additive order, then **either**
`x` and `y` are both integers, **or** `P` has order exactly `2` and `4x, 8y ∈ ℤ`
(equivalently `x = m/4`, `y = n/8` for integers `m,n` — i.e. `den x ∣ 4`, `den y ∣ 8`).

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — a Weierstrass curve with integral coefficients.

Hypotheses (Lean side):
- `{x y : ℚ}` and `hpt : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular
  rational affine point on the curve over `ℚ`.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion (finite order).

Conclusion (math): `(x,y ∈ ℤ)` OR `(ord P = 2 ∧ 4x ∈ ℤ ∧ 8y ∈ ℤ)`.

Conclusion (Lean):
```lean
((∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y)
  ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (∃ n : ℤ, (n : ℚ) = 4 * x) ∧ ∃ m : ℤ, (m : ℚ) = 8 * y)
```

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: a theorem **named after people** (Nagell–Lutz) **and** the primary main result
of the project (`## Main results` lists exactly `lutz_nagell_integrality_general`). Both
BIG triggers fire. Literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (the body is
a ~35-line case analysis over the torsion order). Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz torsion integral coords general Weierstrass                                                 | yes  | short form `y²=x³+Ax+B`: `x,y∈ℤ`, `y=0 or y²∣D` | Wikipedia, NumberAnalytics, Harvard/Alpoge "Nagell-Lutz quickly" |
|  2 | WebSearch (general form)         | Lutz-Nagell general Weierstrass `a₁..a₆`, 2-torsion `4x 8y` integral, Cassels                            | yes  | **general: `x,y∈ℤ` OR order 2 with `x=m/4, y=n/8`** | Wikipedia "Generalization" — **verbatim match to the Lean decl** |
|  3 | WebSearch (named-after / source) | Silverman AEC VIII torsion integral general Weierstrass division polynomial                              | yes  | Silverman AEC (Mordell–Weil, formal group, VII–VIII) | confirms textbook home; formal-group/`p`-adic proof |
|  4 | WebSearch (Cassels, exact case)  | Cassels LMSST torsion 2-torsion den 4 / den 8 general Weierstrass proof                                 | yes  | order `m=pⁿ`: `x=a/D², y=b/D³`; `m=2ⁿ` ⇒ den 4 / den 8 | Cassels *LMSST: 24 Lectures on Elliptic Curves* (1991), the canonical general-model source |
|  5 | ChatGPT MCP                      | "precise general-Weierstrass Nagell-Lutz, 2-torsion exceptional case, generality, formal-group proof"   | n/a  | — | **MCP DOWN** (Codex exec failed both attempts; env note confirms). Substituted by #1–#4 + #10. |
|  6 | Local references                 | `.mathlib-quality/references/`                                                                          | n/a  | (no references dir)                | directory absent for this project — recorded n/a |
|  7 | nLab                             | "Nagell-Lutz theorem"                                                                                    | n/a  | — | nLab has no Nagell–Lutz page; not a categorical concept. Recorded n/a (arithmetic of EC, outside nLab's coverage). |
|  8 | nCatLab                          | (categorical?)                                                                                          | n/a  | — | not a categorical concept (diophantine integrality of torsion). n/a. |
|  9 | Stacks Project                   | torsion integral Weierstrass / Nagell-Lutz                                                              | n/a  | — | Stacks is scheme-theoretic foundations; no diophantine Nagell–Lutz. n/a. |
| 10 | MathOverflow / Math.SE           | general Weierstrass torsion not integral, 2-torsion `x=m/4`                                             | yes  | confirms torsion need NOT be integral in general models; `4x,8y` is the sharp bound | matches the order-2 exceptional branch |
| 11 | recent arXiv (last 5y)           | Nagell-Lutz number fields / Tate normal form (arXiv 2509.07524, math/0011066)                          | yes  | Nagell–Lutz over imag. quad. fields; Tate-form torsion algorithms | confirms generalization direction = number fields (the project's PID track) |

Protocol pass check: WebSearch ran **4** distinct queries at 3+ generality levels (short
form, general form, named-source) ✓; ChatGPT MCP **down** and explicitly substituted ✓;
local refs absent (n/a) ✓; nLab/nCatLab/Stacks checked → n/a-with-reason ✓; MathOverflow ✓;
arXiv ✓.

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (a.k.a. **Lutz–Nagell**), general-Weierstrass form.
Sources agree on the standard form: **yes**.
Most general *classical* (over ℚ) standard form — **quoting Wikipedia's "Generalization"
verbatim**: for `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with integer coefficients, a rational
point of finite order *"must satisfy: either have integer coordinates, or else have order 2
and coordinates of the form x = m/4, y = n/8, for m and n integers."* This is **exactly** the
Lean conclusion (`∃n, n=4x` ∧ `∃m, m=8y` in the order-2 branch). Cited to Silverman (1986);
the underlying `p`-adic/formal-group proof and the `m=2ⁿ ⇒` den-4/den-8 sharpening are in
Cassels, *LMSST* (1991).
Generality dimensions where the literature varies:
  - **Base ring**: from ℚ (classical Nagell/Lutz) → number fields / ring-of-integers of a
    Dedekind domain (Cassels' valuation-theoretic proof; arXiv 2509.07524 over imaginary
    quadratic fields). The most general is "fraction field of a Dedekind/PID base".
  - **Model**: short Weierstrass (`x,y∈ℤ`, `y²∣D`) → general Weierstrass (the order-2 `4x,8y`
    exception appears). The Lean decl is at the general-model level.
Disagreement with the literature: **none** — the Lean statement is the textbook general-model form.

---

### Generality analysis — `lutz_nagell_integrality_general`

Literature-standard form (from Phase 3): the **maximally general** form replaces the base ℤ
(fraction field ℚ) by an arbitrary Dedekind/PID base `R` with fraction field `K` (Cassels).

| # | Parameter / hypothesis                       | Current Lean form              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------------------|--------------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ` (base = ℤ, pts ∈ ℚ) | integral Weierstrass over ℤ/ℚ | Weierstrass over a PID/Dedekind `R`, pts ∈ `K = Frac R` | **yes** | Cassels' proof is `v`-adic and works verbatim over any DVR/Dedekind base. **The project itself already proves this** — see `lutz_nagell_integrality_pid` / `lutz_nagell_number_field` (PIDMain.lean). |
| 2 | conclusion order-2 branch: `4x ∈ ℤ ∧ 8y ∈ ℤ` | both `den x ∣ 4` AND `den y ∣ 8` | over `K`: `den x ∣ 4` (the `8y` half is ℚ-specific bookkeeping) | partial | the clean symmetric `4x,8y` pair is sharpest over ℚ; the PID generalization currently states only `den x ∣ 4` (PIDMain L149) — so the ℚ form is in fact *more informative* on the order-2 branch. |
| 3 | `htor : IsOfFinAddOrder P`                   | finite order                   | finite order                      | NO                  | this is the hypothesis of the theorem; cannot be weakened. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in the base-ring dimension: ℤ/ℚ vs
Dedekind/PID).
Number of weakening opportunities found: **1** (base ring; row 1).
Proposed restatement (the maximally-general literature target — which the project *already*
has, modulo the squarefree-primes hypothesis):
```lean
theorem lutz_nagell_integrality_pid {R K} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (...) → Squarefree (p : R)) :
    (IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y) ∨
    (addOrderOf (...) = 2 ∧ (IsFractionRing.den R x : R) ∣ (4 : R))
```
Cost of restatement: **n/a — already exists in-project** (`PIDMain.lean:142`). The ℚ form
under assessment is a deliberate specialization of that track.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | — | already typeclass-driven (`WeierstrassCurve`, `Affine.Point`). |
|  2 | sequences/metric → filters/topological?                                                     | no       | — | purely algebraic/arithmetic; no topology to filterise. |
|  3 | construct an object → universal-property class?                                            | no       | — | it's a property of points, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | — | n/a. |
|  5 | vector-space/field-specific → weaken typeclass to module/(semi)ring?                        | **yes**  | base ℤ/ℚ → PID `R`/`Frac R` (same as Phase 4b row 1) | the whole `WeierstrassCurve`-over-`R` API; localization/`IsFractionRing` API; number-field instances. |
|  6 | 1-categorical → higher-categorical?                                                         | no       | — | n/a. |
|  7 | concrete index (ℤ,ℚ,ℝ) → arbitrary additive group/monoid/ordered structure?                 | **yes**  | the concrete `ℤ → ℚ` is exactly the specialization; general base = PID (= row 5) | unifies with `IsLocalization.IsInteger`/Dedekind machinery. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is the *same* move as Phase 4b (base-ring
generalization to a PID/Dedekind domain), not an additional categorical reformulation.
  - Proposed mathlib-idiomatic restatement: the `lutz_nagell_integrality_pid` form above
    (state over `Frac R` with `IsLocalization.IsInteger`).
  - Cost: **n/a — already proven in-project** (PIDMain.lean).
  - Mathlib downstream this enables: number-field torsion (`lutz_nagell_number_field`),
    composition with mathlib's `IsFractionRing` / `IsLocalization.IsInteger` / Dedekind API.
  - Real mathematical improvement: yes — the general-base form is the one Cassels proves and
    the one that specializes to every number field, not just ℚ.

---

### Diamond / defeq risk — n/a

Declaration kind is **theorem**. Phase 4.5 skipped (theorems introduce no definitional
equalities or typeclass-search paths).

---

### Mathlib search-status: `lutz_nagell_integrality_general`

[A] Lean-Finder       — (MCP tool unavailable in env)        n/a: tool absent
[B] Loogle            — (MCP tool unavailable in env)        n/a: tool absent
[C] LeanSearch        — (MCP tool unavailable in env)        n/a: tool absent
[D] Grep mathlib src  `lutz|nagell` over `.lake/packages/mathlib/Mathlib/`   **no real hits**
        — all matches are author name "Patrick Lutz" (Solvable.lean, AbelRuffini.lean) or
          substrings ("soLvabLe", "NormAL", "integrAL") in unrelated files. **No Nagell–Lutz
          theorem exists in mathlib.**
[E] Structural scan   EllipticCurve dir: `torsion|finite.?order|addOrderOf`   **only `twoTorsionPolynomial`**
        — `Mathlib/AlgebraicGeometry/EllipticCurve/` has `Weierstrass.lean` (incl.
          `twoTorsionPolynomial`, `Δ`), `DivisionPolynomial/{Basic,Degree}.lean`, Affine/
          Jacobian/Projective point groups, `Reduction.lean`. `Mathlib/NumberTheory/`
          has `EllipticDivisibilitySequence.lean`. **None states integrality of torsion points.**
          No occurrence of `addOrderOf`/`IsOfFinAddOrder` applied to elliptic-curve points
          with an integrality conclusion anywhere in mathlib.

Searched for both:
  - the user's current form (general Weierstrass over ℤ/ℚ): **not in mathlib**.
  - the literature-standard general form (over a Dedekind/PID base): **not in mathlib** either
    (mathlib has zero Nagell–Lutz content at any generality).

Concluded: **not in mathlib** (method [D] authoritative-grep + [E] structural scan exhausted;
methods [A–C] MCP tools unavailable in this environment but [D]/[E] are conclusive for an
absence claim — a present theorem would necessarily appear under `lutz`/`nagell` or as an
`addOrderOf … → integral` statement in the EllipticCurve tree, and neither exists).

---

### Call sites — `lutz_nagell_integrality_general`

Internal use count: **2** (within NagellLutz, excluding the declaring file `GeneralMain.lean`)
External-to-file callers: **1 distinct file** (`GeneralDiscriminant.lean`) — plus it underlies
the *entire* public API of the project (see below).

| Caller file:line                  | Usage pattern (one-line excerpt)                                   |
|-----------------------------------|--------------------------------------------------------------------|
| GeneralDiscriminant.lean:160      | `rcases lutz_nagell_integrality_general W hns' h2P_tor with ...`    |
| GeneralDiscriminant.lean:219      | `rcases lutz_nagell_integrality_general W hpt htor with ...`        |

Downstream public consumers (transitive, the project's headline results):
  - `lutz_nagell_integrality_short` (ShortWeierstrass.lean) — short-model corollary.
  - `lutz_nagell_integrality`, `lutz_nagell` (Main.lean) — the user-facing Nagell–Lutz theorem
    ("Theorem 1.1 of *Nagell-Lutz, quickly*").
  - the PID/number-field track (`lutz_nagell_integrality_pid`, `lutz_nagell_number_field`,
    PIDMain.lean) is the parallel general-base version.

Inline-derivation grep (re-derived elsewhere without using the decl?): **(none)** — every
integrality consumer routes through this lemma or its short/PID siblings.

Call-sites signal: **K = 2 internal uses + foundational to the public API, no inline
re-derivation → real API, YES-leaning.**

---

### Composition check (Phase 6)

Can `lutz_nagell_integrality_general` be derived from mathlib in ≤3 chained calls?

Attempt 1: any combination of `WeierstrassCurve.twoTorsionPolynomial`, division-polynomial
lemmas, `Affine.Point` group API.
  - Mathlib decls used: those listed in [E].
  - Result: **fails**. Mathlib supplies the *objects* (division polynomials, 2-torsion
    polynomial, the point group, EDS) but **no lemma** relating a point's finite order to the
    integrality of its coordinates. The entire arithmetic content (denominators of torsion
    points are controlled; `p`-adic/formal-group reduction; the `m=2ⁿ` den-4/den-8 sharpening)
    is missing.
  - Notes: the project's own proof needs **four** deep project-local lemmas —
    `prime_order_integrality_general` (GeneralPrimeOrder.lean:149),
    `integral_of_nsmul_integral_general` (GeneralIntegralMultiple.lean:82),
    `integrality_of_order_four_general` (GeneralPrimeOrder.lean:118),
    `bounded_den_of_order_two_general` (GeneralPrimeOrder.lean:167) — **none of which exist in
    mathlib** (grep over `.lake/packages/mathlib/` returns empty), themselves resting on ~880
    lines of `General*` infrastructure plus the forked division-polynomial/EDS development.

Conclusion: **NOT-COMPOSABLE.** This is the deep theorem itself, not a ≤3-call wrapper.

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): identified as the **Nagell–Lutz theorem**, general-Weierstrass
  form; the Lean conclusion matches Wikipedia's "Generalization" *verbatim* (`x,y∈ℤ` OR
  order 2 with `x=m/4, y=n/8`); cited to Silverman (1986), proof in Cassels *LMSST* (1991).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — base fixed at ℤ/ℚ,
  whereas the literature-standard (Cassels) and the project's own `lutz_nagell_integrality_pid`
  hold over an arbitrary PID/Dedekind base / number field.
- Mathlib search (Phase 5): **not in mathlib** at any generality (no Nagell–Lutz content
  whatsoever; only `twoTorsionPolynomial` + division polynomials + EDS as building blocks).
- Composition check (Phase 6): **NOT-COMPOSABLE** (depends on 4 deep project-local lemmas +
  ~880 lines of infrastructure absent from mathlib).

**Rationale (1–2 paragraphs):**

This is a genuine, named, headline theorem that mathlib is **missing entirely** — there is no
Nagell–Lutz theorem in mathlib at any generality (the only `lutz`/`nagell` strings in the
source tree are the author name "Patrick Lutz" and substrings of unrelated words). Mathlib
ships the *ingredients* — `WeierstrassCurve.twoTorsionPolynomial`, the
`DivisionPolynomial/{Basic,Degree}` files, the Affine/Jacobian point groups, and
`NumberTheory/EllipticDivisibilitySequence` — precisely the toolbox one would build the proof
on, but it has never assembled them into the integrality-of-torsion conclusion. The decl is
emphatically not composable from mathlib in ≤3 calls: its proof routes through four
project-local lemmas (`prime_order_integrality_general`, `integral_of_nsmul_integral_general`,
`integrality_of_order_four_general`, `bounded_den_of_order_two_general`), none of which exist
upstream, themselves resting on ~880 lines of `General*` infrastructure plus the forked
division-polynomial / EDS development. So mathlib should have this, and it is real API (2
internal call sites, foundation of the project's entire public `lutz_nagell` surface, no inline
re-derivation).

The reason the verdict is **generalise-first** rather than add-as-is is the base ring. The
maximally-general literature form (Cassels' valuation-theoretic proof) holds over any
Dedekind/PID base — over every number field, not just ℚ — and **the project has already proven
exactly this** in `lutz_nagell_integrality_pid` / `lutz_nagell_number_field` (PIDMain.lean).
The `_general` declaration under assessment is the deliberate ℤ→ℚ specialization of that PID
track. Per mathlib's iron rule (add the most general form that makes sense — modules not vector
spaces), the *upstreaming unit* should be the PID/number-field statement, with the ℚ form
recovered as a one-line corollary. Note this is **not** a cost-driven downgrade: the general
form is *already proven*, so generalising costs nothing here — it is purely "PR the more general
sibling that already exists, not the specialization." One genuine subtlety for the eventual PR:
the ℚ form's order-2 branch states the sharper symmetric pair `4x∈ℤ ∧ 8y∈ℤ`, whereas the
current PID form states only `den x ∣ 4`; the upstreamed general statement should carry the
full `den x ∣ 4 ∧ den y ∣ 8` (or `4x, 8y` integral) bound so the ℚ corollary loses nothing.

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the user's ℤ/ℚ form strictly narrower than the
    Cassels general-base (Dedekind/PID) standard form.
  - MODERN-IDIOM (Bourbaki 2.0): same move — base ℤ/ℚ → PID `R` / `Frac R` via
    `IsFractionRing` + `IsLocalization.IsInteger` (Phase 4c rows 5, 7).

**Proposed restatement** (the general-base form — already in-project as
`lutz_nagell_integrality_pid`, PIDMain.lean:142; the upstreaming target, ideally with the
`8y`/`den y ∣ 8` half of the order-2 branch restored):
```lean
theorem lutz_nagell_integrality_pid {R K} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)
    {x y : K} (hpt : (curveK R K W).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) → Squarefree (p : R)) :
    (IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y) ∨
    (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧
      (IsFractionRing.den R x : R) ∣ (4 : R) /- ∧ (IsFractionRing.den R y : R) ∣ 8 -/) := by
  sorry -- already proven in-project; the `den y ∣ 8` half may need adding
```
Estimated cost of regeneralisation: **CHEAP** — the general form is already fully proven in the
project. The only work is (a) deciding the canonical upstream statement (whether to keep the
`Squarefree` hypothesis or derive it / restrict to number fields), and (b) optionally restoring
the `den y ∣ 8` half of the order-2 branch. The ℚ `lutz_nagell_integrality_general` then becomes
a one-line corollary (`R := ℤ`, `K := ℚ`, with `Squarefree (p:ℤ)` automatic for primes).

**Mathlib downstream this enables:**
  - the whole `WeierstrassCurve`-over-a-general-`CommRing` API composes with the result.
  - `IsFractionRing` / `IsLocalization.IsInteger` / Dedekind-domain machinery (the integrality
    conclusion is stated in mathlib's canonical "is an integer of `R`" vocabulary).
  - immediate number-field torsion corollaries (`lutz_nagell_number_field`) without re-proof —
    the form the literature's modern generalizations (arXiv 2509.07524, imaginary quadratic
    fields) actually use.
  - the old ℚ form was *blocked* from all of the above by hard-coding ℤ/ℚ.

**PR grouping:** ship as one Nagell–Lutz PR alongside the sibling results that share the
infrastructure — `lutz_nagell_integrality` / `lutz_nagell_discriminant` / `lutz_nagell`
(Main.lean) and `lutz_nagell_pid_discriminant` / `lutz_nagell_number_field` (PIDMain.lean) —
gated behind upstreaming the forked `DivisionPolynomial`/`EllipticDivisibilitySequence`
extensions this project carries.

**Next action:** run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`
to tension the ℚ form against both the Cassels general-base target and the in-project PID form,
settle the canonical upstream statement (base hypotheses + the `den y ∣ 8` branch), then take
the PID/number-field statement to mathlib with the ℚ version as a corollary. Proposed location:
`Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean` (new file), or under
`Mathlib/AlgebraicGeometry/EllipticCurve/`. Pre-PR: `/cleanup` the file; reviewer from recent
`Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the David Ang division-polynomial line).

---

## Next step

Run `/generalise LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_general`, settle the
canonical general-base statement (the in-project `lutz_nagell_integrality_pid` is the target,
ideally restoring the `den y ∣ 8` order-2 bound), then PR the PID/number-field form to mathlib
(new file `Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean`) with the ℤ/ℚ
`lutz_nagell_integrality_general` recovered as a one-line corollary — bundled with the sibling
`lutz_nagell*` results and gated on upstreaming the forked division-polynomial / EDS extensions.
