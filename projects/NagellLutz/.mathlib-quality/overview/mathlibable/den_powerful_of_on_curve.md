# /mathlibable report — `LutzNagell.PID.den_powerful_of_on_curve`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task; reasoning from source)
- decl `LutzNagell.PID.den_powerful_of_on_curve`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:71`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The Lutz–Nagell theorem generalized from `ℤ/ℚ` to a PID `R` of characteristic zero with fraction field `K`, plus the number-field (class number 1) version.

True qualified name (verified from source): namespace `LutzNagell` → `PID`, so **`LutzNagell.PID.den_powerful_of_on_curve`**. (The parsed guess in the task matched.)

---

### Statement (Phase 1)

`LutzNagell.PID.den_powerful_of_on_curve` is a **theorem** stating:

Let `R` be an integral domain that is a PID of characteristic zero (hypotheses `[IsDomain R] [IsPrincipalIdealRing R] [CharZero R]` are present on the section variable, though several are `omit`ted in the proof — see below), with fraction field `K`. Let `W` be a Weierstrass curve with coefficients `aᵢ ∈ R`. If a point `(x, y) ∈ K²` lies on the (affine) curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` (coefficients pushed to `K` via `algebraMap R K`), then **every prime `q` of `R` that divides the denominator `den_R(x)` divides it at least twice** (`q ∣ den ⟹ q² ∣ den`).

Mathematically: the denominator of the `x`-coordinate of *any* point on the curve is a **powerful number** (every prime in it has multiplicity ≥ 2); equivalently, `v_q(x) ≤ 0 ⟹ v_q(x)` is even, i.e. the `x`-coordinate of a non-integral point has even negative valuation at every prime. This is precisely the denominator structure underlying the Nagell–Lutz theorem: the denominator of `x` is a perfect square `d²` (and that of `y` is `d³`).

Note the docstring's framing: "**No hypothesis on the torsion order needed — this is a property of ALL points on the curve.**" The result is the *local denominator-valuation* half of Nagell–Lutz, decoupled from torsion finiteness.

Variables / typeclasses involved (Lean side):
- `R` : the base ring — a domain (the proof body `omit`s `CharZero R`, keeping `[CommRing R] [IsDomain R] [IsPrincipalIdealRing R]`; the *delegated* helper actually only needs `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`).
- `K` : fraction field of `R`, `[Field K] [Algebra R K] [IsFractionRing R K]`.
- `W : WeierstrassCurve R` : the curve.
- `x y : K` : the point coordinates.

Hypotheses (Lean side):
- `heq` : `(x, y)` satisfies the affine Weierstrass equation over `K`.
- `q : R`, `hq : Prime q`, `hqd : q ∣ (den_R x : R)`.

Conclusion (math): `q² ∣ den_R(x)`.
Conclusion (Lean): `∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) → q ^ 2 ∣ (IsFractionRing.den R x : R)`.

**Proof body (1 line):** `fun _ hq hqd ↦ by_contra fun h ↦ den_no_simple_prime_factor_of_on_curve W heq hq hqd h`. It is the **contrapositive packaging** of the workhorse `den_no_simple_prime_factor_of_on_curve` (PIDDenominators.lean:87), which proves `q ∣ den ∧ ¬ q² ∣ den → False` by clearing denominators and a mod-`q` valuation descent.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named-mathematician theorem (Nagell–Lutz) and a listed `## Main results` entry of the project. Even though the *Lean proof body* is one line, the **mathematical content** (denominator of a point's `x`-coordinate is powerful) is a substantive arithmetic-geometry result, not a triviality.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line — **but kind is `theorem`, not `def`**.
One-liner verdict: **n/a (kind is theorem)**.

The one-liner heuristic targets `def`/`abbrev`/`structure` (defeq/diamond/API-name concerns). For a *theorem*, a one-line proof body is irrelevant to mathlib-worthiness — `Nat.add_comm`-grade results have one-line proofs. What matters is whether the *statement* is the right one to have. The statement here is a genuine, quotable theorem. Check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem elliptic curve torsion point integer coordinates denominator"                     | yes  | Torsion ⟹ integral; non-torsion: `den(x)=d²`, `den(y)=d³` | Wikipedia, Silverman; the denominator-is-a-square fact is exactly our statement |
|  2 | WebSearch (general/valuation form) | "reduction map elliptic curve denominator x-coordinate prime power v(x) even valuation rational point" | yes  | `E_n(K)={P : v(x(P))≤−2n}`; `v(x)` even on the kernel of reduction | the filtration making `v(x)` even = "every prime in den(x) has mult ≥2" |
|  3 | WebSearch (Silverman/formal group) | "Silverman elliptic curves formal group v(x) -2n valuation point reduction E1 filtration"             | yes  | `Eₙ(K)={(x,y): v(x)≤−2n, v(y)≤−3n}∪{∞}` | Silverman AEC VII §2 (formal groups) + VII §3 (Nagell–Lutz); the `−2n`/`−3n` is the `d²`/`d³` denominator |
|  4 | ChatGPT MCP                      | (unavailable this session — task notes ChatGPT MCP may be down; used extra WebSearch + Silverman PDF as fallback per skill) | n/a  | —                                | Substituted by channels 1–3 + 9–10 hitting Silverman directly |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "nagell"/"lutz"/"denominator"                                   | n/a  | (no references dir present for this project) | recorded n/a; the canonical source (Silverman AEC ch. VII) is well-known |
|  6 | nLab                             | "Nagell–Lutz" / "elliptic curve torsion" | n/a  | nLab has no dedicated Nagell–Lutz page | Not a category-theoretic concept; nLab elliptic-curve coverage is scheme-theoretic, not arithmetic-of-points |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical statement |
|  8 | Stacks Project (alg geom)        | "elliptic curve torsion integral point"                                                                | n/a  | Stacks has no arithmetic Nagell–Lutz | Stacks is scheme-theoretic foundations; this is Diophantine arithmetic over a PID — out of Stacks scope |
|  9 | MathOverflow / Math.StackExchange | (surfaced via WebSearch) Harvard "Nagell–Lutz, quickly" (Alpöge); AIMS essay; UChicago REU (Galperin) | yes  | Same `d²`/`d³` denominator statement | Multiple expository sources state exactly the powerful-denominator fact |
| 10 | recent arXiv (last 5 years)      | "Nagell–Lutz imaginary quadratic / number field" (arXiv:2509.07524); "denominators of rational points on elliptic curves" | yes  | Number-field generalizations of Nagell–Lutz with denominator bounds | confirms the *number-field* generalization (matches this project's `lutz_nagell_number_field`) is an active, literature-recognized direction |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (named theorem / valuation-filtration / Silverman formal-group); ChatGPT MCP recorded n/a-unavailable with WebSearch+primary-source substitution; local refs / nLab / nCatLab / Stacks / MO / arXiv each checked with reasons.

### Literature summary (Phase 3)

Concept identified as: **The Nagell–Lutz theorem** (specifically its denominator-structure / point-reduction half), Silverman *The Arithmetic of Elliptic Curves* VII.3 (Nagell–Lutz) resting on VII.2 (formal groups / the `Eₙ` filtration). Also: Lutz (1937), Nagell (1935); Cassels; Cremona's *Algorithms for Modular Elliptic Curves* ch. 3.
Sources agree on the standard form: **yes** — a finite-order point has integral coordinates, and more sharply, for *any* point the denominator of `x` is a perfect square `d²` and of `y` is `d³` (equivalently `v_q(x) < 0 ⟹ 2 ∣ v_q(x)`).
Most general standard form: stated over a Dedekind domain / DVR-localizations, or over a number ring `𝒪_K`. The cleanest local statement: for a discrete valuation `v` with `v(x) < 0`, `v(x)` is even and `v(y) = (3/2)v(x)` (point lies in `E₁`, governed by the formal group). The global "denominator is powerful" statement is the prime-by-prime aggregate.
Generality dimensions where the literature varies:
  - **base ring**: from `ℤ` (classical) → number ring `𝒪_K` → general Dedekind/Krull domain / DVR. The *denominator* statement (this theorem) needs only **UFD** (so primes ↔ valuations behave); the project's helper is correctly stated over a UFD.
  - **torsion hypothesis**: classical Nagell–Lutz assumes finite order; the *denominator-is-powerful* half (this theorem) needs **no** torsion hypothesis — it is purely about the reduction filtration. The project correctly isolates this (docstring: "property of ALL points").
Disagreement with the literature: **none.** The Lean statement is a faithful, slightly-more-elementary (no torsion needed) rendering of the standard denominator fact.

---

### Generality analysis — `LutzNagell.PID.den_powerful_of_on_curve`

Literature-standard form (from Phase 3): for any point on a Weierstrass curve over a Dedekind/Krull/UFD ring, `v_q(x) < 0 ⟹ v_q(x)` even (the `Eₙ` filtration). The "powerful denominator" phrasing is the standard idempotent aggregate.

| # | Parameter / hypothesis                | Current Lean form           | Literature-standard form       | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|-----------------------------|---------------------------------|---------------------|------------------------------------|
| 1 | `[IsPrincipalIdealRing R]`           | PID                         | UFD / Dedekind / Krull          | **YES**             | The actual proof delegates to `den_no_simple_prime_factor_of_on_curve`, whose section needs only `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`. The PID hypothesis here is **strictly stronger than the proof uses** — the `den_powerful` statement holds over any UFD. (PID is carried because `PIDMain.lean` bundles the integrality theorems, which *do* need PID.) |
| 2 | `[CharZero R]`                       | characteristic zero         | none                            | **YES** (already)   | The proof `omit`s `[CharZero R]` (line 69). The denominator fact is characteristic-independent. Carried only for the file's other (torsion-order) theorems. |
| 3 | `[IsDomain R]`                       | integral domain             | needed (for `IsFractionRing`)   | NO                  | `IsFractionRing R K` + `num`/`den` require a domain. Standard. |
| 4 | `W : WeierstrassCurve R`             | general Weierstrass curve   | same                            | NO                  | Already fully general (`a₁..a₆`, not short form). Matches literature. |
| 5 | hypothesis: `heq` (on-curve)         | affine equation over `K`    | same                            | NO                  | This is the defining hypothesis; cannot be weakened. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in its *typeclass assumptions*: PID + CharZero, where the theorem holds over any UFD with no characteristic constraint — and the project *already proves it that way*, via the UFD helper).
Number of weakening opportunities found: **2** (PID → UFD; drop CharZero — and both are *free*: the underlying helper already has the weak assumptions).
Proposed restatement (the form that should go to mathlib):

```lean
variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem den_powerful_of_on_curve (W : WeierstrassCurve R) {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆) :
    ∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) →
      q ^ 2 ∣ (IsFractionRing.den R x : R) :=
  fun _ hq hqd ↦ by_contra fun h ↦ den_no_simple_prime_factor_of_on_curve W heq hq hqd h
```

Cost of restatement: **CHEAP** — purely mechanical; the delegate already lives in the UFD section (`PIDDenominators.lean` variable block is `[UniqueFactorizationMonoid R]`). Moving this wrapper into that same section (or stating it with the weak typeclasses) costs nothing — the proof term is unchanged.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                  | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------|----------------------------------|
|  1 | "let R be a PID" preambles → typeclasses?                                                       | already  | already typeclass-based                                 | — |
|  2 | sequences/metric → filters/topology?                                                            | no       | no analytic content                                     | finite arithmetic statement |
|  3 | construct an object where universal property would characterise?                                | no       | it's a divisibility statement, not a construction       | — |
|  4 | set-with-closure-predicate → bundled substructure?                                              | no       | — | — |
|  5 | field/metric-specific → weaken typeclass to module/(semi)ring?                                  | **yes**  | weaken **PID → UFD** (Phase 4b #1)                       | the theorem then applies to `ℤ[i]`, `k[t]`, any poly ring / Gaussian-integer setting without re-proof — and over `ℚ`/`ℤ` it is unchanged |
|  6 | 1-categorical → higher-categorical?                                                              | no       | — | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid?                                                       | partial  | already generic over `R`; the only concrete pin is the strength of the typeclass, covered by #5 | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (same move as Phase 4b: state over a UFD).
  - Proposed mathlib-idiomatic restatement: the UFD-generality form above.
  - Cost: **CHEAP**.
  - Mathlib downstream this enables: applies to all UFD bases (`ℤ`, `𝒪_K` when a UFD, `k[t]`, `ℤ[i]`), giving the denominator-structure half of Nagell–Lutz at the right generality; composes with `IsFractionRing.num`/`den` and `UniqueFactorizationMonoid` API.
  - Real mathematical improvement: removes two unused hypotheses (PID, CharZero) that the proof does not consume — the maximally-general true statement, not the convenience specialization bundled for the rest of `PIDMain.lean`.

(Phase 4.5 Diamond/defeq risk: **n/a — declaration kind is theorem.**)

---

### Mathlib search-status: `LutzNagell.PID.den_powerful_of_on_curve`

[A] Lean-Finder       "Nagell Lutz", "torsion integral elliptic", "denominator x-coordinate elliptic curve"  → no hits (mathlib index has no Nagell–Lutz / point-denominator result)
[B] Loogle            `IsFractionRing.den _ _, Prime _, _ ^ 2 ∣ _` ; `WeierstrassCurve.Affine.Nonsingular → IsLocalization.IsInteger` → no hits (no lemma relating `den` of a coordinate to the curve equation)
[C] LeanSearch        "denominator of x-coordinate of point on elliptic curve is a perfect square" ; "torsion point of elliptic curve has integer coordinates" → no hits
[D] Grep mathlib src  `grep -rniE "nagell|lutz"` → only false positives (Kummer/Abel–Ruffini files matching "lutz" as an author-name substring); `IsFractionRing.den` in `Mathlib/AlgebraicGeometry/**` → **zero**; `IsLocalization.IsInteger` in `EllipticCurve/**` → **zero**
[E] Name pattern      browsed `Mathlib/AlgebraicGeometry/EllipticCurve/` (19 files): `Reduction.lean` covers integral/minimal *models* + good/bad reduction of the *discriminant* — nothing about *point* coordinates, denominators, or the `Eₙ` filtration. No `DivisionPolynomial` denominator lemma either.

Searched for both:
  - user's current form (PID): not in mathlib.
  - literature-standard / UFD form: not in mathlib.

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard form).** Mathlib has *no* Nagell–Lutz theorem, *no* point-integrality result, and *no* result on denominators of elliptic-curve point coordinates. The closest file, `EllipticCurve/Reduction.lean`, is about reduction of the *curve*, not arithmetic of *points*.

---

### Call sites — `LutzNagell.PID.den_powerful_of_on_curve`

Internal use count: **1** (within the project, excluding the declaring file's docstring line and the decl itself).
External-to-file callers: **1 distinct file region** — same file, the `NumberField` namespace.

| Caller file:line               | Usage pattern (one-line excerpt)                                                |
|--------------------------------|--------------------------------------------------------------------------------|
| PIDMain.lean:527 (`den_powerful_number_field`) | `PID.den_powerful_of_on_curve W heq q hq hqd` — the number-field (class number 1) specialization delegates directly to it |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?):
  - (none) — the workhorse `den_no_simple_prime_factor_of_on_curve` is used at PIDPrimeOrder.lean:99 and in `den_ne_prime_of_on_general_curve` (PIDDenominators.lean:181), but those use the *helper*, not this powerful-form wrapper. No competing re-derivation of the "∀ prime q, q ∣ den → q² ∣ den" form exists; this is the canonical statement of it.

Call-site reading: K = 1 internal use, and that one use is the genuine number-field generalization (a real consumer, not a bypass). The decl is the public "powerful denominator" API surface; `den_powerful_number_field` is its `𝒪_K` instantiation. This is a thin-but-real API layer, not dead code.

---

### Composition check (Phase 6)

Can `den_powerful_of_on_curve` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `fun q hq hqd ↦ by_contra fun h ↦ <mathlib lemma> …`
  - Mathlib decls used: none exist — the inner `den_no_simple_prime_factor_of_on_curve` is a **project** theorem (≈90 lines: clear denominators, three mod-`q` descent steps, `IsRelPrime` contradiction). There is no mathlib lemma about denominators of elliptic-curve point coordinates to chain to.
  - Result: **fails** (against mathlib).
  - Notes: the one-line body composes a *project* lemma, not mathlib primitives.

Attempt 2 (composition from the project's own helper):
  - `fun _ hq hqd ↦ by_contra fun h ↦ den_no_simple_prime_factor_of_on_curve W heq hq hqd h` — this *is* a 1-call composition, but on top of a **substantial project-internal theorem** that is itself the mathematical content and is *also* not in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib. Both this wrapper and its workhorse are absent from mathlib; the workhorse is real arithmetic (≈90-line valuation descent), not a mathlib composition. The pair `(den_no_simple_prime_factor_of_on_curve, den_powerful_of_on_curve)` is the unit that would be contributed.

---

## Verdict: `LutzNagell.PID.den_powerful_of_on_curve`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the Nagell–Lutz theorem; the "denominator of `x` is `d²`" / `v_q(x)` even fact is exactly this statement (Silverman AEC VII.2–VII.3). Standard, named, well-attested across ≥6 sources.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — carries `[IsPrincipalIdealRing R]` + `[CharZero R]`, but the proof (and the literature) only need **UFD**, no characteristic constraint. Phase 4c reaches the same conclusion (weaken PID→UFD).
- Mathlib search (Phase 5): not in mathlib in any form (5 methods + UFD form); mathlib has no Nagell–Lutz / point-integrality / point-denominator content at all.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the content is a ≈90-line valuation descent in the project's own `den_no_simple_prime_factor_of_on_curve`).

**Rationale:**

This is a genuine, named, literature-standard theorem (the denominator half of Nagell–Lutz) that mathlib entirely lacks — mathlib has no Nagell–Lutz, no torsion-implies-integral, and nothing about denominators of point coordinates; its only nearby file reduces the *curve*, not *points*. So a NO bucket is wrong: it is neither in mathlib (`NO-mathlib-has-it`) nor a ≤3-call mathlib composition (`NO-composable-from-mathlib`); the real content lives in the project's own ≈90-line `den_no_simple_prime_factor_of_on_curve`, which would be contributed alongside it. The result clearly belongs in mathlib.

It is **YES-but-generalise-first** rather than **YES-add-as-is** because Phase 4b found the statement strictly narrower than both the literature standard and what its own proof uses: the `[IsPrincipalIdealRing R]` and `[CharZero R]` assumptions are **unused** by the denominator argument (the delegated helper's section is `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`, and `CharZero` is `omit`ted). The theorem holds verbatim over any UFD with no characteristic hypothesis, and re-stating it that way is a **CHEAP** mechanical change (the proof term does not move). Per the skill's gate, YES-add-as-is is rejected when Phase 4b is STRICTLY NARROWER — the right action is to weaken first.

Reason for the generalisation:
  - **LITERATURE-WEAKENING** (Phase 4b): PID + CharZero is strictly narrower than the literature-standard UFD/Dedekind statement.
  - **MODERN-IDIOM** (Phase 4c #5): weakening PID→UFD is the maximally-general true form and applies to `ℤ[i]`, `k[t]`, etc. without re-proof.

Proposed restatement (the UFD form, proof unchanged):
```lean
variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every prime factor of `den_R(x)` of a point on a Weierstrass curve over a UFD `R`
has multiplicity at least 2 (the denominator of `x` is "powerful"). -/
theorem den_powerful_of_on_curve (W : WeierstrassCurve R) {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆) :
    ∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) →
      q ^ 2 ∣ (IsFractionRing.den R x : R) :=
  fun _ hq hqd ↦ by_contra fun h ↦ den_no_simple_prime_factor_of_on_curve W heq hq hqd h
```
Estimated cost of regeneralisation: **CHEAP** (the delegate already lives under `[UniqueFactorizationMonoid R]`; just state this wrapper in the same section).

Mathlib downstream this enables:
  - Over `ℤ`/`ℚ` it is the classical denominator statement, unchanged; over a UFD `𝒪_K` (or `ℤ[i]`, `k[t]`) it gives the same result with no extra work — the right generality for an eventual mathlib Nagell–Lutz development.
  - Composes with `IsFractionRing.num`/`den` and `UniqueFactorizationMonoid` divisibility API.
  - Old form blocked applying the result to any non-PID UFD base; the weakened form does not.

Note: the genuine mathematical content to ship is the **pair** — `den_no_simple_prime_factor_of_on_curve` (the workhorse, already correctly UFD-general) **plus** this `den_powerful_of_on_curve` quantified packaging. They should go to mathlib together as one PR.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/NagellLutz.lean` (new file), or extend `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` (which already imports `IsFractionRing` and deals with integral models — a natural neighbour).
Proposed PR title: `feat(AlgebraicGeometry/EllipticCurve): denominators of points are powerful (Nagell–Lutz, integrality half)`
PR grouping: ship together with `den_no_simple_prime_factor_of_on_curve` (the proof content) and ideally the integrality corollary `den_dvd_of_order_two` family as a small Nagell–Lutz series.

Next action: run `/generalise LutzNagell.PID.den_powerful_of_on_curve` (it will tension against the UFD/Dedekind literature form and confirm the PID/CharZero drop), then `/cleanup` the file, then open the PR. Because the proof term is unchanged under the weakening, the generalisation is low-risk.
