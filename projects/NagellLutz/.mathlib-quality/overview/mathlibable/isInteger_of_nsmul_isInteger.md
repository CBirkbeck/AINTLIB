# /mathlibable report — `LutzNagell.PID.isInteger_of_nsmul_isInteger`

> Invocation: `/overview` Step-9 mathlibable assessment, single declaration, full 10-phase
> workflow run via the `mathlib-quality:mathlibable` skill.

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief; `.lake/build/lib` empty). Reasoned from source + the pinned `.lake/packages/mathlib` tree.
- decl `LutzNagell.PID.isInteger_of_nsmul_isInteger`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:80` (theorem head; `:= by`-proof body opens at line 86 — the `:93` in the task brief is the file's closing `end LutzNagell`, the line after the decl's `end PID`).
- kind:                      theorem
- has sorry:                 no
- true qualified name:       `LutzNagell.PID.isInteger_of_nsmul_isInteger` — VERIFIED. File opens `namespace LutzNagell` (line 15) then `namespace PID` (line 16); base name `isInteger_of_nsmul_isInteger`. Matches the task brief's parsed name exactly.
- module docstring summary:  "Integral multiple implies integral point (over UFDs)": if `n • P` has integral affine coordinates on a Weierstrass curve over `K = Frac(R)`, then `P` already has integral affine coordinates. Explicitly a **generalization of `GeneralIntegralMultiple.lean` from ℤ/ℚ to a UFD `R`**.

---

### Statement (Phase 1)

`LutzNagell.PID.isInteger_of_nsmul_isInteger` is a theorem stating the following:

Let `R` be a unique factorization domain with fraction field `K`, and let `W : WeierstrassCurve R`
be a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ R`. Let
`curveK R K W := W.map (algebraMap R K)` be its base change to `K`. Let `P = (x, y)` be a nonsingular
affine point on `curveK R K W`, and `n` a nonzero integer (nonzero also as an element of `R`) such
that `n • P = P' = (x', y')` is also a nonsingular affine point. If `P'` has **integral** affine
coordinates (`x', y' ∈ range(algebraMap R K)`, i.e. `IsLocalization.IsInteger R x'` and `… y'`), then
`P` has integral affine coordinates (`x, y ∈ range(algebraMap R K)`). This is the **integral-descent
step** of the Nagell–Lutz theorem, stated over a UFD base: integrality of a nonzero multiple forces
integrality of the point.

Variables / typeclasses involved (Lean side):
- `{R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — the UFD base ring.
- `{K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` — its fraction field.
- `(W : WeierstrassCurve R)` — a general (long) Weierstrass curve over `R`.
- `{x y : K}` — the affine coordinates of `P`, a priori only in `K`.
- `{n : ℤ}` — the multiplier (the `ℤ`-action on the Mordell–Weil group).
- `{x' y' : K}` — the affine coordinates of `P' = n • P`.

Hypotheses (Lean side):
- `(hns : (curveK R K W).toAffine.Nonsingular x y)` — `P` is a nonsingular point.
- `(hn : n ≠ 0)` — nonzero multiplier (in ℤ).
- `(hn_R : (n : R) ≠ 0)` — the image of `n` in `R` is nonzero (needed because `R` may have positive characteristic; over ℤ this follows from `hn`).
- `(hns' : (curveK R K W).toAffine.Nonsingular x' y')` — `P'` is nonsingular.
- `(hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')` — `n • P = P'`.
- `(hx' : IsLocalization.IsInteger R x')` — `x'` is integral over `R` (in the image of `algebraMap R K`).
- `(_hy' : IsLocalization.IsInteger R y')` — `y'` integral. **Unused** (the `_` prefix): `y`-integrality of `P` is re-derived from `x`-integrality via the curve equation, so `y'`-integrality is never consumed.

Conclusion (math): `x ∈ R` and `y ∈ R` (more precisely, both lie in `range(algebraMap R K)`).

Conclusion (Lean): `IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`.

Proof shape (≈4 lines): destructure `hx' = ⟨c, hc⟩` to name the integer `c : R` with `algebraMap R K c = x'`;
apply the x-coordinate descent lemma `x_isInteger_of_nsmul_x_isInteger W hns hn hn_R hns' hnP hc` to get
`x ∈ R` (via `x₀`); then pair it with the y-from-x lemma
`y_isInteger_of_x_isInteger_on_curve W ((curveK_equation_iff R K W x y).mp hns.left) hx₀`. The substantive
content lives in the two called lemmas:
- `x_isInteger_of_nsmul_x_isInteger` (same file, `:65`) — uses the multiplication-by-`n` x-coordinate
  identity `x' · ΨSqₙ(x) = Φₙ(x)` (`x_coord_nsmul_eq`, `:39`, a ≈21-line Jacobian-coordinate proof) plus
  monicity of `Φₙ − C c · ΨSqₙ` (`monic_Φ_sub_smul_ΨSq`, `:26`) plus mathlib's integral-root theorem.
- `y_isInteger_of_x_isInteger_on_curve` (`PIDPrimeOrder.lean:37`) — `y` is a root of the monic
  `X² + C c₁ X + C c₀ ∈ R[X]` from the curve equation, again by the integral-root theorem.

---

### Size classification (Phase 2a)

Verdict: BIG (borderline).
Reason: this is the **integral-descent structural step of a person-named theorem** (Nagell–Lutz). It is a
`theorem` (introduces no new structure), but it is one of the load-bearing lemmas of a named result, so by
the skill's "named after a person" criterion it is treated as BIG. Its call sites (`PIDMain.lean:100, 128`)
are inside the two integrality cases of the UFD-track Nagell–Lutz main theorem.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-line check is **n/a**. (Body is ≈4 substantive lines:
two `obtain`s and one `exact ⟨…, …⟩` over two delegated lemma calls — multi-line, not a glue/`rfl` lemma.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem elliptic curve torsion integral point division polynomial proof if nP integral then P integral" | yes  | `x(nP) = φₙ/ψₙ²`; `φₙ` monic of degree `n²` in x; "if `n·(x,y)` integral then `x,y ∈ ℤ`" | Wikipedia; Alpoge "Nagell-Lutz, quickly" (Harvard); Galperin (UChicago REU); Li (Michigan REU); en-academic; HandWiki — all give the monic-numerator descent route via division polynomials. Silverman AEC VIII cited as the standard reference. |
|  2 | WebSearch (general form)         | "Nagell-Lutz theorem generalization Dedekind domain ring of integers number field elliptic curve torsion integrally closed" | yes  | same descent lemma; base = ring of integers `𝒪_K` of a number field / global field | Wikipedia: "generalizes to **arbitrary number fields** and more general cubic equations"; Springer *manuscripta math* "Torsion points on elliptic curves over a **global field**"; arXiv:2509.07524 (imaginary quadratic, class number one). Confirms ℤ/ℚ is a specialisation, not the ceiling. |
|  3 | WebSearch (named-after / function-field generalisation)| "Nagell-Lutz theorem elliptic curve function field k(t) algebraic function field torsion integrality division polynomial" | yes  | "generalized and strengthened versions exist both for K an algebraic **number field** and where K is an algebraic **function field**" | confirms the base ring runs from ℤ → 𝒪_K → function-field rings (e.g. `k[t]`), i.e. exactly the UFD/Dedekind territory the project's `R` covers; "over number fields a weaker version — denominator cannot be too large" (that is the *prime-order* refinement, a different project lemma, not this descent step). |
|  4 | ChatGPT MCP                      | (intended) "Maximal generality of the base ring for the descent argument: integrally closed vs UFD? Is ℤ/ℚ a pure specialisation of the UFD form?" | n/a (server down) | —                        | **MCP attempted; Codex backend errored out** (consistent with the task brief: "ChatGPT MCP may be down — use fallbacks"). Substituted by (a) the literature rows 1–3, (b) direct mathematical analysis: the only ring-theoretic fact the descent uses is "a root in `Frac R` of a monic polynomial over `R` lies in `R`", which is *precisely* the definition of `R` integrally closed in `Frac R`; a UFD is integrally closed, so UFD suffices (and is what mathlib's integral-root theorem is stated for), and (c) the project's own sorry-free UFD proof, which empirically answers the generality question — the ℤ/ℚ twin's whole proof is a one-line call to this UFD lemma. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/`                                    | n/a  | (no references dir)                | `projects/NagellLutz/.mathlib-quality/references/` absent; `refs/` absent (the gitignored local PDF store is not symlinked in this checkout). Recorded n/a. |
|  6 | nLab                             | "Nagell-Lutz theorem" / "elliptic curve torsion"                                                       | n/a  | —                                | nLab has no Nagell–Lutz page; the descent lemma is an arithmetic, not categorical, statement. n/a — not a categorical concept. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "elliptic curve torsion integral point"                                                                | n/a  | —                                | Stacks develops the scheme-theory of elliptic curves but not the arithmetic of rational/integral torsion or Nagell–Lutz. n/a. |
|  9 | MathOverflow / Math.StackExchange| "Nagell-Lutz nP integral implies P integral division polynomial generality"                            | yes  | confirms the standard route; threads note the argument needs only an integrally-closed / DVR base | MO/MSE Nagell–Lutz threads reproduce the monic-numerator + bounded-denominator argument; the integrality (vs denominator-bound) half needs only that the base is integrally closed. |
| 10 | recent arXiv (last 5 years)      | "Nagell-Lutz theorem imaginary quadratic / number field / global field generalization"                | yes  | arXiv:2509.07524 (2025) "Nagell–Lutz for Imaginary Quadratic Fields, class number one"; Springer "global field" | the theorem is **actively generalised** beyond ℤ/ℚ to number-field and function-field bases — ℤ/ℚ is a specialisation. |

Protocol pass: WebSearch ran 3 distinct queries at different generality levels (specific descent form / number-field
generalisation / function-field generalisation) ✓; ChatGPT MCP attempted, server down, documented with substitute ✓;
local refs checked (absent → n/a) ✓; nLab checked ✓; Stacks / nCatLab / MO / arXiv each checked or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: the **integral-descent step of the Nagell–Lutz theorem** — "if `n • P` is integral then
`P` is integral" — proved via the multiplication-by-`n` x-coordinate formula `x([n]P) = φₙ(P)/ψₙ(P)²` (mathlib
names: `Φₙ`/`ΨSqₙ`), with `Φₙ` monic in x of degree `n²` and `deg Φₙ > deg ΨSqₙ`, reducing `x`-integrality to
the integral-root theorem for monic polynomials, and `y`-integrality to the same via the curve equation.

Sources agree on the standard form: yes. Every treatment (Silverman AEC VIII; Washington; the REU notes
Galperin/Li; Alpoge "Nagell-Lutz, quickly"; Wikipedia; HandWiki; PlanetMath) uses the same division-polynomial
denominator route.

Most general standard form: the argument needs only that the base ring is **integrally closed in its fraction
field** (so a fraction-field element that is a root of a monic polynomial over the ring lies in the ring). It is
stated over ℤ/ℚ for the classical Nagell–Lutz; the literature (Wikipedia "arbitrary number fields"; Springer
"global field"; arXiv:2509.07524; the function-field version) generalises it to rings of integers of number
fields, to function-field rings, and to DVRs. The project proves the **UFD** version (`R` a
`UniqueFactorizationMonoid`, `K = Frac R`) — which is the **mathlib-natural realisation**, because mathlib's
integral-root theorem `isInteger_of_is_root_of_monic` is stated for exactly a UFD `A` with `IsFractionRing A K`.

Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → ring of integers of a number field / global field → DVR → function-field ring `k[t]`.
    Mathematically-maximal standard for *this* step = integrally closed domain; mathlib-natural realisation = UFD
    (UFD ⊂ integrally closed; mathlib's integral-root API stops at UFD).
  - integrality predicate: "`∈ ℤ`" / "`∈ 𝒪_K`" → "in the image of `algebraMap R K`" = `IsLocalization.IsInteger R`.

Disagreement with the literature: none. The project's Lean statement is the integrally-closed/UFD form the
literature points at; the classical ℤ/ℚ statement is its `R := ℤ` instance.

---

### Generality analysis — `LutzNagell.PID.isInteger_of_nsmul_isInteger`

Literature-standard form (from Phase 3): the descent lemma over a base ring integrally closed in its fraction
field. Mathlib-natural realisation: `R` a UFD, `K = Frac R`, integrality = `IsLocalization.IsInteger R` — **which
is exactly the current Lean form.**

| # | Parameter / hypothesis                | Current Lean form                                | Literature-standard form                           | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|--------------------------------------------------|----------------------------------------------------|---------------------|----------------------------------|
| 1 | base ring of the curve `W`            | `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` | integrally closed domain (UFD as mathlib realisation) | MARGINAL (see note) | The only ring-theoretic fact used is "root of monic over `R` in `Frac R` ⟹ in `R`" = `R` integrally closed. A UFD is integrally closed, so the current form is a hair stronger than the bare minimum — BUT mathlib's `isInteger_of_is_root_of_monic` is itself only stated at UFD generality, so the UFD hypothesis is the **right mathlib-realisable ceiling today**. Weakening to `IsIntegrallyClosed` would first require generalising mathlib's integral-root theorem (not currently available as `isInteger_of_is_root_of_monic`). |
| 2 | coordinate field                      | `[Field K] [Algebra R K] [IsFractionRing R K]`   | `K = Frac R`                                        | NO                  | Already the fraction field via the canonical `IsFractionRing` typeclass — maximally general (any model of `Frac R`). |
| 3 | integrality predicate                 | `IsLocalization.IsInteger R x` (`∈ range (algebraMap R K)`) | "lies in `R` / `𝒪_K`"                         | NO                  | Already the canonical mathlib predicate; matches the literature's "integral coordinate". |
| 4 | `[DecidableEq K]`                      | present                                           | not mathematically needed                          | YES (cosmetic)      | Decidable equality of a field is classical; this instance is a residue of the Jacobian/Affine point machinery in the proof. A `Classical`/`open Classical` cleanup could likely drop it, but it is not a *generality* defect, just a tidy-up. |
| 5 | `n ≠ 0` AND `(n : R) ≠ 0`             | both carried separately                          | `n ≠ 0` with `n` invertible-enough in `R`          | NO (essential)      | Both are essential to `natDegree_ΨSq`/`leadingCoeff_Φ`/monicity. Over a general UFD of positive characteristic the second does NOT follow from the first, so carrying it separately is correct (over ℤ it would follow). |
| 6 | unused hypothesis `_hy'`              | `IsLocalization.IsInteger R y'` (unused)          | —                                                  | DROP                | The `_`-prefixed `_hy'` is never used (the proof re-derives `y ∈ R` from `x ∈ R` via the curve equation). Should be dropped on the way to mathlib — a signature cleanup, not a generalisation. |

**This declaration IS the generalisation target the project's own ℤ/ℚ assessment recommends.** The companion
`/mathlibable` report for the ℤ/ℚ twin `integral_of_nsmul_integral_general`
(`.mathlib-quality/overview/mathlibable/integral_of_nsmul_integral_general.md`) concluded `YES-but-generalise-first`
and proposed, verbatim, *this very declaration* as the restatement to upstream. So at the UFD/`IsFractionRing`/
`IsInteger` level, the current form is already the recommended mathlib form.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (at the mathlib-realisable ceiling).
Number of weakening opportunities found: 0 substantive (rows 4 and 6 are cosmetic signature tidy-ups — drop
`[DecidableEq K]` if cheap, drop the unused `_hy'` — neither is a mathematical generalisation; row 1's
`IsIntegrallyClosed` weakening is blocked behind generalising mathlib's own integral-root theorem and is not a
cheap in-scope move).
Proposed restatement: none required for generality. Optional signature cleanup before a PR: drop the unused
`(_hy' : IsLocalization.IsInteger R y')` parameter; investigate removing `[DecidableEq K]`.

Cost of (optional) cleanup: CHEAP — mechanical signature edit; the proof body never touches `_hy'`.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | already fully typeclass-driven (`UniqueFactorizationMonoid`, `IsFractionRing`, `Nonsingular`) | — |
|  2 | sequences/metric → filters/topological?                                                                  | no       | purely algebraic; no topology/limits | — |
|  3 | construct an object → universal-property class?                                                          | no       | it is a Prop, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | n/a | — |
|  5 | vector-space/metric/field-specific → weaken via typeclass hierarchy?                                      | no (already done) | the base ring is **already** the general `UniqueFactorizationMonoid R` with `IsFractionRing R K`; this is the endpoint of the very weakening Q5 asks for — the ℤ/ℚ twin is the un-weakened form, this is the weakened one | — |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/monoid?                                                       | no       | the multiplier `n` is correctly `ℤ` (the `ℤ`-action on the Mordell–Weil group); generalising `n` past ℤ is not meaningful | — |
|  8 | concrete-object proof betrays an abstract form (named identifier vanishes after first unfolding)?         | no       | the proof is already abstract over `R`/`K`; no concrete object is unfolded away — the statement is the general one | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no — the declaration is already in the modern, maximally-general mathlib idiom.** It is
the *result* of applying the Bourbaki-2.0 weakening (ℤ → UFD `R`, ℚ → `Frac R`, `∃ cast` → `IsLocalization.IsInteger R`)
to the classical statement; the ℤ/ℚ twin is the pre-modernisation form. There is no further contemporary
reformulation that is a real organisational improvement (row 1 `IsIntegrallyClosed` is gated behind a mathlib
gap, not an idiom choice). One-line reason: this decl is the idiomatic target, not a candidate for further
idiom-shifting.

---

### Diamond / defeq risk — `LutzNagell.PID.isInteger_of_nsmul_isInteger`

n/a — declaration kind is `theorem` (Phase 4.5 skipped; theorems introduce no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `LutzNagell.PID.isInteger_of_nsmul_isInteger`

[A] Lean-Finder       — (index unavailable in this environment)                                  n/a: reasoned from grep over `.lake/packages/mathlib`
[B] Loogle            `WeierstrassCurve.Φ`/`ΨSq` ↔ `Affine.Point` smul; `IsInteger` of nsmul     no hits — mathlib never relates `n • P` (group law) to `Φ`/`ΨSq`/integrality
[C] LeanSearch        "if n times a point on an elliptic curve is integral then the point is integral over a UFD"  no hits
[D] Grep mathlib src  `Nagell`, `Lutz`, `nsmul.*[Ii]nteger`, `[Ii]nteger.*nsmul`, `Φ`+`Affine.Point`+`smul`, `smulEval`, `zsmul_eq_smulEval` in `Mathlib/`  no relevant hits
[E] Name pattern      `isInteger_of_nsmul`, `integral_of_nsmul`, division-poly smul formula        no hits in mathlib

Detailed grep evidence (this run, over `.lake/packages/mathlib`):
- `grep -rli "nagell\|lutz" Mathlib/` → the only "Lutz" hits are the *author* Patrick Lutz (FieldTheory copyright
  headers: AbelRuffini, PrimitiveElement, Kummer*, Galois, Normal); "Nagell" matches nothing relevant.
  **Nagell–Lutz is not in mathlib.**
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` define `Φ`, `ΨSq`, `ψ`,
  `preΨ` and their degrees/leading coeffs (`natDegree_Φ`, `natDegree_ΨSq`, `leadingCoeff_Φ` are all present in
  `Degree.lean`). These are the *only* two mathlib files mentioning both `Φ` and `Affine.Point`, and they contain
  **no `smul`/`nsmul`/`zsmul` bridge** to the point group law. Mathlib has the division polynomials and the
  `Affine.Point` group law **separately**; it does NOT have the bridge `x(n • P) · ΨSqₙ(x) = Φₙ(x)`. That bridge
  is precisely the project's `x_coord_nsmul_eq` (`PIDIntegralMultiple.lean:39`, ≈21 lines of Jacobian-coordinate
  reasoning via `zsmul_eq_smulEval`, `smulEval`, `X_eq_of_equiv`) — `smulEval`/`zsmul_eq_smulEval` do not exist in
  mathlib at all (only the *generic* `X_eq_of_equiv` Jacobian lemma exists, `Jacobian/Basic.lean:191`, which the
  project reuses).
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is purely about integer-indexed sequences
  (`normEDS`, `preNormEDS`, `complEDS`, …) — **no `Affine.Point`, no x-coordinate, no `IsInteger`, no
  `Nonsingular`.** (The project even *forks* this file plus the two DivisionPolynomial files into
  `LutzNagell/{EllipticDivisibilitySequence,DivisionPolynomial,DivisionPolynomialDegree}.lean` — project copies
  that import the project's EDS to avoid `normEDS`/`complEDS` name clashes. So the project's `W.Φ`/`W.ΨSq` are
  project copies, but mathlib has definitional equivalents.)
- The only mathlib building block actually used: `Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`
  `isInteger_of_is_root_of_monic` (**Integral root theorem**), stated for `{A K} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [Field K] [Algebra A K] [IsFractionRing A K]` (header line 61) — **exactly** the
  generality of the project's PID track. (Confirmed: mathlib does NOT carry a strictly-more-general
  `IsIntegrallyClosed` variant of this corollary under that name.)

Searched for both: the project's UFD form AND the classical ℤ/ℚ form (and the intermediate number-field form).
Neither the descent lemma nor its smul-formula prerequisite is in mathlib in any of these forms.

Concluded: **not in mathlib** (all methods exhausted, all generality levels). Mathlib has only the final building
block (`isInteger_of_is_root_of_monic`) and the generic Jacobian lemma `X_eq_of_equiv`; the elliptic-curve-specific
content — the smul→division-polynomial formula and the descent lemma built on it — is absent.

---

### Call sites — `LutzNagell.PID.isInteger_of_nsmul_isInteger` (Phase 6.0)

Internal use count: **3** (within the project, excluding the declaring file).
External-to-file callers: 2 distinct files (`PIDMain.lean`, `GeneralIntegralMultiple.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                                                  |
|--------------------------------|-----------------------------------------------------------------------------------|
| PIDMain.lean:100               | `exact isInteger_of_nsmul_isInteger W hpt (Int.natCast_ne_zero.mpr hk_pos.ne') …` (prime-order-divides case) |
| PIDMain.lean:128               | `exact isInteger_of_nsmul_isInteger W hpt (Int.natCast_ne_zero.mpr hk_pos.ne') …` (four-divides-order case)  |
| GeneralIntegralMultiple.lean:89| `obtain ⟨hxi, hyi⟩ := PID.isInteger_of_nsmul_isInteger W hns hn (by exact_mod_cast hn) hns' hnP` (ℤ/ℚ twin delegates here) |

All three call sites are live and load-bearing: the two in `PIDMain.lean` are inside the integrality cases of the
UFD-track Nagell–Lutz main theorem; the one in `GeneralIntegralMultiple.lean` is the ℤ/ℚ twin's *entire* proof
body (the twin adds zero content over this lemma). **K = 3, no inline re-derivation, used across two files and as
the engine of its own ℤ/ℚ specialisation → strong "real API node" composability signal → leans YES.**

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?):
  - (none) — every consumer that needs "nP integral ⟹ P integral" calls this lemma. The ℤ/ℚ twin
    `integral_of_nsmul_integral_general` is NOT an inline re-derivation; it is a thin `isInteger_int_iff` wrapper
    that *delegates to* this lemma. So this is the canonical, non-bypassed implementation.

---

### Composition check (Phase 6)

Can `LutzNagell.PID.isInteger_of_nsmul_isInteger` be derived from mathlib in ≤3 chained calls?

Attempt 1: `isInteger_of_is_root_of_monic` (mathlib) applied to `Φₙ − C c · ΨSqₙ`, then `…` for `y`.
  - Mathlib decls used: `isInteger_of_is_root_of_monic` (×2, for `x` and `y`).
  - Result: **fails as a standalone ≤3-call composition.** `isInteger_of_is_root_of_monic` needs, as a hypothesis,
    that `x` is a root of that monic polynomial — i.e. `x' · ΨSqₙ(x) = Φₙ(x)`. That equation is the
    multiplication-by-`n` x-coordinate formula, which is **not in mathlib** (no smul↔division-polynomial bridge).
    Producing it requires the ≈21-line `x_coord_nsmul_eq` (Jacobian coordinates: `zsmul_eq_smulEval`, `smulEval`,
    `X_eq_of_equiv`, then the `evalEval → Φ/ΨSq` conversions `evalEval_φ_eq_eval_Φ`,
    `evalEval_Ψ_sq_eq_eval_ΨSq`). It also needs monicity (`monic_Φ_sub_smul_ΨSq`, a degree computation using
    `natDegree_Φ`/`leadingCoeff_Φ`/`natDegree_ΨSq`) and the `y`-from-`x` step
    (`y_isInteger_of_x_isInteger_on_curve`, itself another `isInteger_of_is_root_of_monic` application after
    extracting a monic quadratic from the curve equation). This is a genuine multi-lemma development across three
    files, not a 1–3 call composition.
  - Notes: the single mathlib call `isInteger_of_is_root_of_monic` does the *last* step of each half, but the
    inputs it requires are exactly the missing-from-mathlib content.

(Note: the lemma *is* a ≤3-call composition of **in-project** lemmas — `x_isInteger_of_nsmul_x_isInteger` +
`y_isInteger_of_x_isInteger_on_curve` + the `curveK_equation_iff`/`obtain` plumbing. But composability is judged
against **mathlib**, not against the project's own not-yet-upstreamed lemmas. The mathlib building blocks alone do
not give it.)

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The substantive content (the smul→`Φ`/`ΨSq` x-coordinate
formula) is missing from mathlib; only the two final integral-root steps are mathlib one-liners.

---

## Verdict: `LutzNagell.PID.isInteger_of_nsmul_isInteger`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): standard integral-descent step of Nagell–Lutz; the natural/maximal base for *this
  step* is an integrally-closed domain, and the literature actively generalises Nagell–Lutz to number-field /
  function-field bases (Wikipedia "arbitrary number fields"; Springer "global field"; arXiv:2509.07524). The
  project's UFD form is the mathlib-natural realisation of that ceiling.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** at the mathlib-realisable ceiling — 0 substantive
  weakenings. The base ring is already the general `UniqueFactorizationMonoid R` with `IsFractionRing R K`;
  `IsLocalization.IsInteger R` is already the canonical integrality predicate; `[DecidableEq K]` and the unused
  `_hy'` are cosmetic signature tidy-ups, not generalisations. Phase 4c: already in the modern idiom (it is the
  *output* of the ℤ→UFD modernisation, with the ℤ/ℚ twin as the un-modernised input). The companion ℤ/ℚ report
  proposes *this declaration verbatim* as its `YES-but-generalise-first` target.
- Mathlib search (Phase 5): **not in mathlib** in any form; the smul→division-polynomial bridge is absent (the two
  DivisionPolynomial files and the EDS file carry no point-group ↔ `Φ`/`ΨSq` link), only the final
  `isInteger_of_is_root_of_monic` exists (and at exactly UFD generality).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the missing piece is the multiplication-by-`n`
  x-coordinate formula, a real ≈21-line lemma); call-sites K = 3 across two files, no inline re-derivation.

**Rationale (1–2 paragraphs):**

This declaration is a genuine, missing-from-mathlib result — the integral-descent step of the Nagell–Lutz theorem
— stated at the **right** level of generality for mathlib. Unlike its ℤ/ℚ twin (which the project's own overview
classifies as a "special-case of PID" and whose `/mathlibable` report returned `YES-but-generalise-first` pointing
at *this* lemma), the PID/UFD form here is already maximally general against the mathlib-realisable ceiling: the
base is the general `UniqueFactorizationMonoid R`, the field is the canonical `Frac R` via `IsFractionRing`, and
integrality is the canonical `IsLocalization.IsInteger R`. The descent argument uses ℤ/ℚ nowhere; the single
ring-theoretic fact it relies on — "a root in `Frac R` of a monic polynomial over `R` lies in `R`" — is exactly
"`R` integrally closed", and mathlib packages it (for a UFD) as `isInteger_of_is_root_of_monic`, whose typeclass
header is verbatim the project's UFD hypotheses. So the UFD form is not over- or under-general: it is the precise
generality at which both the literature's descent argument and mathlib's existing integral-root API live.

The substantive content mathlib lacks is the multiplication-by-`n` x-coordinate identity
`x(n • P) · ΨSqₙ(x) = Φₙ(x)` connecting the `Affine.Point` group law to the division polynomials `Φ`/`ΨSq`. This
is a concrete, nameable gap: mathlib has the division polynomials (`DivisionPolynomial/{Basic,Degree}.lean`, with
`natDegree_Φ`/`leadingCoeff_Φ`/`natDegree_ΨSq` all present) and it has the `Affine.Point`/`Jacobian.Point` group
law, but it has **no lemma relating a scalar multiple of a point to its division-polynomial coordinates** — a
`grep` for `smul`/`nsmul`/`zsmul` across the two `Φ`/`ΨSq` files returns nothing, and `smulEval`/
`zsmul_eq_smulEval` (the project's bridge machinery) do not exist in mathlib. That bridge is the canonical link
between `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial` and the point group law, and torsion /
height / EDS results all want it. Because the descent lemma is NOT-COMPOSABLE from mathlib (the bridge is real
≈21-line content, not a ≤3-call glue), MAXIMALLY GENERAL (Phase 4b), and absent from mathlib in every form (Phase
5), the verdict gate selects **YES-add-as-is**. (Note on Phase-7 gate: YES-add-as-is is permitted precisely
because Phase 4b returned MAXIMALLY GENERAL — the STRICTLY-NARROWER finding that forced the ℤ/ℚ twin to
`YES-but-generalise-first` does *not* apply here; this lemma is the generalisation.)

WHY add it (refactor-actionable):
  - **New content mathlib is missing:** the integral-descent step of Nagell–Lutz over a UFD, and — more
    fundamentally — the multiplication-by-`n` x-coordinate bridge `x(n • P) · ΨSqₙ(x) = Φₙ(x)` it rests on.
  - **The specific gap:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` define
    and compute the degrees of `Φ`/`ΨSq` but contain **zero** lemmas connecting them to `Affine.Point` scalar
    multiplication (verified by grep: no `smul`/`nsmul`/`zsmul` in those files); `Mathlib/NumberTheory/`
    `EllipticDivisibilitySequence.lean` is sequence-only (no points). The canonical "what division polynomials are
    *for*" lemma — the multiplication-by-`n` denominator formula on actual points — is the missing API. Nagell–Lutz
    itself is entirely absent (only the author "Patrick Lutz" appears).
  - **How it composes:** with the bridge in place, `isInteger_of_is_root_of_monic` (already in mathlib at UFD
    generality) immediately gives x-integrality; the curve equation + the same integral-root theorem gives
    y-integrality. Downstream, the bridge unlocks torsion-point integrality over any UFD — ℤ (classical
    Nagell–Lutz), `ℤ[i]` and other rings of integers of number fields (arXiv:2509.07524 territory), and `k[t]`
    (function-field elliptic curves / EDS over function fields) — and composes with the `IsLocalization.IsInteger`
    / `IsFractionRing` / `IsIntegrallyClosed` APIs.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Point.lean` (new) for the
smul-formula bridge `x_coord_nsmul_eq` and the monicity helper `monic_Φ_sub_smul_ΨSq`; the descent lemma
`isInteger_of_nsmul_isInteger` (with its x-step and y-step) either there or in a new
`Mathlib/NumberTheory/EllipticCurve/NagellLutz.lean`.

Proposed PR title: "feat(AlgebraicGeometry/EllipticCurve): multiplication-by-n x-coordinate formula and the
Nagell–Lutz integral-descent lemma over a UFD".

PR grouping (REQUIRED — ship as one coherent contribution, NOT one decl at a time):
  - `x_coord_nsmul_eq` (the smul → `Φ`/`ΨSq` x-coordinate bridge) — the keystone new API.
  - `monic_Φ_sub_smul_ΨSq` (monicity of `Φₙ − C c · ΨSqₙ`).
  - `x_isInteger_of_nsmul_x_isInteger` (x-integrality descent).
  - `y_isInteger_of_x_isInteger_on_curve` (y-from-x on the curve; `PIDPrimeOrder.lean:37`).
  - `isInteger_of_nsmul_isInteger` (this decl — the packaged descent step).
  - Their `General*` (ℤ/ℚ) twins are **NOT** separate contributions — they are the `R := ℤ` specialisations and
    should not be upstreamed (the project's own overview marks them "special-case of PID").

Pre-PR checklist before opening:
  - [ ] `/generalise LutzNagell.PID.isInteger_of_nsmul_isInteger` — confirm no cheap further weakening (in
        particular, check whether mathlib now has, or the PR should also add, the `IsIntegrallyClosed` form of
        `isInteger_of_is_root_of_monic` so the base could drop from UFD to integrally-closed; if not cheap, ship
        UFD).
  - [ ] Drop the unused `(_hy' : IsLocalization.IsInteger R y')` parameter; investigate removing `[DecidableEq K]`
        via `Classical`.
  - [ ] `/cleanup` the PID-track files (`PIDIntegralMultiple.lean`, `PIDPrimeOrder.lean`, `PIDCurve.lean`,
        `ZSMul.lean`, the project's `DivisionPolynomial*` copies) — full audit + diff gates — and reconcile the
        project's forked `Φ`/`ΨSq`/EDS copies back against mathlib's originals (the fork exists only to dodge
        `normEDS` name clashes; for a mathlib PR the originals are used).
  - [ ] Pick a mathlib reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the
        DivisionPolynomial / EDS author David Kurniadi Angdinata is the natural reviewer).

---

## Next step

Open a mathlib PR for the **UFD-general** Nagell–Lutz integral-descent step
(`LutzNagell.PID.isInteger_of_nsmul_isInteger`) bundled with its prerequisite
multiplication-by-`n` x-coordinate bridge `x(n • P) · ΨSqₙ(x) = Φₙ(x)` (`x_coord_nsmul_eq`), the monicity helper,
the x-step, and the y-step — as one coherent contribution. First run
`/generalise LutzNagell.PID.isInteger_of_nsmul_isInteger` to confirm UFD is the right ceiling (vs a possible
`IsIntegrallyClosed` weakening gated behind generalising mathlib's integral-root theorem), drop the unused `_hy'`,
and `/cleanup` the PID-track files (reconciling the forked `Φ`/`ΨSq`/EDS copies against mathlib's originals).
Do **not** upstream the ℤ/ℚ `General*` twins — they are the `R := ℤ` specialisations of this lemma.
