# /mathlibable report — `LutzNagell.PID.den_dvd_of_order_two`

_Assessment date: 2026-06-22. Mathlib pin: `d90090f` (Lean `v4.31.0-rc2`), read directly from
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. Local Lean build is
stale per the task brief; presence/absence in mathlib is established by **direct grep of the pinned
checkout** (authoritative for this pin) plus WebSearch, not the live loogle/leansearch indices._

_This report is the **PID-track twin** of the already-written `bounded_den_of_order_two_general.md`
(the ℤ⊂ℚ track). That sibling explicitly defers to **this** declaration as its
"strictly-sharper-and-more-general PID twin" (`den_dvd_of_order_two`, concluding the sharp
`den_R(x) ∣ 4` over a domain/UFD base). So whereas the General report was BORDERLINE because it is the
*weaker, ℚ-unfolded* form, this report assesses the **canonical / preferred** order-2 form — the one the
project's own `06-generalization.md §2` recommends unifying on._

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  direct read of the pinned mathlib checkout. The declaration's full statement and proof were read
  from source (`PIDPrimeOrder.lean:176–196`).
- decl `LutzNagell.PID.den_dvd_of_order_two`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:179`
- qualified name:           ✓ **VERIFIED** `LutzNagell.PID.den_dvd_of_order_two`
                            — `namespace LutzNagell` (line 24) → `namespace PID` (line 25); base name
                            `den_dvd_of_order_two` (line 179). The task's parsed guess
                            `LutzNagell.PID.den_dvd_of_order_two` is exact.
- kind:                     theorem
- has sorry:                no (complete proof, lines 183–196: `ψ₂ = 0` from torsion → `Ψ₂Sq(x) = 0`
                            via the CoordinateRing identity → rational-root `den_dvd_of_is_root` +
                            `leadingCoeff_Ψ₂Sq = 4` → `den_R(x) ∣ 4`).
- module docstring summary: "Prime-order torsion integrality for Weierstrass curves over UFDs" —
                            generalisation of `GeneralPrimeOrder.lean` from `ℤ/ℚ` to a UFD `R` with
                            fraction field `K`; when `(p:R)` is squarefree, odd-prime-order torsion is
                            integral, and (this lemma) for order 2 the `x`-denominator divides 4.

---

### Statement (Phase 1)

`den_dvd_of_order_two` is a theorem stating: let `R` be a UFD (an integral domain with unique
factorisation) with fraction field `K`, `W : WeierstrassCurve R` a general Weierstrass model with
coefficients in `R`, and `curveK R K W` its base-change to `K`. Let `P = (x, y)` be a nonsingular
affine `K`-point. If `P` is a **2-torsion** point (`(2 : ℤ) • P = 0` in the Jacobian point group), and
`(4 : R) ≠ 0`, then **the denominator of `x` divides `4`**: `den_R(x) ∣ (4 : R)`.

This is the **order-2 branch** of the Nagell–Lutz integrality argument over a UFD — the *one* case where
full integrality genuinely fails: a 2-torsion `x` need not lie in `R`, but its `R`-denominator is
bounded, dividing the leading coefficient `4` of the 2-division polynomial `Ψ₂Sq = 4x³+b₂x²+2b₄x+b₆`.
It is the sharp, basis-independent form of the classical "`x = m/4`" clause; it is structurally
parallel to the sibling order-4 branch `integrality_of_order_four_squarefree` and the odd-prime branch
`prime_order_integrality_squarefree` (both of which *do* conclude full integrality).

Proof outline (faithful to the body): from `2 • P = 0` the project bridge
`evalEval_ψ_eq_zero_of_zsmul_eq_zero` gives `ψ₂(x,y) = 0` (here `ψ_two` says `ψ 2 = ψ₂`). The
CoordinateRing identity `mk_ψ₂_sq` (i.e. `mk ψ₂² = mk (C Ψ₂Sq)`) plus the project eval bridge
`evalEval_eq_of_mk_eq` turns `ψ₂ = 0` into `Ψ₂Sq(x) = 0` (a univariate root at the affine `x`). Pulling
`Ψ₂Sq` back along `map_Ψ₂Sq` to `R[X]` gives `aeval x W.Ψ₂Sq = 0`; the rational-root theorem
`den_dvd_of_is_root` then gives `den_R(x) ∣ W.Ψ₂Sq.leadingCoeff`, and `leadingCoeff_Ψ₂Sq (4≠0) = 4`
finishes `den_R(x) ∣ 4`.

Variables / typeclasses involved (Lean side):
- `R : Type*` with `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — a UFD (the natural home
  of `IsFractionRing.den` + the rational-root theorem).
- `K : Type*` with `[Field K] [Algebra R K] [IsFractionRing R K]` — the fraction field (`DecidableEq K`
  is `omit`-ted for this lemma).
- `W : WeierstrassCurve R` — general Weierstrass model with `aᵢ ∈ R`.
- `curveK R K W` — the base-change `W.map (algebraMap R K)` (project abbrev).

Hypotheses (Lean side):
- `h4_ne : (4 : R) ≠ 0` — automatic for `CharZero R` (needed so `deg Ψ₂Sq = 3` and `leadingCoeff = 4`).
- `hns : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` nonsingular (gives curve equation + `≠ O`).
- `h2 : (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0` — `2 • P = 0`.

Conclusion (math): a 2-torsion point on a general Weierstrass model over a UFD `R` (`(4:R)≠0`) has
`den_R(x) ∣ 4`.
Conclusion (Lean): `(IsFractionRing.den R x : R) ∣ (4 : R)`.

---

### Size classification (Phase 2a)

**Verdict: SMALL** (an internal step inside a BIG named theorem).
Reason: this is a **helper lemma** — one of the three torsion-order branches feeding the
Nagell–Lutz integrality dichotomy (the *exceptional* 2-torsion branch). It is *not* listed under the
file's `## Main results` (those are `y_isInteger_of_x_isInteger_on_curve` and
`isInteger_of_root_squarefree_leading_coeff`); the section header is "Order-2 torsion: bounded
denominators". The enclosing **PID Nagell–Lutz theorem** `lutz_nagell_integrality_pid`
(`PIDMain.lean:142`, the BIG named target) takes its `addOrderOf P = 2` disjunct
(`addOrderOf P = 2 ∧ den_R(x) ∣ 4`) and discharges it with *this* lemma. Structurally parallel to
`integrality_of_order_four_squarefree` (order-4 branch) and `prime_order_integrality_squarefree`
(odd-prime branch).

(Note: literature width is EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **n/a** — skipped. (Body is a
multi-step tactic proof, lines 183–196: the `ψ₂=0` torsion bridge, the `Ψ₂Sq`-root derivation through
the CoordinateRing identity, the pullback along `map_Ψ₂Sq`, and the `den_dvd_of_is_root` +
`leadingCoeff_Ψ₂Sq` rational-root call.)

---

### Literature search table — EXHAUSTIVE protocol

This phase re-runs the exhaustive protocol for the **sharp `den_R(x) ∣ 4` over a UFD/domain base**
form (the distinguishing content of *this* decl), and inherits the already-established 10-channel sweep
from the sibling `bounded_den_of_order_two_general.md` (same underlying mathematics, same date-window).

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell–Lutz 2-torsion `x`-coordinate denominator divides 4, general Weierstrass                         | yes  | general model: 2-torsion satisfies `4x³+b₂x²+2b₄x+b₆ = 0`, leading coeff 4 ⇒ `den(x) ∣ 4`; short model gives `y=0`, integral `x` | Dummit ENM lec.19; Doud (Tate normal form, arXiv:math/0011066); Wikipedia/PlanetMath/Alpoge "Nagell-Lutz, quickly"; Li (UMich REU); unizg §15-3 |
|  2 | WebSearch (general form)         | Silverman / Nagell–Lutz over Dedekind domain / number field, 2-torsion denominator, place-by-place      | yes  | place-by-place integrality of torsion; 2 the lone obstruction (`den(x) ∣ 4`); generalised to number fields / Dedekind domains | Silverman–Tate (ETH PDF); arXiv:2509.07524 (2025, imaginary-quadratic Nagell–Lutz–Cassels); arXiv:1411.5341 (quadratic-field torsion); Derickx thesis |
|  3 | WebSearch (named-after / source) | Silverman AEC VIII.7 / Silverman–Tate Ch.II 2-adic denominator of torsion `x`                            | yes  | Silverman AEC VIII.7 / S–T Ch.II: integrality via local (incl. 2-adic) denominators; prime 2 the only obstruction to full integrality | Silverman AEC; Silverman–Tate "Rational Points on Elliptic Curves"; Husemöller |
|  4 | ChatGPT MCP                      | (MCP down in this env per task brief; substituted by WebSearch #1–3 covering the general-model `den∣4` + the Dedekind/number-field generalisation) | n/a  | —                                                                                    | tool genuinely down (env brief warned); compensated by the explicit "den ∣ 4" / general-model statements in #1 and the Dedekind/number-field hits in #2 |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                              | n/a  | (directories absent)                                                                 | no `references/` under `.mathlib-quality/` (only `overview/`), no `refs/` store present. n/a (matches all sibling reports). |
|  6 | nLab                             | "Nagell–Lutz theorem" / torsion of elliptic curves                                                      | no   | —                                                                                    | nLab has no dedicated Nagell–Lutz page (elementary Diophantine result) — corroborates sibling reports |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                                                    | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell–Lutz / torsion integrality over a Dedekind base                                                  | n/a  | —                                                                                    | Stacks does scheme-theoretic AG foundations, not Diophantine arithmetic of `E` torsion denominators — corroborates sibling reports |
|  9 | MathOverflow / Math.SE           | why `x=m/4` (den ∣ 4) for order-2 on a general Weierstrass model; 2 the only bad prime                  | yes  | community proofs match Silverman/Cassels; 2 the unique prime whose `x`-denominator can survive (→ den ∣ 4) | "A Neighbourhood of Infinity" exposition; Math.SE folklore textbook proof |
| 10 | recent arXiv (last 5 years)      | Nagell–Lutz over number fields / imaginary quadratic; divisibility by 2 of rational points              | yes  | arXiv:2509.07524 (2025) Nagell–Lutz–Cassels over imaginary quadratic fields; arXiv:1702.02255 "divisibility by 2 of rational points" — both treat 2-torsion specially | confirms the **general base (number field / Dedekind / UFD) place-by-place `den(x) ∣ 4`** is the live research baseline; **no Lean/mathlib version** |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (general-model
`den ∣ 4`, the Dedekind/number-field generalisation, the Silverman named-after source); local refs
checked (absent → n/a); nLab/Stacks/nCatLab checked and reasoned n/a; MathOverflow-class expositions +
recent arXiv both checked and hit. ChatGPT MCP genuinely down (tool error, not a skip), compensated by
the explicit general-model `den ∣ 4` and Dedekind/number-field WebSearch hits.

### Literature summary (Phase 3)

Concept identified as: **the order-2 branch of the Nagell–Lutz integrality theorem, in its sharp,
basis-independent form** — "a 2-torsion point on a general Weierstrass model over `R` has
`den_R(x) ∣ 4`", proved via the 2-division relation `ψ₂ = 0` and the univariate
`Ψ₂Sq = 4x³+b₂x²+2b₄x+b₆`, whose **leading coefficient is 4**, so the **rational-root theorem** gives
`den(x) ∣ 4`.

Sources agree on the standard form: **yes.** For the **general Weierstrass model** the order-2 case is
exactly `4x³+b₂x²+2b₄x+b₆ = 0` (leading coeff 4), giving `den(x) ∣ 4` — the precise statement (Dummit,
Doud, Math.SE). The short-model `y²=x³+Ax+B` "clause" (2-torsion ⇒ `y=0`, `x` integral) is the special
case; the *named* object is the whole Nagell–Lutz theorem (Silverman AEC VIII.7, Silverman–Tate,
Cassels, Husemöller), of which this is the order-2 component. Wikipedia/HandWiki's generalised statement
phrases the same content as "order 2 and coordinates of the form `x=m/4, y=n/8`" (the ℚ unfolding —
which is the *General*-track sibling, not this sharp form).

Most general standard form: over a **Dedekind domain / number field / PID / UFD** `R` with fraction
field `K`, place-by-place, general Weierstrass model, stated sharply as **`den_R(x) ∣ 4`** (Silverman;
arXiv:2509.07524 is exactly such a number-field generalisation). **This is precisely the form this decl
states** — base `R` a UFD, conclusion `den_R(x) ∣ (4:R)`. So unlike its General-track sibling, this decl
is *at* the maximally-general standard form, not a specialisation of it.

Generality dimensions where the literature varies:
  - **Base**: short-model `ℤ ⊂ ℚ` ↔ number field / Dedekind / PID / **UFD** `R ⊂ K`, place-by-place
    (most general). **This decl = UFD `R ⊂ Frac R`** — the general end.
  - **Model**: short `y²=x³+Ax+B` ↔ **general Weierstrass** (this decl uses the **general** model — good;
    the general model is exactly where `den(x) ∣ 4` (not `den=1`) is the sharp 2-torsion statement).
  - **Conclusion form**: sharp **`den(x) ∣ 4`** (Silverman; basis-independent) ↔ unfolded `4x,8y∈ℤ`
    (the *General*-track ℚ specialisation). **This decl = the sharp `den ∣ 4`** — the preferred form.

Disagreement with the literature: **none** — it is a faithful Lean rendering of the order-2 case of the
generalised Nagell–Lutz theorem, at the literature's maximally-general base and in its sharp
(basis-independent) conclusion form.

---

### Generality analysis — `den_dvd_of_order_two`

Literature-standard form (from Phase 3): the order-2 denominator bound over an arbitrary
Dedekind/PID/UFD `R` with fraction field `K` (place-by-place), general Weierstrass model, stated sharply
as **`den_R(x) ∣ (4:R)`**.

| # | Parameter / hypothesis                              | Current Lean form                              | Literature-standard form                      | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|------------------------------------------------|-----------------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` | UFD                                       | Dedekind domain / number-field ring of integers / PID / UFD | **borderline / NO at this engine** | `den_dvd_of_is_root` (the rational-root theorem this proof *calls*) itself requires `[UniqueFactorizationMonoid A]` in mathlib (`RationalRoot.lean:22`), and `IsFractionRing.den` lives in the UFD/`NumDen` API. So **UFD is the minimal base in which the very tools of the proof are defined** — weakening to a general Dedekind domain would need a *different* (ideal-theoretic) denominator theory mathlib's `IsFractionRing.den` doesn't provide. The UFD form is the natural mathlib home; **already maximally general for this proof technique.** |
| 2 | `K = Frac R` via `[IsFractionRing R K]`             | abstract fraction field                        | fraction field                                | **NO** (already abstract) | uses `IsFractionRing R K` (any fraction field), not the concrete `FractionRing R` — already maximally general. |
| 3 | conclusion `(IsFractionRing.den R x : R) ∣ (4:R)`   | **sharp, basis-independent `den ∣ 4`**         | sharp `den_R(x) ∣ 4`                           | **NO — already sharp**   | this IS the Silverman / mathlib-idiom form. (The *weaker* `4x,8y∈ℤ` unfolding is the General-track sibling; this decl does not have that defect.) |
| 4 | `h4_ne : (4:R) ≠ 0`                                 | explicit hypothesis                            | needed (`deg Ψ₂Sq = 3`)                       | **partial** | could be replaced by `[CharZero R]` (which implies it and is the intended use), but the bare `(4:R)≠0` is *more general* than `CharZero` (covers e.g. odd-characteristic-but-`4≠0` rings). The docstring already notes it is "automatic for `CharZero R`". Keeping `(4:R)≠0` is the more-general choice — correct as is. |
| 5 | torsion encoding `2•P=0` (`h2`)                     | `(2:ℤ)•P=0`                                    | identical                                     | **NO** (essential)  | "2-torsion" is the defining hypothesis. Correct as is. |
| 6 | general Weierstrass model                            | general (`a₁..a₆`)                             | general                                       | **NO** (already general) | already at the right model-generality — strictly more general than the short corollary. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for this proof technique). The base is a UFD `R` — the
minimal ring in which mathlib's `den_dvd_of_is_root` + `IsFractionRing.den` (the proof's own tools) are
even defined; the model is general Weierstrass; the conclusion is the sharp, basis-independent
`den_R(x) ∣ (4:R)` — the Silverman/mathlib-idiom form. The only thinkable further weakening (UFD →
general Dedekind domain) is **NOT available at this engine**: it would require an ideal-theoretic
denominator theory that mathlib's value-level `IsFractionRing.den` does not provide, i.e. a different
proof, not a weakening of this one.
Number of weakening opportunities found: **0** (within the `IsFractionRing.den`/rational-root API; a
Dedekind-domain generalisation is a *different theorem*, out of scope for this assessment of *this*
decl).
Proposed restatement: **none needed** — the statement is already the maximally-general, sharp,
mathlib-idiomatic form. (Contrast: its General-track sibling `bounded_den_of_order_two_general` IS a
specialisation of this decl — `R=ℤ, K=ℚ`, conclusion unfolded to `4x,8y∈ℤ` — and `06-generalization.md
§2` recommends retiring the General one in favour of *this* one.)
Cost of restatement: **n/a** (already in the target form).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                                                              | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|--------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                | no — already done | already stated over `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] … [IsFractionRing R K]` with the sharp `IsFractionRing.den R x ∣ (4:R)` | composes with all of `RationalRoot.lean` / `Localization/NumDen.lean` (`IsFractionRing.den`) + mathlib's base-change EC API |
|  2 | sequences/metric → filters/topological?                                                            | no       | purely algebraic Diophantine statement; no analysis                                  | — |
|  3 | construct an object → universal-property class?                                                    | no       | it's a `Prop`; nothing constructed                                                   | — |
|  4 | set-with-closure-predicate → bundled-substructure?                                                 | no       | n/a                                                                                  | — |
|  5 | vector-space/field-specific → weaken to modules/(semi)ring?                                        | no — already at the floor | base is already a UFD `R ⊂ Frac R` (the floor for `IsFractionRing.den` + rational-root); cannot weaken further without a new denominator theory | — |
|  6 | 1-categorical → higher-categorical?                                                                | no       | n/a | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/monoid?                                                | no       | the order `2` and constant `4 = lead(Ψ₂Sq)` are mathematically essential (*the* 2-torsion case); the base is already the abstract `R` (not a concrete index) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — this decl IS already the modern, mathlib-idiomatic form (it is in fact
the *target* that the modern-idiom analysis of its General-track sibling proposed: sharp
`IsFractionRing.den R x ∣ (4:R)` over an abstract UFD base). There is no contemporary reformulation that
improves its organisation; it already uses `IsFractionRing.den` directly, an abstract fraction field,
and the general Weierstrass model.
  - One-line reason this is not a modernisation move: the statement already realises the sharp,
    basis-independent, typeclass-parametrised form; the only "further" generalisation (UFD → Dedekind)
    is a *different theorem* requiring ideal-theoretic denominators, not a re-idiomisation of this one.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `den_dvd_of_order_two`

Method note: the local Lean build is stale, so the live loogle/leansearch indices may not reflect this
exact pin. The authoritative check is a **direct grep of the pinned mathlib checkout** the project
builds against (`.lake/packages/mathlib`, `d90090f`), plus reading the EC + EDS + RationalRoot source.
This corroborates the identical (independently-run) Phase-5 conclusions in the sibling reports
(`bounded_den_of_order_two_general.md`, `integrality_of_order_four_general.md`).

[A] Lean-Finder       "2-torsion elliptic curve x-coordinate denominator divides 4 over a UFD"          n/a — index MCP unavailable in env; substituted by [D]/[E] grep over the pinned tree.
[B] Loogle            `(2:ℤ)•_ = 0 → (IsFractionRing.den _ _ : _) ∣ 4` over EC points (type pattern)      n/a — index unavailable; grep substitute. (No lemma of this shape exists — see [D].)
[C] LeanSearch        "Nagell–Lutz 2-torsion point x-coordinate denominator divides 4"                   n/a — index unavailable; grep substitute.
[D] **Grep mathlib src (authoritative, exact pin)**:
      • `grep -rni "nagell|lutz"` over `Mathlib/`                                       → **only the unrelated mathematician Patrick Lutz** (Galois theory). **No Nagell–Lutz theorem.**
      • `grep "addOrderOf|IsOfFinAddOrder"` ∩ `AlgebraicGeometry/EllipticCurve/`        → **0 occurrences** (no torsion↔denominator/integrality result anywhere; the affine/Jacobian API stops at the abstract group law).
      • `grep "two.*torsion|den.*4|IsFractionRing.den|integrality"` ∩ EC/EDS dirs        → **0** torsion-denominator results (only polynomial/EDS identities + `twoTorsionPolynomial` in `Weierstrass.lean:305`, which is just the *polynomial*, no denominator/torsion-point theorem).
      • `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` → has the **building blocks** this proof consumes: `WeierstrassCurve.Ψ₂Sq` (`Basic.lean:117`), `C_Ψ₂Sq` (`Basic.lean:120`), `Affine.CoordinateRing.mk_ψ₂_sq` (`Basic.lean:128`), `ψ_two` (`Basic.lean`), `map_Ψ₂Sq` (`Basic.lean`), `leadingCoeff_Ψ₂Sq` (`Degree.lean:85`, **`= 4` given `(4:R)≠0`**) — but **no torsion-denominator theorem**.
      • `Mathlib/RingTheory/Polynomial/RationalRoot.lean` (`den_dvd_of_is_root` `:50`/`:89`) + `Mathlib/RingTheory/Localization/NumDen.lean` (`IsFractionRing.den`) → the rational-root + denominator tools the proof uses (require `[UniqueFactorizationMonoid A]`). Generic; not EC-specific.
[E] Name pattern      `theorem … order_two … den` / `… two_torsion …` / `nagell_lutz` in mathlib         no hits.

Searched for both:
  - the user's current form (`2•P=0` ⇒ `den_R(x) ∣ 4`, over a UFD base, general Weierstrass) — **not in
    mathlib**.
  - the literature-standard / general form (Dedekind/number-field base, `den(x) ∣ 4`) — **not in
    mathlib** either (grep found zero torsion-denominator results at *any* generality).

_Project-framing note (the task flagged that this project forks `Mathlib.…DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and runs duplicated General/PID tracks): the proof
of THIS decl consumes the division-polynomial API by its `WeierstrassCurve.…` names (`Ψ₂Sq`, `ψ_two`,
`map_Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`, `mk_ψ₂_sq`). **Every one of those building-block names exists in
mathlib AND is re-declared (shadowed) in the project** — `Ψ₂Sq` in `DivisionPolynomial.lean:40`,
`leadingCoeff_Ψ₂Sq` in `DivisionPolynomialDegree.lean:81` (identical `= 4` statement to mathlib's
`Degree.lean:85`), etc., all under `namespace WeierstrassCurve`. So the fork **shadows** mathlib's
identically-named lemmas. The mathlib originals it forks contain only the polynomial machinery, **never
this 2-torsion denominator theorem** — so this decl is decidedly **not** already upstream; mathlib has
only the building blocks._

Concluded: **not in mathlib** (all methods exhausted, both the user's UFD form and the more-general
Dedekind/number-field form). Mathlib has the **building blocks** (`Ψ₂Sq`, `ψ_two`,
`leadingCoeff_Ψ₂Sq = 4`, `map_Ψ₂Sq`, `mk_ψ₂_sq`, `den_dvd_of_is_root`, `IsFractionRing.den`) — which the
project forks — but **not** this order-2 denominator step, and **no** torsion↔denominator/integrality
theorem at any generality.

---

### Call sites — `den_dvd_of_order_two`

Internal use count: **1** (within the NagellLutz project, excluding the declaring file
`PIDPrimeOrder.lean:179`).
External-to-file callers: **1 distinct file** (`PIDMain.lean`).

| Caller file:line                   | Usage pattern (one-line excerpt)                                                                       |
|------------------------------------|--------------------------------------------------------------------------------------------------------|
| PIDMain.lean:157                   | `exact ⟨hord2, den_dvd_of_order_two W (Nat.cast_ne_zero.mpr (by norm_num)) hpt (nsmul_eq_zero_affine_to_jac W h2P)⟩` |

The single caller is the **order-2 disjunct of `lutz_nagell_integrality_pid`** itself (the parent PID
Nagell–Lutz theorem, `PIDMain.lean:142`). When `addOrderOf P = 2`, the main theorem's conclusion takes
its right disjunct (`addOrderOf P = 2 ∧ den_R(x) ∣ 4`) and discharges it with this lemma — i.e. this is
*the* lemma that supplies the sharp "or else order 2 with `den_R(x) ∣ 4`" clause of the formalised
generalised Nagell–Lutz statement over a UFD. (Note: the parent's conclusion is *literally*
`den_R(x) ∣ 4`, so this lemma's sharp form is exactly what the main theorem exposes — no unfolding.)

Inline-derivation grep (was the equivalent re-derived elsewhere without calling this lemma?): **(none)**
— the only other place the order-2 denominator content lives is the parallel **General-track** lemma
`bounded_den_of_order_two_general` (`GeneralPrimeOrder.lean:167`), which is the *weaker, ℚ-specialised*
analogue (separate file, `ℤ⊂ℚ` base, unfolded `4x,8y∈ℤ`), i.e. a *special case of this decl*, not an
inline re-derivation of the UFD statement.

Call-sites reading: **K = 1** (one external-to-file caller, the order-2 disjunct of the main theorem).
Per the skill's call-sites table, "K = 1 internal use only" leans toward NO-composable / the
"possibly-the-wrong-abstraction" reading — *but* here the lemma is a **named, docstring'd, standard
clause** of a classical theorem's statement (the sharp `den(x) ∣ 4` order-2 case), tightly bundled with
its sibling branches (`integrality_of_order_four_squarefree`, `prime_order_integrality_squarefree`). Its
mathlib-worthiness is inseparable from the worthiness of the whole Nagell–Lutz development — exactly the
pattern that resolved the siblings `integrality_of_order_four_general` and
`bounded_den_of_order_two_general` to BORDERLINE.

---

### Composition check (Phase 6)

Can `den_dvd_of_order_two` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: get `Ψ₂Sq(x)=0` from `2•P=0`, then rational-root (`den_dvd_of_is_root` +
`leadingCoeff_Ψ₂Sq = 4`).
  - Mathlib decls used: `WeierstrassCurve.ψ_two`, `WeierstrassCurve.Ψ₂Sq`,
    `Affine.CoordinateRing.mk_ψ₂_sq`, `leadingCoeff_Ψ₂Sq`, `map_Ψ₂Sq`, `den_dvd_of_is_root` (all
    present in mathlib / forked).
  - Result: **fails as a ≤3-call composition.** Two of the steps need non-trivial *project* inputs that
    mathlib does not provide:
      (a) `ψ₂(x,y) = 0` from `2•P=0` comes from `evalEval_ψ_eq_zero_of_zsmul_eq_zero` — a **project
          bridge** through Jacobian coordinates (`nsmul_eq_zero_affine_to_jac`, `x_coord_nsmul_eq`,
          the `Z=0`-at-identity machinery), not a mathlib lemma;
      (b) passing from `ψ₂=0` to `Ψ₂Sq(x)=0` uses the CoordinateRing identity `mk_ψ₂_sq` together with
          the **project eval bridge** `evalEval_eq_of_mk_eq` (`evalEval_pow`, `zero_pow`, `evalEval_C`)
          — no mathlib one-liner connects the bivariate `ψ₂` vanishing to the univariate `Ψ₂Sq` root at
          an affine point;
      (c) the `map_Ψ₂Sq` pullback + `den_dvd_of_is_root` + `leadingCoeff_Ψ₂Sq` rational-root call is the
          only genuinely mathlib-composable tail (≈2 calls), but it consumes the output of (a)+(b).
  - Notes: the body (lines 183–196) is a genuine multi-step proof — the `ψ₂=0` bridge, the
    `Ψ₂Sq`-root derivation through the CoordinateRing identity, the pullback, and the rational-root
    `den ∣ 4` call — not a one-liner.

Attempt 2 (alternate angle): even targeting only the rational-root tail `den_dvd_of_is_root` directly,
it still needs `aeval x W.Ψ₂Sq = 0` as input, which is precisely the project-bridge content (a)+(b) and
is **not** available in mathlib (mathlib has no lemma producing a univariate division-polynomial root at
a torsion point).

Conclusion: **NOT-COMPOSABLE** from mathlib alone. Mathlib (incl. the forked division-polynomial API)
supplies `Ψ₂Sq`, `leadingCoeff_Ψ₂Sq = 4`, `map_Ψ₂Sq`, `mk_ψ₂_sq`, and the generic rational-root call,
but the surrounding inputs (the Jacobian-to-`ψ₂` bridge and the `ψ₂=0 → Ψ₂Sq(x)=0` CoordinateRing/eval
bridge) are project lemmas with no mathlib analog. This is more than a 1–3 mathlib-call composition.

---

## Verdict: `LutzNagell.PID.den_dvd_of_order_two`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the **order-2 branch** of the classical generalised Nagell–Lutz theorem
  (Silverman AEC VIII.7 / Silverman–Tate / Dummit / Doud), in its **sharp, basis-independent
  `den_R(x) ∣ 4` form over a UFD base** — exactly the maximally-general standard form (number-field /
  Dedekind generalisations: arXiv:2509.07524 (2025), arXiv:1411.5341). Mathlib has **no** Nagell–Lutz
  theorem and **no** torsion↔denominator result at any generality.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for this proof technique — UFD base (the floor
  for mathlib's `IsFractionRing.den` + `den_dvd_of_is_root`), general Weierstrass model, sharp
  `IsFractionRing.den R x ∣ (4:R)` conclusion. Modern-idiom (4c) = **no further idiom available**: this
  decl *is* the modern/idiomatic target (it is the very form the General-track sibling's 4c proposed).
  Its weaker ℚ-unfolded twin `bounded_den_of_order_two_general` is a *specialisation of this decl*; the
  project's `05-duplications.md:67` + `06-generalization.md §2` recommend unifying on **this** sharp
  form.
- Mathlib search (Phase 5): **not in mathlib** (both the UFD form and the Dedekind/number-field form);
  direct grep of the pinned checkout finds zero Nagell/Lutz hits (only the unrelated Galois-theory
  author) and zero torsion↔denominator results. Mathlib has the building blocks `Ψ₂Sq`, `ψ_two`,
  `leadingCoeff_Ψ₂Sq = 4`, `map_Ψ₂Sq`, `mk_ψ₂_sq`, `den_dvd_of_is_root`, `IsFractionRing.den` (which the
  project forks), but not this step.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine multi-step proof whose inputs (Jacobian↔`ψ₂`
  bridge, the `ψ₂=0 → Ψ₂Sq(x)=0` CoordinateRing/eval bridge) are project lemmas, not a ≤3 mathlib-call
  chain. **K = 1** call site (the order-2 disjunct of the PID main theorem).

**Rationale (1–2 paragraphs):**

This is a faithful, sorry-free Lean rendering of a genuine, classical, named clause of mathematics — the
order-2 case of the generalised Nagell–Lutz integrality theorem, the *one* case where full integrality
fails — and, crucially, it is rendered in the **sharp, maximally-general, mathlib-idiomatic form**:
`den_R(x) ∣ (4:R)` over an abstract UFD `R ⊂ K = Frac R`, general Weierstrass model. Unlike its
General-track sibling `bounded_den_of_order_two_general` (which is the *weaker* `ℤ⊂ℚ` / `4x,8y∈ℤ`
unfolding, and came out BORDERLINE for being narrower-and-weaker-than-standard), **this decl has no
generality or sharpness defect** — it is precisely the form the sibling's own modern-idiom analysis
proposed as the target, and the project's `06-generalization.md §2` recommends retiring the General one
in favour of *this* one. Mathlib does not have it (mathlib has *no* Nagell–Lutz and *no*
torsion↔denominator theorem at any generality; only the division-polynomial + rational-root
infrastructure this proof consumes, which the project moreover *forks*), so it is neither
`NO-mathlib-has-it` nor `NO-composable-from-mathlib` (the inputs to the rational-root call — the
Jacobian↔`ψ₂` bridge and the `ψ₂=0 → Ψ₂Sq(x)=0` eval bridge — are project lemmas, not a ≤3 mathlib-call
chain).

Why not the clean `YES-add-as-is` then, given the statement is already maximally general and sharp? For
the same *structural* reason its siblings came out BORDERLINE: this is an **intermediate helper with a
single call site** (the order-2 disjunct of `lutz_nagell_integrality_pid`), tightly coupled to its
sibling order-4 / odd-prime branches and to the **forked** division-polynomial track, and it is one half
of an **unresolved General↔PID duplication** (this PID `den ∣ 4` form vs the General `4x,8y∈ℤ` form). Its
mathlib-worthiness is therefore inseparable from three judgment calls the skill must not make alone:
whether the **whole Nagell–Lutz theorem** is headed upstream (this branch rides along with that PR, not
as an independent addition); whether — having confirmed this is the *canonical* track — the order-2 step
is exposed as a standalone public lemma or kept `private`/inlined inside the Nagell–Lutz file (K=1 use);
and whether the project's **forks** of `WeierstrassCurve.{Ψ₂Sq, ψ_two, leadingCoeff_Ψ₂Sq, map_Ψ₂Sq,
mk_ψ₂_sq}` are reconciled against mathlib's identically-named originals first (the prerequisite — the
upstreamed proof must build on mathlib's versions, not the project's shadows). The parent theorem
`lutz_nagell_integrality_pid` is the BIG named target; this helper is a branch of it. (Net: a *stronger*
YES-leaning than the General sibling — no generality/idiom blocker remains — but the
helper/single-call-site + forked-deps + which-track packaging questions keep the honest verdict at
BORDERLINE.)

**Numbered questions (≤5):**

1. Is the **whole PID Nagell–Lutz theorem** (`lutz_nagell_integrality_pid`, `PIDMain.lean:142`) being
   upstreamed to mathlib? If yes, this order-2 branch rides along as the lemma supplying the sharp
   "`den_R(x) ∣ 4`" disjunct, and the remaining question is only "expose it as a named lemma, or inline
   it into the main proof?"
2. Confirm this **PID `den ∣ 4` track is the canonical one to upstream** (over the General-track
   `4x,8y∈ℤ` form, which `05-duplications.md:67` / `06-generalization.md §2` classify as a weaker ℚ
   special-case of *this* decl) — so mathlib doesn't receive two near-duplicate order-2 lemmas. (Strongly
   indicated; just needs sign-off.)
3. Given the single call site (`PIDMain.lean:157`, the order-2 disjunct), should the order-2 step be a
   **standalone public mathlib lemma** or a `private`/inlined step inside the Nagell–Lutz file?
4. Will the project's **forks** of `WeierstrassCurve.{Ψ₂Sq, ψ_two, leadingCoeff_Ψ₂Sq, map_Ψ₂Sq,
   mk_ψ₂_sq}` (in `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean`) be **reconciled against
   mathlib's identically-named originals** before upstreaming? They are the prerequisite; the upstreamed
   proof must build on mathlib's versions, not the project's shadows.
5. Is a UFD base acceptable as the upstream form, or is a **Dedekind-domain / number-field**
   generalisation wanted first? (Note: weakening UFD → Dedekind is a *different theorem* — mathlib's
   value-level `IsFractionRing.den` + `den_dvd_of_is_root` require a UFD; an ideal-theoretic denominator
   version is out of scope for *this* proof. The UFD form is the natural mathlib home and already covers
   `ℤ`, `ℚ`, and PIDs / rings of integers that are UFDs.)

Next action: user answers the questions; re-run `/mathlibable` on the chosen canonical order-2 form once
the General↔PID dedup and the fork reconciliation are settled. The most likely resolution, if Nagell–Lutz
is headed upstream, is that this helper is **absorbed into the Nagell–Lutz PR** — kept as the sharp
`den_R(x) ∣ 4` step over the UFD base (this exact statement), the weaker General-track twin retired, and
the step likely `private`/inlined — after first reconciling the forked `DivisionPolynomial.*`
dependencies against mathlib's originals.

---

## Next step

User answers the 5 questions above. If the PID Nagell–Lutz theorem is bound for mathlib, treat this
order-2 branch as an **internal step of that PR** — kept in its current sharp `den_R(x) ∣ 4` form over
the UFD base (it is already the canonical, maximally-general, idiomatic statement; the General-track
`4x,8y∈ℤ` twin should be retired, not this one), and likely `private`/inlined given its single call
site — after first reconciling the forked `WeierstrassCurve.{Ψ₂Sq, leadingCoeff_Ψ₂Sq, …}` dependencies
against mathlib's originals. As an isolated declaration it is a genuine, sharp, maximally-general
contribution that mathlib lacks; the BORDERLINE is purely about packaging (which track / standalone vs
inlined / fork reconciliation), not about the statement's form.
