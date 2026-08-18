# /mathlibable report — `LutzNagell.LutzNagellTheorem.bounded_den_of_order_two_general`

_Assessment date: 2026-06-21. Mathlib pin: `d90090f` (Lean `v4.31.0-rc2`), read directly from
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. Local Lean build is
stale per the task brief; presence/absence in mathlib is established by **direct grep of the pinned
checkout** (authoritative for this pin) plus WebSearch, not the live loogle/leansearch indices. This
report reuses the protocol of, and is consistent with, the sibling reports already written for this
file — in particular the closely-parallel `integrality_of_order_four_general.md` (the order-4 branch),
`lutz_nagell_integrality_general.md` (the parent theorem), `prime_order_integrality_general` and
`y_integral_of_x_integral_on_general_curve`._

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  direct read of the pinned mathlib checkout. The declaration's full statement and proof were read
  from source (`GeneralPrimeOrder.lean:167–203`).
- decl `LutzNagell.LutzNagellTheorem.bounded_den_of_order_two_general`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:167`
- qualified name:           ✓ **VERIFIED** `LutzNagell.LutzNagellTheorem.bounded_den_of_order_two_general`
                            — `namespace LutzNagell` (line 19) → `namespace LutzNagellTheorem`
                            (line 20); base name `bounded_den_of_order_two_general` (line 167). Matches
                            the task's parsed guess exactly.
- kind:                     theorem
- has sorry:                no (complete proof, lines 171–203: `ψ₂ = 0` from torsion → `Ψ₂Sq(x) = 0` →
                            rational-root `den ∣ 4` → explicit ℚ denominator-clearing to `4x, 8y ∈ ℤ`).
- module docstring summary: "Prime-order and order-4 torsion integrality for general Weierstrass curves":
                            if `P ≠ 0` has odd prime order or order 4 on a general Weierstrass curve with
                            integral coefficients, then `P` has integral affine coordinates; **for order
                            2, we prove the weaker bound `4x, 8y ∈ ℤ`** (this lemma).
- decl docstring:           "If `2•P = 0` on a general integral curve, then `4x ∈ ℤ` and `8y ∈ ℤ`. From
                            `ψ₂ = 0`: `2y + a₁x + a₃ = 0`. Substituting into the curve equation gives
                            `4x³ + b₂x² + 2b₄x + b₆ = 0`, with leading coefficient 4. By the rational root
                            theorem, `x.den ∣ 4`, so `4x ∈ ℤ`. Then `8y = -4(a₁x + a₃) ∈ ℤ`."

---

### Statement (Phase 1)

`bounded_den_of_order_two_general` is a theorem stating: let `W : WeierstrassCurve ℤ` be an
integral-coefficient (general) Weierstrass curve, `curveQ W` its base-change to ℚ, and `P = (x, y)` a
nonsingular affine rational point. If `P` has **(2-)torsion** — encoded as `(2 : ℤ) • P = 0` in the
Jacobian point group (`h2`) — then **`4x` and `8y` are integers**:
`(∃ n : ℤ, (n:ℚ) = 4*x) ∧ (∃ m : ℤ, (m:ℚ) = 8*y)`.

This is the **order-2 branch** of the Nagell–Lutz integrality argument, and the *one case where full
integrality fails*: a 2-torsion point need not have integer coordinates, only `x ∈ ¼ℤ`, `y ∈ ⅛ℤ`. It
is structurally parallel to the sibling order-4 branch `integrality_of_order_four_general` and the
odd-prime branch `prime_order_integrality_general` (both of which *do* conclude full integrality).

Proof outline (faithful to the docstring): from `2 • P = 0` the project bridge
`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` gives `ψ₂(x,y) = 0`; unfolding `ψ₂` yields the affine
2-division relation `2y + a₁x + a₃ = 0`. Squaring/substituting into the curve equation (via the
Coordinate-ring identity `mk_ψ₂_sq` and the eval bridge `evalEval_eq_of_mk_eq`) gives
`Ψ₂Sq(x) = 4x³ + b₂x² + 2b₄x + b₆ = 0`. As `Ψ₂Sq ∈ ℤ[X]` has **leading coefficient 4**
(`leadingCoeff_Ψ₂Sq`), the rational-root theorem `den_dvd_of_is_root` gives `x.den ∣ 4`, hence
`4x ∈ ℤ` (explicit ℚ denominator-clearing, lines 190–201). Finally `8y = -4(a₁x + a₃)` is an integer
(lines 202–203, from the 2-division relation).

Variables / typeclasses involved (Lean side):
- `W : WeierstrassCurve ℤ` — integral general-Weierstrass model.
- `curveQ W : WeierstrassCurve ℚ` — project abbrev (`GeneralCurve.lean`), the base-change `W ⊗ ℚ`.

Hypotheses (Lean side):
- `hns : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` nonsingular (gives the curve equation + `≠ O`).
- `h2 : (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0` — `2 • P = 0`.

Conclusion (math): a rational 2-torsion point on an integral general-Weierstrass model has
`x ∈ ¼ℤ` and `y ∈ ⅛ℤ`.
Conclusion (Lean): `(∃ n : ℤ, (n:ℚ) = 4*x) ∧ ∃ m : ℤ, (m:ℚ) = 8*y`.

---

### Size classification (Phase 2a)

**Verdict: SMALL** (an internal step inside a BIG named theorem).
Reason: this is a **helper lemma** — one of the three torsion-order branches feeding the Nagell–Lutz
integrality dichotomy (the *exceptional* 2-torsion branch). It is *not* listed under any
`## Main results`; the file header marks it as the "Order-2 torsion: bounded denominators" section.
The enclosing **Nagell–Lutz theorem** (`lutz_nagell_integrality_general`, assessed YES) is the BIG
named target; this lemma is one supporting branch of it, structurally parallel to
`integrality_of_order_four_general` (order-4 branch) and `prime_order_integrality_general` (odd-prime
branch).

(Note: literature width is EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **n/a** — skipped. (Body is a
multi-step tactic proof: `ψ₂=0` bridge, the `Ψ₂Sq`-root derivation, the rational-root den bound, and
two explicit denominator-clearing constructions — lines 171–203.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz order-2 torsion, `x = m/4, y = n/8`, division polynomial                                     | yes  | **verbatim** generalized statement: "any rational point of finite order has integer coordinates, **or else have order 2 and coordinates of the form `x=m/4, y=n/8`**, for `m, n` integers" — exactly this lemma's conclusion | Wikipedia (Nagell–Lutz), HandWiki, en-academic mirror, Alpoge "Nagell-Lutz, quickly", "A Neighbourhood of Infinity" |
|  2 | WebSearch (general form)         | general Weierstrass 2-torsion `4x³+b₂x²+2b₄x+b₆`, rational root, denominator of `x` divides 4            | yes  | "for 2-torsion points in generalized Weierstrass equations, **the denominator of the `x`-coordinate divides 4**"; standard form `y² = 4x³+b₂x²+2b₄x+b₆` | Dummit ENM notes; Doud (Tate normal form, arXiv:math/0011066); UCSB chap.2; sciencedirect "Computing the Rational Torsion of an Elliptic Curve" |
|  3 | WebSearch (named-after / source) | Silverman AEC VIII / Silverman–Tate Nagell-Lutz, 2-adic denominator of torsion `x`-coordinate           | yes  | Silverman AEC VIII.7 / Silverman–Tate Ch.II: integrality via local (p-adic, incl. **2-adic**) denominators; the prime `2` is the lone obstruction to full integrality (giving den ∣ 4) | Silverman AEC; Silverman–Tate "Rational Points on Elliptic Curves"; Husemöller |
|  4 | ChatGPT MCP                      | (MCP down in this env per task brief; substituted by WebSearch #1–3 covering the verbatim `m/4,n/8` form) | n/a  | —                                                                                    | tool genuinely down (environment brief warned); compensated by the **verbatim Wikipedia/HandWiki `x=m/4, y=n/8` match** and the explicit "den ∣ 4" statements in #2 |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                              | n/a  | (directories absent)                                                                 | no `references/` dir under `.mathlib-quality/` (only `overview/`), no `refs/` store present. Recorded n/a (matches sibling reports). |
|  6 | nLab                             | "Nagell-Lutz theorem" / torsion of elliptic curves                                                      | no   | —                                                                                    | nLab has no dedicated Nagell–Lutz page (elementary Diophantine result, not a categorical concept) — corroborates sibling reports |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                                                    | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell-Lutz / torsion integrality                                                                       | n/a  | —                                                                                    | Stacks does scheme-theoretic AG foundations, not Diophantine arithmetic of `E/ℚ` torsion — corroborates sibling reports |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz 2-torsion denominator, why `x=m/4` for order 2                                               | yes  | community proofs match Silverman/Cassels; 2 is the only prime where the x-denominator can survive (→ den ∣ 4) | "A Neighbourhood of Infinity" exposition; Algebra Teahouse; folklore textbook proof |
| 10 | recent arXiv (last 5 years)      | Nagell-Lutz generalisations (imaginary quadratic / number fields); divisibility by 2 of rational points  | yes  | arXiv:2509.07524 (2025) Nagell–Lutz over imaginary quadratic fields; arXiv:1702.02255 "divisibility by 2 of rational points" — both treat 2-torsion specially | confirms the classical general-Weierstrass-over-ℚ form is the baseline; **no Lean/mathlib version** |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (the specific
order-2 `m/4, n/8` form, the general-Weierstrass "den ∣ 4" form, the named-after/Silverman source);
the standard form, generality, and the order-2 branch's *exceptional* role were probed; local refs
checked (absent → n/a); nLab/Stacks/nCatLab checked and reasoned n/a; MathOverflow-class expositions +
recent arXiv both checked and hit. ChatGPT MCP is genuinely down (tool error, not a skip), compensated
by the **verbatim Wikipedia/HandWiki `x=m/4, y=n/8` match**.

### Literature summary (Phase 3)

Concept identified as: **the order-2 branch of the Nagell–Lutz integrality theorem** — "a rational
2-torsion point on an integral general-Weierstrass model has `x ∈ ¼ℤ` and `y ∈ ⅛ℤ`", proved via the
**2-division relation** `ψ₂ = 0` (i.e. `2y + a₁x + a₃ = 0`) and the univariate
`Ψ₂Sq = 4x³ + b₂x² + 2b₄x + b₆`, whose **leading coefficient is 4**, so the **rational-root theorem**
gives `x.den ∣ 4`.

Sources agree on the standard form: **yes — and this time the match is verbatim.** Wikipedia's
generalized Nagell–Lutz statement says torsion points have integer coordinates "**or else have order 2
and coordinates of the form `x=m/4, y=n/8`**" — which is *exactly* the Lean conclusion
`∃ n, n=4x ∧ ∃ m, m=8y`. So unlike the order-4 branch (which is an unnamed internal step), the order-2
`m/4, n/8` bound is an **explicitly stated clause** of the standard generalized theorem. The *named*
object in the literature is still the **whole Nagell–Lutz theorem** (Silverman AEC, Silverman–Tate,
Cassels, Husemöller); the 2-torsion clause is a component of its statement, not a separately-named
theorem.

Most general standard form: over a **Dedekind domain / number field / PID** `R` with fraction field
`K` (place-by-place), general Weierstrass model, with the bound phrased as **`den_R(x) ∣ 4`** (the
basis-independent sharp form; Silverman). The "`4x, 8y ∈ ℤ`" unfolding is a ℚ-specific convenience.
This lemma is the `ℤ ⊂ ℚ` instance in the *unfolded* `∃:ℤ` form. (arXiv:2509.07524 is exactly such a
number-field generalisation.)

Generality dimensions where the literature varies:
  - **Base**: ℚ (this lemma) ↔ number field / Dedekind / PID `R ⊂ K`, place-by-place (most general).
  - **Model**: short `y²=x³+Ax+B` ↔ **general Weierstrass** (this lemma uses the **general** model — good;
    in the short model the order-2 case has `2y=0`, i.e. `y=0`, and `x³+Ax+B=0` with integer `x`).
  - **Conclusion form**: sharp **`den(x) ∣ 4`** (Silverman; basis-independent) ↔ unfolded **`4x, 8y ∈ ℤ`**
    (this lemma; ℚ-specific, *weaker*: it discards the `y`-denominator-divides-8 sharpness and re-packages
    as bespoke `∃:ℤ` witnesses).

Disagreement with the literature: **none** mathematically — it is a faithful (indeed verbatim-clause)
Lean rendering of the order-2 case of the generalized Nagell–Lutz theorem. The only gap is one of
*sharpness/idiom*: the literature/PID-standard `den(x) ∣ 4` is sharper and basis-independent than the
`4x, 8y ∈ ℤ` unfolding used here.

---

### Generality analysis — `bounded_den_of_order_two_general`

Literature-standard form (from Phase 3): the order-2 denominator bound over an arbitrary Dedekind
domain / PID `R` with fraction field `K` (place-by-place), general Weierstrass model, stated sharply as
**`den_R(x) ∣ (4:R)`**.

**Decisive fact: the maximally-general form already exists, in this very project.** The parallel PID
track declares `PIDPrimeOrder.den_dvd_of_order_two` (`PIDPrimeOrder.lean:179`), which is *exactly* this
lemma generalised **and sharpened**: over `R`/`K` with hypothesis `(4 : R) ≠ 0` (automatic for
`CharZero R`) and conclusion `(IsFractionRing.den R x : R) ∣ (4 : R)`. The project's own duplication
analysis (`.mathlib-quality/overview/analysis/05-duplications.md:67`) records this pair as
"Morally yes (2-torsion den bound) — Parallel (`Ψ₂Sq` root + `den_dvd_of_is_root`) — **special-case
(PID states `den∣4`; General's `4x,8y∈ℤ` is the ℚ unfolding)**". The generalisation analysis
(`06-generalization.md` §2) is even blunter: "**`General` is weaker than `PID`** … the `General` version
then *manually* unpacks `den ∣ 4` into the `4x, 8y` witnesses, **losing information**"; recommended
target = state the ℤ branch as `den ∣ 4` and derive `4x, 8y ∈ ℤ` only where a caller wants them.

| # | Parameter / hypothesis                              | Current Lean form                  | Literature-standard form (= PID twin)        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|------------------------------------|-----------------------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`, point over `curveQ W`     | base `ℤ`, field `ℚ`                | `R` a domain/UFD with `(4:R)≠0`, `K = FractionRing R`, point on `W.map (R→K)` | **yes** (already done in PID twin) | The descent generalises place-by-place. `(4:ℤ)≠0` holds trivially, so the General lemma is the `R=ℤ` instance. The PID twin `den_dvd_of_order_two` *is* the weakening — already proved, with `omit [DecidableEq K]` so it needs essentially nothing beyond a fraction-field. |
| 2 | conclusion `∃ n:ℤ, (n:ℚ)=4x ∧ ∃ m:ℤ, (m:ℚ)=8y`      | unfolded `∃:ℤ`, **weaker**         | sharp `den_R(x) ∣ (4:R)`                       | **yes** (PID twin states it) | mathlib/Silverman idiom is the divisibility `den(x) ∣ 4` (sharp, basis-independent). The `4x,8y∈ℤ` repackaging *discards* the `den(y) ∣ 8` sharpness and introduces an ad-hoc `∃:ℤ` surface. CHEAP to restate; the PID twin already does. |
| 3 | torsion encoding `2•P=0` (`h2`)                     | `(2:ℤ)•P=0`                        | identical (`h2`) — same in PID twin           | **NO** (essential)  | "2-torsion" is the defining hypothesis; the PID twin uses the identical `h2`. Correct as is. |
| 4 | general Weierstrass model                            | general (`a₁..a₆`)                | general                                       | **NO** (already general) | already at the right model-generality — strictly more general than the short corollary. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER / WEAKER THAN STANDARD** (base fixed to `ℤ⊂ℚ`; and the
conclusion is the *information-losing* `4x,8y∈ℤ` unfolding rather than the sharp `den(x) ∣ 4`) — though
already maximally general in the *model* dimension.
Number of weakening/sharpening opportunities found: **2** (base ring `ℤ→` domain/UFD `R` with `(4:R)≠0`;
conclusion `4x,8y∈ℤ →` sharp `den_R(x) ∣ 4`).
Proposed restatement: **it already exists** — `PIDPrimeOrder.den_dvd_of_order_two` (over `R`/`K`,
`(4:R)≠0`, concluding `den_R(x) ∣ 4`). The General lemma is its `R=ℤ, K=ℚ` instance, with the
denominator divisibility then *unfolded* (and partly discarded) into the `4x,8y` witnesses.
Cost of regeneralisation: **already paid** (the PID twin is fully proved, sorry-free, in the same
project). The "cost" is *deduplication / consolidation* (and reverting to the sharp conclusion), not
new mathematics.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                                                              | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|--------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                | yes      | state over `[CommRing R] [IsDomain R] … [IsFractionRing R K]` with `den_R(x) ∣ (4:R)` (exactly the PID twin's signature) instead of `ℤ⊂ℚ` + `∃:ℤ` | composes with all of `RationalRoot.lean` / `Localization/Rat.lean` (`IsFractionRing.den`) + mathlib's base-change EC API |
|  2 | sequences/metric → filters/topological?                                                            | no       | purely algebraic Diophantine statement; no analysis                                  | — |
|  3 | construct an object → universal-property class?                                                    | no       | it's a `Prop`, nothing constructed                                                   | — |
|  4 | set-with-closure-predicate → bundled-substructure?                                                 | no       | n/a                                                                                  | — |
|  5 | vector-space/field-specific → weaken to modules/(semi)ring?                                        | yes      | the `ℤ⊂ℚ` base weakens to a domain/UFD `R ⊂ FractionRing R` (row 1 of 4a) — done by the PID twin | unifies with number-field Nagell–Lutz (arXiv:2509.07524); reuses the same `Ψ₂Sq` root + rational-root machinery |
|  6 | 1-categorical → higher-categorical?                                                                | no       | n/a | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/monoid?                                                | partial  | the order `2` (and the constants `4`, `8`) are mathematically essential (this is *the* 2-torsion case, and `4 = lead(Ψ₂Sq)`); base `ℤ→R` is the real generalisation (covered by #5) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (two real improvements, both already realised by the PID twin:
the sharp `IsFractionRing.den R x ∣ (4:R)` conclusion; domain/UFD base with `(4:R)≠0`).
  - Proposed mathlib-idiomatic restatement: **`den_dvd_of_order_two`** verbatim — over `R` a
    domain/UFD, `K := FractionRing R`, `W : WeierstrassCurve R`, 2-torsion point `P` on `W.map (R→K)`,
    `(4:R)≠0`; conclusion `(IsFractionRing.den R x : R) ∣ (4:R)`.
  - Cost: **already paid** (the PID twin is proved). Consolidation + revert-to-sharp-conclusion only.
  - Mathlib downstream this enables: a base-independent, *sharp* order-2 denominator bound usable for
    number-field Nagell–Lutz; direct reuse of `IsFractionRing.den` / `den_dvd_of_is_root` without the
    `ℤ→ℚ` `∃:ℤ` shim; the `4x,8y∈ℤ` witnesses derived only where actually needed.
  - Real mathematical improvement: removes a redundant `ℤ⊂ℚ` specialisation AND restores the lost
    `den(y) ∣ 8` sharpness; the statement becomes the genuine "2-torsion x-denominator divides 4 over
    any domain" lemma — the Silverman-standard form.

NOTE (cost caveat, per the skill's gate): cost may inform *sequencing* but cannot by itself downgrade
the verdict bucket. The decisive factors here are (a) the **already-existing, sharper, more-general PID
twin in the same project** and (b) the **whole-theorem packaging/dedup scope** — not cost.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `bounded_den_of_order_two_general`

Method note: the local Lean build is stale, so the live loogle/leansearch indices may not reflect this
exact pin. The authoritative check is a **direct grep of the pinned mathlib checkout** the project
builds against (`.lake/packages/mathlib`, `d90090f`), plus reading the EC + EDS + RationalRoot source.
This corroborates the identical (independently-run) Phase-5 conclusions in all sibling reports.

[A] Lean-Finder       "2-torsion elliptic curve x coordinate denominator divides 4"                  n/a — index MCP unavailable in env; substituted by [D]/[E] grep over the pinned tree.
[B] Loogle            `(2:ℤ)•_ = 0 → _ → (∃ _:ℤ, _ = 4*_) ∧ _` over EC points (type pattern)          n/a — index unavailable; grep substitute. (No lemma of this shape exists — see [D].)
[C] LeanSearch        "Nagell-Lutz 2-torsion point x = m/4 y = n/8"                                   n/a — index unavailable; grep substitute.
[D] **Grep mathlib src (authoritative, exact pin)**:
      • `grep -rni "nagell|lutz"` over `Mathlib/`                                       → **only the unrelated mathematician Patrick Lutz** (Galois theory). **No Nagell–Lutz theorem.**
      • `grep "addOrderOf|IsOfFinAddOrder"` ∩ `AlgebraicGeometry/EllipticCurve/`        → **0 occurrences** (no torsion↔EC denominator/integrality result anywhere; the affine/Jacobian API stops at the abstract group law).
      • `grep "order.*two|two.*torsion|m/4|n/8|den.*4|integrality"` ∩ EC/EDS dirs        → **0** torsion-denominator results (only polynomial/EDS identities).
      • `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` → has the **building blocks** this proof consumes: `WeierstrassCurve.Ψ₂Sq` (`Basic.lean:117`), `C_Ψ₂Sq` (`Basic.lean:120`), `ψ_two` (`Basic.lean:415`), `map_Ψ₂Sq` (`Basic.lean:502`), `leadingCoeff_Ψ₂Sq` (`Degree.lean:85`, **`= 4`**) — but **no torsion-denominator theorem**.
      • `Mathlib/RingTheory/Polynomial/RationalRoot.lean` + `Localization/Rat.lean`     → `den_dvd_of_is_root` (`:89`), `isFractionRingDen` (`Rat.lean:31`) — the rational-root tools the proof uses. Generic; not EC-specific.
[E] Name pattern      `theorem … order_two … den` / `… two_torsion …` / `nagell_lutz` in mathlib       no hits.

Searched for both:
  - the user's current form (`2•P=0` ⇒ `4x,8y∈ℤ`, over `ℤ⊂ℚ`, general Weierstrass) — **not in mathlib**.
  - the literature-standard / general form (domain base, `den(x) ∣ 4`) — **not in mathlib** either
    (grep found zero torsion-denominator results at *any* generality).

_Project-framing note (the task flagged that this project forks `Mathlib.…DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and runs duplicated General/PID tracks): the proof
of THIS decl consumes the division-polynomial API by its `WeierstrassCurve.…` names (`Ψ₂Sq`, `ψ_two`,
`map_Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`, `mk_ψ₂_sq`). **Every one of those building-block names exists in
mathlib AND is re-declared (shadowed) in the project** — `Ψ₂Sq` in `DivisionPolynomial.lean:40`,
`leadingCoeff_Ψ₂Sq` in `DivisionPolynomialDegree.lean:81`, etc., all under `namespace WeierstrassCurve`.
So the fork **shadows** mathlib's identically-named lemmas. The mathlib originals it forks contain only
the polynomial machinery, **never this 2-torsion denominator theorem** — so this decl is decidedly
**not** already upstream; mathlib has only the building blocks._

Concluded: **not in mathlib** (all methods exhausted, both the user's form and the general/sharp form).
Mathlib has the **building blocks** (`Ψ₂Sq`, `ψ_two`, `leadingCoeff_Ψ₂Sq = 4`, `map_Ψ₂Sq`,
`den_dvd_of_is_root`) — which the project forks — but **not** this order-2 denominator step, and **no**
torsion↔denominator/integrality theorem at any generality.

---

### Call sites — `bounded_den_of_order_two_general`

Internal use count: **1** (within the NagellLutz project, excluding the declaring file
`GeneralPrimeOrder.lean:167`).
External-to-file callers: **1 distinct file** (`GeneralMain.lean`).

| Caller file:line                   | Usage pattern (one-line excerpt)                                                                       |
|------------------------------------|--------------------------------------------------------------------------------------------------------|
| GeneralMain.lean:123               | `exact ⟨hord2, bounded_den_of_order_two_general W hpt (nsmul_eq_zero_affine_to_jac W h2P)⟩`            |

The single caller is the **order-2 disjunct of `lutz_nagell_integrality_general`** itself (the parent
Nagell–Lutz theorem). When `addOrderOf P = 2`, the main theorem's conclusion takes its right disjunct
(`addOrderOf P = 2 ∧ 4x,8y∈ℤ`) and discharges it with this lemma — i.e. this is *the* lemma that
supplies the "or else order 2 with `x=m/4, y=n/8`" clause of the formalised generalized Nagell–Lutz
statement.

Inline-derivation grep (was the equivalent re-derived elsewhere without calling this lemma?): **(none)**
— the only other place the order-2 denominator content lives is the parallel **PID-track engine**
`den_dvd_of_order_two` (`PIDPrimeOrder.lean:179`), which is the *sharper, more general* analogue
(separate file, domain/UFD base, sharp `den ∣ 4`), not an inline re-derivation of the ℚ statement.

Call-sites reading: **K = 1** (one external-to-file caller, the order-2 disjunct of the main theorem).
Per the skill's call-sites table, "K = 1 internal use only" leans toward NO-composable / the
"possibly-the-wrong-abstraction" reading — *but* here the lemma is a **named, docstring'd, standard
clause** of a classical theorem's statement (the verbatim `x=m/4, y=n/8` case), tightly bundled with
its sibling branches (`integrality_of_order_four_general`, `prime_order_integrality_general`). Its
mathlib-worthiness is inseparable from the worthiness of the whole Nagell–Lutz development — exactly
the pattern that resolved the sibling `integrality_of_order_four_general` to BORDERLINE.

---

### Composition check (Phase 6)

Can `bounded_den_of_order_two_general` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: get `Ψ₂Sq(x)=0` from `2•P=0`, then rational-root (`den_dvd_of_is_root` +
`leadingCoeff_Ψ₂Sq = 4`), then clear denominators to `4x,8y∈ℤ`.
  - Mathlib decls used: `WeierstrassCurve.ψ_two`, `WeierstrassCurve.Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`,
    `map_Ψ₂Sq`, `den_dvd_of_is_root`, `isFractionRingDen` (all present in mathlib / forked).
  - Result: **fails as a ≤3-call composition.** Two of the steps need non-trivial *project* inputs that
    mathlib does not provide:
      (a) `ψ₂(x,y) = 0` from `2•P=0` comes from `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` — a
          **project bridge** through Jacobian coordinates (`zsmul_eq_smulEval`, `Z_eq_zero_of_equiv`),
          not a mathlib lemma;
      (b) passing from `ψ₂=0` to `Ψ₂Sq(x)=0` uses the CoordinateRing identity `mk_ψ₂_sq` together with
          the **project eval bridge** `evalEval_eq_of_mk_eq` (`evalEval_pow`, `zero_pow`, `evalEval_C`)
          — no mathlib one-liner connects the bivariate `ψ₂` vanishing to the univariate `Ψ₂Sq` root at
          an affine point;
      (c) the final `8y∈ℤ` step re-uses the 2-division relation `2y + a₁x + a₃ = 0` extracted in (a).
  - Notes: the body (lines 171–203) is a genuine multi-step proof — the `ψ₂=0` bridge, the `Ψ₂Sq`-root
    derivation, the `den ∣ 4` rational-root call, and **two explicit denominator-clearing
    constructions** (`field_simp`/`push_cast`/`linarith` to produce the `∃ n` and `∃ m` witnesses) —
    not a one-liner.

Attempt 2 (alternate angle, the sharp form): even targeting only `den(x) ∣ 4` (the PID-twin
conclusion), the rational-root call `den_dvd_of_is_root` still needs `Ψ₂Sq(x)=0` as input, which is
precisely the project-bridge content (a)+(b) and is **not** available in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib alone. Mathlib (incl. the forked division-polynomial API)
supplies `Ψ₂Sq`, `leadingCoeff_Ψ₂Sq = 4`, and the generic rational-root call, but the surrounding
inputs (the Jacobian-to-`ψ₂` bridge and the `ψ₂=0 → Ψ₂Sq(x)=0` CoordinateRing/eval bridge) are project
lemmas with no mathlib analog, plus the bespoke ℚ denominator-clearing. This is more than a 1–3
mathlib-call composition.

---

## Verdict: `LutzNagell.LutzNagellTheorem.bounded_den_of_order_two_general`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the **order-2 branch** of the classical generalized Nagell–Lutz theorem
  (Silverman AEC VIII.7 / Silverman–Tate / Alpoge "Nagell-Lutz, quickly" / Dummit & Doud). **This time
  the conclusion is a verbatim clause of the standard statement**: Wikipedia/HandWiki state torsion
  points have integer coordinates "or else have order 2 and coordinates of the form **`x=m/4, y=n/8`**"
  — exactly the Lean conclusion. The underlying sharp fact is "**`den(x) ∣ 4`**" (Silverman). Mathlib
  has **no** Nagell–Lutz theorem.
- Generality analysis (Phase 4): **STRICTLY NARROWER AND WEAKER THAN STANDARD** — base fixed `ℤ⊂ℚ`, and
  the conclusion is the *information-losing* `4x,8y∈ℤ` unfolding rather than the sharp `den(x) ∣ 4`. The
  maximally-general AND sharper form **already exists in this project** as
  `PIDPrimeOrder.den_dvd_of_order_two` (over a domain `R`/`K`, `(4:R)≠0`, concluding `den_R(x) ∣ 4`);
  the project's own `05-duplications.md:67` calls this General decl "the ℚ unfolding" / "special-case of
  PID", and `06-generalization.md §2` flags that the General version "**manually unpacks `den ∣ 4`…
  losing information**". Modern-idiom (4c) = **yes** (the PID twin is the idiomatic, sharp form). Already
  maximally general in the *model* dimension.
- Mathlib search (Phase 5): **not in mathlib** (both the user's form and the general/sharp form); direct
  grep of the pinned checkout finds zero Nagell/Lutz hits (only the unrelated Galois-theory author) and
  zero torsion↔denominator results at any generality. Mathlib has the building blocks `Ψ₂Sq`, `ψ_two`,
  `leadingCoeff_Ψ₂Sq = 4`, `map_Ψ₂Sq`, `den_dvd_of_is_root` (which the project forks), but not this step.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine multi-step proof whose inputs (Jacobian↔`ψ₂`
  bridge, the `ψ₂=0 → Ψ₂Sq(x)=0` CoordinateRing/eval bridge, and the bespoke ℚ denominator-clearing) are
  project lemmas, not a ≤3 mathlib-call chain. **K = 1** call site (the order-2 disjunct of the main
  theorem).

**Rationale (1–2 paragraphs):**

This is a faithful, sorry-free Lean rendering of a genuine, classical, and explicitly-named clause of
mathematics — the order-2 (`x=m/4, y=n/8`) case of the generalized Nagell–Lutz integrality theorem,
the *one* case where full integrality fails — and mathlib does not have it (mathlib has *no* Nagell–Lutz
and *no* torsion↔denominator theorem at any generality; it has only the division-polynomial and
rational-root infrastructure this proof consumes, which the project moreover *forks*). So it is neither
`NO-mathlib-has-it` (nothing to point at upstream) nor `NO-composable-from-mathlib` (the inputs to the
rational-root call — the Jacobian↔`ψ₂` bridge and the `ψ₂=0 → Ψ₂Sq(x)=0` eval bridge — are project
lemmas, not a ≤3 mathlib-call chain). On the YES side, two things hold it back from a clean verdict.
First, the conclusion is **both narrower AND strictly weaker than the standard/mathlib-idiom form**: the
literature (Silverman) and the project's own PID twin state the sharp, basis-independent
`den(x) ∣ 4`, whereas this decl manually unfolds that to `4x,8y∈ℤ` over `ℤ⊂ℚ`, *discarding* the
`den(y) ∣ 8` sharpness — which by the skill's gate forbids `YES-add-as-is`. Second, and decisively, **the
maximally-general AND sharper form already exists in this same project**:
`PIDPrimeOrder.den_dvd_of_order_two` is the `R`/`K`/`den ∣ 4` generalisation, of which this General decl
is essentially the `R=ℤ, K=ℚ` instance *with the conclusion unfolded and weakened* (the project's
`05-duplications.md` classifies it as "the ℚ unfolding … special-case of PID"). So this is not a
candidate for `YES-but-generalise-first` *in isolation* either — the generalisation isn't hypothetical
work, it's an existing, sharper duplicate, and the real question is **which of the two parallel tracks to
upstream and whether to keep the weak `4x,8y∈ℤ` form at all**.

That makes the honest verdict **BORDERLINE**, for the same structural reason its sibling
`integrality_of_order_four_general` came out BORDERLINE: this is an **intermediate helper with a single
call site** (the order-2 disjunct of `lutz_nagell_integrality_general`), tightly coupled to its sibling
branches and to the forked division-polynomial track, and it exists in **two near-duplicate copies**
(General ℤ⊂ℚ `4x,8y∈ℤ` vs PID `R`/`K` `den ∣ 4` — the latter sharper). It should ship to mathlib **only
as an internal step of the complete Nagell–Lutz theorem**, in mathlib's idiom (`IsFractionRing.den …`,
general base, the sharp `den ∣ 4` conclusion, with the `4x,8y∈ℤ` witnesses derived only where a caller
wants them), after the General↔PID duplication is resolved — which track is canonical, whether to keep
the weak unfolded form, and whether the order-2 branch is exposed as a standalone lemma or inlined into
the main proof, are packaging-and-scope judgment calls the skill should not make alone. (The parent
theorem `lutz_nagell_integrality_general` was assessed **YES** — `YES-but-generalise-first` in the report
header; this helper rides along with that PR rather than being an independent addition.)

**Numbered questions (≤5):**

1. Is the **whole Nagell–Lutz theorem** (`lutz_nagell_integrality_general`, assessed YES) being
   upstreamed to mathlib? If yes, this order-2 branch rides along as the lemma supplying the
   "`x=m/4, y=n/8`" disjunct — restated in mathlib idiom — and the question collapses to "expose it as a
   named lemma, or inline it into the main proof?"
2. The project already has the strictly-**sharper and more general** `den_dvd_of_order_two` (domain/UFD
   base, `(4:R)≠0`, sharp `den_R(x) ∣ 4`). Which of the two parallel tracks — **General (ℤ⊂ℚ,
   `4x,8y∈ℤ`)** or **PID (`R`/`K`, `den ∣ 4`)** — is the intended canonical form to upstream, so mathlib
   doesn't receive two near-duplicate order-2 lemmas?
3. Should the upstreamed order-2 step state the **sharp `IsFractionRing.den R x ∣ (4:R)`** (the
   PID-twin/Silverman idiom) rather than the current `4x,8y∈ℤ` unfolding, which discards the
   `den(y) ∣ 8` sharpness? (Strongly preferred — mathlib favours the sharp, basis-independent form; the
   `4x,8y∈ℤ` witnesses should be derived only where a downstream caller needs them.)
4. Is the order-2 branch worth exposing as a **standalone public lemma** in mathlib at all, given its
   single call site is the order-2 disjunct of `lutz_nagell_integrality_general`? Or should it be a
   `private`/`local` step (or inlined) inside the Nagell–Lutz file?
5. Before any of this: are the project's **forks** of `WeierstrassCurve.{Ψ₂Sq, ψ_two, leadingCoeff_Ψ₂Sq,
   map_Ψ₂Sq, mk_ψ₂_sq}` (in `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean`) going to be
   **reconciled against mathlib's identically-named originals** before upstreaming? They are the
   prerequisite; the upstreamed proof must build on mathlib's versions, not the project's shadows.

Next action: user answers the questions; re-run `/mathlibable` on the chosen canonical order-2 form
(most likely the **sharp PID `den ∣ 4` form**, or the bundled Nagell–Lutz statement) to resolve the
verdict. The most likely resolution, if Nagell–Lutz is headed upstream, is that this helper is
**absorbed into the Nagell–Lutz PR** — restated as the sharp `den ∣ 4` step over the canonical base and
likely kept `private`/inlined — rather than shipped as an independent declaration in its current weak
`4x,8y∈ℤ` / `∃:ℤ` form.

---

## Next step

User answers the 5 questions above. If the Nagell–Lutz theorem is bound for mathlib, treat this order-2
branch as an **internal step of that PR** — restated over the canonical base in the **sharp `den(x) ∣ 4`
form** (deduplicating the General↔PID pair, with the `4x,8y∈ℤ` witnesses derived only where needed) and
likely kept `private`/inlined — after first reconciling the forked `DivisionPolynomial.*` dependencies
against mathlib's originals. As an isolated declaration in its current `ℤ⊂ℚ` / `4x,8y∈ℤ` / `∃:ℤ` form, it
is **not** an independent mathlib addition.
