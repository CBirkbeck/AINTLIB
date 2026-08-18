# /mathlibable report — `LutzNagell.PID.integrality_of_order_four_squarefree`

_Assessment date: 2026-06-22. Mathlib pin: `09b373db6e24` (toolchain `v4.32.0-rc1`), read directly
from `/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. The local Lean
build is stale per the task brief, so **mathlib presence/absence is established by direct grep of the
pinned checkout** (authoritative for this pin) plus **independent WebSearch** for the literature
standard. Every load-bearing claim — the statement + proof, the building blocks in mathlib, the
absence of any Nagell–Lutz / torsion-integrality result, the call sites, the literature-standard
reduction-theoretic form, the relation to the General twin and the PID apex — was re-verified from
primary sources in this run. The verdict (YES-but-generalise-first) coincides with the sibling PID-track
apex `lutz_nagell_integrality_pid` (assessed 2026-06-21, same bucket, same literature ground) and is
consistent with the General twin `integrality_of_order_four_general` (BORDERLINE, whose named
generalisation target **is this very declaration**)._

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  a direct read of the pinned mathlib checkout. Full statement + proof read from
  `PIDPrimeOrder.lean:151–172`.
- decl `LutzNagell.PID.integrality_of_order_four_squarefree`:
                            ✓ resolved at `PIDPrimeOrder.lean:151` (the `theorem` keyword line; the
                            task brief's "line 151" is exact).
- qualified name:           ✓ **VERIFIED** `LutzNagell.PID.integrality_of_order_four_squarefree`
                            — `namespace LutzNagell` (line 24) → `namespace PID` (line 25); base name
                            `integrality_of_order_four_squarefree` (line 151). Matches the task's
                            parsed guess exactly.
- kind:                     theorem
- has sorry:                no — complete proof (lines 156–172): `ψ_four` factor split via
                            `mul_eq_zero`, then `preΨ₄`-root → `IsInteger R x` via
                            `isInteger_of_root_squarefree_leading_coeff`, then `y` via
                            `y_isInteger_of_x_isInteger_on_curve`; else `ψ₂=0` ⇒ `2•P=0` contradiction.
- module docstring summary: "Prime-order torsion integrality for Weierstrass curves over UFDs":
                            when `(p : R)` is squarefree (the prime does not ramify), torsion points of
                            odd prime order have integral coordinates; the core new theorem
                            `isInteger_of_root_squarefree_leading_coeff` combines the rational-root
                            theorem with the generalized denominator lemma. This decl is the **order-4
                            (2-power) branch** living in the same file.

---

### Statement (Phase 1)

`integrality_of_order_four_squarefree` states: let `R` be a UFD (`[CommRing R] [IsDomain R]
[UniqueFactorizationMonoid R]`) with fraction field `K` (`[Field K] [Algebra R K] [IsFractionRing R K]`),
let `W : WeierstrassCurve R` be a Weierstrass curve with coefficients in `R`, and let `P = (x, y)` be a
nonsingular affine point on the base-change `curveK R K W = W.map (algebraMap R K)`. If `P` has **exact
order 4** — encoded as `4 • P = 0` (`h4`, in the Jacobian point group) together with `2 • P ≠ 0`
(`h2ne`, in the affine group) — and **`2` is squarefree in `R`** (`hsf : Squarefree (2 : R)`, i.e. the
prime `2` does not ramify), then **both coordinates of `P` are `R`-integers**:
`IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`.

This is the **order-4 (2-power) branch** of the division-polynomial proof of Nagell–Lutz, generalised
from the classical `ℤ ⊂ ℚ` base to an arbitrary UFD `R ⊂ K = Frac(R)`. The proof (read from source):
from `4 • P = 0` one gets `ψ₄(x,y) = 0` (project bridge `evalEval_ψ_eq_zero_of_zsmul_eq_zero`); the
factorisation `WeierstrassCurve.ψ_four : ψ₄ = C(preΨ₄)·ψ₂` then splits the vanishing via `mul_eq_zero`.
In the `preΨ₄(x) = 0` case, `x` is a root of `W.preΨ₄ ∈ R[X]` whose **leading coefficient is `2`**
(`leadingCoeff_preΨ₄`, valid since `Squarefree (2:R) ⇒ (2:R) ≠ 0`), and `Squarefree (2:R)` makes that
leading coefficient squarefree; the **core squarefree-leading-coeff integrality lemma**
`isInteger_of_root_squarefree_leading_coeff` (rational-root theorem `den_dvd_of_is_root` + the
denominator lemma `den_no_simple_prime_factor_of_on_curve`) then forces `x ∈ R`, and `y ∈ R` follows
from the curve equation (`y_isInteger_of_x_isInteger_on_curve`). In the `ψ₂(x,y) = 0` case,
`two_nsmul_eq_zero_of_ψ₂_eq_zero` gives `2 • P = 0`, contradicting `h2ne`.

Variables / typeclasses (Lean side):
- `R : Type*` with `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — a UFD base ring.
- `K : Type*` with `[Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` — its fraction field.
- `W : WeierstrassCurve R` — general Weierstrass model with `R`-coefficients.

Hypotheses (Lean side):
- `hns : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` nonsingular on `W ⊗ K` (gives the curve
  equation and `P ≠ O`).
- `h4 : (4 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0` — `4 • P = 0`.
- `h2ne : (2 : ℕ) • Affine.Point.some _ _ hns ≠ 0` — `2 • P ≠ 0` (so `P` has order exactly 4).
- `hsf : Squarefree (2 : R)` — the prime `2` is unramified in `R` (the global surrogate hypothesis).

Conclusion (math): a `K`-point of exact order 4 on a Weierstrass model over a UFD `R`, with `2`
unramified, has `R`-integer coordinates.
Conclusion (Lean): `IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`.

---

### Size classification (Phase 2a)

**Verdict: SMALL** (an internal branch inside a BIG named theorem).
Reason: a **helper lemma** — the order-4 (2-power) branch of the Nagell–Lutz integrality dichotomy,
structurally parallel to the odd-prime branch `x_isInteger_of_odd_prime_torsion_squarefree`
(`PIDPrimeOrder.lean:113`) and the order-2 branch `den_dvd_of_order_two` (`:179`). It is **not** itself
listed under `## Main results` (those live in `PIDMain.lean`: `lutz_nagell_integrality_pid`,
`lutz_nagell_number_field`, the discriminant theorems). The enclosing **Nagell–Lutz integrality
theorem** `lutz_nagell_integrality_pid` (`PIDMain.lean:142`, assessed YES-but-generalise-first) is the
BIG named target; this decl is one supporting branch of its proof.

(Literature width is EXHAUSTIVE regardless. SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. **n/a** — skipped. (Body is a multi-line tactic
proof with genuine `rcases mul_eq_zero.mp hψ₄ with hpreΨ | hψ₂` case analysis, lines 157–172, each
branch several `have`s deep.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem division polynomial order 4 torsion point integer coordinates elliptic curve proof" | yes  | division polynomials encode the denominators of mult-by-`n`; the order-4 case is an **internal step** of the div-poly proof, not a named standalone result | Alpoge "Nagell–Lutz, quickly" (Harvard); Wikipedia "Nagell–Lutz theorem"; Galperin (UChicago REU); A Neighbourhood of Infinity |
|  2 | WebSearch (general form)         | "Nagell-Lutz over number fields / Dedekind domain torsion integral reduction prime by prime"            | yes  | **standard proof is prime-by-prime via reduction / formal groups (Silverman AEC VII–VIII)**: a torsion point is `𝔭`-integral at every prime `𝔭` whose residue characteristic does not divide its order; needs only a **DVR at each prime**, no global PID and no `Squarefree (p:R)` surrogate | Silverman AEC VII.3 (formal group) + VIII.7.1 (Nagell–Lutz); the global-PID/squarefree packaging is a surrogate the standard theory avoids |
|  3 | WebSearch (named-after / source) | Silverman AEC VIII.7 / Silverman–Tate Ch.II / Cassels LMSST                                              | yes  | integrality via local (p-adic, incl. 2-adic) denominators; the `p=2` / order-4 part is the **2-adic descent**: `x.den` is a power of `2`, excluded by the local condition | Silverman AEC; Silverman–Tate "Rational Points on Elliptic Curves"; Husemöller; Cassels |
|  4 | ChatGPT MCP                      | (math second-opinion on the standard generality of the order-4 / 2-power step)                          | n/a  | —                   | MCP unavailable in this env per task brief; compensated by Silverman AEC VII–VIII (#2,#3) + the explicit div-poly order-4 description (#1) |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                              | n/a  | (absent)            | confirmed this session: no `references/` dir (only `overview/`); `refs/` store not present. Recorded n/a. |
|  6 | nLab                             | "Nagell-Lutz theorem" / "torsion of elliptic curves"                                                     | no   | —                   | nLab has no dedicated Nagell–Lutz page (elementary Diophantine result, not a categorical concept) |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | Nagell-Lutz / torsion integrality of `E/K`                                                               | n/a  | —                   | Stacks does scheme-theoretic AG foundations, not the Diophantine arithmetic of `E(K)_tor` |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz via division polynomials, order-4 / 2-power torsion integrality; reduction approach          | yes  | community proofs match Silverman/Cassels; `x`-coord denominators only grow under reduction; order-4 = 2-adic descent step | A Neighbourhood of Infinity exposition; MO threads on Nagell–Lutz over number fields |
| 10 | recent arXiv (last 5 years)      | Nagell-Lutz generalisations to number fields / imaginary quadratic fields                                | yes  | **arXiv:2509.07524 (2025)** generalises Nagell–Lutz to imaginary quadratic fields with class number one; cites the classical ℤ statement | confirms base-ring generalisation (ℤ → number field/Dedekind) is the natural move (= what the PID track does); **no Lean/mathlib version exists** |

Protocol passes: WebSearch ran **3 distinct queries** at different generality levels (the order-4/`ψ₄`
step; the reduction-theoretic Dedekind/number-field form; the named-after / Silverman source). The
standard form, its generality, and the order-4 step's role were probed. Local refs checked (absent →
n/a); nLab/Stacks/nCatLab checked and reasoned n/a; MathOverflow-class expositions and recent arXiv both
checked and hit. ChatGPT MCP genuinely unavailable, compensated by Silverman AEC VII–VIII and the
verbatim div-poly order-4 description.

### Literature summary (Phase 3)

Concept identified as: **the order-4 (2-power) branch of the Nagell–Lutz integrality theorem** — "a
torsion point of exact order 4 on a Weierstrass model has integer coordinates", proved via the
**division-polynomial factorisation** `ψ₄ = preΨ₄ · ψ₂`, the **rational-root theorem** on `preΨ₄`
(leading coefficient `2` ⇒ the denominator of `x` is supported only at `2`), and a **denominator/2-adic
condition** excluding a simple factor of `2` in the denominator.

Sources agree on the standard form: **yes**, with two nuances:
  1. The *named* object is the **whole Nagell–Lutz theorem** (Silverman AEC VIII.7.1, Silverman–Tate,
     Cassels, Husemöller); the **order-4 case is an internal step**, not a separately named result.
  2. The standard *proof* of the integrality is **prime-by-prime via reduction / formal groups**
     (Silverman AEC VII.3 + VIII.7): a torsion point is `𝔭`-integral at every prime `𝔭` of good
     reduction whose residue characteristic does not divide its order. This needs only a **DVR at each
     prime** — **not** a global PID, and **not** the `Squarefree (p : R)` ("`p` unramified") surrogate.

Most general standard form: over a **Dedekind domain** `R` with fraction field `K`, torsion points are
`R`-integral provided that at each relevant prime the residue characteristic does not divide the order
(automatically the case away from finitely many primes). The PID + `Squarefree (2:R)` form is a global
surrogate for this local condition.

Generality dimensions where the literature varies:
  - **Base**: ℤ (classical) ↔ UFD (this track) ↔ **Dedekind / DVR-per-prime** (most general, standard).
  - **Ramification hypothesis**: `Squarefree (2:R)` global surrogate (this decl) ↔ **local "residue char
    ∤ order at each good prime"** (standard reduction form — strictly weaker / more natural).
  - **Model**: short `y²=x³+Ax+B` ↔ **general Weierstrass** (this decl uses the **general** model — good).
  - **Integrality encoding**: `IsLocalization.IsInteger R x` — already the mathlib idiom (good; the
    General twin's bespoke `∃ x₀:ℤ` encoding has already been modernised away here).

Disagreement with the literature: **none on correctness.** This is a faithful Lean rendering of the
order-4 step. The only gap to the literature standard is *generality*: the `Squarefree (2:R)` + UFD
packaging is a global surrogate for the standard prime-by-prime reduction condition over a Dedekind
domain.

---

### Generality analysis — `integrality_of_order_four_squarefree`

Literature-standard form (from Phase 3): the same order-4 integrality over a **Dedekind domain** `R`
(DVR at each prime), general Weierstrass model, with the **local** ramification/good-reduction condition
("residue characteristic ∤ order at each relevant prime") in place of the global `Squarefree (2:R)`, and
`IsLocalization.IsInteger R` (already used here).

**Decisive framing fact, re-verified this session by reading `PIDPrimeOrder.lean:151–172` and the General
twin's report directly: this declaration is ALREADY the maximally-general form *within the project* — it
is exactly the restatement that the General twin `integrality_of_order_four_general`
(`GeneralPrimeOrder.lean:118`, assessed BORDERLINE) names as its generalisation target.** The General
twin is the `R=ℤ, K=ℚ` specialisation (with `Squarefree (2:ℤ)` discharged for free, since 2 is prime in
ℤ) and is an independently-written parallel proof, not a caller of this decl (confirmed: grep shows the
General decl does not invoke the squarefree one). So the "generalise toward the PID form" move is
**already done** by this decl. The remaining generalisation is the *next* one, toward the
reduction-theoretic Dedekind/DVR form — identical to the gap identified for the sibling apex
`lutz_nagell_integrality_pid` (which carries the same `Squarefree (p:R)` surrogate and was assessed
YES-but-generalise-first on exactly this ground).

| # | Parameter / hypothesis                              | Current Lean form                  | Literature-standard form                        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|------------------------------------|-------------------------------------------------|---------------------|----------------------------------|
| 1 | `[UniqueFactorizationMonoid R]` (UFD base)          | UFD `R`                            | **Dedekind domain** `R` (DVR at each prime)     | **yes**             | The standard proof is local (prime-by-prime reduction), needing only a DVR at each prime; a Dedekind domain supplies exactly that and is the canonical mathlib setting (`IsDedekindDomain`). UFD is a convenient global surrogate that the rational-root route exploits, but it is narrower than the standard hypothesis. |
| 2 | `hsf : Squarefree (2 : R)`                           | `2` unramified, **global**         | **local**: at each prime `𝔭` above `2`, residue char ∤ order (here ord = 4, char = 2 must be excluded) | **yes** | `Squarefree (2:R)` is a global stand-in for "`2` is unramified," used so the squarefree-leading-coeff rational-root lemma applies. The standard 2-adic descent needs the condition only at primes above `2`. Strictly weaker / more natural in the reduction formulation. |
| 3 | order-4 encoding `4•P=0` (`h4`) + `2•P≠0` (`h2ne`)   | `4•P=0` ∧ `2•P≠0`                  | identical                                       | **NO** (essential)  | "exact order 4" is the defining hypothesis of this branch; correct as is (the order `4` is mathematically essential, not an incidental index). |
| 4 | general Weierstrass model                            | general (`a₁..a₆`)                 | general                                         | **NO** (already general) | already at the right model-generality — strictly more general than a short-form corollary. |
| 5 | integrality `IsLocalization.IsInteger R x/y`         | `IsInteger R`                      | `IsInteger R`                                   | **NO** (already idiomatic) | already the mathlib idiom; no change needed (this decl already improves on the General twin's `∃ x₀:ℤ` encoding). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — base `[UniqueFactorizationMonoid R]` (UFD) is
narrower than the standard `[IsDedekindDomain R]`, and the global `Squarefree (2:R)` hypothesis is a
surrogate for the strictly-weaker local good-reduction condition. (It is already maximally general in the
*model* and *integrality-encoding* dimensions, and is already the generalisation target of the General
twin.)
Number of weakening opportunities found: **2** (UFD → Dedekind/DVR base; global `Squarefree (2:R)` →
local residue-characteristic condition).
Proposed restatement: the order-4 specialisation of the reduction-theoretic Nagell–Lutz over a Dedekind
domain (see Phase 4c / Phase 7 for the target shape). Its proof does **not** survive — it needs
reduction-of-elliptic-curves + formal-group-torsion infrastructure that mathlib does not yet have.
Cost of regeneralisation: **EXPENSIVE** — mathlib has no reduction map for elliptic curves and no
formal-group torsion theory. (Per the skill gate, EXPENSIVE does not downgrade the verdict; it informs
sequencing only.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation                                                              | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|--------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                | partial  | base via `[IsDedekindDomain R] [IsFractionRing R K]`; the integrality is **already** `IsLocalization.IsInteger R` (no change needed there — already modernised vs. the General twin's `∃ x₀:ℤ`) | composes with mathlib's `IsLocalization` / `IsDedekindDomain` / height-one-spectrum localisation APIs |
|  2 | sequences/metric → filters/topological?                                                            | no       | purely algebraic Diophantine statement; no analysis                                  | — |
|  3 | construct an object → universal-property class?                                                    | no       | it's a `Prop`; nothing constructed                                                   | — |
|  4 | set-with-closure-predicate → bundled-substructure?                                                 | no       | n/a                                                                                  | — |
|  5 | vector-space/field-specific → weaken to modules/(semi)ring?                                        | yes      | the **UFD + global `Squarefree (2:R)`** packaging weakens to a **Dedekind domain with the local good-reduction condition** (the reduction-theoretic form) — exactly the standard generality from Phase 3 | torsion-injection `E(K)_tor ↪ Ẽ(k_𝔭)` at good primes; uniform PID / number-field / local-field corollaries; classical ℚ as a one-liner |
|  6 | 1-categorical → higher-categorical?                                                                | no       | n/a | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/monoid?                                                | partial  | the order `4` is mathematically essential (this is *the* order-4 case), not an incidental index; the real generalisation is the base ring `R` and the ramification hypothesis (covered by #1/#5) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — the reduction-theoretic Dedekind/DVR formulation with the local
good-reduction condition is the contemporary mathlib idiom and removes the global-UFD + `Squarefree (2:R)`
redundancy. (The integrality encoding is *already* idiomatic here — `IsLocalization.IsInteger R` — so that
part of the modernisation is already realised, distinguishing this decl from its General twin.)
  - Proposed mathlib-idiomatic restatement: the order-4 specialisation of
    `WeierstrassCurve.torsion_isInteger_of_goodReduction` over `[IsDedekindDomain R] [IsFractionRing R K]`
    (target shape in Phase 7); `Squarefree (2:R)` replaced by the local condition at primes above `2`.
  - Cost: **EXPENSIVE** — requires elliptic-curve reduction + formal-group torsion, not yet in mathlib.
  - Mathlib downstream this enables: torsion-injection `E(K)_tor ↪ Ẽ(k_𝔭)` at good primes (the standard
    tool for *bounding* torsion subgroups); uniform PID / number-field (class-number-1) / local-field
    corollaries; classical ℚ Nagell–Lutz as a one-line specialisation; composability with a future
    Néron-model / good-reduction API.
  - Real mathematical improvement: replaces a global combinatorial surrogate (UFD + per-prime squarefree
    image) with the genuine local good-reduction statement the literature uses — it is the right form, and
    everything proved here over a UFD falls out as a corollary.

NOTE (cost caveat, per the skill's gate): cost may inform *sequencing* but cannot by itself downgrade the
verdict bucket. The decisive factor here is the Phase-4b STRICTLY-NARROWER finding (UFD + global
`Squarefree` vs. the reduction-theoretic Dedekind/DVR standard), not cost.

---

### Diamond / defeq risk — Phase 4.5

**n/a** — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).
The six-row table is skipped per the skill's scope rule. Proceeding to Phase 5.

---

### Mathlib search-status: `integrality_of_order_four_squarefree`

Method note: local Lean build stale, so live loogle/leansearch indices may not reflect this pin. The
authoritative check is a **direct grep of the pinned mathlib checkout** (`.lake/packages/mathlib`,
`09b373db6e24`), plus reading the EC + EDS + RationalRoot source. All greps below were **re-run this
session**.

[A] Lean-Finder       "order 4 torsion elliptic curve integral coordinates over UFD / Dedekind"   n/a — index MCP unavailable in env; substituted by [D]/[E] grep over the pinned tree.
[B] Loogle            `Squarefree (2:_) → (4:ℤ)•_=0 → _ → IsLocalization.IsInteger _ _ ∧ _`         n/a — index unavailable; grep substitute. (No lemma of this shape exists — see [D].)
[C] LeanSearch        "order four torsion point on a Weierstrass curve has integer coordinates"     n/a — index unavailable; grep substitute.
[D] **Grep mathlib src (authoritative, exact pin — re-run this session)**:
      • `grep -rIn -iw "nagell"` over `Mathlib/`                                          → **ZERO hits in file contents** (the earlier filename matches were a coincidence of substrings; no `.lean` body contains "Nagell" or "Lutz"). **No Nagell–Lutz theorem in mathlib.**
      • `grep -rIn "IsInteger"` over `AlgebraicGeometry/EllipticCurve/` and `NumberTheory/EllipticDivisibilitySequence.lean` → **0 occurrences** — no torsion↔integrality result anywhere; the affine/Jacobian/EDS API stops at the abstract group law and the division/torsion **polynomials**.
      • `grep -rIn "torsion"` over `AlgebraicGeometry/EllipticCurve/`                       → only the **2-torsion polynomial** machinery (`Weierstrass.lean:300+`, `twoTorsionPolynomial`) and division-polynomial comments (`DivisionPolynomial/Basic.lean:91`) — **no integrality-of-torsion theorem.**
      • `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean` (building blocks, **confirmed present**): `preΨ₄` (`Basic.lean`), `coeff_preΨ₄ : … = 2` (`Degree.lean:130`), **`leadingCoeff_preΨ₄ (h : (2:R)≠0) : … = 2` (`Degree.lean:145`)**, `natDegree_preΨ₄`, `preΨ₄_ne_zero`; plus (per the proof's consumption) `ψ_four`, `map_preΨ₄` — **but NO integrality theorem.** (The project **re-defines/shadows** these under its own `namespace WeierstrassCurve` in `DivisionPolynomial.lean:346` (`ψ_four`), `:433` (`map_preΨ₄`), `DivisionPolynomialDegree.lean:141` (`leadingCoeff_preΨ₄`).)
      • `Mathlib/RingTheory/Polynomial/RationalRoot.lean` (imported by this file, **confirmed present**): `den_dvd_of_is_root`, `isInteger_of_is_root_of_monic`, `isInteger_of_isUnit_den` — the generic rational-root tools (not EC-specific).
[E] Name pattern      `theorem … integrality_of_order_four` / `…four_torsion…` / `nagell_lutz` in mathlib   → no hits.

Searched for both:
  - the user's current form (`Squarefree (2:R)` + `4•P=0 ∧ 2•P≠0` ⇒ `IsInteger R x ∧ IsInteger R y`, over a
    UFD, general Weierstrass) — **not in mathlib**.
  - the literature-standard / general form (Dedekind/DVR base, local good-reduction condition, order-4) —
    **not in mathlib** either (grep found zero torsion-integrality results at *any* generality).

_Project-framing note (the task flagged that this project forks `Mathlib.…DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and runs duplicated General/PID tracks): the proof of
THIS decl consumes the division-polynomial API by its `WeierstrassCurve.…` names (`ψ_four`, `preΨ₄`,
`leadingCoeff_preΨ₄`, `map_preΨ₄`), which the project **shadows** under its own `namespace WeierstrassCurve`.
The mathlib originals it forks contain **only** the polynomial machinery, **never** this integrality
theorem — so this decl is decidedly **not** already upstream; mathlib has only the building blocks._

Concluded: **not in mathlib** (all methods exhausted, both the user's form and the general reduction form).
Mathlib has the **building blocks** (`preΨ₄`, `leadingCoeff_preΨ₄ = 2`, `ψ_four`, `den_dvd_of_is_root`,
`isInteger_of_isUnit_den`) — which the project forks — but **not** this order-4 integrality step, and **no**
torsion↔integrality theorem at any generality.

---

### Call sites — `integrality_of_order_four_squarefree`

(Re-grepped this session over `projects/`, excluding the declaring file `PIDPrimeOrder.lean:151`.)

Internal use count: **1**.
External-to-file callers: **1 distinct file** (`PIDMain.lean`).

| Caller file:line       | Usage pattern (one-line excerpt)                                                                                  |
|------------------------|------------------------------------------------------------------------------------------------------------------|
| PIDMain.lean:126       | `obtain ⟨hx'_int, hy'_int⟩ := integrality_of_order_four_squarefree W hns' (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne) hsf2` |

The single caller is the helper at `PIDMain.lean:~110` (the "`4 ∣ addOrderOf P`" dispatch branch of
`lutz_nagell_integrality_pid`): it reduces a finite-order point whose order is divisible by 4 to a
multiple `k•P` of exact order 4, applies this lemma, then descends to `P` via `isInteger_of_nsmul_isInteger`.

Inline-derivation grep (equivalent re-derived elsewhere without calling this lemma?): **(none)** — the only
other place the order-4 integrality content lives is the parallel **General-track engine**
`integrality_of_order_four_general` (`GeneralPrimeOrder.lean:118`), which is the *less* general `ℤ⊂ℚ`
analogue (separate file, independently written), **not** an inline re-derivation of the UFD statement.

Call-sites reading: **K = 1** (one external-to-file caller, the order-4 branch of the PID main theorem).
The skill's table reads "K = 1" as a weak NO-composable / wrong-abstraction lean — **but** here the lemma
is a **named, docstring'd branch of a classical theorem's proof**, tightly bundled with its sibling branches
(odd-prime `x_isInteger_of_odd_prime_torsion_squarefree`, order-2 `den_dvd_of_order_two`). Crucially, it has
a **real caller** and an **independent multi-branch proof** (not a thin wrapper like the NO-composable
sibling `x_integral_of_nsmul_x_integral_general`), so the NO-composable signal does **not** transfer. Its
mathlib-worthiness is inseparable from that of the whole PID Nagell–Lutz development.

---

### Composition check (Phase 6)

Can `integrality_of_order_four_squarefree` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `mul_eq_zero.mp` on `ψ₄(P)=0`, then rational-root (`den_dvd_of_is_root` /
`isInteger_of_isUnit_den`) on the `preΨ₄` factor.
  - Mathlib decls used: `WeierstrassCurve.ψ_four`, `mul_eq_zero`, `den_dvd_of_is_root`,
    `leadingCoeff_preΨ₄` (all present in mathlib / the fork).
  - Result: **fails as a ≤3-call composition.** Each "call" needs non-trivial *project* inputs that mathlib
    does not provide:
      (a) `ψ₄(P) = 0` comes from `evalEval_ψ_eq_zero_of_zsmul_eq_zero` — a project bridge through Jacobian
          coordinates (`zsmul_eq_smulEval`, `Z_eq_zero_of_equiv`), not a mathlib lemma;
      (b) `x ∈ R` from the `preΨ₄`-root needs `isInteger_of_root_squarefree_leading_coeff` — the project's
          **core** lemma combining the rational-root theorem with the denominator lemma
          `den_no_simple_prime_factor_of_on_curve` (which uses `Squarefree (2:R)` to exclude a simple prime
          factor of the denominator); no mathlib counterpart;
      (c) the `ψ₂(P)=0 ⇒ 2•P=0` contradiction branch needs `two_nsmul_eq_zero_of_ψ₂_eq_zero` (project) →
          `Affine.Point.add_of_Y_eq` (mathlib), plus `h2ne`;
      (d) the final `y∈R` step needs `y_isInteger_of_x_isInteger_on_curve` (project).
  - Notes: the body (lines 157–172) is a genuine multi-step proof — `rcases … with hpreΨ | hψ₂`, two branches
    each with several `have`s, `rw`/`change`/`absurd`/`obtain` reasoning — not a one-liner.

Attempt 2 (alternate angle): treat the `preΨ₄` branch as pure rational-root once `ψ₄(P)=0` and the
squarefree-denominator exclusion exist — but producing those two inputs is precisely the mathematical content
and is **not** available in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib alone. Mathlib (incl. the forked division-polynomial API) supplies
the `ψ_four` factorisation and the generic rational-root call, but the surrounding inputs (the
Jacobian-to-`ψ₄` bridge, the squarefree-leading-coeff integrality lemma + denominator exclusion, the order-2
contradiction, the `y`-integrality) are project lemmas with no mathlib analog. Far more than a 1–3 mathlib-call
composition.

---

## Verdict: `LutzNagell.PID.integrality_of_order_four_squarefree`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): the order-4 case is an internal step of the **Nagell–Lutz theorem**; the
  standard *proof* of integrality is **prime-by-prime via reduction / formal groups** over a Dedekind
  domain (Silverman AEC VII.3 + VIII.7.1), needing only a DVR at each prime — **no global UFD and no
  `Squarefree (2:R)` surrogate**. Number-field generalisations are active (arXiv:2509.07524, 2025); no
  Lean/mathlib version exists.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — UFD base (narrower than
  `IsDedekindDomain`) + global `Squarefree (2:R)` (surrogate for the strictly-weaker local good-reduction
  condition). Already maximally general in the *model* and *integrality-encoding* (`IsInteger R`) dimensions,
  and already the named generalisation target of the General twin. Phase 4c confirms the reduction-theoretic
  Dedekind/DVR form is a genuine modernisation. Cost EXPENSIVE (does not downgrade the verdict).
- Mathlib search (Phase 5): **not in mathlib** at any generality (zero `Nagell`/`Lutz`, zero
  torsion↔integrality in `EllipticCurve/`); mathlib has only the **building blocks** (the division-polynomial
  API + generic rational-root tools), which the project forks.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the proof routes through four project-specific lemmas
  (Jacobian→`ψ₄` bridge, `isInteger_of_root_squarefree_leading_coeff`, the order-2 contradiction, the
  `y`-integrality) with no mathlib analog.

**Rationale:**

Mathlib genuinely lacks this. There is no integrality-of-torsion result for elliptic curves anywhere in
`Mathlib/AlgebraicGeometry/EllipticCurve/` (only the `AddCommGroup` on points and the division/torsion
*polynomials*), and "Nagell"/"Lutz" appear nowhere in the source — so this is a real gap, not a duplicate.
It is not `NO-mathlib-has-it`, and as the order-4 branch of an original multi-file development with a genuine
multi-step proof it is not `NO-composable`. The decl is also already the maximally-general form **within the
project**: it is precisely the restatement the General twin `integrality_of_order_four_general` (BORDERLINE)
names as its target, and unlike that twin it already uses the idiomatic `IsLocalization.IsInteger R` encoding
rather than a bespoke `∃ x₀:ℤ` shim.

It is nevertheless **not** `YES-add-as-is`, for exactly the reason the sibling apex
`lutz_nagell_integrality_pid` was assessed `YES-but-generalise-first`: Phase 4b finds the current form
strictly narrower than the literature-standard form. Silverman AEC VIII.7.1 proves torsion-integrality
**prime-by-prime via reduction / formal groups**, which needs only a DVR at each prime and **no global
UFD**; the "`R` is a UFD and `2` has squarefree (unramified) image" packaging is a global surrogate the
standard theory avoids, and `Squarefree (2:R)` is strictly stronger than the local "residue characteristic
∤ order at primes above 2" condition that the 2-adic descent actually requires. The correct mathlib target
is the reduction-theoretic statement over a Dedekind domain, from which the UFD, PID, number-field
(class-number-1) and classical-ℚ order-4 cases all fall out as corollaries. Per the skill's gate, a
STRICTLY-NARROWER Phase-4b verdict forces `YES-but-generalise-first`, not `YES-add-as-is` — and the
EXPENSIVE regeneralisation cost (mathlib lacks the reduction + formal-group-torsion infrastructure) informs
*sequencing* only, not the bucket. This keeps the whole PID Nagell–Lutz family (`lutz_nagell_integrality_pid`,
`lutz_nagell_number_field`, and this order-4 branch) on one consistent upstreaming track.

Reason for the generalisation:
  - **LITERATURE-WEAKENING:** Phase 4b — the user's form (UFD base + global `Squarefree (2:R)`) is strictly
    narrower than the reduction-theoretic Dedekind/DVR form with the local good-reduction condition.
  - **MODERN-IDIOM (Bourbaki 2.0):** Phase 4c — the reduction-map / formal-group formulation is the
    contemporary mathlib idiom and removes the global-UFD + `Squarefree` redundancy. (The `IsInteger R`
    integrality encoding is *already* idiomatic here.)

Proposed restatement (target shape; the current proof does **not** survive — it needs new infrastructure):
```lean
-- Stated at a single prime via reduction; assemble globally over a Dedekind domain.
-- Requires: reduction of elliptic curves + formal-group torsion (NOT yet in mathlib).
-- The order-4 case is the specialisation `addOrderOf P = 4`.
theorem WeierstrassCurve.torsion_isInteger_of_goodReduction
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K}
    (hpt : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hgood : ∀ 𝔭, /- good reduction at 𝔭 ∧ residue char 𝔭 ∤ addOrderOf P -/ True) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  sorry
```
Estimated cost of regeneralisation: **EXPENSIVE** — mathlib has no reduction map for elliptic curves and no
formal-group torsion theory; this is substantial new infrastructure. (EXPENSIVE does not downgrade the
verdict; cost informs *sequencing* — ship the UFD form to the project now, target the reduction form for the
eventual mathlib PR — but is not itself the reason for the bucket.)

Mathlib downstream this enables (MODERN-IDIOM):
  - torsion-injection `E(K)_tor ↪ Ẽ(k_𝔭)` at good primes — the standard tool for *bounding* torsion subgroups.
  - uniform UFD / PID / number-field (class-number-1) / local-field corollaries, and classical ℚ Nagell–Lutz
    (order-4 case) as a one-line specialisation.
  - composability with a future Néron-model / good-reduction API.
  - proofs blocked by the current global form (anything genuinely local at one prime) become available.

Next action: this is a genuine contribution but **not yet in its mathlib-canonical form**. Treat it together
with the sibling apex — run `/generalise LutzNagell.PID.lutz_nagell_integrality_pid` (the order-4 branch
generalises in lockstep with it) to tension against both the literature-standard reduction form (Phase 3) and
the modern reduction-map idiom (Phase 4c) before any mathlib PR. In the meantime the UFD form is correct and
useful **within the project** (it powers the `4 ∣ order` branch of `lutz_nagell_integrality_pid`, hence the
discriminant theorem and the number-field corollary) — keep it; the generalisation is a mathlib-upstreaming
concern, not a project defect. Realistically the mathlib path is: first upstream elliptic-curve reduction +
formal-group torsion, then state the reduction-theoretic Nagell–Lutz, then recover this order-4 statement as a
corollary.

---

## Next step

Run `/generalise LutzNagell.PID.lutz_nagell_integrality_pid` (the order-4 branch
`integrality_of_order_four_squarefree` regeneralises in lockstep) — tension the UFD + global-`Squarefree (2:R)`
form against the reduction-theoretic Dedekind/DVR standard form before opening any mathlib PR. Keep the UFD
form in the project (it powers `lutz_nagell_integrality_pid` and thence the discriminant + number-field
results); the generalisation is the upstreaming target, gated on mathlib first acquiring elliptic-curve
reduction + formal-group torsion infrastructure.
