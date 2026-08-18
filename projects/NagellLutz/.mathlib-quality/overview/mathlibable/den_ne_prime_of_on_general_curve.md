# /mathlibable report — `LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`

> AINTLIB /overview Step-9 full mathlibable assessment, single declaration.
> Reasoned from source (local Lean build stale per task brief; ChatGPT MCP down — WebSearch +
> grep-over-pinned-mathlib `.lake/packages/mathlib/` used as the substitute search channels).
> This report supersedes the earlier draft and corrects one stale claim (the General lemma is **no
> longer** a ~94-line monolith — it is already a thin delegating corollary; see Phase 1 / Phase 6).

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (environment: local build stale per task brief; reasoned from source).
- decl `LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralDenominators.lean:42`
                            (the `theorem` keyword is on line 42; the prompt's `:57` points inside the
                            same declaration's body. Same decl, name verified.)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Denominators on general Weierstrass curves" — the ℚ/ℤ special case of
  the UFD result `PID.den_not_prime_of_on_curve`; if a rational point's `x.den` equals a prime `p`
  on an integral general Weierstrass curve, derive `False`.

Qualified name VERIFIED from source: declared under `namespace LutzNagell` → `namespace
LutzNagellTheorem`, so the fully-qualified name is
`LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`. ✓ (matches the parsed name in the prompt).

---

### Statement (Phase 1)

`den_ne_prime_of_on_general_curve` is a **theorem** stating:

Let `W` be a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with all coefficients
`aᵢ ∈ ℤ`. Let `(x, y)` be a **rational** point on `W` (i.e. `x, y ∈ ℚ` satisfying the Weierstrass
equation over `ℚ`). If the denominator of `x` in lowest terms equals a prime number `p`
(`x.den = p`), then we reach a contradiction (`False`).

Equivalently (contrapositive): no rational point on an integral Weierstrass curve has `x`-coordinate
whose reduced denominator is exactly a prime.

Variables / typeclasses involved (Lean side):
- `W : WeierstrassCurve ℤ` — a Weierstrass curve with integer coefficients.
- `{x y : ℚ}` — the (affine) coordinates of the rational point.

Hypotheses (Lean side):
- `heq : y² + a₁·x·y + a₃·y = x³ + a₂·x² + a₄·x + a₆` (coefficients cast `ℤ → ℚ`) — `(x,y)` lies on `W`.
- `{p : ℕ} (hp : p.Prime)` — `p` is a prime natural number.
- `hden : x.den = p` — the reduced denominator of `x` is exactly `p`.

Conclusion (math): contradiction — such a configuration cannot occur.
Conclusion (Lean): `False`.

**Note (no torsion hypothesis).** The lemma has *no* finite-order / torsion assumption. It is the
pure local statement: lying on the integral curve already forbids `x.den` from being a prime. (The
torsion of Nagell–Lutz enters elsewhere in the project — the division-polynomial / rational-root
bound supplies `x.den ∣ p`; this lemma supplies the complementary `x.den ≠ p`, jointly forcing
`x.den = 1`.)

**Proof shape (from source — important correction).** The current body (`GeneralDenominators.lean`
lines 45–52) is **NOT** a long monolithic descent. It is a ~8-line **delegating corollary**:
1. `hden_prime : Prime (IsFractionRing.den ℤ x : ℤ)` via `Int.prime_iff_natAbs_prime` + the mathlib
   bridge `Rat.isFractionRingDen x` (which gives `(IsFractionRing.den ℤ x).natAbs = x.den`) + `hden`.
2. `refine PID.den_not_prime_of_on_curve W (K := ℚ) (y := y) ?_ hden_prime`, then
   `simpa only [algebraMap_int_eq, eq_intCast] using heq` to match the curve equation.
The actual p-adic descent (clear denominators, reduce mod `q` three times) lives in the **general UFD
lemma** `PID.den_no_simple_prime_factor_of_on_curve` in `PIDDenominators.lean`, which
`den_not_prime_of_on_curve` (the `den = prime` corollary) and hence this ℤ/ℚ lemma both invoke.

(The project's older `/overview` analysis files — `05-duplications.md`, `06-generalization.md`,
`07-api-and-junk.md` — describe this decl as a "~94-line monolith subsumed by PID". That is **stale**:
the dedup has since been partly done; the General lemma now *delegates* to the PID track instead of
re-proving it. The verdict below is unchanged — indeed reinforced — by this correction.)

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an intermediate technical lemma in the Nagell–Lutz integrality argument (the denominator /
reduction-mod-`p` step), not a named theorem and not a top-level "Main result" in its own right —
a helper consumed by `GeneralPrimeOrder.lean`. Not named after a person/place (the *theorem*
Nagell–Lutz is named; this isolated denominator step is not).

(Literature width run EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem` (not a `def`/`abbrev`/`structure`) → one-liner check is **n/a**. (For the record
the body is ~8 lines of tactic, a delegating corollary; not a `def` body in any case.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "Nagell-Lutz theorem proof denominator x-coordinate rational point Weierstrass curve is integral"        | yes  | the denominator step of Nagell–Lutz: a rational point has `(x,y)=(q/d², s/d³)`, `gcd(·,d)=1` | Wikipedia "Nagell–Lutz"; Alpoge "Nagell–Lutz, quickly" (Harvard); Dummit NEU notes lec 19; surya-teja blog |
| 2  | WebSearch (general / parity form)| "denominator x-coordinate rational point elliptic curve perfect square v_p valuation even cannot equal single prime" | yes  | `x(P)=A_P/B_P²`; den(x) is a perfect square ⇒ `v_p(den x)` EVEN ⇒ never a single prime | researchgate "On the denominators of rational points on elliptic curves"; MIT 18.783 Lec 23/24; Poonen 18.095 |
| 3  | WebSearch (named / Silverman)    | "Silverman Arithmetic Elliptic Curves VII.3 reduction mod p torsion injective denominator prime point bad reduction" | yes  | reduction-kernel filtration `E_n(K)`; `P=(X,Y)↦ -X/Y`; on `E_n`, `v(x)=-2n`, `v(y)=-3n` | Silverman AEC ch. VII–VIII (Springer "Reduction mod p and Torsion Points"); full PDF (pdmi.ras.ru) |
| 4  | ChatGPT MCP                      | (named-vs-step? maximally-general form? valuation-parity? historical reference?)                         | n/a  | —                   | **MCP DOWN** per task brief (Codex exec failed). Fell back to WebSearch + standard-theory knowledge. Recorded as attempted. |
| 5  | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`                                                       | n/a  | —                   | directory **absent** (`.mathlib-quality/` holds only `overview/`). Recorded n/a with reason. |
| 6  | nLab                             | "Nagell–Lutz" / "elliptic curve formal group" / "reduction of an elliptic curve"                        | n/a  | —                   | no dedicated nLab page; classical Diophantine NT, covered by Silverman/Cassels not nLab. Looked; n/a. |
| 7  | nCatLab                          | —                                                                                                       | n/a  | —                   | not a (higher-)categorical concept — a divisibility/integrality lemma. |
| 8  | Stacks Project                   | "elliptic curve torsion integral" / "Weierstrass denominator"                                            | n/a  | —                   | Stacks covers scheme/stack foundations, not the arithmetic Nagell–Lutz statement. Looked; n/a. |
| 9  | MathOverflow / MSE               | "points on an elliptic curve with prime denominator"                                                     | yes  | den(x) is a perfect square `B²` ⇒ can't be one prime (would need odd valuation) | arXiv:2307.09406 "a question about points on an elliptic curve with prime denominator" (descent-via-isogeny ⇒ finitely many) |
| 10 | recent arXiv (≤5 yr)             | "denominators of rational points on elliptic curves"; "B_P equal to a prime / perfect power"            | yes  | den sequence = elliptic divisibility sequence; `B_P=`prime is a finiteness (descent) problem | arXiv:math/0606003; arXiv:1411.7787 (perfect powers, function fields); EDS literature |

Protocol pass check:
- WebSearch ran **4** distinct queries at different generality levels (specific Nagell–Lutz step;
  general `A/B²` valuation-parity; Silverman reduction/formal-group; MO prime-denominator/descent). ✓ (≥3 required)
- ChatGPT MCP attempted with the required prompts (named-vs-step, maximally-general form, parity,
  historical reference) — **down**; recorded with reason. ✓ (attempted)
- Local references checked → absent, n/a with reason. ✓
- nLab checked → n/a with reason. ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or recorded n/a with reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the reduction-mod-`p` / formal-group denominator step of the Nagell–Lutz
theorem** (Silverman, *The Arithmetic of Elliptic Curves*, ch. VII–VIII; Cassels, *LMSST 24*; MIT
18.783 Lec 23/24).

Sources agree on the standard form: **yes**. It is **not a named theorem** — it is a standard
*intermediate step*. The clean underlying fact, stated in every treatment:

> For a rational point `(x,y)` on an integral Weierstrass curve, the denominator of `x` is a perfect
> square `B²` and that of `y` is `B³` (with the `gcd` conditions). Equivalently, for every prime `p`,
> `v_p(den x)` is **even** (`= 2k`, with `v_p(den y) = 3k`), because the point lies in the
> reduction-kernel filtration `E_k(ℚ_p)`. A point with `v_p(den x) = 1` (i.e. `den x = p` exactly) is
> therefore impossible.

Most general standard form: the **full valuation-parity / `E_n`-filtration statement** — `v_q(den x)`
is even for any prime `q` of the relevant ring (DVR / Dedekind / number field, or the fraction field
of a UFD with a prime element `q`). The "`den x = p` ⇒ False" form is the multiplicity-1 corollary.

Generality dimensions where the literature varies:
- **Base ring/field**: `ℚ` (classical Nagell–Lutz) → number fields / their rings of integers →
  fraction field `K` of an arbitrary DVR / Dedekind / **UFD** `R` with a prime `q`. The most general
  *elementary* form is over a UFD with fraction field `K`.
- **Strength of conclusion**: "`den x ≠ p`" (multiplicity 1) ⊂ "`q ∣ den x` exactly once ⇒ False"
  (multiplicity-1, any prime `q`) ⊂ "`v_q(den x)` even, `= ⅔·v_q(den y)`" (full parity).

Disagreement with the literature: **none**. The Lean statement is a faithful — but strictly narrow —
instance (`R = ℤ`, `K = ℚ`, multiplicity exactly 1, conclusion `False`).

---

### Generality analysis — `den_ne_prime_of_on_general_curve`

Literature-standard form (from Phase 3): for a Weierstrass curve over the fraction field `K` of a
UFD `R`, and a prime `q ∈ R`, if `q ∣ den_R(x)` exactly once then `False` (equivalently `v_q(den x)`
is even). Classical Nagell–Lutz is the `R = ℤ`, `K = ℚ` instance.

| # | Parameter / hypothesis              | Current Lean form                | Literature-standard form                       | Weaker form exists? | Reason it can / can't be weakened |
|---|-------------------------------------|----------------------------------|------------------------------------------------|---------------------|-----------------------------------|
| 1 | base ring `W : WeierstrassCurve ℤ`  | `ℤ`                              | any UFD `R` (PID/Dedekind/DVR ⊂ this)          | **yes**             | the descent uses only: `R` a UFD with a prime `q` and fraction field `K`. No special feature of `ℤ`. **Already realised** in the project's PID track: `[CommRing R][IsDomain R][UniqueFactorizationMonoid R]`. |
| 2 | coordinate field (implicit `ℚ`)     | `ℚ`                              | fraction field `K` of `R`                      | **yes**             | proof is pure `IsFractionRing R K` num/den manipulation; nothing ℚ-specific beyond the `Rat.isFractionRingDen` bridge (itself removable in the general form). |
| 3 | `hden : x.den = p` (multiplicity 1) | denominator *equals* the prime   | `q ∣ den(x)` **exactly once** (`q∣den, q²∤den`) | **yes**             | `den = p` is the strongest multiplicity-1 hypothesis; the general lemma asks only `q ∣ den` once. `den = p` ⇒ `p ∣ den ∧ p² ∤ den` immediately (exactly how `den_not_prime_of_on_curve` discharges it). |
| 4 | `p : ℕ` prime                       | nat prime                        | prime element `q` of `R`                       | yes                 | `Nat.Prime p` ⇒ `Prime (p:ℤ)` (the proof already routes through this, line 47–48); generalises to `Prime q` in `R`. |
| 5 | conclusion `False`                  | `False`                          | `False` (cor.) / `v_q(den x)` even (full)      | partly              | the full statement strengthens to the parity equation; the `False` multiplicity-1 corollary is what both project versions prove. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **4** (base ring, coordinate field, multiplicity hypothesis,
prime type) — all four collapse into a single generalisation already carried out in the project.

Proposed restatement (the general form — and it already exists, sorry-free, in this project):

```lean
-- LutzNagell/LutzNagellTheorem/PIDDenominators.lean (already proven, sorry-free)
theorem den_no_simple_prime_factor_of_on_curve {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {q : R} (hq : Prime q)
    (hqd : q ∣ (IsFractionRing.den R x : R))
    (hq2 : ¬ q ^ 2 ∣ (IsFractionRing.den R x : R)) : False
-- and its `den = prime` corollary, also already proven:
-- theorem den_not_prime_of_on_curve … (hp : Prime (IsFractionRing.den R x : R)) : False
```

The ℤ/ℚ lemma is recovered by `R := ℤ`, `K := ℚ`, `q := (p : ℤ)` via the `Rat.isFractionRingDen`
bridge — which is *exactly what the current body already does*. So the generalisation is not just
cheap, it is **already realised and already invoked** by this very declaration.

Cost of restatement: **CHEAP** — no new mathematics; the general proof is *already written,
sorry-free, and already the delegate of this lemma*. The only project-side work is to delete the ℤ/ℚ
wrapper and re-derive its two `GeneralPrimeOrder.lean` call sites from the PID corollary.

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
| 1  | "let X be a foo" preambles → typeclasses/instances?                                                   | yes      | replace concrete `ℤ`/`ℚ` by `[UniqueFactorizationMonoid R]` + `[IsFractionRing R K]` (exactly the PID track) | composes with all of mathlib's `IsFractionRing` num/den API (`IsFractionRing.num_den_reduced`, `mk'_num_den'`) |
| 2  | sequences/metric → filters/nets/topology?                                                             | no       | — (no analytic/limit content; pure divisibility) | — |
| 3  | construct object where universal-property class fits?                                                 | no       | — | — |
| 4  | set-with-closure-predicate → bundled substructure?                                                    | no       | — | — |
| 5  | vector-space/metric/field-specific → weaken typeclass hierarchy?                                      | yes      | `ℤ`-PID / `ℚ`-field hard-coding → UFD / `IsFractionRing` (overlaps row 1) | the full Localization `NumDen` API applies |
| 6  | 1-categorical → higher-categorical?                                                                   | no       | — | — |
| 7  | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/ordered structure?                                | yes      | `ℤ` base ring → general UFD `R` (overlaps rows 1, 5) | unifies with the project's own UFD/PID track and any future Dedekind-base Nagell–Lutz |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**
- Proposed mathlib-idiomatic restatement: the UFD-+-`IsFractionRing` form
  `den_no_simple_prime_factor_of_on_curve` above (rows 1/5/7 all point at the same move).
- Cost: **CHEAP** (already realised, sorry-free, in `PIDDenominators.lean`).
- Mathlib downstream this enables: composes with `Mathlib/RingTheory/Localization/NumDen.lean`
  (`IsFractionRing.num`, `.den`, `.num_den_reduced`, `.mk'_num_den'`) — mathlib's own fraction-field
  num/den API — rather than the `ℚ`-only `Rat.num`/`Rat.den`. Reusable for Nagell–Lutz over number
  fields and any UFD base.
- Real mathematical improvement: removes a redundant ℚ-only wrapper and states the result at the
  genuine generality the proof supports (no use of any special feature of `ℤ`).

(Both the literature-standard form **and** the modern mathlib idiom point at the *same* generalised
statement — the UFD / `IsFractionRing` form — which already exists in the project.)

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities and no
typeclass-search paths, so the six-row diamond/defeq table does not apply. Skipped per spec.

---

### Mathlib search-status: `den_ne_prime_of_on_general_curve`

(Mathlib pinned in this workspace at `.lake/packages/mathlib/` — pin `09b373db6e24`, toolchain
v4.32.0-rc1. The `lean_loogle` / `lean_leansearch` mathlib-index tools are not callable in this
environment, so Methods A–C are recorded with the substitute actually run — grep over the pinned
mathlib source, Method D — plus reasoning.)

[A] Lean-Finder       n/a: AI index tool not callable here.
[B] Loogle            n/a: `lean_loogle` not callable here. Intended patterns:
                        `WeierstrassCurve.Affine.Equation _ _ _ → _`, `Rat.den _ = _ → False`,
                        `Prime _ → _ ∣ IsFractionRing.den _ _ → False`. (See Method D for the
                        equivalent source grep.)
[C] LeanSearch        n/a: `lean_leansearch` not callable here. Intended NL queries: "rational point
                        on Weierstrass curve denominator prime"; "Nagell Lutz integral torsion";
                        "denominator of x coordinate is a square".
[D] Grep mathlib src  Ran (substitutes A–C), over `.lake/packages/mathlib/Mathlib`:
                        • `Nagell` → **0 hits** anywhere in mathlib. `Lutz` (word) → only Apache
                          copyright headers (author *Patrick Lutz*; FieldTheory files) — unrelated.
                        • `den.*Prime` / `denominator.*prime` tied to a Weierstrass `Equation` → **no hits**.
                        • EC formal group / point reduction / filtration: grep `formalGroup`,
                          `FormalGroup`, `reductionMap`, `ker.*reduction`, `E_1`, `E_n` over
                          `AlgebraicGeometry/EllipticCurve/` → **0 hits**. (`Mathlib/RingTheory/
                          FormalGroup/` has *abstract* formal groups, but there is **no** formal group
                          OF an elliptic curve, no `P ↦ -X/Y` reduction map, no `E_n` filtration.)
                        • `AlgebraicGeometry/EllipticCurve/Reduction.lean` exists but reduces the
                          **curve** (`IsIntegral`/`IsMinimal`/`reduction`/`IsGoodReduction` over a
                          DVR) — grep `den|Point|coordinate|torsion|integral point` → **0 hits**.
                          No statement about denominators of *point* coordinates; no Nagell–Lutz.
                        • `AlgebraicGeometry/EllipticCurve/Affine/Point.lean`: grep
                          `den|Rat|integral|IsFractionRing` → only the CoordinateRing-is-a-domain
                          plumbing; **no** denominator / integrality-of-a-rational-point lemma.
                        • EC division-polynomial dir has only `Basic.lean` + `Degree.lean`
                          (`preΨ`, `preΨ₄`, `preΨ'` defined upstream) — **no** integrality /
                          denominator consequence of the division polynomials.
                        • Bridge `Rat.isFractionRingDen` **does** exist
                          (`RingTheory/Localization/Rat.lean:31`) — it is mathlib's, used by this
                          proof; it is *not* the Nagell–Lutz content, just the `x.den ↔ natAbs den`
                          identification.
[E] Name pattern      Grepped `den_ne_prime` / `den_no_simple_prime` / `den_not_prime` /
                        `integral.*torsion` / `reduction.*kernel` across mathlib → matches **only** in
                        the AINTLIB project tree, none in mathlib.

Searched for both:
  - the user's current form (`x.den = p` ⇒ False over ℚ): **not in mathlib**.
  - the literature-standard general form (UFD / `IsFractionRing`, `q ∣ den` once ⇒ False; and the full
    `v_q(den x)` even / `E_n` filtration): **not in mathlib** — mathlib lacks the prerequisite
    formal-group-of-an-EC and point-reduction infrastructure entirely.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard general
form). Mathlib has *neither* this specialisation, *nor* any more-general form, *nor* the building-block
machinery (EC formal group / reduction-on-points / `E_n` filtration) it would descend from.

---

### Call sites — `den_ne_prime_of_on_general_curve`

Internal use count: **2** (within NagellLutz, excluding the declaring file `GeneralDenominators.lean`).
External-to-file callers: **1** distinct file (`GeneralPrimeOrder.lean`). Verified directly against
the `.lean` source.

| Caller file:line                              | Usage pattern (one-line excerpt)                                                        |
|-----------------------------------------------|------------------------------------------------------------------------------------------|
| `GeneralPrimeOrder.lean:107`                  | `exact absurd h (fun h ↦ den_ne_prime_of_on_general_curve W ((curveQ_equation_iff W x y).mp hns.left) hp h)` — odd-prime-order integrality: from `x.den ∣ p` + primality, rule out `x.den = p`, leaving `x.den = 1`. |
| `GeneralPrimeOrder.lean:138`                  | `exact absurd h (fun h ↦ den_ne_prime_of_on_general_curve W ((curveQ_equation_iff W x y).mp hns.left) (by decide) h)` — order-4 case: rule out `x.den = 2`, leaving `x.den = 1`. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - The **PID track** independently proves the strictly more general
    `PIDDenominators.den_no_simple_prime_factor_of_on_curve` and its corollary `den_not_prime_of_on_curve`
    (used by `PIDPrimeOrder.lean` and `PIDMain.lean`). This is not an inline re-derivation of *this*
    lemma — it is the **general version of which this is the explicit ℤ/ℚ specialisation**. The current
    `den_ne_prime_of_on_general_curve` body literally *calls* `PID.den_not_prime_of_on_curve`
    (`GeneralDenominators.lean:51`), so the relationship is "thin wrapper → general lemma", confirmed
    by reading the source (and, more loosely, by the project's own `/overview` dedup notes, which are
    stale on the "monolith" wording — see Phase 1 correction).

Call-sites signal: **K = 2 internal uses, both in one downstream file, both inside `absurd (…)` to
discharge `x.den = (prime)`.** Real API (consumers depend on it), but those same consumers can be
re-pointed at the general PID corollary with a 1–2 line adaptation (supply `q ∣ den`, `q² ∤ den` from
`x.den = p` — i.e. exactly what `den_not_prime_of_on_curve` already does internally). Per the skill's
pattern table this is the "K=2, but a strictly-more-general sibling already exists in the project"
case → leans **generalise-first** rather than add-as-is.

---

### Composition check (Phase 6)

Can `den_ne_prime_of_on_general_curve` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: derive from a mathlib EC / denominator primitive.
  - Mathlib decls used: — none exist. Mathlib has no point-coordinate-denominator lemma, no formal
    group of an EC, no reduction-on-points map, no `E_n` filtration, no Nagell–Lutz (Phase 5).
  - Result: **fails**. There is nothing in mathlib to chain.

Attempt 2: derive from the project's own general PID corollary.
  - `PID.den_not_prime_of_on_curve` (project, not mathlib) gives it in ~3 lines — and *this is
    literally the current proof*: build `Prime (IsFractionRing.den ℤ x)` from `x.den = p` via
    `Int.prime_iff_natAbs_prime` + `Rat.isFractionRingDen`, then `refine PID.den_not_prime_of_on_curve
    W …` + `simpa` to translate `heq`.
  - Result: **succeeds — but the building block is in the AINTLIB project, NOT in mathlib.**

Conclusion: **NOT-COMPOSABLE (from mathlib).** It composes only from a *project* lemma (itself the
better mathlib candidate), not from mathlib primitives. This rules out `NO-composable-from-mathlib` —
that bucket requires the building blocks to live in mathlib.

---

## Verdict: `LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): standard, *unnamed* reduction-mod-`p` denominator step of Nagell–Lutz;
  the maximally-general elementary standard form is the valuation-parity / `E_n`-filtration fact over
  a UFD/DVR/number-field, of which "`den x = p` ⇒ False" is the multiplicity-1 corollary (Silverman
  AEC VII–VIII; Cassels LMSST 24; MIT 18.783 Lec 23/24; researchgate "On the denominators of rational
  points on elliptic curves"; arXiv:2307.09406).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 4 collapsible weakenings (base
  ring `ℤ`→UFD, field `ℚ`→`IsFractionRing K`, `den=p`→`q∣den` once, `ℕ`-prime→`Prime q`); the modern
  mathlib idiom (Phase 4c) points at the *same* UFD/`IsFractionRing` form.
- Mathlib search (Phase 5): **not in mathlib** — neither this form, nor the general form, nor the
  prerequisite EC-formal-group / point-reduction machinery.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (composes only from a *project* lemma)
  — so the `NO-composable` bucket is excluded.

**Rationale:**

The mathematical content is genuine and absent from mathlib (no Nagell–Lutz, no formal group of an
elliptic curve, no reduction map on points, no `E_n` filtration — Phase 5 grep is empty across the
whole `AlgebraicGeometry/EllipticCurve/` tree), so a `NO` verdict is wrong: mathlib neither *has* it
(`NO-mathlib-has-it` ✗) nor can *compose* it from mathlib primitives (`NO-composable` ✗ — the
composing lemma lives in the AINTLIB project). But it cannot enter mathlib *as-is* either: Phase 4b
shows the `ℤ`/`ℚ`, "denominator *equals* a prime" form is strictly narrower than the standard
statement, and the project **already contains** the correctly-generalised, sorry-free proof
`PIDDenominators.den_no_simple_prime_factor_of_on_curve` (and its `den_not_prime_of_on_curve`
corollary) over a UFD `R` with fraction field `K`. The generalisation uses no feature of `ℤ` the
proof doesn't already abstract — indeed the current ℤ/ℚ lemma's entire body is a ~8-line *delegation*
to that UFD corollary. This is the textbook `YES-but-generalise-first` situation: the right mathlib
contribution is the general form; the narrow ℤ/ℚ lemma is the specialisation wrapper.

One honest caveat on *sequencing* (not on the bucket): even the UFD multiplicity-1 corollary is a
fairly specialised standalone lemma. Mathlib's canonical route to Nagell–Lutz would first build the
formal group / reduction-kernel filtration `E_n` and state the full parity theorem (`v_q(den x)`
even); the present corollary would then fall out. So the *form* to upstream and the *timing* are a
mathlib-maintainer call. This does not make the verdict ambiguous between buckets — under every
reading the narrow ℤ/ℚ form should NOT be added as-is, and the generalised UFD form is what belongs —
so the bucket is firmly `YES-but-generalise-first`, with the upstreaming-vs-wait-for-formal-groups
question recorded for the human.

**Reason for the generalisation:**
- LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the literature-standard
  (UFD / fraction-field, multiplicity-1) form.
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c found the contemporary mathlib formulation
  (`[UniqueFactorizationMonoid R]` + `[IsFractionRing R K]`) composing with mathlib's own
  `Localization/NumDen` API instead of `ℚ`-only `Rat.den`.

**Proposed restatement** (already proven, sorry-free, in the project — this lemma's own delegate):

```lean
theorem den_no_simple_prime_factor_of_on_curve {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K}
    (heq : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {q : R} (hq : Prime q)
    (hqd : q ∣ (IsFractionRing.den R x : R))
    (hq2 : ¬ q ^ 2 ∣ (IsFractionRing.den R x : R)) : False
-- ℤ/ℚ corollary (essentially the current `den_ne_prime_of_on_general_curve`, kept as a thin wrapper):
-- exact PID.den_not_prime_of_on_curve W (R := ℤ) (K := ℚ) heq'
--   (Int.prime_iff_natAbs_prime.mpr (by rw [Rat.isFractionRingDen x, hden]; exact hp))
```

Estimated cost of regeneralisation: **CHEAP** (the general proof already exists, is sorry-free, and is
*already invoked* by this lemma; only the two `GeneralPrimeOrder.lean` call sites need a 1–2 line
adaptation, or — preferably — the project keeps a thin ℤ/ℚ corollary internally and upstreams only
the general lemma).

Mathlib downstream this enables:
- Composes with `Mathlib/RingTheory/Localization/NumDen.lean` (`IsFractionRing.num`, `.den`,
  `.num_den_reduced`, `.mk'_num_den'`) — mathlib's general num/den API, not `Rat.*`.
- Reusable for Nagell–Lutz over number fields / rings of integers and any UFD base, and as the
  multiplicity-1 corollary of an eventual formal-group / `E_n`-filtration `v_q(den x)`-parity theorem.

**Next action:** run `/generalise LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`
(it will tension against both the literature-standard UFD form from Phase 3 and the modern-idiom
`IsFractionRing` form from Phase 4c — which here coincide and are *already realised* as
`PIDDenominators.den_no_simple_prime_factor_of_on_curve`). Within AINTLIB this is a dedup: drop the
ℤ/ℚ wrapper (or keep it as a one-line corollary) and ensure its two `GeneralPrimeOrder.lean` call
sites go through the PID corollary (the standing `/cleanup` recommendation in
`overview/analysis/05-duplications.md` / `06-generalization.md`). For mathlib, upstream the **general**
UFD / `IsFractionRing` statement — and surface to a mathlib maintainer the sequencing question below.

**Open question for a human (sequencing, not bucket):** Should the standalone UFD multiplicity-1
corollary be upstreamed now, or wait and be packaged as a corollary of the full formal-group /
reduction-kernel `E_n`-filtration (`v_q(den x)` even) theorem — the larger piece of EC infrastructure
mathlib currently lacks?

---

## Next step

Run `/generalise LutzNagell.LutzNagellTheorem.den_ne_prime_of_on_general_curve`, targeting the
already-existing general form `PIDDenominators.den_no_simple_prime_factor_of_on_curve`
(UFD `R` + `IsFractionRing R K`). Within AINTLIB this is a dedup: drop/thin the ℤ/ℚ wrapper and route
its two `GeneralPrimeOrder.lean` call sites through the PID corollary. For mathlib, upstream the
general (UFD / `IsFractionRing`) statement, after the maintainer decides standalone-now vs.
package-with-formal-group-filtration.
