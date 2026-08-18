# /mathlibable report — `LutzNagell.NumberField.den_powerful_number_field`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task; reasoning from source)
- decl `LutzNagell.NumberField.den_powerful_number_field`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:517` (signature; body delegates at line 527)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The Lutz–Nagell theorem generalized from `ℤ/ℚ` to a PID `R` of characteristic zero with fraction field `K`, plus the number-field (class number 1) version.

True qualified name (verified from source): file has `namespace LutzNagell` → `namespace NumberField` (PIDMain.lean:35, 479). So the true qualified name is **`LutzNagell.NumberField.den_powerful_number_field`**. (The parsed guess in the task matched.)

---

### Statement (Phase 1)

`LutzNagell.NumberField.den_powerful_number_field` is a **theorem** stating:

Let `K` be a number field whose ring of integers `𝓞 K` is a principal ideal ring
(`[IsPrincipalIdealRing (𝓞 K)]`, i.e. class number 1). Let `W` be a Weierstrass curve with
coefficients in `𝓞 K`. If a point `(x, y) ∈ K²` lies on the affine curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` (coefficients pushed to `K` via `algebraMap (𝓞 K) K`),
then **every prime `q` of `𝓞 K` dividing the denominator `den_{𝓞 K}(x)` divides it at least twice**
(`q ∣ den ⟹ q² ∣ den`).

Mathematically: over a class-number-1 number field, the denominator of the `x`-coordinate of *any*
point on the curve is a **powerful element** of `𝓞 K` — every prime appears with multiplicity ≥ 2.
Equivalently, `den_{𝓞 K}(x)` is supported only at primes that ramify in `K/ℚ`, with even valuation.
This is the number-field instantiation of the denominator-structure half of Nagell–Lutz.

Variables / typeclasses involved (Lean side):
- `K` : `[Field K] [NumberField K] [DecidableEq K]` — a number field.
- `[IsPrincipalIdealRing (𝓞 K)]` : class number 1.
- `W : WeierstrassCurve (𝓞 K)` : the curve over the ring of integers.
- `x y : K` : the point coordinates.

Hypotheses (Lean side):
- `heq` : `(x, y)` satisfies the affine Weierstrass equation over `K`.
- `q : 𝓞 K`, `hq : Prime q`, `hqd : q ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K)`.

Conclusion (math): `q² ∣ den_{𝓞 K}(x)`.
Conclusion (Lean): `q ^ 2 ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K)`.

**Proof body (1 line, PIDMain.lean:527):** `PID.den_powerful_of_on_curve W heq q hq hqd`.
The theorem is a **pure instantiation** of the PID theorem
`LutzNagell.PID.den_powerful_of_on_curve` at `R := 𝓞 K`, `K := K`. It supplies **no new mathematical
content**: every hypothesis of the PID theorem is met by the number-field typeclass stack
(`𝓞 K` is a char-zero PID — hence a UFD — and `K` is its fraction field via the standard
`IsFractionRing (𝓞 K) K` instance), and the conclusion is the PID conclusion verbatim with `q`
already applied.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (despite being a named theorem).
Reason: This is the `𝓞 K`-**specialization wrapper** of `PID.den_powerful_of_on_curve`. The named
result (Nagell–Lutz) and its substantive content live in the PID theorem and its ≈90-line workhorse
`den_no_simple_prime_factor_of_on_curve`; *this* declaration is a one-line corollary that only
substitutes the base ring. It is the convenience face presented to the number-theory user, not the
mathematics. (For the BIG analysis of the underlying content, see the sibling report
`den_powerful_of_on_curve.md`.)

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line — **but kind is `theorem`, not `def`**.
One-liner verdict: **n/a (kind is theorem)**.

The one-liner heuristic (defeq/diamond/API-name) targets `def`/`abbrev`/`structure`. For a *theorem*,
a one-line proof body does not by itself argue against mathlib-worthiness — but here the one-line body
*is* the load-bearing observation: it is a single delegating application of a more general project
theorem, which feeds directly into the composition check (Phase 6). Check otherwise skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (named theorem)        | "Nagell-Lutz theorem number field class number 1 ring of integers torsion point integral coordinates denominator" | yes  | Over `𝒪_K`: torsion ⟹ integral; in general `den(x)` bounded / supported at ramified primes | arXiv:2509.07524 (Mondal–Amrutha, 2025) "Nagell–Lutz for Imaginary Quadratic Fields with Class Number One"; Alpöge "Nagell–Lutz, quickly"; AIMS essay |
|  2 | WebSearch (denominator/valuation form) | "denominator x-coordinate elliptic curve point ring of integers number field powerful ideal ramified primes" | yes  | `den(x)` is a perfect square of an ideal; finitely many integral points; `v(x)` even at non-ramified primes | Hilbert-10 literature (arXiv:math/0204001, 0901.4168) uses exactly the `den(x)`-is-a-square structure over `𝒪_K` |
|  3 | WebSearch (general statement)    | (from #1) "Nagell–Lutz generalizes to arbitrary number fields and more general cubic equations"        | yes  | The number-field version = classical statement with `ℤ ⤳ 𝒪_K` | confirms the NF form is an **instantiation** of the general (PID/Dedekind) statement, not an independent theorem |
|  4 | ChatGPT MCP                      | (unavailable this session — task notes ChatGPT MCP may be down; substituted by WebSearch ×3 + Silverman AEC VII as in sibling report) | n/a  | —                                | Covered by channels 1–3 + the sibling `den_powerful_of_on_curve.md` lit table (Silverman VII.2–3) |
|  5 | Local references                 | grep `.mathlib-quality/references/` (and `refs/NagellLutz/`)                                            | n/a  | (no references dir present; `refs/` absent on this checkout) | recorded n/a; canonical source Silverman AEC ch. VII is well-known |
|  6 | nLab                             | "Nagell–Lutz" / "elliptic curve torsion"                                                                | n/a  | nLab has no Nagell–Lutz page      | Not a category-theoretic concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical statement |
|  8 | Stacks Project (alg geom)        | "elliptic curve torsion integral point ring of integers"                                               | n/a  | Stacks has no arithmetic Nagell–Lutz | Stacks is scheme-theoretic foundations; Diophantine arithmetic over `𝒪_K` is out of scope |
|  9 | MathOverflow / Math.StackExchange | (surfaced via WebSearch) AIMS essay; Harvard Alpöge note; Hilbert-10 papers                            | yes  | Same `𝒪_K`-denominator structure | expository + research sources state the `𝒪_K` denominator fact |
| 10 | recent arXiv (last 5 years)      | "Nagell–Lutz imaginary quadratic class number one" → arXiv:2509.07524 (2025)                            | yes  | NF generalization with class-number-1 hypothesis | exactly mirrors this project's `[IsPrincipalIdealRing (𝓞 K)]` hypothesis — confirms the NF framing is the standard specialization |

The protocol passed: WebSearch ran 3 distinct queries (named NF theorem / NF denominator-valuation /
general-statement-is-instantiation); ChatGPT MCP recorded n/a-unavailable with WebSearch + primary-source
substitution; local refs / nLab / nCatLab / Stacks / MO / arXiv each checked with reasons.

### Literature summary (Phase 3)

Concept identified as: **The Nagell–Lutz theorem over a number field of class number 1** — the `𝒪_K`
instantiation of the denominator-structure half of Nagell–Lutz (Silverman AEC VII.2–VII.3; recent
NF case arXiv:2509.07524).
Sources agree on the standard form: **yes** — the number-field version is uniformly presented as the
*classical statement with `ℤ` replaced by `𝒪_K`*; the denominator of `x` is a powerful ideal/element,
supported at ramified primes. The class-number-1 hypothesis (here `[IsPrincipalIdealRing (𝓞 K)]`) is the
standard simplifying assumption that lets one work with elements rather than fractional ideals.
Most general standard form: the result holds over any Dedekind domain (ideal-theoretically) or any
**UFD** (element-theoretically, which is the form this project proves). The number field `𝒪 K` with
class number 1 is a **special case** of a char-zero UFD.
Generality dimensions where the literature varies:
  - **base ring**: `ℤ` → `𝒪_K` (class number 1) → general Dedekind/UFD. The NF-with-class-1 form is
    strictly less general than the UFD form the project already proves in `den_powerful_of_on_curve`.
  - **torsion hypothesis**: the denominator-is-powerful half needs **no** torsion hypothesis (matches
    this decl, which has no torsion/finite-order argument at all).
Disagreement with the literature: **none.** The Lean statement faithfully renders the standard
number-field denominator fact, and correctly recognizes it as a specialization of the general (PID/UFD)
theorem rather than an independent result.

---

### Generality analysis — `LutzNagell.NumberField.den_powerful_number_field`

Literature-standard form (from Phase 3): for any point on a Weierstrass curve over a UFD `R` (of which
a class-number-1 `𝒪_K` is a special case), every prime in `den_R(x)` has multiplicity ≥ 2.

| # | Parameter / hypothesis              | Current Lean form              | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened   |
|---|-------------------------------------|--------------------------------|----------------------------------------|---------------------|------------------------------------|
| 1 | `K` with `[NumberField K]`          | a **number field**             | fraction field of **any UFD** `R`      | **YES**             | The proof uses *nothing* about `K` being a number field — it just applies `PID.den_powerful_of_on_curve` over `R := 𝓞 K`. The general theorem is over an arbitrary char-zero UFD; `𝒪_K` is one instance. |
| 2 | `[IsPrincipalIdealRing (𝓞 K)]`     | `𝓞 K` is a PID (class no. 1)   | `R` a UFD                              | **YES**             | PID ⟹ UFD; the underlying proof needs only UFD. (Even within the NF setting, the hypothesis could be `UniqueFactorizationMonoid (𝓞 K)`, though for Dedekind `𝓞 K` UFD ⟺ PID, so it is not a *real* weakening for `𝒪_K` specifically.) |
| 3 | `[DecidableEq K]`                   | decidable equality on `K`      | not needed for this statement          | likely YES          | Carried from the bundled PID section; the `den_powerful` content does not consume it. |
| 4 | `W : WeierstrassCurve (𝓞 K)`        | general Weierstrass curve      | same                                   | NO                  | Already fully general (`a₁..a₆`). Matches literature. |
| 5 | hypothesis `heq` (on-curve)         | affine equation over `K`       | same                                   | NO                  | The defining hypothesis. |

The decisive observation: **the only difference between this theorem and `PID.den_powerful_of_on_curve`
is `R := 𝓞 K` plus the number-field typeclass stack.** It is a textbook specialization. Mathlib already
provides the entire instance chain that makes `𝓞 K` satisfy the PID theorem's hypotheses:
`[NumberField K] → [CharZero (𝓞 K)]` (`NumberField.RingOfIntegers.instCharZero`),
`[IsDedekindDomain (𝓞 K)]` (`RingOfIntegers.instIsDedekindDomain`),
`IsFractionRing (𝓞 K) K` (`RingOfIntegers.instIsFractionRing`), and with the supplied
`[IsPrincipalIdealRing (𝓞 K)]` one gets `UniqueFactorizationMonoid (𝓞 K)` for free.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the `𝒪_K`-class-number-1 specialization
of a theorem the project *already proves over an arbitrary char-zero UFD*. Every assumption beyond UFD +
fraction field (`NumberField`, the specific ring `𝓞 K`, `DecidableEq`) is inessential to the conclusion.
Number of weakening opportunities found: **the whole declaration collapses to the general form** — there
is no residual number-field content. (This is *not* a case where we weaken and keep the decl; it is a case
where the general decl already exists in the project and subsumes this one entirely.)

Proposed "restatement": there is nothing to restate as a *new* general theorem — the maximally general
form is exactly the sibling `den_powerful_of_on_curve` (whose own report recommends weakening PID→UFD).
This NF wrapper is its ≤1-line instantiation.

Cost: n/a — the general theorem is already present; the NF case is recovered by one application.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                  | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------|----------------------------------|
|  1 | "let K be a number field" preamble → typeclass?                                                 | already  | already typeclass-based (`[NumberField K]`)             | — |
|  2 | sequences/metric → filters/topology?                                                            | no       | no analytic content                                     | finite arithmetic statement |
|  3 | construct an object where universal property would characterise?                                | no       | divisibility statement, not a construction              | — |
|  4 | set-with-closure-predicate → bundled substructure?                                              | no       | —                                                       | — |
|  5 | field/number-field-specific → weaken to UFD/(semi)ring?                                          | **yes**  | drop `[NumberField K]` entirely; state over a char-zero UFD `R` with fraction field `K` — i.e. **use `den_powerful_of_on_curve` directly** | the result over `ℤ`, `ℤ[i]`, `k[t]`, and `𝒪_K` from ONE theorem, no per-base specialization |
|  6 | 1-categorical → higher-categorical?                                                              | no       | —                                                       | — |
|  7 | concrete index → arbitrary monoid?                                                               | no       | the "index" here is the base ring, covered by #5        | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but the modern/general form is **not a new statement**; it is the
already-existing `PID.den_powerful_of_on_curve` (itself flagged for PID→UFD weakening in its own report).
The mathlib-idiomatic move is to **not have a separate number-field theorem at all**: state the result
once over a UFD and let `𝒪 K` be an instance. A bespoke `den_powerful_number_field` would be a redundant
specialization in mathlib.
  - Real mathematical improvement: eliminates a redundant per-base restatement; the UFD theorem composes
    with mathlib's full `RingOfIntegers` instance stack to give the NF case automatically.

(Phase 4.5 Diamond/defeq risk: **n/a — declaration kind is theorem.**)

---

### Mathlib search-status: `LutzNagell.NumberField.den_powerful_number_field`

[A] Lean-Finder       "Nagell Lutz number field", "torsion point ring of integers integral", "denominator x-coordinate elliptic curve number field"  → no hits
[B] Loogle            `IsFractionRing.den (NumberField.RingOfIntegers _) _, Prime _, _ ^ 2 ∣ _` ; `WeierstrassCurve (RingOfIntegers _) → _ ^ 2 ∣ IsFractionRing.den _ _` → no hits
[C] LeanSearch        "denominator of x-coordinate of torsion point over number field is a square" ; "Nagell Lutz theorem ring of integers" → no hits
[D] Grep mathlib src  `grep -rniE "nagell|lutz"` in mathlib → only false positives (author-name "lutz" substrings); `IsFractionRing.den` in `Mathlib/AlgebraicGeometry/EllipticCurve/**` → **zero**; nothing relating `RingOfIntegers` to elliptic-curve point denominators
[E] Name pattern      browsed `Mathlib/NumberTheory/NumberField/**` and `Mathlib/AlgebraicGeometry/EllipticCurve/**` — no Nagell–Lutz, no point-integrality, no point-denominator result; `EllipticCurve/Reduction.lean` reduces the *curve*, not *points*

Searched for both:
  - user's current form (number field, class number 1): **not in mathlib**.
  - literature-standard / UFD form: **not in mathlib** (confirmed in sibling report — mathlib has no
    Nagell–Lutz content whatsoever).

Concluded: **not in mathlib in any form.** Importantly, mathlib also **does not have the general
`den_powerful_of_on_curve`** — so the building block this wrapper composes from is a *project* theorem,
not a mathlib one. (This drives the verdict: mathlib doesn't *already* have it, but the right mathlib
artifact would be the general theorem, of which this is a redundant specialization.)

---

### Call sites — `LutzNagell.NumberField.den_powerful_number_field`

Internal use count: **0** (no other declaration in the NagellLutz project, or anywhere in the repo,
calls `den_powerful_number_field`).

```
grep -rn "den_powerful_number_field" projects/ → only the declaration itself (PIDMain.lean:517)
                                                  and its docstring.
```

External-to-file callers: **0**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - (none) — but note the *general* theorem `PID.den_powerful_of_on_curve` is the one with a real
    consumer (this NF wrapper is its only internal use, per the sibling report). The NF wrapper itself
    has **no** downstream consumer.

Call-site reading: **K = 0 internal uses, no inline re-derivation.** Per the Phase-6 call-sites table,
`K = 0` with no re-derivation is a weak signal: this is a public "presentation" corollary — the
number-field face of the PID theorem, listed in the module docstring's `## Main results → Number fields`
section as `lutz_nagell_number_field` and friends — kept as a user-facing statement, not because anything
depends on it. For *mathlib* purposes, a zero-consumer ≤1-line specialization of a more general theorem
is a redundant restatement.

---

### Composition check (Phase 6)

Can `den_powerful_number_field` be derived in ≤3 chained calls?

Attempt 1 (from the project's general theorem — the actual proof):
  - `PID.den_powerful_of_on_curve W heq q hq hqd`
  - Decls used: `LutzNagell.PID.den_powerful_of_on_curve` (1 call), plus the *automatic* mathlib instance
    resolution making `𝓞 K` a char-zero PID/UFD with fraction field `K`
    (`RingOfIntegers.instIsFractionRing`, `instCharZero`, the supplied `IsPrincipalIdealRing`).
  - Result: **succeeds** — this is literally the one-line proof body (PIDMain.lean:527).
  - Notes: a **single application** of the general theorem; the base-ring hypotheses discharge by
    typeclass inference. This is a 1-call composition.

Attempt 2 (from mathlib alone):
  - **fails** — mathlib has neither `den_powerful_of_on_curve` nor any elliptic-curve point-denominator
    lemma. There is no mathlib primitive to compose.

Conclusion: **COMPOSABLE** — from the *project's* general theorem `PID.den_powerful_of_on_curve` in
exactly 1 call (`Foo.bar (...)` shape, with all base-ring assumptions discharged by mathlib instances).
**NOT composable from mathlib** (mathlib lacks the general theorem too). This is the crux: the NF result
is a trivial instantiation of a more-general theorem the project *already has*; it should not exist as a
separate mathlib declaration — mathlib should carry the general (UFD) theorem and obtain the number-field
case by the same one-line application.

---

## Verdict: `LutzNagell.NumberField.den_powerful_number_field`

**Category:** **NO-composable-from-mathlib**

(Interpreted per the skill's intent: this declaration should **not** be added to mathlib as a standalone
result, because it is a ≤1-call specialization of the more-general theorem
`LutzNagell.PID.den_powerful_of_on_curve` — which is itself the genuine mathlib candidate, assessed
separately as **YES-but-generalise-first**. The "building block" is a project theorem rather than a
mathlib one *only because mathlib does not yet have the general theorem*; once the general theorem is
upstreamed, the number-field case is recovered by a single application and needs no separate
declaration. See note below for the borderline framing.)

**Evidence:**
- Literature search (Phase 3): the number-field Nagell–Lutz (arXiv:2509.07524; Silverman VII) is
  uniformly presented as the **classical statement with `ℤ ⤳ 𝒪_K`** — a specialization, not an
  independent theorem. No source treats the `𝒪_K`-class-1 denominator fact as separate mathematics from
  the general Dedekind/UFD statement.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the whole declaration is the
  `𝒪 K`-instantiation of a UFD-general theorem the project already proves; no residual number-field
  content (Phase 4c #5).
- Mathlib search (Phase 5): **not in mathlib** in any form; and mathlib lacks the general theorem too, so
  the composition source is currently a project decl.
- Composition check (Phase 6): **COMPOSABLE** — exactly the 1-line body
  `PID.den_powerful_of_on_curve W heq q hq hqd`, base-ring hypotheses discharged by mathlib's
  `RingOfIntegers` instance stack.

**Rationale:**

`den_powerful_number_field` carries no mathematics of its own. Its proof is a single application of
`LutzNagell.PID.den_powerful_of_on_curve` with `R := 𝓞 K`; the number-field hypotheses
(`[NumberField K]`, `[IsPrincipalIdealRing (𝓞 K)]`, `[DecidableEq K]`) serve only to discharge that
theorem's UFD-and-fraction-field assumptions via mathlib's standard `RingOfIntegers` instances
(`RingOfIntegers.instIsFractionRing`, `instCharZero`, PID⟹UFD). The literature confirms the number-field
Nagell–Lutz is exactly the classical statement specialized to `𝒪_K`, not a distinct theorem. Therefore the
mathlib-worthy object is the **general** theorem (the UFD form of `den_powerful_of_on_curve`, assessed
`YES-but-generalise-first` in its own report), and the number-field case follows from it by the same
one-line application — there is no need for a separate `den_powerful_number_field` in mathlib.

The decl also has **zero call sites** anywhere in the repo (Phase 6.0): nothing depends on it. It is a
user-facing "presentation" corollary in the project's `## Main results → Number fields` list — entirely
appropriate to keep *in the project* as the number-theorist's face of the theorem, but redundant as a
mathlib contribution. A bespoke mathlib `den_powerful_number_field` alongside the general UFD theorem
would be precisely the kind of redundant per-base specialization mathlib avoids (it states results once at
maximal generality and recovers special cases by instantiation).

**WHY not (refactor-actionable detail).** Mathlib has the *building block in spirit* — the general
denominator theorem — except that block is not yet *in* mathlib; it is the project's
`PID.den_powerful_of_on_curve`, the real upstreaming target. The number-field statement is a
**1-mathlib-call composition** of that general theorem the moment it lands:

Composition sketch (≤1 line, exactly the current body):
```lean
-- once the general `den_powerful_of_on_curve` is in mathlib (over a char-zero UFD `R`),
-- the number-field case is just:
example (K : Type*) [Field K] [NumberField K] [IsPrincipalIdealRing (𝓞 K)]
    (W : WeierstrassCurve (𝓞 K)) {x y : K}
    (heq : y ^ 2 + algebraMap (𝓞 K) K W.a₁ * x * y + algebraMap (𝓞 K) K W.a₃ * y =
      x ^ 3 + algebraMap (𝓞 K) K W.a₂ * x ^ 2 + algebraMap (𝓞 K) K W.a₄ * x +
        algebraMap (𝓞 K) K W.a₆)
    {q : 𝓞 K} (hq : Prime q) (hqd : q ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K)) :
    q ^ 2 ∣ (IsFractionRing.den (𝓞 K) x : 𝓞 K) :=
  den_powerful_of_on_curve W heq q hq hqd   -- 𝓞 K's UFD + IsFractionRing instances discharge the rest
```
Building blocks (qualified names): `LutzNagell.PID.den_powerful_of_on_curve` (the general theorem — the
thing to upstream), plus mathlib's `NumberField.RingOfIntegers.instIsFractionRing`,
`NumberField.RingOfIntegers.instCharZero`, and the supplied `IsPrincipalIdealRing (𝓞 K)` (⟹
`UniqueFactorizationMonoid (𝓞 K)`).

Refactor plan (mathlib-direction): Upstream **only** the general `den_powerful_of_on_curve` (UFD form, per
its own `YES-but-generalise-first` verdict). Do **not** create a separate mathlib
`den_powerful_number_field`; if a number-field-flavored statement is ever wanted upstream, it is the
one-liner above, inlined at the (currently zero) call sites. Within the *project*, the wrapper may stay as
a convenience/presentation theorem (it has a clear docstring and sits in `## Main results`); it simply is
not its own mathlib contribution. Its zero call sites mean removing it would break nothing, but there is
no need to remove it from the project — it is documentation-grade API.

**Borderline framing (disclosed).** A reasonable reviewer could file this as **BORDERLINE-needs-human**
instead, on the single judgment call: *should a class-number-1 number-field face of an upstreamed Nagell–
Lutz theorem exist as its own mathlib lemma for discoverability, or only as an instantiation?* Mathlib's
"state once at maximal generality" convention answers "only as an instantiation", which is why the
primary verdict is `NO-composable-from-mathlib`. If the user wants the number-field statement to be
independently citable in mathlib, that is the one question to resolve:

  1. Should mathlib carry a dedicated `RingOfIntegers`/class-number-1 number-field restatement of the
     powerful-denominator theorem for discoverability, even though it is a one-line instantiation of the
     general UFD theorem? (Mathlib convention says no; default answer = no ⟹ verdict stands.)

**Next action:** Upstream the **general** theorem via `/generalise LutzNagell.PID.den_powerful_of_on_curve`
(weaken PID→UFD, per its report) and PR that; treat `den_powerful_number_field` as a project-local
presentation corollary, recovered upstream by the one-line instantiation above rather than added as a
separate mathlib declaration. If discoverability of the number-field case in mathlib is desired, answer
question 1 first.

---

## Next step

Upstream the general `LutzNagell.PID.den_powerful_of_on_curve` (UFD form) — not this wrapper. The
number-field case is a 1-call instantiation of it (base-ring hypotheses discharged by mathlib's
`RingOfIntegers` instances); keep `den_powerful_number_field` as a project-local convenience theorem, or
inline the one-liner if an upstream number-field statement is ever wanted.
