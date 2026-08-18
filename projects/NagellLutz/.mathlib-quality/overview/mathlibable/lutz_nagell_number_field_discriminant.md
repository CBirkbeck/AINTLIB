# /mathlibable report — `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoned from source
- decl `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:533`
- qualified name:           `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`
                            (nested `namespace LutzNagell` → `namespace NumberField`; VERIFIED from source)
- kind:                     theorem
- has sorry:                no (body is a single application of the PID lemma)
- module docstring summary: Lutz–Nagell theorem generalised from ℤ/ℚ to a char-0 PID `R` with
                            fraction field `K`, plus a number-field specialisation track.

---

### Statement (Phase 1)

`lutz_nagell_number_field_discriminant` states:

> Let `K` be a number field whose ring of integers `𝓞 K` is a principal ideal ring
> (equivalently `classNumber K = 1`). Let `W` be a Weierstrass curve with coefficients
> in `𝓞 K`, discriminant `Δ`. Let `(x, y)` be a nonzero point on `W / K` of finite
> (additive) order, whose coordinates are integral: `x = algebraMap (x₀)`, `y = algebraMap (y₀)`
> with `x₀, y₀ ∈ 𝓞 K`. Assume every prime `p` dividing the torsion order is squarefree in `𝓞 K`.
> Set `κ₀ = 2·y₀ + a₁·x₀ + a₃` (the value of `∂F/∂y`, i.e. the 2-division / ψ₂ value).
> Then **either `κ₀ = 0`, or `κ₀² ∣ 4·Δ`**.

This is the general-Weierstrass form of the classical Nagell–Lutz divisibility conclusion.
Over `ℚ` with short Weierstrass `y² = x³ + Ax + B` one has `κ₀ = 2y`, so `κ₀² = 4y²` and the
conclusion specialises to `y² ∣ 4A³ + 27B²` (the classical "y = 0 or y² ∣ D").

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K] [DecidableEq K]` — the number field
- `[IsPrincipalIdealRing (𝓞 K)]` — class number 1
- `W : WeierstrassCurve (𝓞 K)` — integral Weierstrass model
- `{x y : K}` — affine coordinates of the point in `K`

Hypotheses (Lean side):
- `hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion
- `hsf_all : ∀ p, p.Prime → p ∣ addOrderOf … → Squarefree (p : 𝓞 K)` — unramified-at-torsion hypothesis
- `hx : algebraMap (𝓞 K) K x₀ = x`, `hy : algebraMap (𝓞 K) K y₀ = y` — integrality of the coordinates

Conclusion (math): `κ₀ = 0  ∨  κ₀² ∣ 4Δ`, with `κ₀ = 2y₀ + a₁x₀ + a₃`.
Conclusion (Lean): `(2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4 * W.Δ`

**Proof body (load-bearing):**
```lean
  PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy
```
The theorem is a **one-application specialisation** of the PID-track theorem
`LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion` (PIDMain.lean:401), obtained by
instantiating that theorem's `variable`s `{R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
[CharZero R] {K} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` at `R := 𝓞 K`,
`K := K`. All instances (`𝓞 K` is a char-0 PID with fraction field `K`) are found by
typeclass resolution; no mathematical work happens in this declaration.

---

### Size classification (Phase 2a)

Verdict: **BIG** (named theorem) — but in a qualified sense.
Reason: "Lutz–Nagell" is a theorem named after people, so the *result* is BIG and squarely
in the literature. However, **this particular declaration** is not the result — it is the
number-field *specialisation wrapper* of the PID-track result that carries the actual content.
The BIG status attaches to the underlying `PID.lutz_nagell_pid_discriminant_of_torsion`.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line, but kind is **theorem**, so the one-liner *def* analysis
does not apply. Recorded as a note: the theorem is a single-application specialisation of a
more general same-project theorem — the analogue of a one-liner wrapper. This biases Phase 7
toward a NO bucket (the general form is what carries value), exactly as the one-liner heuristic
would for a def.

Conclusion: n/a (theorem) — but the "thin wrapper over a more general result" signal is strong.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem elliptic curve torsion point y divides discriminant statement"            | yes  | `y = 0 ∨ y² ∣ D` over ℚ (Wikipedia) | classical conclusion confirmed verbatim |
|  2 | WebSearch (general / NF form)    | "Nagell-Lutz number field ring of integers integral torsion points generalization"             | yes  | NF generalisation exists; recent arXiv 2509.07524 for imaginary quadratic, class number 1 | matches the project's class-number-1 hypothesis |
|  3 | WebSearch (general Weierstrass)  | "(2y + a1 x + a3)^2 divides discriminant torsion 2-division polynomial"                          | yes (partial) | short-Weierstrass `β² ∣ 4A³+27B²` (Dummit/Wikipedia); general κ₀ form not stated verbatim but is the standard ψ₂ reformulation | confirms short-W corollary; general form is the textbook 2-division reformulation |
|  4 | WebSearch (Silverman / p-adic)   | "Silverman arithmetic of elliptic curves Nagell-Lutz ... p-adic valuation any number field"     | yes  | proof is valuation-theoretic (Silverman VIII; Anqi Li p-adic notes) | minimal hypothesis is a DVR at each prime — see Phase 4 |
|  5 | ChatGPT MCP                      | self-contained Q on standard form + maximal generality + triviality of NF specialisation        | n/a  | MCP DOWN (Codex exec failed) | environment note warned MCP may be down; compensated with extra WebSearch channels #3,#4 + WebFetch of #2 |
|  6 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`; `ls refs/`                                | n/a  | no references dir; no `refs/` dir present | recorded n/a (dirs absent) |
|  7 | WebFetch (arXiv 2509.07524)      | precise statement + hypotheses of the imaginary-quadratic class-number-1 Nagell–Lutz            | yes  | proves **integrality** (coords in 𝓞_K / ℤ[√D]); explicitly does NOT prove the discriminant-divisibility | confirms divisibility is the *classical* part being generalised here |
|  8 | nLab                             | Nagell–Lutz theorem                                                                              | n/a  | nLab has no Nagell–Lutz / elliptic-curve-torsion-integrality entry | arithmetic-of-EC result, outside nLab's category-theory focus |
|  9 | nCatLab                          | —                                                                                               | n/a  | not a categorical concept | n/a with reason |
| 10 | Stacks Project                   | Nagell–Lutz / torsion integrality                                                               | n/a  | Stacks has elliptic-curve scheme theory but not this Diophantine torsion result | arithmetic Diophantine statement, not in Stacks' scope |
| 11 | MathOverflow / Math.SE           | (covered transitively via #1–#4 result pages: MIT 18.783, unizg, Galperin REU, Alpoge notes)    | yes  | same standard forms; "y ∣ D ⟹ y² ∣ D" sharper variant noted | multiple lecture notes corroborate |
| 12 | recent arXiv (last 5 yr)         | (#2/#7) arXiv 2509.07524 (2025); ScienceDirect S0022314X12001163 (hyperelliptic analogue)       | yes  | NF generalisation is active recent literature | the NF direction is genuinely of current interest |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (#1 specific, #2 NF-general, #3 general-Weierstrass, #4 proof/most-general-setting). ✓
- ChatGPT MCP attempted with a standard-form + generality + triviality question; **server down** (compensated by extra WebSearch #3/#4 and a WebFetch of the primary NF source). ✓ (documented failure, not a skip)
- Local references checked (absent → n/a). ✓
- nLab / nCatLab / Stacks / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (a.k.a. Lutz–Nagell), discriminant-divisibility
conclusion for torsion points, in its **general-Weierstrass / number-field** form.

Sources agree on the standard form: **yes**.
- Classical (ℚ, short Weierstrass): `y = 0 ∨ y² ∣ D`, `D = 4A³+27B²` (often sharpened to `y ∣ D`).
- General Weierstrass: replace `2y` by the 2-division value `κ₀ = 2y + a₁x + a₃` (= `ψ₂`), giving
  `κ₀ = 0 ∨ κ₀² ∣ 4Δ`. This is the textbook reformulation; the project's short-Weierstrass
  corollary `lutz_nagell_number_field_cubicDisc_discriminant` reproduces `y₀² ∣ 4a₄³+27a₆²+…`.
- Number-field generalisation (class number 1 / 𝓞_K a PID): recent literature (arXiv 2509.07524,
  2025) treats exactly this regime — confirming the hypothesis set the project uses.

Most general standard form: stated over the **ring of integers of a number field of class
number 1** (or, in the proof's natural habitat, **a Dedekind/PID base with valuation at each
prime**). The conclusion `κ₀² ∣ 4Δ` is the discriminant-divisibility half; the integrality half
is the other (recent) half.

Generality dimensions where the literature varies:
  - base ring: ℤ → 𝓞_K (class number 1) → general PID/Dedekind of char 0. The valuation-theoretic
    proof needs only a DVR per prime; PID/class-number-1 is the convenient global packaging.
  - curve model: short Weierstrass → general Weierstrass (the κ₀ = ψ₂ reformulation).

Disagreement with the literature: **none**. The project's `κ₀² ∣ 4Δ` is the correct, standard
general-Weierstrass discriminant-divisibility statement.

---

### Generality analysis — `lutz_nagell_number_field_discriminant`

Literature-standard form (from Phase 3): the discriminant-divisibility conclusion holds over any
class-number-1 number-field ring of integers — and, by the valuation-theoretic proof, over any
char-0 PID/Dedekind base. **The project already has this more-general form** as a separate
declaration: `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion` (PIDMain.lean:401), stated
for `R` any `[CommRing] [IsDomain] [IsPrincipalIdealRing] [CharZero]` with fraction field `K`.

| # | Parameter / hypothesis              | Current Lean form                              | Literature / more-general form               | Weaker form exists? | Reason |
|---|-------------------------------------|------------------------------------------------|-----------------------------------------------|---------------------|--------|
| 1 | base ring                            | `R = 𝓞 K` for `K` a number field, `[IsPrincipalIdealRing (𝓞 K)]` | any char-0 PID `R` with `IsFractionRing R K` | **YES** | the proof (via PID track) never uses that `R` is a *number-field* ring of integers — only PID + char 0. The general form is literally the declaration this one calls. |
| 2 | `[NumberField K]` + `[DecidableEq K]`| number field                                   | arbitrary fraction field of the PID            | **YES** | `NumberField K` is unused by the mathematics; it only supplies the PID instance on `𝓞 K`. |
| 3 | `hsf_all` (squarefree-at-torsion)    | stated for primes of `𝓞 K`                     | same, for primes of the PID `R`                | n/a (carried verbatim into the general form) | identical in both forms |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the number-field *specialisation*
of an already-present, strictly-more-general PID theorem).
Number of weakening opportunities found: 2 (base ring → char-0 PID; drop `NumberField`/`DecidableEq` cruft).
Proposed "restatement": there is nothing to restate — the more-general theorem **already exists**
in the same file as `PID.lutz_nagell_pid_discriminant_of_torsion`. The number-field declaration is
its image under `R := 𝓞 K`.
Cost of restatement: **CHEAP** (the general form is already proved; this decl is a 1-line instantiation).

Note: this is NOT a "generalise the proof" situation. The general proof is done. This decl is a
specialisation wrapper. The mathlib-relevant object is the **PID** theorem.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let K be a number field" → typeclass instead of bundled hypothesis?                        | already is (typeclass) | — | — |
|  2 | sequences/metric → filters/topology?                                                         | no | — | finite/algebraic statement; no analysis |
|  3 | construct an object → universal-property class?                                              | no | — | it's a divisibility proposition |
|  4 | set-with-closure-predicate → bundled substructure?                                           | no | — | no substructure here |
|  5 | field/metric-specific → weaken typeclass hierarchy?                                          | **yes** | state over a char-0 **PID** (already done as `PID.lutz_nagell_pid_discriminant_of_torsion`), or even a Dedekind/DVR base | the PID form already specialises to *every* class-number-1 number field, not just `K` |
|  6 | 1-categorical → higher-categorical?                                                          | no | — | n/a |
|  7 | concrete index → arbitrary algebraic structure?                                              | partially (= row 5: `𝓞 K` → general PID) | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is **already realised** by the sibling declaration
`PID.lutz_nagell_pid_discriminant_of_torsion`. The mathlib-idiomatic target is "char-0 PID base
with fraction field `K`" (mathlib's idiom: state over the weakest algebraic typeclass that carries
the proof, then let `𝓞 K` be an instance). The number-field decl is the un-idiomatic specialisation.
Real improvement: yes — the PID form composes with *any* class-number-1 ring (rational, quadratic,
cyclotomic-of-class-number-1, …) for free; the `K`-specific form does not.

---

### Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equality or typeclass-search path).

---

### Mathlib search-status: `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`

[A] Lean-Finder       n/a — mathlib-index NL search tool not available in this env (only LSP + web exposed)
[B] Loogle            n/a — Loogle MCP not available in this env; substituted exhaustive source grep (method D)
[C] LeanSearch        n/a — LeanSearch MCP not available in this env; substituted WebSearch + source grep
[D] Grep mathlib src  Searched `Mathlib/` for: `Lutz`/`Nagell` (word-boundary), `Lutz–Nagell`/`Nagell–Lutz`;
                      `IsOfFinAddOrder`/`addOrderOf`/`FinAddOrder` in `EllipticCurve/`;
                      torsion-point integrality / `IsLocalization.IsInteger` + torsion;
                      `twoTorsionPolynomial`, `twoTorsionPolynomial_discr`, `Δ`/discriminant + dvd.
                      → **no hits** for any Nagell–Lutz / torsion-coordinate-divides-Δ statement.
                      The only "Lutz" hits are **copyright lines** ("Patrick Lutz") in Galois-theory
                      files — false positives, not the theorem.
[E] Name pattern      Grepped decl/dot-notation name patterns; nothing in mathlib namespace.

What mathlib DOES have (building blocks, not the result):
  - `WeierstrassCurve.twoTorsionPolynomial` + `twoTorsionPolynomial_discr` (`= 16 * W.Δ`)
    — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (the ψ₂ polynomial + its discriminant)
  - `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` (Ψₙ machinery)
  - `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (EDS — and even this has open TODOs:
    "prove that `normEDS` satisfies `IsEllDivSequence`" is *not yet done*)
  - `WeierstrassCurve.Affine.Point`, `IsOfFinAddOrder`, `addOrderOf` (the torsion vocabulary)

Searched for both:
  - the user's current form (number-field, class number 1): not in mathlib
  - the literature-standard / more-general form (PID, or short-Weierstrass `y²∣D`): not in mathlib

Concluded: **not in mathlib** — neither this number-field form nor the general PID form nor the
classical `y² ∣ D` form. Mathlib has division-polynomial / EDS / 2-torsion-polynomial *building
blocks* but **no Nagell–Lutz theorem and no torsion-integrality / torsion-discriminant-divisibility
statement of any kind**.

---

### Call sites — `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`

Internal use count: **0** (within the project, excluding the declaring line).
External-to-file callers: **0** distinct files.

grep across `projects/` for `lutz_nagell_number_field_discriminant`:
  - PIDMain.lean:533 — the declaration head itself
  - (no other occurrence anywhere)

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: the *content* (κ₀² ∣ 4Δ from torsion) is derived once, in the PID track
(`PID.lutz_nagell_pid_discriminant_of_torsion`, PIDMain.lean:401) — that is the real theorem; the
number-field decl just re-exposes it. Not an independent re-derivation, a deliberate wrapper.

Call-sites signal: **K = 0 internal uses, theorem-wrapper over a more general sibling.** Per the
Phase 6.0.1 table this is a "K = 1-or-0 use → possibly the wrong abstraction / could be inlined"
pattern, leaning **NO-composable-from-mathlib**: the value is in the general PID theorem, not in
this 𝓞_K specialisation.

---

### Composition check (Phase 6)

Can `lutz_nagell_number_field_discriminant` be derived in ≤3 chained calls?

Attempt 1: `PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy`
  - Decls used: `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion` (the project's own general theorem)
  - Result: **succeeds** — this is literally the entire proof body (a single application).
  - Notes: the number-field theorem is exactly the PID theorem at `R := 𝓞 K`, `K := K`. The four
    instances `[IsDomain (𝓞 K)]`, `[IsPrincipalIdealRing (𝓞 K)]` (hypothesis), `[CharZero (𝓞 K)]`,
    `[IsFractionRing (𝓞 K) K]` are all supplied by mathlib's number-field API; no math is done here.

Conclusion: **COMPOSABLE** — a 1-call specialisation of an existing (more general) theorem.

Caveat on the mathlib framing: the parent it composes from is a **project** theorem, not a mathlib
theorem (mathlib has neither). So "composable from mathlib" is true only once the *parent* PID
theorem is itself in mathlib. The actionable reading: **the PID theorem is the mathlib candidate;
this number-field decl is a downstream 1-line instantiation that should NOT be a separate mathlib
lemma.** If a number-field-specific convenience corollary is ever wanted in mathlib, it is a
1-line `example`/specialisation of the PID lemma, inlined at need.

---

## Verdict: `LutzNagell.NumberField.lutz_nagell_number_field_discriminant`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz discriminant-divisibility; standard form `κ₀ = 0 ∨ κ₀² ∣ 4Δ`
  (general Weierstrass), with the maximal natural base being a char-0 PID/Dedekind ring (valuation proof).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — this is the `R := 𝓞 K`
  specialisation of the already-proved, strictly-more-general `PID.lutz_nagell_pid_discriminant_of_torsion`.
- Mathlib search (Phase 5): **not in mathlib** (no Nagell–Lutz, no torsion-integrality, no torsion-Δ
  divisibility — in either the number-field or PID or classical form). Only division-polynomial / EDS /
  2-torsion-polynomial building blocks exist.
- Composition check (Phase 6): **COMPOSABLE** — one application of the project's PID theorem.

**Rationale:**

This declaration is a thin number-field *specialisation wrapper*: its whole body is the single
application `PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy`, instantiating the
project's PID-track theorem at `R := 𝓞 K`. No mathematics happens in it; `NumberField K` and
`DecidableEq K` are used only to summon the PID/char-0/fraction-field instances on `𝓞 K`. It has
**zero call sites** anywhere in the project. By mathlib's iron rule (add the most general form), the
correct object to consider for mathlib is the **PID theorem** `lutz_nagell_pid_discriminant_of_torsion`,
which already subsumes this one and every other class-number-1 case (rational, quadratic, cyclotomic…)
for free. Shipping this 𝓞_K-only specialisation *as a separate mathlib lemma* would be exactly the
"vector-spaces-instead-of-modules" anti-pattern the skill exists to catch — a redundant narrowing of a
result whose general form is the real contribution.

Note carefully that mathlib has **neither** form: the Nagell–Lutz theorem is entirely absent. So the
overall *body of work* here is genuinely mathlib-worthy — but the mathlibable unit is the **PID
declaration**, not this wrapper. For this specific declaration the verdict is NO-composable: it is a
≤1-call specialisation that, in a mathlib world, would be inlined as a one-line `example` or simply
not exist (callers would use the general PID theorem with `R := 𝓞 K` directly).

**WHY not (refactor-actionable):**
Mathlib has the building blocks (`WeierstrassCurve.twoTorsionPolynomial`, the `DivisionPolynomial.*`
and `EllipticDivisibilitySequence` machinery) but not the theorem — and crucially the *project itself*
already carries the strictly-more-general form. This declaration is a 1-call composition over that
general form. It should not be a standalone mathlib lemma.

Mathlib / project building block:
  `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`
  at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:401`
  (general char-0 PID base; this is the mathlib candidate — assess/PR *that* one)

Composition sketch (≤3 lines) — the number-field statement as a 1-call specialisation:
```lean
example (K : Type*) [Field K] [NumberField K] [DecidableEq K]
    [IsPrincipalIdealRing (𝓞 K)] (W : WeierstrassCurve (𝓞 K)) {x y : K}
    (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) → Squarefree (p : 𝓞 K))
    {x₀ y₀ : 𝓞 K} (hx : algebraMap (𝓞 K) K x₀ = x) (hy : algebraMap (𝓞 K) K y₀ = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨ (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ :=
  PID.lutz_nagell_pid_discriminant_of_torsion W hpt htor hsf_all hx hy
```

Call sites in our project (from Phase 6.0): **K = 0**.

Refactor plan: there are no call sites to update. If this project wants to keep a number-field-facing
API surface, that is a *project* convenience and fine to keep locally — but it does **not** travel to
mathlib as its own lemma. When the underlying result is upstreamed, upstream the **PID** theorem
(`lutz_nagell_pid_discriminant_of_torsion`); any number-field user writes the one-line specialisation
above (or applies the PID theorem with `R := 𝓞 K` directly). Next action for *this* decl: do not PR it
standalone; fold it into the PID theorem's PR as, at most, a documented one-line `example`, or drop it.

**Next action:** Run `/mathlibable LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion` — *that* is
the declaration carrying the mathlibable content (very likely YES-add-as-is or YES-but-generalise-first,
since mathlib has no Nagell–Lutz theorem at all). This number-field wrapper rides along with it as a
one-line specialisation, not as an independent lemma.

---

## Next step

Assess and (if green) upstream the general PID theorem `LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion`
instead of this wrapper. For this declaration specifically: NO standalone mathlib lemma — it is a
≤1-call specialisation of that general theorem (inline as a one-line `example` at most; K = 0 call sites).
