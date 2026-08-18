# /mathlibable report — `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality`

_AINTLIB `/overview` Step-9 single-declaration mathlibable assessment, NagellLutz project
(Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic divisibility sequences).
Run 2026-06-21. Mode A (single declaration), full workflow._

_Environment notes: local `lake build` is **stale** (per task brief); presence/absence in mathlib
established by **direct grep of the pinned checkout** at
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib` (mathlib pin
`09b373db6e24`, toolchain `leanprover/lean4:v4.32.0-rc1`), plus WebSearch — not the live
loogle/leansearch indices. ChatGPT-math MCP recorded `n/a` per the same brief; compensated by the
sibling reports' lit tables + extra grep. This report **reuses and cross-checks** the four sibling
reports already on disk for this Nagell–Lutz family:_
- `lutz_nagell_integrality_short.md` → **YES-add-as-is** (the direct parent / load-bearing form),
- `lutz_nagell_integrality_general.md` → **YES-but-generalise-first** (the general-Weierstrass engine),
- `lutz_nagell_general.md` → **YES-add-as-is**,
- `lutz_nagell_discriminant_general.md` → **YES-but-generalise-first**.

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); statement + proof read
                            directly from source `Main.lean:31–39`; the whole `main` builds green per
                            `CLAUDE.md`, so the decl elaborates.
- decl `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean:35`
                            (`theorem lutz_nagell_integrality`; statement 35–38, proof body line 39).
- qualified name:           ✓ **VERIFIED** `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality`
                            — `namespace LutzNagell` (Main.lean:24) → `namespace LutzNagellTheorem`
                            (Main.lean:25); base name `lutz_nagell_integrality` (Main.lean:35). The
                            task's parsed guess matches exactly.
- kind:                     theorem
- has sorry:                no — the body is the single term `lutz_nagell_integrality_short A B hpt htor`.
- module docstring summary: `Main.lean` is the **top-level façade** for the Lutz–Nagell theorem on the
                            short Weierstrass curve `y² = x³ + Ax + B`. It re-packages results proved in
                            the three imported sibling modules (`ShortWeierstrass`, `GeneralMain`,
                            `GeneralDiscriminant`) into the named theorem `lutz_nagell` and its two halves.
                            **All heavy mathematics lives in the imports; this file is specialization glue.**

---

### Statement (Phase 1)

`lutz_nagell_integrality` is **part 1 (integrality) of the Nagell–Lutz theorem, short Weierstrass
model**, in its *user-facing-façade* phrasing:

Let `A, B ∈ ℤ` with `Δ_{A,B} = -16·(4A³ + 27B²) ≠ 0`, and let `E : y² = x³ + Ax + B` be the
short Weierstrass curve over `ℚ` (base-changed from `ℤ`). If `(x, y) ∈ ℚ²` is a nonsingular affine
point that is a **nonzero torsion point** (`IsOfFinAddOrder` of the group point `Affine.Point.some`),
then `x` and `y` are both integers.

This is conjunct (1) of the classical Nagell–Lutz theorem, specialised to the short model and
packaged with the curve's `Δ ≠ 0` ("`E` is elliptic") hypothesis.

Variables / typeclasses (Lean side):
- `A B : ℤ` — the short-model curve coefficients.
- `{x y : ℚ}` — the affine coordinates of the rational point.

Hypotheses (Lean side):
- `hΔ : (shortCurveZ A B).Δ ≠ 0` — the integral curve has nonzero discriminant (i.e. `E` is elliptic).
  **This hypothesis is NOT used in the body** (see Phase 6.0 / the file inventory note) — it is carried
  for signature uniformity with the sibling `lutz_nagell_discriminant` / `lutz_nagell` and discarded.
- `hpt : (shortCurveQ A B).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point of the curve.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point has finite additive order (torsion).

Conclusion (math): a nonzero rational torsion point on `y² = x³ + Ax + B` has integer coordinates.

Conclusion (Lean): `(∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`.

**Relation to siblings (load-bearing for the verdict).** The entire proof body is
`lutz_nagell_integrality_short A B hpt htor` (Main.lean:39). Compare the parent:

```lean
-- Main.lean:35  (THIS decl)
theorem lutz_nagell_integrality (A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y :=
  lutz_nagell_integrality_short A B hpt htor          -- hΔ NOT passed / NOT used

-- GeneralMain.lean:153  (the parent — YES-add-as-is on disk)
theorem lutz_nagell_integrality_short (A B : ℤ)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by ...
```

The two have **identical conclusions**; this decl differs **only** by the extra `hΔ` hypothesis,
which it does not consume. So `lutz_nagell_integrality` is a *strictly weaker* (more-hypotheses,
same-conclusion) **one-call wrapper** around the already-YES `lutz_nagell_integrality_short`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (named-after-people: Nagell 1935 / Lutz 1937) — *with the caveat that the
mathematical content is wholly carried by the sibling `lutz_nagell_integrality_short`*. As an
artifact, this particular declaration is **glue**: a façade re-export inside the project's top-level
packaging file. It is the user-facing *name* for the short-form integrality result, but contributes
no new content over its parent.

(Note: literature width is EXHAUSTIVE regardless; the lit search below is the full Nagell–Lutz sweep,
shared with the sibling reports.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` → the one-line-**definition** heuristic is
**n/a**. (For the record the *proof* body is a single term, `lutz_nagell_integrality_short A B hpt
htor` — a one-call re-export; that observation feeds Phase 6, not Phase 2b.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The concept is the **Nagell–Lutz theorem**, integrality half, short Weierstrass model — a flagship
classical theorem. The full sweep was performed for the siblings and is reproduced/cross-checked here.

| #  | Channel                          | Query                                                                                       | Hit? | Standard form found                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz short Weierstrass `y²=x³+Ax+B` torsion integer coordinates proof                 | yes  | `(α,β)≠O` torsion ⇒ `α,β∈ℤ`; then `β=0` or `β²∣4A³+27B²` | Wikipedia, HandWiki, NumberAnalytics, Alpöge, Anqi Li, lecture notes — all agree on conjunct (1) |
|  2 | WebSearch (general form)         | Nagell-Lutz general Weierstrass `a₁..a₆`, order-2 `x=m/4 y=n/8`                              | yes  | general model: integer coords, **or** order 2 with `x=m/4, y=n/8` | Wikipedia "Generalization"; the short form is the `a₁=a₂=a₃=0` case (no order-2 escape) |
|  3 | WebSearch (named-after/textbook) | Silverman–Tate *Rational Points on Elliptic Curves* Nagell-Lutz finite order; `Δ` elliptic   | yes  | `(x,y)≠O` finite order ⇒ `x,y∈ℤ`; theorem stated for an **elliptic** curve (`Δ≠0`) | Silverman–Tate UTM Ch. II; Silverman *AEC* VIII.7; Husemöller; Alpöge "Nagell–Lutz, quickly" Thm 1.1 (the project's cited target) |
|  4 | ChatGPT MCP                      | standard short-form Nagell-Lutz; is `Δ≠0` needed for the integrality half?                   | n/a  | (MCP down per brief)                             | recorded n/a; compensated by #1–#3 + textbook record + the sibling reports |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                       | n/a  | (directories absent)                             | confirmed absent this checkout (refs are local-only & gitignored; none synced) — n/a |
|  6 | nLab                             | Nagell-Lutz / torsion points of an elliptic curve                                            | yes  | confirms `x,y∈ℤ`, `y=0 ∨ y²∣D`; "effective method for `E(ℚ)_tors`" | ncatlab.org torsion-points page; statement, no fuller generalisation |
|  7 | nCatLab (categorical)            | —                                                                                           | n/a  | not a categorical concept                        | Diophantine/arithmetic statement; no higher-categorical reformulation — n/a |
|  8 | Stacks Project (alg geom)        | torsion elliptic curve integral model / Nagell-Lutz                                          | n/a  | only moduli-stack/Picard-torsion items           | Stacks covers `M_{1,1}`, not Diophantine torsion-coordinate bounds — n/a |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz statement; integrality is conjunct (1); does it need `Δ≠0`                       | yes  | matches #1–#3; worked `E(ℚ)_tors` computations    | community expositions agree; integrality stated for an elliptic curve |
| 10 | recent arXiv (last 5 yrs)        | Nagell-Lutz imaginary quadratic fields / p-adic; Lean/mathlib formalization                  | yes  | arXiv:2509.07524 (2025, imag. quad. fields); Li p-adic notes; **no Lean formalisation surfaced** | live, actively-extended object; not yet in mathlib/Lean |

Protocol passes: WebSearch ran ≥3 distinct queries at different generality levels (specific short form,
general form, named-after/textbook); ChatGPT MCP attempted (n/a, down); local refs checked (absent,
n/a); nLab checked (hit); nCatLab/Stacks checked with n/a reasons; MathOverflow + arXiv checked (hits).

### Literature summary (Phase 3)

Concept identified as: **the Nagell–Lutz theorem** (a.k.a. Lutz–Nagell), integrality part, short
Weierstrass form.
Sources agree on the standard form: **yes.** For `y²=x³+Ax+B`, `A,B∈ℤ`, a nonzero finite-order rational
point has `x,y∈ℤ` (then `y=0 ∨ y²∣4A³+27B²`). The textbook statements (Silverman–Tate, Silverman *AEC*,
Husemöller, Alpöge) phrase it for an **elliptic** curve — i.e. they carry the `Δ ≠ 0` hypothesis as part
of "let `E` be an elliptic curve `y²=x³+Ax+B`." So the `hΔ` in this decl **matches the textbook framing**
of the theorem, even though the project's hypothesis-minimal sibling `_short` shows it is not logically
needed for the integrality half.
Most general standard form: the general-Weierstrass `a₁..a₆` version (order-2 escape `x=m/4, y=n/8`),
and over number fields / a PID base (arXiv:2509.07524) — both **already formalised separately** in this
project (`lutz_nagell_integrality_general`, `lutz_nagell_integrality_pid`/`lutz_nagell_number_field`).
Generality dimensions where the literature varies: curve model (short ⊂ general Weierstrass); base ring
(ℚ ⊂ number fields/PID). The short-ℚ form under assessment is the textbook-default, least-general member.
Disagreement with the literature: **none** for the mathematical content; the only divergence is the
presence/absence of the (logically-redundant-for-integrality, but textbook-standard) `Δ≠0` hypothesis.

---

### Generality analysis — `lutz_nagell_integrality` (Phase 4)

Literature-standard form (Phase 3): short-Weierstrass integrality is a standard named statement; the
strictly-more-general standard forms are the general-Weierstrass `a₁..a₆` version and the number-field /
PID version.

| # | Parameter / hypothesis                              | Current Lean form             | Literature-standard / better form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|-------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | `hΔ : (shortCurveZ A B).Δ ≠ 0`                      | global `Δ ≠ 0`                | **droppable for the integrality half**    | **yes — drop it**   | The parent `lutz_nagell_integrality_short` (GeneralMain.lean:153) proves the **same conclusion without `hΔ`**; this decl carries and discards it. The hypothesis-minimal form already exists in-project. |
| 2 | curve = `shortCurveQ A B` (`a₁=a₂=a₃=0`)            | short Weierstrass over ℚ      | general Weierstrass `a₁..a₆` over ℤ/ℚ      | yes (more general)  | The general form is `lutz_nagell_integrality_general` (GeneralMain.lean:110), already in-project (YES-but-generalise-first). |
| 3 | base ring ℤ → ℚ                                     | integers/rationals            | PID `R` / `Frac R`, number fields          | yes (more general)  | `lutz_nagell_integrality_pid` / `lutz_nagell_number_field` (PIDMain.lean), already in-project. |
| 4 | `hpt : Nonsingular x y`                             | nonsingular at the point      | nonsingular at the point                   | NO                  | needed to form the group point. |
| 5 | `htor : IsOfFinAddOrder …`                          | finite order                  | finite order (torsion)                     | NO                  | the defining hypothesis of the theorem. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**, in **two** distinct senses:
1. **Redundant-hypothesis narrowness (the decisive one):** it adds an *unused* `hΔ` over its parent
   `lutz_nagell_integrality_short`, so among the two short-ℚ integrality statements in the project it is
   the *weaker* one (more hypotheses, same conclusion). The hypothesis-minimal form already exists.
2. **Model/base narrowness:** strictly narrower than the general-Weierstrass and PID/number-field
   forms — but those are *already realised* as separate in-project siblings, so this is the standard
   "named specialisation" axis, not a missing-generality defect.

Number of weakening opportunities found: **3** (drop `hΔ`; generalise model; generalise base) — **all
three already realised elsewhere in the project** (`_short`, `_general`, `_pid`).
Proposed restatement: none to author — the strictly-better forms already exist (`lutz_nagell_integrality_short`
is the immediate hypothesis-minimal target; the general/PID forms subsume the model/base axes).
Cost of restatement: **n/a** (nothing to re-prove; the better forms are present).

This is the crux: unlike `_short` (whose narrowness was purely the harmless model/base axis, hence
YES-add-as-is), **this** decl's *primary* narrowness is a redundant hypothesis whose removal yields a
sibling that is already classified YES-add-as-is. That blocks a YES-add-as-is verdict for the wrapper.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | — | already minimal/typeclass-native (`WeierstrassCurve`, `IsOfFinAddOrder`, `Nonsingular`). |
|  2 | sequences/metric → filters/topological?                                  | no       | — | no limiting/topological content. |
|  3 | construction → universal-property class?                                 | no       | — | it's a theorem, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                        | partial  | could phrase via an `E(ℚ)_tors` integral-valued subgroup | mathlib has no such bundled torsion-subgroup API yet; not a real improvement over `∃ x₀ : ℤ`. |
|  5 | vector-space/field-specific → weaken typeclass?                           | yes→sep. | base ℤ/ℚ → PID/number field | the in-project PID track (axis #3 above); a *separate* theorem, not a reorg of this one. |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | not categorical. |
|  7 | concrete index ℤ/ℚ → arbitrary monoid/group?                             | no       | — | the ℤ/ℚ here is the arithmetic content (integrality *over ℤ*), not an incidental index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — the statement already speaks mathlib's native vocabulary; the only
"abstraction" axis (PID/number-field base) is a distinct, separately-formalised theorem. No contemporary
reformulation organises *this* short-ℚ wrapper better. (Phase 4c does not flip the verdict.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `lutz_nagell_integrality` (Phase 5)

[A] Lean-Finder       n/a — live index not consulted (build stale); substituted by [D] direct grep of the exact pin.
[B] Loogle            pattern: `IsOfFinAddOrder` on `WeierstrassCurve`/`Affine.Point` ⇒ `(∃ _:ℤ, (_:ℚ)=x) ∧ (∃ _:ℤ, (_:ℚ)=y)` — no such index hit known; [D] authoritative for this pin.
[C] LeanSearch        NL: "Nagell-Lutz", "torsion point of elliptic curve has integer coordinates" — not consulted live; covered by [D].
[D] Grep mathlib src  `grep -rniE "nagell|lutz" .lake/packages/mathlib/Mathlib/` → **only "Patrick Lutz"** (Galois-theory author: AbelRuffini, Solvable, PrimitiveElement, Galois/*, …); **zero** Nagell–Lutz hits. `grep -rniE "torsion|IsOfFinAddOrder|addOrderOf" Mathlib/AlgebraicGeometry/EllipticCurve/` → only `twoTorsionPolynomial` (2-torsion *polynomial*, `discr = 16Δ`) + 2-torsion docstrings; **no torsion-point→integrality theorem at any generality**. `IsOfFinAddOrder` occurs **nowhere** under `AlgebraicGeometry/`. → **no hits**
[E] Name pattern      `lutz_nagell` / `nagell_lutz` / `*torsion*integral*` over the EC tree → **no hits**.

Searched for both:
  - the user's current form (short-ℚ torsion integrality, with `Δ≠0`) — **absent**;
  - the literature-standard / better forms (hypothesis-minimal short form; general-Weierstrass; PID /
    number-field; each half independently) — **all absent**.

Concluded: **not in mathlib** (direct grep of the pinned checkout exhausted, plus the better forms).
Mathlib ships the entire elliptic-curve *substrate* — `WeierstrassCurve`, the affine group law, `Δ`,
`twoTorsionPolynomial`, `DivisionPolynomial/*`, `NumberTheory/EllipticDivisibilitySequence` (the very
files this project forks) — but has **never connected any of it to the arithmetic of torsion points**.
(Consistent with all four sibling reports.)

---

### Composition check (+ call-sites signal) (Phase 6)

#### Call sites — `lutz_nagell_integrality` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file): **K = 0.**
In-file uses: **1** — Main.lean:71, inside the body of the public `lutz_nagell`
(`obtain ⟨⟨x₀, hx⟩, ⟨y₀, hy⟩⟩ := lutz_nagell_integrality A B hΔ hpt htor`).
External-to-file callers: **0.**
Whole-repo grep for the exact token `lutz_nagell_integrality` (excluding `_short`/`_general`/`_pid`)
returns **only** the declaration (Main.lean:35) and that single sibling call (Main.lean:71).

| Caller file:line | Usage pattern (one-line excerpt)                                   |
|------------------|--------------------------------------------------------------------|
| Main.lean:71     | `… := lutz_nagell_integrality A B hΔ hpt htor` (body of `lutz_nagell`, same file) |

Inline-derivation grep (is the same statement re-derived without this decl?): the integrality content
*is* re-derived/used elsewhere — but always via the **parent** `lutz_nagell_integrality_short`
(Main.lean:39 is itself the only consumer of `_short` outside `GeneralMain.lean`), not via this wrapper.
So this wrapper has **no consumer outside its own file** and is bypassed by everything except the one
sibling theorem packaged next to it.

Interpretation (per the call-sites table in the skill): **K = 0 external + only 1 in-file use, and that
single use is a 1-call wrapper of an already-YES sibling** → the "wrong abstraction / could be inlined"
signal, leaning NO/BORDERLINE — *not* the capstone-export signal that `lutz_nagell` (the full theorem)
or `lutz_nagell_integrality_short` (the load-bearing form, K=1 to the public API) legitimately carry.
The headline short-form *theorem* the project exports is `lutz_nagell` (the combined statement) and the
mathlib-worthy integrality lemma is `lutz_nagell_integrality_short`; this `lutz_nagell_integrality`
sits between them purely as packaging.

#### Composition attempt (Phase 6a)

Can `lutz_nagell_integrality` be derived from **mathlib** in ≤3 chained calls?

Attempt 1 (from mathlib): any mathlib torsion-integrality lemma to chain to?
  - Mathlib decls used: — (none exist; Phase 5).
  - Result: **fails** — mathlib has no Nagell–Lutz / torsion-integrality content at any generality.

Attempt 2 (the actual body): `lutz_nagell_integrality_short A B hpt htor`.
  - Decls used: **`LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_short` — a PROJECT theorem, not
    a mathlib primitive** (and itself a deep development resting on the `General*` track + forked
    DivisionPolynomial/EDS files).
  - Result: it **is** a genuine 1-call composition — but of a *project* sibling, **not** of mathlib.
    The discarded `hΔ` makes it a strictly-weaker restatement of that sibling.

Conclusion: **NOT-COMPOSABLE *from mathlib*** (mathlib lacks every building block). It **IS** a trivial
1-call wrapper of the in-project `lutz_nagell_integrality_short` (adding a redundant hypothesis). This is
the structurally important fact: relative to mathlib it is not composable, but relative to the project it
is a redundant re-export dominated by an already-YES sibling — which is exactly why the verdict is a
human judgment call rather than a clean YES or a clean NO-composable (the skill's NO-composable bucket
requires the *building blocks to be in mathlib*, which here they are not).

---

## Verdict: `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): a **named classical theorem** (Nagell 1935 / Lutz 1937); the Lean
  statement is the textbook short-ℚ integrality conjunct (1), stated for an elliptic curve (`Δ≠0`),
  matching Silverman–Tate / Silverman *AEC* VIII.7 / Husemöller / Alpöge. Not in Lean/mathlib.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — primarily because it carries a
  **redundant, discarded `hΔ`** over the hypothesis-minimal sibling `lutz_nagell_integrality_short`
  (already YES-add-as-is on disk); secondarily it is the short/ℚ specialisation of the in-project
  general and PID forms. Phase 4c modern-idiom = no.
- Mathlib search (Phase 5): **not in mathlib** at any generality (zero Nagell/Lutz; only
  `twoTorsionPolynomial` + division-polynomial/EDS building blocks).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib**, but it **IS a 1-call wrapper of the
  project sibling `lutz_nagell_integrality_short`**, differing only by the unused `hΔ`. Call sites:
  **K = 0 external, 1 in-file**, the wrong-abstraction/bypassed signal.

**Rationale (why BORDERLINE, not a clean bucket):**

The *mathematics* here — short-Weierstrass integrality of rational torsion points — is a genuine,
named, mathlib-missing theorem, and on those grounds alone one is tempted toward a YES. But this
particular declaration is **not the right carrier** of that content: its entire body is the single
call `lutz_nagell_integrality_short A B hpt htor`, and it differs from `lutz_nagell_integrality_short`
**only** by an extra `hΔ : Δ ≠ 0` hypothesis that it never uses. The sibling `_short` — the
hypothesis-minimal form — is already assessed **YES-add-as-is** on disk and is the form the project
actually leans on (it is what `Main.lean:39` delegates to, and the only thing the integrality content
routes through). So among the project's own statements, `lutz_nagell_integrality` is the *strictly
weaker* of two short-ℚ integrality theorems, with **K = 0 external call sites** and only one in-file
use (by the combined `lutz_nagell`). A YES-add-as-is verdict is gate-blocked (Phase 4b = STRICTLY
NARROWER, and a strictly-better in-project form exists); a clean NO-composable-from-mathlib is also
wrong, because the bucket *requires the building blocks to live in mathlib*, and here the one building
block (`_short`) is itself a project decl that is supposed to be upstreamed.

What remains is a real **judgment call about mathlib's API surface** that the skill is not entitled to
make alone: *should mathlib carry a named short-form integrality theorem that bundles the `Δ ≠ 0`
("`E` is elliptic") hypothesis — matching how every textbook (Silverman–Tate, Silverman AEC,
Husemöller, Alpöge) states it — or should it expose only the hypothesis-minimal `_short` form and let
users supply `Δ≠0` separately?* The literature genuinely states the theorem with `Δ≠0`, so the
wrapper is not "wrong"; it is the *textbook framing*. But mathlib style generally prefers the
hypothesis-minimal lemma plus, at most, a thin convenience corollary. Which of those mathlib wants —
and whether the convenience corollary is worth a named slot at all, given it is dead outside its file —
is the open question. (Cross-check: this verdict is consistent with the family — `_short`,
`_general`, `lutz_nagell` are the YES carriers of the content; this façade wrapper is the one member
that is pure packaging.)

**Numbered questions for the human (≤5):**
  1. Should mathlib's *user-facing* short-Weierstrass Nagell–Lutz integrality statement carry the
     textbook `Δ ≠ 0` ("`E` is elliptic") hypothesis (this decl), or should mathlib expose only the
     hypothesis-minimal `lutz_nagell_integrality_short` and leave `Δ≠0` to the caller?
  2. If `Δ≠0` is wanted on the public statement: is it acceptable that the hypothesis is **logically
     unused** by the integrality half (it is genuinely discarded here), i.e. present purely to signal
     "elliptic curve" / for uniform packaging — or should mathlib avoid stating an unused hypothesis?
  3. Given this exact declaration has **K = 0 external call sites** (only one in-file use, by the
     combined `lutz_nagell`), is a separately-named short-form *integrality-only* theorem warranted at
     all, or should the public surface be just the combined `lutz_nagell` (integrality + discriminant)
     plus the hypothesis-minimal `_short` lemma — making this `lutz_nagell_integrality` redundant?
  4. If the convenience wrapper IS wanted in mathlib, it should be re-derived there as a one-liner from
     `_short` (drop or keep `hΔ` per Q1–Q2) — agreed it ships **with** `_short` in the same Nagell–Lutz
     PR family, never as a standalone lemma?

Next action: the human answers Q1–Q4. If the decision is "hypothesis-minimal only," this decl is dropped
from the upstreaming set (its content is fully carried by `lutz_nagell_integrality_short` → re-aim there)
and locally it can simply be inlined into `lutz_nagell` (replace `lutz_nagell_integrality A B hΔ hpt htor`
at Main.lean:71 with `lutz_nagell_integrality_short A B hpt htor`). If the decision is "keep the
textbook-framed wrapper," it becomes a one-line convenience corollary co-shipped with `_short` in the
Nagell–Lutz PR family (gated, like the rest of the family, on first reconciling the project's forks of
`DivisionPolynomial.*` and `EllipticDivisibilitySequence` against mathlib). Either way, re-run
`/mathlibable LutzNagell.LutzNagellTheorem.lutz_nagell_integrality` after the policy call to lock the
bucket.

---

## Next step

Human answers Q1–Q4 (textbook-framed wrapper-with-`Δ≠0` vs. hypothesis-minimal `_short` only;
and whether a separately-named integrality-only short-form theorem is warranted given K = 0 external
uses). The mathlib-worthy *content* is already captured by the sibling `lutz_nagell_integrality_short`
(YES-add-as-is) and the general/PID engines; this declaration is a façade re-export that adds a
redundant `Δ≠0`. Resolve the API-policy question, then either inline-and-drop it (re-aim to `_short`)
or keep it as a thin corollary co-shipped with `_short` in the Nagell–Lutz PR family — gated on
de-forking the project's DivisionPolynomial / EDS extensions.
