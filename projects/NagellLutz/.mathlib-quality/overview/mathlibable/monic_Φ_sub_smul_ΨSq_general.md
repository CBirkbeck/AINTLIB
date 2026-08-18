# /mathlibable report — `LutzNagell.LutzNagellTheorem.monic_Φ_sub_smul_ΨSq_general`

Mode A (single declaration), full 10-phase workflow. The local Lean build is stale,
so Phase 0 build-clean is asserted from source reading rather than a live `lake build`;
the declaration, its `PID` parent, and every mathlib building block are read directly
from source.

**Verdict supersedes the 2026-06-18 draft of this file.** The earlier draft landed
on `YES-but-generalise-first`; this run revises it to `NO-composable-from-mathlib`.
The reason is in Phase 6: the earlier draft treated the ℤ→UFD generality gap as the
decisive axis and concluded "ship the general `PID` form", but it did not push the
composition check through the *general* form. When you do, the fully-general
`PID.monic_Φ_sub_smul_ΨSq` is itself a ≤3-call composition of mathlib primitives —
`Φ` is **already proven monic in mathlib** (`leadingCoeff_Φ`), and "monic minus a
strictly-lower-degree polynomial is monic" is the stock lemma `Monic.sub_of_left`.
There is no new mathematical content at any generality; the lemma is degree
bookkeeping that should be inlined at its single call site.

---

### Baseline (Phase 0)
- lake build:               (stale locally — reasoned from source per task note)
- decl `…monic_Φ_sub_smul_ΨSq_general`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean:56` (signature), `:58` (statement line), proof on `:59`
- qualified name VERIFIED:  `namespace LutzNagell` → `namespace LutzNagellTheorem`, base
                            name `monic_Φ_sub_smul_ΨSq_general`. Full name:
                            `LutzNagell.LutzNagellTheorem.monic_Φ_sub_smul_ΨSq_general`. ✓
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Integral multiple implies integral point (general Weierstrass
                             curves)": if `n • P` has integral affine coords on a general
                             Weierstrass curve `y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆` over ℚ with
                             `aᵢ ∈ ℤ`, then `P` has integral affine coords. This file holds the
                             ℤ/ℚ specialisations of the UFD-general `PID.*` track.

---

### Statement (Phase 1)

`monic_Φ_sub_smul_ΨSq_general` states: for a Weierstrass curve `W` over `ℤ`, a nonzero
integer `n`, and any integer `c`, the polynomial `Φ_n − C c · ΨSq_n ∈ ℤ[X]` is **monic**.

Here `Φ_n` and `ΨSq_n = ψ_n²` are the standard elliptic-curve division-polynomial objects
giving the multiplication-by-`n` x-coordinate: `x([n]P) = Φ_n(x) / ΨSq_n(x)`, with `Φ_n`
monic of degree `n²` and `ΨSq_n` of degree `n²−1`. The lemma packages the trivial degree
fact that subtracting a constant multiple of the lower-degree denominator from the monic
higher-degree numerator preserves monicity. It exists solely to feed the rational-root
theorem: in `x_isInteger_of_nsmul_x_isInteger` (its sole consumer, via the `PID` parent),
`x` is shown to be a root of `Φ_n − C c · ΨSq_n` (with `c = x'`, the integral x-coordinate
of `n•P`), and `isInteger_of_is_root_of_monic` then forces `x ∈ ℤ`.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — the curve, over `ℤ`.

Hypotheses (Lean side):
- `{n : ℤ} (hn : n ≠ 0)` — nonzero multiplier (so `deg Φ_n = n² > deg(C c · ΨSq_n)`).
- `(c : ℤ)` — the constant scalar (the integral x-coordinate of `n•P` at the call site).

Conclusion (math): `Φ_n − c·ψ_n²` is a monic integer polynomial.
Conclusion (Lean): `(W.Φ n - C c * W.ΨSq n).Monic`.

Proof body (Lean): `PID.monic_Φ_sub_smul_ΨSq W (by exact_mod_cast hn) c` — i.e. it is a
**verbatim forwarding** to the UFD-general `PID` lemma at `R = ℤ`, the cast `(n : ℤ) ≠ 0`
following from `(n : ℤ) ≠ 0` by `exact_mod_cast`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/bookkeeping lemma (monicity by degree counting) that exists only to supply
the `Monic` hypothesis of `isInteger_of_is_root_of_monic`. Not a named theorem, not a project
main result, not a new structure. (Literature width was run EXHAUSTIVE regardless, per
protocol.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — one-line check **n/a**. (Note: the body
*is* a single forwarding line, which reinforces the "thin specialisation wrapper" reading, but
the formal Phase-2b gate applies to definitions, not lemmas.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | elliptic curve division polynomial phi_n monic degree n^2 Nagell-Lutz integral points                  | yes  | `Φ_n` monic of degree `n²`; `ψ_n²` degree `n²−1`     | Silverman AEC VIII; Alpöge "Nagell-Lutz, quickly" (Harvard); Anqi Li MIT 18.784 Nagell-Lutz writeup; Sutherland 18.783 |
|  2 | WebSearch (general form)         | "division polynomial" psi_n phi_n "monic" x-coordinate multiplication-by-n elliptic curve              | yes  | `x([n]P)=φ_n/ψ_n²`, `φ_n=xψ_n²−ψ_{n−1}ψ_{n+1}`, `φ_n` monic | MIT 18.783 #5/#6 notes; Stange "Division Polynomials for Arbitrary Isogenies"; Moody alt-model papers |
|  3 | WebSearch (named-after / aliases)| (covered by #1) Nagell–Lutz integrality argument structure                                              | yes  | the subtract-and-apply-rational-root step is done **inline** in every source | The exact poly `Φ_n − c·ψ_n²` is **never named** — it is a throwaway intermediate |
|  4 | ChatGPT MCP                      | standard form + generality + historical evolution of "Φ_n − c·ψ_n² monic"                              | n/a  | MCP unavailable this session (task note)             | Compensated by the extra WebSearch generality passes (#1–#3) + local mathlib-source reading of the `PID` parent and `DivisionPolynomial.Degree` |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial" / "monic"                                | n/a  | no `references/` dir; no `refs/NagellLutz/`          | both directories absent (confirmed) — recorded n/a |
|  6 | nLab                             | division polynomial / elliptic curve x-coordinate isogeny                                              | n/a  | nLab has no division-polynomial / Nagell-Lutz page   | not a category-theoretic concept; nLab silent on this elementary arithmetic-geometry fact |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                                    | not a categorical statement (a degree inequality on `ℤ[X]`) |
|  8 | Stacks Project (alg geom)        | division polynomial / multiplication-by-n / monic numerator                                            | n/a  | Stacks has no elliptic-curve division-polynomial tag | Stacks does not treat elementary elliptic-curve division polynomials at this level |
|  9 | MathOverflow / Math.StackExchange| degree of φ_n ψ_n elliptic curve; why x([n]P) numerator monic                                          | yes  | confirms `deg φ_n = n²`, `φ_n` monic; bound `deg ψ_n² = n²−1` | standard Q&A; nobody names `Φ_n − c·ψ_n²` — it's a step, not a theorem |
| 10 | recent arXiv (last 5 years)      | "Common valuations of division polynomials" (Au-Yeung/Warwick); Stange 2025 isogeny division polys     | yes  | reuse the monicity + degree facts; never isolate this lemma | confirms the facts are folklore-standard and used inline |

### Literature summary (Phase 3)

Concept identified as: the **monic numerator of the multiplication-by-`n` x-coordinate**,
`Φ_n` (a.k.a. `φ_n`), and its degree relationship to `ΨSq_n = ψ_n²`. The specific object of
this lemma — `Φ_n − c·ψ_n²` — is **not a named concept**; it is the polynomial whose integer
roots one feeds to the rational-root theorem in the standard Nagell-Lutz integrality proof.

Sources agree on the standard form: **yes**. Universally: `φ_n` monic, `deg φ_n = n²`,
`deg ψ_n² = n²−1`, `x([n]P) = φ_n/ψ_n²`. (Silverman AEC Ch. VIII Exercises; Sutherland MIT
18.783 Lectures 5–6; Alpöge Harvard note; Anqi Li MIT Nagell-Lutz writeup.)

Most general standard form (of the *underlying facts*): `φ_n` is monic of degree `n²` over
**any** base ring where the leading coefficient is a unit (it is `1`, so over any commutative
ring), and `ψ_n²` has degree `≤ n²−1`. Both facts are **already in mathlib** (Phase 5).

Generality dimensions where the literature varies:
  - base ring: classically `ℚ`/`ℤ` or a field; modern treatments (and mathlib) state the
    division polynomials over an arbitrary commutative ring `R`. The most general is "arbitrary
    `R`" — which is exactly where mathlib's `WeierstrassCurve.Φ`/`ΨSq` live.
  - the constant `c`: literature uses `c = x'` (a specific integer); the lemma abstracts it to
    an arbitrary scalar. This abstraction is free (the degree count never uses what `c` is).

Disagreement with the literature: **none**. The lemma is a faithful, slightly-abstracted
(arbitrary `c`) packaging of a standard degree fact.

**Signal:** the literature search found the *underlying facts* everywhere but found **no
named/isolated lemma** matching `Φ_n − c·ψ_n²` monic. Per the Phase-3 note, "no isolated
literature lemma" for a degree-bookkeeping step points away from YES-add-as-is and toward
NO-composable / NO-mathlib-has-it. Phase 5/6 confirm which.

---

### Generality analysis — `monic_Φ_sub_smul_ΨSq_general` (Phase 4)

Literature-standard form (from Phase 3): the facts "`Φ_n` monic of degree `n²`" and
"`deg(C c · ΨSq_n) ≤ n²−1 < n²`" hold over an arbitrary commutative ring (`Φ_n`'s leading
coefficient is `1`); monicity of the difference then follows for any such ring.

| # | Parameter / hypothesis        | Current Lean form           | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-----------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `W : WeierstrassCurve ℤ`     | curve over `ℤ`              | curve over arbitrary comm. ring   | **yes**             | The degree facts hold over any commutative ring; the project **already has** the general version — `PID.monic_Φ_sub_smul_ΨSq` over a domain, and the degree facts hold even more generally. The ℤ form is a strict specialisation. |
| 2 | `{n : ℤ} (hn : n ≠ 0)`       | `(n : ℤ) ≠ 0`              | `(n : R) ≠ 0` (so `deg ψ_n²` exact) | n/a (this is the right hyp) | The `PID` parent already uses `(n : R) ≠ 0`; the ℤ wrapper re-casts `n ≠ 0` to it. |
| 3 | `(c : ℤ)`                    | arbitrary scalar in `ℤ`    | arbitrary scalar in `R`           | **yes**             | Same ring-generalisation as #1; `c` plays no role beyond `natDegree_C_mul_le`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `R = ℤ` specialisation of a
form that holds over arbitrary commutative rings — and the project *itself already contains*
the more general `PID.monic_Φ_sub_smul_ΨSq` over a domain, of which this lemma is a one-line
re-cast).

Number of weakening opportunities found: 2 (base ring; scalar ring).

Proposed restatement (the general form already exists in-project):
```lean
-- already in projects/.../PIDIntegralMultiple.lean, lines 24–35, over a domain R:
theorem monic_Φ_sub_smul_ΨSq {n : ℤ} (hn : (n : R) ≠ 0) (c : R) :
    (W.Φ n - C c * W.ΨSq n).Monic
-- and the underlying degree facts hold over an arbitrary CommRing.
```
Cost of restatement: **CHEAP** — but moot: the generalised form is already present in the
project, and (Phase 6) it too is a ≤3-call mathlib composition. The narrowness is *not* what
decides this verdict — composability is.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                | Applies? | Proposed reformulation | Downstream |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclasses/instances?                                                                | no       | —                      | already typeclass-driven (`[CommRing]`, `[NoZeroDivisors]`) |
|  2 | sequences/metric → filters/topology?                                                                     | no       | —                      | purely algebraic degree fact; no analysis |
|  3 | construct an object → universal-property class?                                                          | no       | —                      | it is a `Prop` (a `Monic` proof), constructs nothing |
|  4 | set-with-closure → bundled substructure?                                                                 | no       | —                      | no substructure here |
|  5 | vector-space/field-specific → weaken typeclasses?                                                         | yes (weak) | state the degree facts over `CommRing` not `ℤ`/domain | this is the Phase-4b ring-generalisation; mathlib's `Φ`/`ΨSq` API already lives there |
|  6 | 1-categorical → higher-categorical?                                                                       | no       | —                      | n/a |
|  7 | concrete index `ℤ` → arbitrary additive structure?                                                        | no       | `n : ℤ` is correct (division polys are ℤ-indexed) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the plain ring-generalisation already covered by 4b/the
existing `PID` lemma). There is no contemporary mathlib reformulation that turns this
degree-bookkeeping `Prop` into something organisationally richer — it is and should remain a
one-line consequence of the monic-`Φ` and degree lemmas. One-line reason: a `Monic` degree
inequality has no structure to filter-ise, classify, or categorify.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (a `Prop`); it introduces no definitional equalities and no
typeclass-search paths. Skipped.

---

### Mathlib search-status: `monic_Φ_sub_smul_ΨSq_general` (Phase 5)

[A] Lean-Finder       "phi_n minus c psi_n squared monic", "division polynomial monic difference"   no hits — index unavailable this session; covered by [D]/[E] direct source grep
[B] Loogle            `Monic (WeierstrassCurve.Φ _ _ - C _ * WeierstrassCurve.ΨSq _ _)`              no hits — no such combined lemma in mathlib (confirmed by [D] grep over `Mathlib/`)
[C] LeanSearch        "the polynomial Phi_n minus a constant times Psi_n squared is monic"           no hits — index unavailable; covered by [D]
[D] Grep mathlib src  `grep -rn "sub_smul_ΨSq\|monic_Φ"  Mathlib/`                                    **no hits** — the combined lemma is NOT in mathlib
[E] Building blocks   grep `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` + `Mathlib/Algebra/Polynomial/Monic.lean` | **all present** (see below)

Searched for both:
  - the user's current form (`Φ_n − C c · ΨSq_n` monic over ℤ) — not in mathlib;
  - the literature-standard / general form (same over arbitrary `CommRing`) — the *combined*
    lemma is not in mathlib **but every building block is**:

| Mathlib building block                                  | Location                                                         | Gives |
|---------------------------------------------------------|------------------------------------------------------------------|-------|
| `WeierstrassCurve.leadingCoeff_Φ` (`Φ_n` is monic, lc = 1) | `…/DivisionPolynomial/Degree.lean:442`                          | `(W.Φ n).Monic` (via `Monic` ⇔ `leadingCoeff = 1`) |
| `WeierstrassCurve.natDegree_Φ` (`= n.natAbs²`)          | `…/DivisionPolynomial/Degree.lean:435`                          | degree of the minuend |
| `WeierstrassCurve.natDegree_ΨSq` (`= n.natAbs²−1`)      | `…/DivisionPolynomial/Degree.lean:361`                          | degree of the subtrahend factor |
| `Polynomial.natDegree_C_mul_le`                         | `Mathlib/Algebra/Polynomial/Degree/Lemmas.lean:95`              | `deg(C c · ΨSq_n) ≤ deg ΨSq_n` |
| `Polynomial.degree_lt_degree`                           | `Mathlib/Algebra/Polynomial/Degree/Operations.lean:150`        | lifts `natDegree <` to `degree <` |
| `Polynomial.Monic.sub_of_left`                          | `Mathlib/Algebra/Polynomial/Monic.lean:446`                    | monic `−` strictly-lower-degree ⇒ monic |

Concluded: **not in mathlib as a combined lemma, but mathlib has all the building blocks**
(crucially, `Φ_n` is **already proven monic** in mathlib via `leadingCoeff_Φ`, and
`Monic.sub_of_left` is the stock "monic minus lower-degree" lemma). → composition check (Phase 6).

---

### Call sites — `monic_Φ_sub_smul_ΨSq_general` (Phase 6.0)

Grep `projects/ --include="*.lean" --exclude-dir=.lake` for `monic_Φ_sub_smul_ΨSq_general`
(excluding the declaring lines `GeneralIntegralMultiple.lean:56–59`):

Internal use count: **0** (zero callers of the `_general` ℤ-wrapper anywhere in the project).
External-to-file callers: **0**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | the `_general` wrapper is **never called** |

Inline-derivation grep — is the equivalent re-derived elsewhere without using this wrapper?
  - **Yes.** The ℤ/ℚ consumer chain does **not** go through `monic_Φ_sub_smul_ΨSq_general` at
    all. The actual integrality proof `x_integral_of_nsmul_x_integral_general`
    (`GeneralIntegralMultiple.lean:66`) forwards straight to the **`PID` parent**
    `PID.x_isInteger_of_nsmul_x_isInteger`, which internally calls the **`PID`**
    `monic_Φ_sub_smul_ΨSq` (`PIDIntegralMultiple.lean:77`) — never the ℤ wrapper.
  - So the ℤ-specialised `_general` lemma is a **dead wrapper**: it exists for naming symmetry
    with the rest of the `*_general` track, but no consumer uses it (they use the `PID` form
    one level down).

What the K = 0 + bypass pattern tells us (per Phase 6.0.1): "`K = 0` internal uses BUT the same
statement is re-derived/used inline at the `PID` level" ⇒ **NO-composable** — it is a wrapper
that consumers bypass.

### Composition check (Phase 6)

Can `monic_Φ_sub_smul_ΨSq_general` (equivalently its `PID` parent, since the wrapper is `:= PID.…`)
be derived from mathlib in ≤3 chained calls? **Yes — and the in-project `PID` proof already _is_
exactly that composition**, copied here verbatim from `PIDIntegralMultiple.lean:30–35`:

```lean
example {n : ℤ} (hn : (n : R) ≠ 0) (c : R) : (W.Φ n - C c * W.ΨSq n).Monic := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine Monic.sub_of_left (leadingCoeff_Φ _ n) (degree_lt_degree ?_)   -- mathlib lemma 1 (sub_of_left) + 2 (leadingCoeff_Φ)
  calc (C c * W.ΨSq n).natDegree
      _ ≤ (W.ΨSq n).natDegree     := natDegree_C_mul_le _ _              -- mathlib lemma 3
      _ = n.natAbs ^ 2 - 1        := natDegree_ΨSq _ hn                  -- mathlib lemma 4
      _ < n.natAbs ^ 2            := Nat.pred_lt (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn0))
      _ = (W.Φ n).natDegree       := (natDegree_Φ _ n).symm             -- mathlib lemma 5
```

Attempt 1 (the actual proof): `Monic.sub_of_left (leadingCoeff_Φ …) (degree_lt_degree <degree calc>)`.
  - Mathlib decls used: `Monic.sub_of_left`, `leadingCoeff_Φ`, `degree_lt_degree`,
    `natDegree_C_mul_le`, `natDegree_ΨSq`, `natDegree_Φ` (all confirmed present in Phase 5).
  - Result: **succeeds** — this *is* the proof. The "spine" is a **single** mathlib call
    `Monic.sub_of_left h_monic h_degree`; the `h_monic` argument is a **direct mathlib lemma**
    (`leadingCoeff_Φ`, i.e. `Φ` is already monic in mathlib), and `h_degree` is a pure degree
    inequality assembled from three mathlib degree lemmas via a `calc`.
  - Notes: the only non-mathlib glue is the trivial `Nat.pred_lt (pow_ne_zero …)` arithmetic
    (`n²−1 < n²`), which is `omega`/`Nat`-level, not new mathematics.

Conclusion: **COMPOSABLE.** The result — at *every* generality, ℤ or arbitrary `CommRing` — is a
≤3-substantive-call composition over mathlib's existing `DivisionPolynomial.Degree` API plus the
stock `Monic.sub_of_left`. Per Phase 6's heuristic table, "`Foo.bar (Bar.baz …)` (one function
call, with a degree side-goal)" is composable; this is precisely that shape, with the degree
side-goal discharged by a 3-lemma `calc`. There is **no new mathematical content** to capture in
a mathlib lemma: mathlib *already* knows `Φ` is monic and *already* has "monic − lower-degree =
monic."

---

## Verdict: `LutzNagell.LutzNagellTheorem.monic_Φ_sub_smul_ΨSq_general`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the facts (`Φ_n` monic, degree `n²`; `ψ_n²` degree `n²−1`) are
  textbook-folklore and used **inline** in every Nagell-Lutz source; the specific polynomial
  `Φ_n − c·ψ_n²` is **never named or isolated** as a lemma anywhere — it is a throwaway step.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (ℤ specialisation of a
  CommRing-general fact), but the general form **already exists in-project** (`PID.…`) and is
  *itself* composable — so narrowness is not the operative axis.
- Mathlib search (Phase 5): the combined lemma is **not** in mathlib, but **all building blocks
  are**, including `leadingCoeff_Φ` (mathlib already proves `Φ` monic) and `Monic.sub_of_left`.
- Composition check (Phase 6): **COMPOSABLE** — the proof *is* a ≤3-call mathlib composition
  (`Monic.sub_of_left (leadingCoeff_Φ …) (degree_lt_degree <3-lemma calc>)`), and the ℤ wrapper
  has **0 call sites** (consumers bypass it via the `PID` form).

**Rationale.**
The decisive facts are two. First, **mathlib already proves the only non-trivial ingredient**:
`WeierstrassCurve.leadingCoeff_Φ` (`DivisionPolynomial/Degree.lean:442`) states `(W.Φ n).leadingCoeff = 1`,
i.e. `Φ_n` is monic. Given that, "`Φ_n` minus a strictly-lower-degree polynomial is monic" is the
**stock library lemma** `Polynomial.Monic.sub_of_left`, and the degree inequality `deg(C c · ΨSq_n)
≤ n²−1 < n² = deg Φ_n` is three more existing mathlib lemmas (`natDegree_C_mul_le`, `natDegree_ΨSq`,
`natDegree_Φ`) glued by `omega`-level arithmetic. So at *every* generality the statement is a ≤3-call
composition with no new mathematical content — the textbook signature of `NO-composable-from-mathlib`.
Second, the call-site evidence corroborates this from the other direction: the ℤ-specialised
`_general` wrapper has **zero callers**; the real integrality proof reaches the monicity fact through
the `PID` parent one level down, so even within the project the wrapper is redundant.

This revises the earlier draft's `YES-but-generalise-first`. That draft was right that the ℤ form is
narrower than the UFD form, but it stopped there and did not push the composition check through the
*general* form. When you do, the general `PID.monic_Φ_sub_smul_ΨSq` is **also** a stock composition —
so "generalise then upstream" would be upstreaming a lemma that mathlib's own `Monic.sub_of_left` +
`leadingCoeff_Φ` already make a one-liner. The mathlibable bar prefers *using* `Monic.sub_of_left` at
the point of need over shipping a bespoke `Φ`-flavoured restatement of it. There is no mathlib gap
here: the gap the earlier draft imagined ("mathlib lacks `Φ_n − c·ψ_n²` monic") is filled the moment
you notice `Φ_n` is already monic in mathlib.

(If a future reviewer disagrees and wants the named convenience lemma kept for readability of the
Nagell-Lutz development, that is a project-style call, not a mathlib-inclusion call — mathlib would
inline it. Recorded here so the dissent is visible, but it does not change the bucket.)

**WHY not (refactor-actionable).**
Mathlib has the building blocks; the user's form (and its `PID` generalisation) is a 1-call
composition `Monic.sub_of_left h_monic h_deg` where `h_monic = leadingCoeff_Φ …` is itself a single
mathlib lemma and `h_deg` is a 3-lemma degree `calc`. No new lemma is warranted in mathlib.

Mathlib building blocks (qualified, with paths):
  - `Polynomial.Monic.sub_of_left` — `Mathlib/Algebra/Polynomial/Monic.lean:446`
  - `WeierstrassCurve.leadingCoeff_Φ` — `…/EllipticCurve/DivisionPolynomial/Degree.lean:442`
  - `WeierstrassCurve.natDegree_Φ` — `…/EllipticCurve/DivisionPolynomial/Degree.lean:435`
  - `WeierstrassCurve.natDegree_ΨSq` — `…/EllipticCurve/DivisionPolynomial/Degree.lean:361`
  - `Polynomial.natDegree_C_mul_le` — `Mathlib/Algebra/Polynomial/Degree/Lemmas.lean:95`
  - `Polynomial.degree_lt_degree` — `Mathlib/Algebra/Polynomial/Degree/Operations.lean:150`

Composition sketch (≤3 spine lines; the proof already in `PIDIntegralMultiple.lean:30–35`):
```lean
refine Monic.sub_of_left (leadingCoeff_Φ _ n) (degree_lt_degree ?_)
calc (C c * W.ΨSq n).natDegree
    _ ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
    _ = n.natAbs ^ 2 - 1    := natDegree_ΨSq _ hn
    _ < n.natAbs ^ 2        := Nat.pred_lt (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn0))
    _ = (W.Φ n).natDegree   := (natDegree_Φ _ n).symm
```

Call sites in our project (from Phase 6.0): **K = 0** for the `_general` wrapper.

Refactor plan:
  1. **The `_general` ℤ wrapper (this declaration):** it has **zero call sites** — delete it
     outright. Nothing downstream references `monic_Φ_sub_smul_ΨSq_general` (the ℤ/ℚ integrality
     chain goes through `PID.x_isInteger_of_nsmul_x_isInteger` → `PID.monic_Φ_sub_smul_ΨSq`, never
     this wrapper). Deleting it is a no-op for the build.
  2. **The `PID` parent `PID.monic_Φ_sub_smul_ΨSq` (its real home):** it has exactly **one** call
     site, `PIDIntegralMultiple.lean:77` inside `x_isInteger_of_nsmul_x_isInteger`. Inline the
     6-line composition above directly there (it is already written, two definitions up in the same
     file), then delete the standalone `PID.monic_Φ_sub_smul_ΨSq`. This removes the bespoke lemma in
     favour of `Monic.sub_of_left` at the point of use. (Optional: keep `PID.monic_Φ_sub_smul_ΨSq` as
     a private helper if the inlined `calc` hurts readability of the rational-root step — a local
     style choice, not a mathlib contribution.)

Net: nothing goes to mathlib; the monicity step is realised by `Monic.sub_of_left` + the existing
`DivisionPolynomial.Degree` lemmas at the single site that needs it.

**Next action:** delete `monic_Φ_sub_smul_ΨSq_general` (0 call sites). At the lone `PID` call site
(`PIDIntegralMultiple.lean:77`), inline the `Monic.sub_of_left (leadingCoeff_Φ …) (degree_lt_degree …)`
composition shown above; optionally retain the `PID` lemma as a `private` local helper. No mathlib PR.
