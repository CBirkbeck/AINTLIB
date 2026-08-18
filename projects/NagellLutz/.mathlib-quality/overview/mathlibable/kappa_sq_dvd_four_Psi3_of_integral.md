# /mathlibable report — `LutzNagell.PID.kappa_sq_dvd_four_Psi3_of_integral`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task brief; decl read directly from source)
- decl `LutzNagell.PID.kappa_sq_dvd_four_Psi3_of_integral`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:242`
- qualified name VERIFIED:  `namespace LutzNagell` (L35) → `namespace PID` (L36) … `end PID` (L475); decl at L242 → `LutzNagell.PID.kappa_sq_dvd_four_Psi3_of_integral` ✓
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The Lutz–Nagell theorem over PIDs and number fields (integrality of torsion coords; κ₀ = 0 or κ₀² ∣ 4Δ).

---

### Statement (Phase 1)

`kappa_sq_dvd_four_Psi3_of_integral` is a theorem stating: if the third
division-polynomial value `Ψ₃(x₀) := 3x₀⁴ + b₂x₀³ + 3b₄x₀² + 3b₆x₀ + b₈`
factors as `Ψ₃(x₀) = κ₀² · c` for some ring element `c`, then `κ₀²` divides
`4 · Ψ₃(x₀)`.

Mathematically this is the trivial chain: the hypothesis exhibits `c` as a
divisibility witness, so `κ₀² ∣ Ψ₃(x₀)`; multiplying the dividend on the left
by `4` preserves divisibility, giving `κ₀² ∣ 4·Ψ₃(x₀)`. The explicit quartic
`Ψ₃(x₀)` plays **no** role — it is an opaque element of the commutative ring
`R`; the lemma is pure divisibility algebra.

Variables / typeclasses (Lean side):
- `R : Type*` with `[CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`
  — but the decl carries `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`,
  so only `CommRing R` is actually used.
- `W : WeierstrassCurve R` — supplies `b₂, b₄, b₆, b₈` only as ring constants
  inside the `Ψ₃` expression; never used as a curve.
- `x₀ κ₀ c : R` — ring elements.

Hypotheses (Lean side):
- `hPsi3 : 3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈ = κ₀^2 * c`
  — the factorisation `Ψ₃(x₀) = κ₀² · c`.

Conclusion (math): `κ₀² ∣ 4·Ψ₃(x₀)`.

Conclusion (Lean): `κ₀ ^ 2 ∣ 4 * (3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈)`.

Proof body (one line):
```lean
dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4
```
`⟨c, hPsi3⟩ : κ₀^2 ∣ Ψ₃(x₀)` (anonymous `Dvd` constructor; witness `c`), then
`dvd_mul_of_dvd_right · 4` promotes it to `κ₀^2 ∣ 4 * Ψ₃(x₀)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper lemma — a single divisibility step feeding the surrounding
`lutz_nagell_pid_discriminant`. Not a `def`/`structure`/`class`, not a named
theorem, not a `## Main results` entry (the module lists the *discriminant*
theorem, not this).

(Literature width was EXHAUSTIVE regardless; BIG/SMALL is narrative only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner-def check is n/a.
(Note for the record: the *proof term* is a single mathlib call — this is the
decisive composability signal, captured in Phase 6.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "divisibility a divides b implies a divides c times b commutative ring standard lemma"                  | yes  | `a ∣ b ⇒ a ∣ c·b` (b = a·q ⇒ c·b = a·(c·q)) | PlanetMath / Wikipedia "Divisibility (ring theory)"; web result states it verbatim as "a standard lemma in ring theory" |
|  2 | WebSearch (general form)         | (same query, general framing) — divisibility in commutative monoid/ring                                | yes  | holds in any commutative monoid  | Property of the multiplicative monoid; no ring/domain/PID structure needed |
|  3 | WebSearch (named-after / aliases / ambient theorem) | "division polynomial psi_3 divides discriminant Nagell-Lutz elliptic curve integrality"  | yes  | `y² ∣ Δ`; `Ψ₃` 3-torsion polynomial | Confirms the *surrounding* Nagell–Lutz machinery is standard (Silverman, Harvard "Nagell–Lutz quickly", MIT 18.783) — but this is the `lutz_nagell_pid_discriminant` result, NOT this trivial promotion lemma |
|  4 | ChatGPT MCP                      | n/a                                                                                                    | n/a  | —                                | MCP reported down in task brief; substituted by Web result #1, which already states the standard form + its one-line proof explicitly |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                    | n/a  | —                                | Directory absent (no `projects/NagellLutz/.mathlib-quality/references/`; no `refs/`) — recorded as n/a |
|  6 | nLab                             | "divisibility" / "divides"                                                                              | n/a  | —                                | Not a categorical concept worth an nLab lookup; the fact `a∣b ⇒ a∣cb` is the defining property of a `∣`-preorder on a monoid — covered by #1/#2 |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                | Not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                                | Trivial monoid divisibility; not a Stacks-grade algebraic-geometry statement |
|  9 | MathOverflow / MSE               | "a divides b implies a divides cb"                                                                      | yes  | textbook one-liner               | Subsumed by #1; treated as folklore everywhere, never stated as a citable named result |
| 10 | recent arXiv (last 5 years)      | (Nagell–Lutz / division-polynomial divisibility, via #3)                                                | yes  | arXiv:1801.02664, 1303.5002 on division-polynomial coefficients | Concern division-polynomial *arithmetic*, not the `a∣b ⇒ a∣4b` step; no analog to this lemma |

The protocol passes: WebSearch ran 3 distinct queries at different generality
levels (specific `a∣b ⇒ a∣cb`, general monoid form, ambient Nagell–Lutz
framing); ChatGPT MCP recorded n/a with reason (down) and its role covered by
Web result #1; local refs checked (absent); nLab/nCatLab/Stacks/MO/arXiv each
checked or n/a'd with reason.

### Literature summary (Phase 3)

Concept identified as: the elementary divisibility property **`a ∣ b ⇒ a ∣ c·b`**
in a commutative monoid (here `R = CommRing`), specialised at `a = κ₀²`,
`c = 4`, `b = Ψ₃(x₀)`. The `Ψ₃` dressing is an opaque ring element.
Sources agree on the standard form: yes — universally folklore; Web result #1
gives both the statement and its two-line proof and calls it "a standard lemma
in ring theory".
Most general standard form: in any (commutative) monoid, `a ∣ b → a ∣ c * b`.
Generality dimensions where the literature varies:
  - algebraic structure: stated for ℤ in number-theory texts, but holds in any
    monoid; the most general is a `Monoid`/`CommMonoidWithZero`.
Disagreement with the literature: none. The Lean form is a *specialisation*
(monoid lemma applied to one curve quantity), not a competing statement.

---

### Generality analysis — `kappa_sq_dvd_four_Psi3_of_integral`

Literature-standard form (from Phase 3): `a ∣ b → a ∣ c * b` in a commutative
monoid — already in mathlib as `dvd_mul_of_dvd_right`.

| # | Parameter / hypothesis        | Current Lean form                        | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|------------------------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` (+ omitted Domain/PID/CharZero) | commutative ring `R`           | commutative monoid                | yes                 | The proof uses only `Dvd` + left-multiplication; `Monoid`/`CommMonoidWithZero` suffices. The curve `W` and constants `b₂…b₈` are inert. |
| 2 | `hPsi3 : Ψ₃(x₀) = κ₀² · c` (specific quartic) | equation defining one curve value | `b = a · c` (abstract)         | yes                 | `Ψ₃(x₀)` is just `b`; `κ₀²` is just `a`; `4` is just `c`. None of the elliptic-curve content is load-bearing. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is a *specialisation
applied to elliptic-curve data*, not a more-general-able statement of its own).
Number of weakening opportunities found: 2 — but weakening doesn't yield a new
mathlib candidate; it yields *exactly* `dvd_mul_of_dvd_right`, which mathlib
already has. So this is not "generalise then add"; it is "the general form is
already in mathlib, and the present decl is a saturated application of it".
Proposed restatement: none worth shipping — the maximally general form IS
`dvd_mul_of_dvd_right`.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass/instance?                                    | no       | — | No bundled-hypothesis preamble to dissolve. |
|  2 | sequences/metric → filters/topology?                                     | no       | — | Purely algebraic; no limits. |
|  3 | construct an object → universal-property class?                          | no       | — | No construction. |
|  4 | set-with-closure → bundled substructure?                                 | no       | — | No substructure. |
|  5 | vector-space/field-specific → weaken typeclasses?                         | yes (degenerately) | drop `CommRing`→`Monoid` | But the weakened form is literally `dvd_mul_of_dvd_right`; not a *new* idiom. |
|  6 | 1-categorical → higher-categorical?                                       | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure?                  | no       | — | No index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (the only "modernisation" is to use the existing
mathlib lemma directly — which is the NO-composable verdict, not a generalise-
first restatement).
One-line reason: there is no contemporary reformulation that improves mathlib
organisation; the contemporary form already exists as `dvd_mul_of_dvd_right`.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `theorem` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `kappa_sq_dvd_four_Psi3_of_integral`

[A] Lean-Finder       "a divides 4 times b from a divides b"        no direct hit for the dressed form; underlying lemma is well-known
[B] Loogle            `?a ∣ ?b → ?a ∣ ?c * ?b`                       HIT → `dvd_mul_of_dvd_right` (and alias `Dvd.dvd.mul_left`)
[C] LeanSearch        "if a divides b then a divides c times b"      HIT → `dvd_mul_of_dvd_right`
[D] Grep mathlib src  `dvd_mul_of_dvd_right`                          HIT → `.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean:172`:
                                                                       `theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b`
                                                                       (alias `Dvd.dvd.mul_left`, L175)
[E] Name pattern      grep `kappa_sq_dvd_four_Psi3` over mathlib + forked DivisionPolynomial/EDS files   no hit — not in mathlib, not in the project's forked `DivisionPolynomial*.lean` / `EllipticDivisibilitySequence.lean` (those hold polynomial identities, not this divisibility step)

Searched for both:
  - the user's dressed form (`κ₀² ∣ 4·Ψ₃(x₀)` given `Ψ₃(x₀)=κ₀²·c`) — not present verbatim;
  - the literature-standard form (`a ∣ b → a ∣ c·b`) — present as `dvd_mul_of_dvd_right`.

Concluded: found the **building block** in mathlib — `dvd_mul_of_dvd_right`
(`Mathlib/Algebra/Divisibility/Basic.lean:172`). The user's form is a single
application of it to an anonymous-constructor divisibility witness. The exact
dressed statement is not (and should not be) in mathlib.

---

### Call sites — `kappa_sq_dvd_four_Psi3_of_integral`

Internal use count: **0** (whole-repo grep over `*.lean`, excluding the
declaring line, returns nothing — the lemma is used nowhere, not even inside
`PIDMain.lean`).
External-to-file callers: 0 files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | (no call sites anywhere in the monorepo) |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - In the sibling theorem `lutz_nagell_pid_discriminant` (same file, L227),
    the analogous hypothesis is supplied by the caller as `hdvd_Psi3` directly
    (a `_ ∣ 4 * (…)` premise), and the helper `kappa_sq_dvd_four_delta`
    (L199) is the one used — `kappa_sq_dvd_four_Psi3_of_integral` is **bypassed**.
    So the project derives the `_ ∣ 4·Ψ₃` fact at the point of need rather than
    through this wrapper.

Signal: K = 0 internal uses, and the surrounding development supplies the same
`4·Ψ₃` divisibility inline/as a premise instead of calling this lemma →
strong NO-composable signal (it is a wrapper that even its own project bypasses).

---

### Composition check (Phase 6)

Can `kappa_sq_dvd_four_Psi3_of_integral` be derived from mathlib in ≤3 chained calls?

Attempt 1: `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4`
  - Mathlib decls used: `dvd_mul_of_dvd_right` (+ the anonymous `Dvd`
    constructor `⟨c, hPsi3⟩`, which is `Dvd.intro`).
  - Result: **succeeds** — this is *verbatim the existing proof body*. One
    mathlib call applied to a one-step witness.
  - Notes: `⟨c, hPsi3⟩ : κ₀^2 ∣ Ψ₃(x₀)` because `hPsi3 : Ψ₃(x₀) = κ₀^2 * c`
    is exactly the `∃ d, Ψ₃(x₀) = κ₀^2 * d` payload; `dvd_mul_of_dvd_right _ 4`
    then yields `κ₀^2 ∣ 4 * Ψ₃(x₀)`.

Conclusion: **COMPOSABLE** — a single mathlib call (well under the ≤3 bound).
Per the Phase-6 heuristic table this is the "`Foo.bar (Bar.baz hx)` — one
function call → composable: yes" row.

---

## Verdict: `LutzNagell.PID.kappa_sq_dvd_four_Psi3_of_integral`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the content is the folklore monoid lemma
  `a ∣ b ⇒ a ∣ c·b`; Web result #1 states it and its proof verbatim as "a
  standard lemma in ring theory". The `Ψ₃`/elliptic-curve dressing is inert.
- Generality analysis (Phase 4): STRICTLY NARROWER — a saturated application
  of the general lemma; the maximally general form already *is* a mathlib decl.
- Mathlib search (Phase 5): building block found — `dvd_mul_of_dvd_right`
  (`Mathlib/Algebra/Divisibility/Basic.lean:172`, alias `Dvd.dvd.mul_left`).
- Composition check (Phase 6): COMPOSABLE in a single call — the proof body
  already *is* that composition.

**Rationale:**

This theorem is a thin wrapper around mathlib's `dvd_mul_of_dvd_right`. Strip
the elliptic-curve vocabulary and the statement is: given `b = a·c`, show
`a ∣ 4·b`. The hypothesis is itself a divisibility witness (`⟨c, hPsi3⟩ :
a ∣ b`), and one application of `dvd_mul_of_dvd_right` finishes it — which is
exactly the existing one-line proof term. There is no elliptic-curve content
in the proof: `Ψ₃(x₀)`, `W`, and the constants `b₂…b₈` are opaque ring
elements, and the decl even `omit`s every typeclass beyond `CommRing`. Nothing
here is novel to mathlib; the general lemma has lived in
`Mathlib/Algebra/Divisibility/Basic.lean` for years.

The call-site evidence makes the verdict decisive: the lemma has **zero**
consumers anywhere in the monorepo, and the one place that needs an
`κ₀² ∣ 4·Ψ₃` fact (`lutz_nagell_pid_discriminant`) takes it as a premise and
routes through `kappa_sq_dvd_four_delta` instead — bypassing this wrapper
entirely. So it is neither a load-bearing API surface nor a mathlib gap; it is
a one-call composition that should be inlined at the (single, hypothetical)
point of use rather than carried as a named lemma, in mathlib or in the
project.

**WHY not (refactor-actionable):**
Mathlib already has the building block `dvd_mul_of_dvd_right`. The user's form
is a *zero-extra-step* composition: feed the hypothesis as a `Dvd` witness and
apply the lemma. No new lemma is warranted — neither upstream (mathlib would
reject a `Ψ₃`-specific restatement of a generic monoid fact) nor in the project
(the lemma is unused).

Mathlib building blocks:
  - `dvd_mul_of_dvd_right` — `.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean:172`
    (alias `Dvd.dvd.mul_left`, L175)
  - the anonymous `Dvd` constructor / `Dvd.intro` — same file, L50

Composition sketch (≤3 lines — this is literally the current body):
```lean
-- given hPsi3 : Ψ₃(x₀) = κ₀^2 * c
example : κ₀ ^ 2 ∣ 4 * Ψ₃(x₀) := dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4
```

Call sites in our project (from Phase 6.0): **K = 0**.
Refactor plan: delete `kappa_sq_dvd_four_Psi3_of_integral` from
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean` (L241–247).
Because K = 0 there are no call sites to update. If a future caller needs the
`κ₀² ∣ 4·Ψ₃` step, inline `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4` at that point
(or, when the divisibility is already in hand as `h : κ₀² ∣ Ψ₃(x₀)`, use
`h.mul_left 4`). Do **not** upstream to mathlib.

Next action: delete `kappa_sq_dvd_four_Psi3_of_integral` from the project;
inline `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4` if/where the step is ever needed.

---

## Next step

Delete `kappa_sq_dvd_four_Psi3_of_integral` from the project; inline the
one-call composition `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4` at any future point of
use. Do not open a mathlib PR — the building block `dvd_mul_of_dvd_right`
already exists and a `Ψ₃`-specific restatement is not mathlib-appropriate.
