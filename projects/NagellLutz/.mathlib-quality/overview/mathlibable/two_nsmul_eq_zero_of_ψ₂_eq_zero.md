# /mathlibable report — `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`

_Assessment date: 2026-06-22. Mathlib pin read directly from
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib`. Local Lean build is
stale per the task brief; presence/absence in mathlib is established by **direct grep + read of the
pinned checkout** (authoritative for this pin) plus WebSearch, not the live loogle/leansearch
indices (the loogle/leansearch MCP tools are not available in this environment — only WebSearch +
ChatGPT-math MCP surfaced; ChatGPT-math was not needed)._

_**Scope note.** This `/mathlibable` invocation targets the **PID-track** declaration
`LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero` (`PIDPrimeOrder.lean:138`). A prior run wrote, to
this same path, the assessment of the **General-track** twin
`LutzNagell.LutzNagellTheorem.two_nsmul_eq_zero_of_ψ₂_eq_zero` (`GeneralPrimeOrder.lean:66`). The two
are the **same lemma modulo base ring** — the project's own duplication analysis
(`.mathlib-quality/overview/analysis/05-duplications.md:63`) records them as
"`GeneralPrimeOrder.two_nsmul_eq_zero_of_ψ₂_eq_zero` ↔ `PIDPrimeOrder.two_nsmul_eq_zero_of_ψ₂_eq_zero`
| Yes (same name!) | Yes (`add_of_Y_eq`) | **UNIFY** (same name, same proof; PID `omit`s
domain/UFD/fraction)". This report now reflects the **PID** declaration the task names; the verdict
is identical, and is consistent with the prior General-track write-up._

---

### Baseline (Phase 0)

- lake build:               ⚠ not re-run (local build stale per task brief); reasoned from source +
  direct read of the pinned mathlib checkout. Full statement + proof read from
  `PIDPrimeOrder.lean:136–146`.
- decl `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:138`
                            (the `theorem` keyword is line 138; the `:= by` body the prompt points at
                            runs lines 141–146).
- qualified name:           ✓ **VERIFIED** `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`
                            — `namespace LutzNagell` (line 24) → `namespace PID` (line 25); base name
                            `two_nsmul_eq_zero_of_ψ₂_eq_zero` (line 138); `end PID`/`end LutzNagell`
                            (lines 213–214). **Matches the task's parsed guess exactly.**
- kind:                     theorem
- has sorry:                no (complete 5-line proof, lines 142–146).
- module docstring summary: "Prime-order torsion integrality for Weierstrass curves over UFDs" —
                            generalisation of `GeneralPrimeOrder.lean` from `ℤ/ℚ` to a UFD `R` with
                            fraction field `K`.
- decl docstring:           "If `ψ₂(x,y) = 0`, then `2 • P = 0` in the affine group."
- **DUPLICATE (the project's General*/PID* fork):** the same-named General-track twin
                            `LutzNagell.LutzNagellTheorem.two_nsmul_eq_zero_of_ψ₂_eq_zero` lives at
                            `GeneralPrimeOrder.lean:66` (over fixed `ℚ`). **This PID version is the
                            *more general* of the two** (arbitrary fraction field `K`, not `ℚ`) and
                            additionally `omit`s `[IsDomain R] [UniqueFactorizationMonoid R]
                            [IsFractionRing R K]` (line 136) — i.e. it needs essentially nothing about
                            `R` beyond `CommRing` for *this* statement. Same verdict applies to both.

---

### Statement (Phase 1)

`LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero` states:

> Let `R` be a commutative ring with `K` a field carrying an `R`-algebra / fraction-field structure
> (the surrounding section's `variable`s; the heavier `[IsDomain R] [UniqueFactorizationMonoid R]
> [IsFractionRing R K]` are explicitly `omit`-ted for this lemma). Let `W : WeierstrassCurve R`,
> `curveK R K W` its base change to `K`, and `(x, y)` a nonsingular affine point of `curveK R K W`.
> If the 2-division polynomial vanishes at the point, `(curveK R K W).ψ₂.evalEval x y = 0`
> (equivalently `2y + a₁x + a₃ = 0`), then `2 • P = 0` for `P = (x, y)` in the affine Mordell–Weil
> group — i.e. `P` has order dividing 2.

This is the **"converse" / easy direction** of the classical 2-torsion characterisation: a
non-identity point on a Weierstrass curve has order dividing 2 iff it is fixed by negation, iff
`y = negY(x,y) = -y - a₁x - a₃`, iff `ψ₂(x,y) = 2y + a₁x + a₃ = 0`.

Variables / typeclasses (Lean side, from the section header `PIDPrimeOrder.lean:29–31`, with
`PIDPrimeOrder.lean:136` `omit`-ting the domain/UFD/fraction-ring assumptions for this lemma):
- `R : Type*` `[CommRing R]` — base ring (domain/UFD/fraction-ring hyps omitted here).
- `K : Type*` `[Field K] [DecidableEq K] [Algebra R K]` — the field of coordinates.
- `W : WeierstrassCurve R`; `curveK R K W` = the base change `W.map (algebraMap R K)`.

Hypotheses (Lean side):
- `hns : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` nonsingular (gives the equation + `≠ O`).
- `hψ : (curveK R K W).ψ₂.evalEval x y = 0` — the 2-division polynomial vanishes at `(x,y)`.

Conclusion (math): `P = (x,y)` is 2-torsion (order divides 2).
Conclusion (Lean): `(2 : ℕ) • (Affine.Point.some _ _ hns) = 0`.

Proof body (verbatim, `PIDPrimeOrder.lean:142–146`):
```lean
  rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at hψ
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := hns) (h₂ := hns) rfl
  simp only [WeierstrassCurve.Affine.negY, curveK]
  linear_combination hψ
```
(The General twin's body is the same composition, written instead as a forward `have hy : y = negY …`
+ `exact add_of_Y_eq rfl hy`. Both end in mathlib's `Affine.Point.add_of_Y_eq`.)

---

### Size classification (Phase 2a)

**Verdict: SMALL.**
Reason: a helper lemma — one direction (the easy converse) of a standard characterisation. Not listed
under any `## Main results`; the file header marks it as the "ψ₂ = 0 implies 2•P = 0" section. It is a
supporting step toward `integrality_of_order_four_squarefree` and ultimately the project's
Nagell–Lutz theorem. The **named** results are the integrality theorems; this is plumbing.

(Literature width is run EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line check **n/a**. (Body is a 5-line tactic
proof anyway: `ψ₂`/`polynomialY` rewrite, `two_nsmul`, `add_of_Y_eq`, a `negY`/`curveK` `simp`, and a
one-line `linear_combination`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell-Lutz, elliptic curve point order 2, 2-division polynomial ψ₂ vanishes iff 2-torsion              | yes  | order-2 points have `y = 0` (short form); div. polys vanish exactly at torsion | Wikipedia (Nagell–Lutz): "either `y = 0`, in which case `P` has order two"; "division polynomials have roots exactly at the `n`-torsion points". Confirms `ψ₂(P)=0 ⟺ P∈E[2]`. |
|  2 | WebSearch (general form)         | Weierstrass curve 2-torsion `y = -y - a₁x - a₃`, negation map / hyperelliptic involution fixed points    | yes  | involution `(x,y) ↦ (x, -y-a₁x-a₃)`; fixed pts = 2-torsion      | the general-Weierstrass negation map; `2P=O ⟺ P=-P ⟺ y = negY(x,y)` (Silverman AEC III.2.3 + 2-torsion). |
|  3 | WebSearch (general principle)    | division polynomial `ψ_n(P)=0 ⟺ nP=O`, `ψ₂ = 2y` initial value                                          | yes  | `P ∈ E[n] ⟺ ψ_n(P) = 0`; `ψ₂ = 2y` (short form)                  | Wikipedia "Division polynomials"; Schoof's algorithm; classical. The long form carries the extra `a₁x+a₃`. |
|  4 | ChatGPT-math MCP                 | (available this run, but not invoked — the standard form + composition are unambiguous from #1–3 + src)  | n/a  | —                                                                | The 2-torsion ⟺ `ψ₂=0` fact is textbook-folklore and the composition is verifiable directly from the pinned mathlib source; a second opinion would add nothing. |
|  5 | Local references                 | `find projects/NagellLutz/.mathlib-quality/references/`; `refs/NagellLutz/`                              | n/a  | (directories absent)                                            | no `references/` dir under `.mathlib-quality/` (only `overview/`); no `refs/` store present. n/a (matches sibling reports). |
|  6 | nLab                             | elliptic curve 2-torsion / division polynomial ψ₂                                                       | no   | —                                                                | nLab treats elliptic curves abstractly, not this elementary coordinate computation. Too elementary/computational for nLab. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                                                | not a categorical statement (a concrete computation on points). |
|  8 | Stacks Project (if alg geom)     | division polynomial / explicit Weierstrass 2-torsion                                                    | n/a  | —                                                                | Stacks does scheme-theoretic AG, not explicit Weierstrass division polynomials / torsion. n/a. |
|  9 | MathOverflow / Math.SE           | 2-torsion ⟺ `y = negY` characterisation, why order-2 means `2y + a₁x + a₃ = 0`                          | yes  | folklore: `2P=O ⟺ P=-P ⟺ y=-y-a₁x-a₃`                            | surfaced inside the WebSearch hits (#1,#2); standard textbook fact. |
| 10 | recent arXiv (last 5 years)      | division polynomials, torsion of elliptic curves; Nagell-Lutz generalisations                          | yes  | same classical `ψ_n(P)=0 ⟺ nP=O`; arXiv:2509.07524 (Nagell–Lutz over imag. quad. fields) | nothing newer/more general for the **ψ₂** direction; the `E[2] ⟺ ψ₂=0` fact is classical and unchanged. **No Lean/mathlib `ψ₂`-phrased lemma anywhere.** |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (the specific
2-torsion `y=0`/`ψ₂` form, the general-Weierstrass negation-map form, the general `ψ_n(P)=0 ⟺ nP=O`
principle); standard form, generality, and the converse direction were probed; local refs checked
(absent → n/a); nLab/Stacks/nCatLab checked and reasoned n/a; MathOverflow-class expositions + recent
arXiv both checked and hit. ChatGPT-math MCP available but not needed (the fact is textbook and the
composition is source-verifiable).

### Literature summary (Phase 3)

Concept identified as: **the 2-torsion characterisation via the negation map / 2-division
polynomial** — for a general Weierstrass curve, a non-identity point `P=(x,y)` has order dividing 2
iff `P = -P`, iff `y = negY(x,y) = -y - a₁x - a₃`, iff `ψ₂(x,y) = 2y + a₁x + a₃ = 0`. This lemma
proves the **easy converse** `ψ₂(P)=0 ⟹ 2P=0`.

Sources agree on the standard form: **yes.** Silverman *AEC* (negation map III.2.3; 2-torsion);
Wikipedia "Division polynomials" (`ψ_n(P)=0 ⟺ P∈E[n]`, with `ψ₂=2y` for the short form) and the
Nagell–Lutz article ("`y=0` ⟺ order two"). The only cosmetic variance: the **short** Weierstrass form
has `ψ₂=2y` (condition `y=0`); the **general/long** form carries the extra `a₁x+a₃` (condition
`2y+a₁x+a₃=0`). This lemma uses the general form — the maximally general AG statement.

Most general standard form: a general Weierstrass equation over **any** base where the point group is
defined (any field; indeed any commutative ring for the polynomial identity). The single implication
proved here (`ψ₂(P)=0 ⟹ 2P=0`) holds with no characteristic restriction.

Generality dimensions where the literature varies:
  - **base**: short form (`y²=x³+Ax+B`, condition `y=0`) ↔ general Weierstrass (`a₁..a₆`, condition
    `2y+a₁x+a₃=0`). This lemma uses the **general** form (good). Base **ring**: fixed `ℚ` (General
    twin) ↔ arbitrary fraction field `K` of a (here merely `CommRing`) `R` — **this PID lemma is the
    `K`-general one**; mathlib's underlying `add_of_Y_eq` is over an arbitrary field `F`.
  - **direction**: full iff (`2P=0 ⟺ ψ₂(P)=0`) ↔ the single implication proved here (only `⟸`).

Disagreement with the literature: **none.** A faithful Lean rendering of the standard converse
direction at general-Weierstrass generality.

---

### Generality analysis — `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`

Literature-standard form (Phase 3): for a general Weierstrass curve over any field `F`,
`2 • P = 0 ⟺ ψ₂(P) = 0` (equivalently `y = negY(x,y)`).

| # | Parameter / hypothesis                        | Current Lean form                              | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------|------------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | base: `W : WeierstrassCurve R`, point over `curveK R K W` | curve over `R`, base-changed to a fraction field `K` (domain/UFD/fraction hyps **omitted** for this lemma) | curve over an arbitrary field `F`        | **yes** — slightly | The proof uses *nothing* about `R`/`K` beyond the field structure of `K` already present in `curveK`. Mathlib's `add_of_Y_eq`/`evalEval_polynomialY`/`negY` are stated over a generic curve. This PID version is already **more general than the `ℚ`-fixed General twin** (any `K`); the only remaining slack is `curveK R K W → ` a bare `W' : WeierstrassCurve F` — but that target **is mathlib's `add_of_Y_eq`** (see Phase 5/6), so generalising buys nothing new. |
| 2 | `hns : Nonsingular x y`                        | nonsingular affine point                       | nonsingular affine point                 | NO                  | `Point.some` requires it; genuinely needed and minimal. |
| 3 | `hψ : ψ₂.evalEval x y = 0`                     | `ψ₂` vanishes                                  | `ψ₂` vanishes (or `y = negY x y`)        | — (phrasing)        | The mathlib-native phrasing is `y = negY x y`; the `ψ₂` wrapper is a cosmetic restatement that `evalEval_polynomialY` strips in one rewrite (Phase 6). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (tied to `curveK R K W` rather than a bare
`WeierstrassCurve F` over an arbitrary field) — though already broader than the `ℚ`-fixed General twin.
Number of weakening opportunities found: **1** (drop `curveK R K W` to a generic `W' : WeierstrassCurve
F`).
However — decisively — the *generalised* statement over an arbitrary field is **already essentially
in mathlib once the ψ₂ wrapper is stripped**: it is `add_self_of_Y_eq` (or `add_of_Y_eq rfl`) composed
with `evalEval_polynomialY` and `two_nsmul`. So the narrowness does **not** push this to
`YES-but-generalise-first`; it reinforces that the lemma is a thin project-specific wrapper. See
Phase 5/6.
Cost of restatement: CHEAP (mechanical) — but moot, because the right move is to inline/demote, not to
generalise-and-ship (the generalised target *is* an existing mathlib lemma).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let W be a curve over `R`/`K`" → typeclass/generic field?                                 | yes      | state over `{F} [Field F] (W : WeierstrassCurve F)` | but that is **exactly `add_of_Y_eq`** already — the modern form *is* the existing mathlib lemma, not a new contribution |
|  2 | sequences/metric → filters/topology?                                                       | no       | n/a — discrete algebraic statement, no limits |  |
|  3 | construct an object → universal property?                                                  | no       | n/a — an implication between equalities |  |
|  4 | set-with-predicate → bundled substructure?                                                 | no       | n/a |  |
|  5 | vector-space/field-specific → weaken typeclasses?                                          | partial  | weaken `curveK R K W` to generic field `F` (row 1) | same as row 1: lands on the existing `add_of_Y_eq` |
|  6 | 1-categorical → higher-categorical?                                                         | no       | n/a |  |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                            | no       | the "2" is intrinsic (2-torsion); generalising the index `n` would be the **full** `ψ_n(P)=0 ⟺ nP=O` theorem — a much bigger separate result, not a restatement of this lemma |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (as a *new* contribution). The only "modernisation" is dropping
`curveK R K W` to a generic field `F`, but that target coincides with mathlib's existing `add_of_Y_eq`
(over a field) — so there is no new idiomatic lemma to ship; the idiomatic form already exists in
mathlib. The contemporary mathlib formulation of "`P` doubles to zero when `y` is fixed by negation" is
precisely `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`, which mathlib already has.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities / typeclass-search paths introduced).

---

### Mathlib search-status: `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`

Method note: the local Lean build is stale and the loogle/leansearch MCP tools are unavailable in this
environment, so the authoritative check is a **direct grep + read of the pinned mathlib checkout**
(`.lake/packages/mathlib`), plus WebSearch. The relevant decls were located and read at the line
numbers below.

[A] Lean-Finder       n/a (index MCP unavailable in env; substituted by direct source grep [D], authoritative for this pin).
[B] Loogle            n/a (index MCP unavailable). Intended type pattern `_ = negY _ _ → _ + _ = 0` / `Nonsingular _ _ → (2:ℕ) • Point.some _ _ _ = 0` → would hit `add_self_of_Y_eq` / `add_of_Y_eq` (confirmed present by [D]).
[C] LeanSearch        n/a (index MCP unavailable). Intended NL intent "point of order two iff y equals negY / doubling a point to zero" → same hits as [B].
[D] **Grep + read mathlib src (authoritative, exact pin)**:
      • `WeierstrassCurve.Affine.Point.add_of_Y_eq`
        — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:672` (and `@[simp]`)
        — `(hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = 0`. **The lemma the project proof actually calls.**
      • `WeierstrassCurve.Affine.Point.add_self_of_Y_eq`
        — `…/Affine/Point.lean:677`
        — `(hy : y₁ = W.negY x₁ y₁) : some _ _ h₁ + some _ _ h₁ = 0`. **Exactly the doubling/2-torsion direction** (literally `add_of_Y_eq rfl hy`).
      • `WeierstrassCurve.ψ₂`
        — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:113`
        — `noncomputable def ψ₂ := W.toAffine.polynomialY`. **`ψ₂` is *definitionally* `polynomialY`.**
      • `WeierstrassCurve.Affine.evalEval_polynomialY`
        — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:195`
        — `W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃`.
      • `WeierstrassCurve.Affine.negY`
        — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:113`
        — `negY x y = -y - W'.a₁ * x - W'.a₃`.
      • `two_nsmul` (generic group lemma, `2 • a = a + a`) — present in `Mathlib/Algebra/…` (used verbatim in the proof; e.g. referenced from `Mathlib/Algebra/CharP/Two.lean:83`).
[E] Name pattern      grep `nagell|lutz` over `Mathlib/` → only the unrelated Galois-theory author *Patrick Lutz*; **no Nagell–Lutz theorem**. grep `two_nsmul|Y_eq|nsmul` in `Affine/Point.lean` → `add_of_Y_eq` (672), `add_self_of_Y_eq` (677). No `ψ₂`-phrased 2-torsion lemma anywhere.

Searched for both:
  - the user's current form (`ψ₂.evalEval x y = 0 → 2•P = 0`, over `curveK R K W`): **not present verbatim** in mathlib.
  - the literature-standard / mathlib-native form (`y = negY x y → P + P = 0`): **present** as `add_self_of_Y_eq` (over an arbitrary field `F`).

_Project-framing note (the task flagged this project forks `Mathlib.…DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, with duplicated General/PID tracks): the proof of
THIS decl consumes mathlib's **affine point-group** API (`Affine.Point.add_of_Y_eq`,
`evalEval_polynomialY`, `negY`) and the `WeierstrassCurve.ψ₂` *definition*. `ψ₂` is among the names the
project also re-declares (`DivisionPolynomial.lean`), but here it is used only via the `ψ₂ = polynomialY`
defeq + `evalEval_polynomialY`, both of which are pure mathlib. The substantive lemma it leans on —
`add_of_Y_eq`/`add_self_of_Y_eq` — lives in `Affine/Point.lean`, which the project does **not** fork. So
the decl is **not** already upstream, but its entire content reduces to upstream mathlib lemmas._

Concluded: **not in mathlib verbatim**, but the **building blocks are present** (`add_of_Y_eq` /
`add_self_of_Y_eq`, `ψ₂ = polynomialY`, `evalEval_polynomialY`, `negY`, `two_nsmul`); the user's exact
ψ₂-phrased form is a ≤3-substantive-call composition of these — see Phase 6.

---

### Call sites — `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero` (PID track)

Internal use count: **1** (within the project, excluding the declaring file's own header).
External-to-file callers: **0** distinct files (the one use is *within the same file*).

| Caller file:line          | Usage pattern (one-line excerpt)                                              |
|---------------------------|------------------------------------------------------------------------------|
| `PIDPrimeOrder.lean:172`  | `· exact absurd (two_nsmul_eq_zero_of_ψ₂_eq_zero W hns hψ₂) h2ne`             |

That single site is inside `integrality_of_order_four_squarefree` (same file, line 151): in the order-4
case, the `ψ₄ = C(preΨ₄) · ψ₂` factorisation gives `preΨ₄(x)=0 ∨ ψ₂(P)=0`; the `ψ₂(P)=0` branch is
closed by deriving `2•P=0` and contradicting `h2ne : 2•P ≠ 0`. Pure local plumbing.

Inline-derivation grep (was the equivalent re-derived elsewhere without calling this lemma?):
  - **General-track twin** `LutzNagell.LutzNagellTheorem.two_nsmul_eq_zero_of_ψ₂_eq_zero`
    (`GeneralPrimeOrder.lean:66`) re-derives the *identical* statement over fixed `ℚ` with an
    essentially identical short proof, used once at `GeneralPrimeOrder.lean:143` in the same
    `absurd … h2ne` pattern. This is the General/PID fork — two copies of the same trivial bridge.

Call-sites reading: **K = 1** internal use, no external callers, plus a near-verbatim twin in the
sister track ⇒ the **"K = 1 / possibly-the-wrong-abstraction — could be inlined"** signal. Combined with
Phase 6 (composes from mathlib in ≤3 calls), the lean is firmly toward **NO-composable-from-mathlib**.

---

### Composition check (Phase 6)

Can `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero` be derived from **mathlib** in ≤3 chained calls?
**Yes.**

The whole content is: turn `ψ₂.evalEval x y = 0` into `y = negY x y` (mechanical — `ψ₂` is *defeq*
`polynomialY`, `evalEval_polynomialY` rewrites it to `2y+a₁x+a₃`, `negY` unfolds to `-y-a₁x-a₃`, and a
single `linear_combination`/`linarith` bridges them), then hand that to mathlib's `add_of_Y_eq rfl`
(equivalently `add_self_of_Y_eq`) after `two_nsmul` turns `2•P` into `P+P`.

Attempt 1 (mathlib-native; this *is* the lemma's own body, lightly rephrased):
```lean
-- given hns : (curveK R K W).toAffine.Nonsingular x y, and hψ : (curveK R K W).ψ₂.evalEval x y = 0
rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at hψ   -- hψ : 2*y + a₁*x + a₃ = 0
rw [two_nsmul]                                                                  -- goal : P + P = 0
apply WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := hns) (h₂ := hns) rfl    -- goal : y = negY x y
simp only [WeierstrassCurve.Affine.negY, curveK]                               -- goal : y = -y - a₁x - a₃
linear_combination hψ
```
  - Mathlib decls used: `ψ₂` (def-unfold), `Affine.evalEval_polynomialY`, `two_nsmul`,
    `Affine.Point.add_of_Y_eq` (or `add_self_of_Y_eq`), `Affine.negY` (def-unfold).
  - Result: **succeeds** — this is literally the declaration's 5-line body. The only non-tactic name is
    the mathlib lemma `add_of_Y_eq`. The proof contains **no** project-specific reasoning; the lone
    `linear_combination hψ` discharges `2y+a₁x+a₃=0 ⟹ y = -y-a₁x-a₃`, a one-step linear fact.
  - Notes: the lemma adds no inductive content, no new API, no reusable abstraction beyond
    `add_of_Y_eq`/`add_self_of_Y_eq`. (The `simp only [… , curveK]` merely unfolds the project's
    `curveK` abbrev so that `negY`'s `a₁,a₃` are the base-changed coefficients — bookkeeping, not math.)

Conclusion: **COMPOSABLE** (≤3 substantive mathlib calls; the rest is definitional unfolding + one
`linear_combination`).

---

## Verdict: `LutzNagell.PID.two_nsmul_eq_zero_of_ψ₂_eq_zero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): standard 2-torsion characterisation (Silverman AEC negation map;
  Wikipedia "Division polynomials" / Nagell–Lutz). Mathlib's native phrasing of this direction is
  `y = negY x y → P + P = 0` (= `add_self_of_Y_eq`), not the ψ₂ wrapper. Form correct, general-Weierstrass.
  Mathlib has **no** Nagell–Lutz theorem (grep: only the unrelated author *Patrick Lutz*).
- Generality analysis (Phase 4): **STRICTLY NARROWER** (tied to `curveK R K W`) — though broader than the
  `ℚ`-fixed General twin — but the generalised target (`WeierstrassCurve F`) **coincides with mathlib's
  existing `add_of_Y_eq`**, so generalising yields nothing new. Modern idiom (4c) = **no new contribution**.
- Mathlib search (Phase 5): not present verbatim; **building blocks present** —
  `add_of_Y_eq` (`Affine/Point.lean:672`) / `add_self_of_Y_eq` (`:677`), `ψ₂ = polynomialY`
  (`DivisionPolynomial/Basic.lean:113`), `evalEval_polynomialY` (`Affine/Basic.lean:195`),
  `negY` (`Affine/Formula.lean:113`), `two_nsmul`.
- Composition check (Phase 6): **COMPOSABLE** in ≤3 substantive mathlib calls — the declaration's own
  5-line body *is* that composition, ending in `add_of_Y_eq`. **K = 1** call site
  (`PIDPrimeOrder.lean:172`, the order-4 helper), no external consumers, plus the verbatim General twin.

**Rationale:**

Mathlib already carries the mathematically substantive content: `Affine.Point.add_self_of_Y_eq`
(`Affine/Point.lean:677`) is exactly "if `y = negY(x,y)` then `P + P = 0`" — the doubling / 2-torsion
direction — and it is defined as `add_of_Y_eq rfl hy`, the very lemma this project proof calls. The
project decl differs only by (a) phrasing the hypothesis through the 2-division polynomial `ψ₂` instead
of through `negY`, and (b) phrasing the conclusion as `2 • P` instead of `P + P`. But `ψ₂` is
*definitionally* `polynomialY` (`Basic.lean:113`), `evalEval_polynomialY` rewrites `ψ₂.evalEval x y` to
`2y+a₁x+a₃` in one step, and since `negY x y = -y - a₁x - a₃` the equivalence `ψ₂(x,y)=0 ⟺ y = negY x y`
is a single `linear_combination`; likewise `2 • P = P + P` is the generic `two_nsmul`. So the lemma is a
≤3-substantive-call composition of existing mathlib API with zero reusable content of its own — its
5-line proof already *is* that composition.

The call-site evidence agrees: exactly **one** internal use (`integrality_of_order_four_squarefree`,
`PIDPrimeOrder.lean:172`), no external consumers, and a verbatim re-derivation in the sister General
track (`GeneralPrimeOrder.lean:66`). That is the "K = 1, wrong-abstraction, inline it" pattern. There is
no mathlib gap to fill: the apparent gap "mathlib lacks a `ψ₂`-phrased 2-torsion lemma" is illusory
because `ψ₂` reduces to `polynomialY` by definition, so any consumer simply rewrites and calls
`add_self_of_Y_eq`. (Note this PID copy is the *more general* of the project's two — arbitrary fraction
field `K`, with `[IsDomain R]/[UFM R]/[IsFractionRing R K]` `omit`-ted — which only sharpens the point
that the base is incidental and the content is upstream.)

**WHY not (refactor-actionable):**

Mathlib has the building blocks; the user's form is a 1–3 mathlib-call composition. Building blocks:
- `WeierstrassCurve.Affine.Point.add_self_of_Y_eq` — `…/Affine/Point.lean:677`
- `WeierstrassCurve.Affine.Point.add_of_Y_eq` — `…/Affine/Point.lean:672`
- `WeierstrassCurve.ψ₂` (defeq `polynomialY`) — `…/DivisionPolynomial/Basic.lean:113`
- `WeierstrassCurve.Affine.evalEval_polynomialY` — `…/Affine/Basic.lean:195`
- `WeierstrassCurve.Affine.negY` — `…/Affine/Formula.lean:113`
- `two_nsmul` — `Mathlib/Algebra/…`

Composition sketch (≤3 substantive lines; the lemma body, inlined at the call site):
```lean
-- at PIDPrimeOrder.lean:172, with hns : (curveK R K W).toAffine.Nonsingular x y
--                              and hψ₂ : (curveK R K W).ψ₂.evalEval x y = 0:
rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY] at hψ₂
rw [two_nsmul]
exact WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁ := hns) (h₂ := hns) rfl
  (by simp only [WeierstrassCurve.Affine.negY, curveK]; linear_combination hψ₂)
```

Refactor plan:
1. At `PIDPrimeOrder.lean:172`, replace `exact absurd (two_nsmul_eq_zero_of_ψ₂_eq_zero W hns hψ₂) h2ne`
   with the inlined composition above wrapped in `absurd … h2ne`; then delete the
   `two_nsmul_eq_zero_of_ψ₂_eq_zero` declaration from `PIDPrimeOrder.lean`. (If the inline reads
   awkwardly, keep it as a tiny `private`/`local` helper in this one file — but it should not be a
   public, mathlib-bound API surface.)
2. Apply the identical treatment to the General twin at `GeneralPrimeOrder.lean:66` / call site `:143`.
3. Because both tracks share this trivial bridge, the cleanest consolidation (a `lane:cleanup`/dedup
   ticket — the duplication analysis already flags this pair as **UNIFY**) is **one** `private` helper
   over a generic field `F` in a shared file, used by both tracks — but even that helper is a thin
   wrapper over `add_self_of_Y_eq` and is **not** mathlib-bound.

**Next action:** delete `two_nsmul_eq_zero_of_ψ₂_eq_zero` from the project (both PID and General copies)
and inline the 3-line composition at the two `absurd … h2ne` call sites, or demote to a single-file
`private` helper / one shared generic-`F` helper. Do **not** propose it for a mathlib PR — mathlib
already has `Affine.Point.add_self_of_Y_eq`, which is the substantive lemma.

---

## Next step

Delete `two_nsmul_eq_zero_of_ψ₂_eq_zero` (PID + General tracks) and inline the composition
`rw [ψ₂, evalEval_polynomialY] … ; rw [two_nsmul]; exact add_of_Y_eq rfl (… linear_combination)` at the
two `absurd … h2ne` call sites (or demote to a `private` per-file / shared generic-`F` helper, per the
existing **UNIFY** duplication ticket). No mathlib PR.

---

_Sources (Phase 1 literature): Nagell–Lutz theorem (Wikipedia); Division polynomials (Wikipedia);
Silverman, Arithmetic of Elliptic Curves (negation map III.2.3; 2-torsion); arXiv:2509.07524 (Nagell–Lutz
over imaginary quadratic fields). Mathlib decls read directly from the pinned `.lake/packages/mathlib`
checkout at the line numbers cited above._
