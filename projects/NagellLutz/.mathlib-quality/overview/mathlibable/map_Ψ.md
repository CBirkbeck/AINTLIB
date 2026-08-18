# /mathlibable report — `WeierstrassCurve.map_ψ`

(Note: this report is for the **lowercase-ψ** lemma `map_ψ` at project
`DivisionPolynomial.lean:459` / mathlib `Basic.lean:536`. A sibling report exists
for the distinct **uppercase-Ψ** lemma `map_Ψ` (mathlib `Basic.lean:526`); on a
case-insensitive filesystem their filenames collide — this file holds the `map_ψ`
assessment.)

## Verdict (TL;DR)

**`NO-mathlib-has-it`** — Mathlib already contains this lemma *verbatim*:
`WeierstrassCurve.map_ψ` at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`,
same namespace, same `@[simp]`, identical statement. The project's copy exists
only because this whole file is a deliberate fork of mathlib's
`DivisionPolynomial.Basic` (to swap the `EllipticDivisibilitySequence`/`normEDS`
import and dodge name clashes), not because the lemma is new.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source — both
                            decl and the mathlib twin elaborate in the pinned tree)
- decl `WeierstrassCurve.map_ψ`:  ✓ resolved at
                            `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:459`
- qualified name:           **`WeierstrassCurve.map_ψ`** (VERIFIED — decl sits inside
                            `namespace WeierstrassCurve` opened at file line 27; call sites
                            in other projects reference it as `WeierstrassCurve.map_ψ`)
- kind:                     `lemma` (carries `@[simp]`)
- has sorry:                no
- module docstring summary: "This is a copy of
                            `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
                            that imports `LutzNagell.EllipticDivisibilitySequence` instead of
                            the mathlib version, to avoid name conflicts (both define `normEDS`,
                            `complEDS`, etc.). See the original file for full documentation."

The docstring is the whole story: this is a vendored fork of a mathlib file, character-identical
except for one import line.

---

### Statement (Phase 1)

`WeierstrassCurve.map_ψ` is a **ring-hom compatibility (naturality) lemma** for the `n`-division
polynomial `ψ` of a Weierstrass curve. For a Weierstrass curve `W` over a commutative ring `R`,
a ring hom `f : R →+* S`, and `n : ℤ`:

> the `n`-division polynomial of the base-changed curve `W.map f` equals the polynomial obtained
> by pushing `W.ψ n` through `f` coefficient-wise.

Variables / typeclasses (Lean side):
- `{R S : Type*} [CommRing R] [CommRing S]` — source/target commutative rings
- `(W : WeierstrassCurve R)` — the curve
- `(f : R →+* S)` — the ring hom along which we base-change
- `(n : ℤ)` — the division index

Hypotheses: none.

Conclusion (math): `ψ_{W.map f}(n) = (mapRingHom f)(ψ_W(n))`, i.e. forming the `n`-division
polynomial commutes with coefficient base change.

Conclusion (Lean):
`(W.map f).ψ n = (W.ψ n).map (mapRingHom f)` — an equation in `S[X][Y]`.
(`ψ n` is bivariate, valued in `R[X][Y]`; hence the `mapRingHom f` push-forward, as opposed to the
plain `f` used by the univariate `map_Ψ₂Sq`/`map_Ψ₃`/… siblings.)

Project proof (line 460–461): `rw [← coe_mapRingHom]; simp [ψ, map_normEDS]`.
Mathlib proof (Basic.lean 537–538): `rw [← coe_mapRingHom]; simp [ψ]`.
Same statement; the only difference is one extra simp lemma in the project's `simp` set.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `simp`-tagged naturality glue lemma — one line of proof, no new mathematical concept,
not a `## Main result`, not named after a person. It is API plumbing for `WeierstrassCurve.map`.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner-def check is **n/a**. (The proof is
short, but the one-line *definition* heuristic only applies to definitions.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

This is a **mathlib-internal bookkeeping lemma** ("forming the division polynomial commutes with
base change of the coefficient ring"). The mathematical *object* — division polynomials `ψ_n` of
an elliptic / Weierstrass curve — is completely standard (Silverman, *The Arithmetic of Elliptic
Curves*, Exercise 3.7; Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2). The
*statement* `map_ψ` itself, however, is not a named theorem in any textbook: it is the obvious
functoriality of a polynomial that is defined by a universal recurrence with coefficients in the
base ring, and every source treats it as automatic. So the literature target here is just
"division polynomials are defined integrally / universally, hence stable under base change", which
all sources confirm.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" base change / "commutes with" ring homomorphism | partial | division polys have integer/universal coefficients → stable under base change | No source *names* this; it is folklore functoriality |
|  2 | WebSearch (general form)         | elliptic curve "division polynomial" universal coefficients ℤ         | yes  | ψ_n ∈ ℤ[a₁..a₆][x,y]; specialises along any ring hom | Silverman/Washington: ψ_n defined over the universal ring |
|  3 | WebSearch (named-after/aliases)  | "n-division polynomial" naturality / functoriality Weierstrass        | no   | — | not a named result; treated as obvious |
|  4 | ChatGPT MCP                      | (MCP down per task — fallback: reasoned from Silverman/Washington + the universal-curve construction) | n/a | confirms #2 | MCP unavailable; substituted textbook reasoning |
|  5 | Local references                 | `.mathlib-quality/references/` grep "division polynomial" / "map"     | n/a  | (no references dir present for NagellLutz) | recorded n/a |
|  6 | nLab                             | "division polynomial"                                                 | no   | — | nLab has no division-polynomial page; concept is elementary AG/NT |
|  7 | nCatLab (categorical)            | —                                                                     | n/a  | — | not a categorical concept |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                 | no   | — | Stacks does not treat elliptic-curve division polynomials |
|  9 | MathOverflow / MSE               | division polynomial coefficients ring / base change                   | yes  | confirms universal/integral coefficients | reinforces #2; no named lemma |
| 10 | recent arXiv (last 5y)           | elliptic divisibility sequence / division polynomial base change      | partial | EDS & division polys defined over base ring, transported by ring homs | matches the `normEDS`-based mathlib construction |

Protocol status: WebSearch ran ≥3 queries at distinct generality; ChatGPT MCP unavailable
(documented fallback to textbook reasoning); local refs, nLab, Stacks, nCatLab, MathOverflow,
arXiv all checked or recorded n/a with a reason.

### Literature summary (Phase 3)

Concept identified as: the **`n`-division polynomial `ψ_n` of a Weierstrass curve** (Silverman,
Washington), implemented in mathlib via **normalised elliptic divisibility sequences** (`normEDS`).
The lemma `map_ψ` is its **base-change naturality**.
Sources agree on the standard form: yes — division polynomials live over the universal ring
`ℤ[a₁,…,a₆]` and specialise along any ring hom; functoriality is automatic and unnamed.
Most general standard form: for any `CommRing` hom `f : R →+* S`, `ψ_{f_*W}(n) = f_*(ψ_W(n))`.
Generality dimensions: the base hypothesis is already the weakest sensible one (`CommRing` +
`RingHom`); there is no weaker structure on which `ψ` is even defined. No literature disagreement.

**Key consequence for the verdict:** the literature confirms the lemma is the standard, maximally
general naturality statement — which is *exactly* why mathlib already states it in precisely this
form (see Phase 5). The lit search does not surface a missing-from-mathlib generalisation; it
confirms the mathlib form is the right one.

---

### Generality analysis (Phase 4)

Literature-standard form: `(W.map f).ψ n = (W.ψ n).map (mapRingHom f)` for any `f : R →+* S`
between commutative rings — identical to the Lean statement.

| # | Parameter / hypothesis      | Current Lean form        | Literature-standard form | Weaker form exists? | Reason |
|---|-----------------------------|--------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`, `[CommRing S]` | commutative rings     | commutative rings        | NO                  | `ψ`/`normEDS` need a `CommRing`; this is the natural floor |
| 2 | `(f : R →+* S)`             | ring homomorphism        | ring homomorphism        | NO                  | base change *is* a ring hom; cannot weaken |
| 3 | `(n : ℤ)`                   | integer index            | integer index            | NO                  | `ψ` is indexed by `ℤ` by definition |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Weakening opportunities found: 0. (And it matches mathlib's form exactly.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Note |
|----|--------------------------------------------------------------------------|----------|------|
|  1 | "let X be a foo" preamble → typeclass/instance?                          | no  | already typeclass-driven (`CommRing`) |
|  2 | sequences/metric → filters/topology?                                     | no  | purely algebraic identity in a polynomial ring |
|  3 | construction → universal property?                                       | no  | `ψ` is the construction; lemma is its naturality |
|  4 | set+closure-predicate → bundled substructure?                            | no  | no substructure involved |
|  5 | vector-space/field-specific → weaker typeclass?                          | no  | already at `CommRing` |
|  6 | 1-categorical → higher-categorical?                                      | no  | a single equation |
|  7 | concrete index ℕ/ℤ/ℝ → general additive structure?                       | no  | `ℤ`-indexing is intrinsic to division polynomials |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — this is a finite algebraic naturality identity; there is no
filter-/category-/typeclass-modernisation move. Mathlib's existing form is already the idiom.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search path introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       "division polynomial base change", "map_ψ Weierstrass"   → hit (mathlib `WeierstrassCurve.map_ψ`)
[B] Loogle            `(WeierstrassCurve.map _ _).ψ _ = _`                      → hit (same decl)
[C] LeanSearch        "n-division polynomial of base-changed Weierstrass curve" → hit (same decl)
[D] Grep mathlib src  `grep -rnE "lemma map_ψ\b" .lake/.../mathlib/Mathlib`     → **HIT**, single match:
                      `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`
[E] Name pattern      `WeierstrassCurve.map_ψ`                                   → hit (same decl)

Searched for both the user's current form and the literature-standard form — they are the same
statement, and mathlib has exactly it.

**Concluded:** found in mathlib as **`WeierstrassCurve.map_ψ`**
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`); **identical form**
(same namespace `WeierstrassCurve`, same `@[simp]` attribute, same statement
`(n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f)`). The two differ only in proof text
(`simp [ψ]` upstream vs. `simp [ψ, map_normEDS]` here).

Direct evidence — the two declarations side by side:

```lean
-- mathlib  Basic.lean:535-538
@[simp]
lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [ψ]

-- project  DivisionPolynomial.lean:458-461   (this declaration)
@[simp]
lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [ψ, map_normEDS]
```

The whole surrounding `section Map` block (`map_ψ₂, map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, map_preΨ',
map_preΨ, map_ΨSq, map_Ψ, map_Φ, map_ψ, map_φ`) is duplicated line-for-line from mathlib —
this lemma is one entry in a wholesale fork of mathlib's file.

---

### Call sites (Phase 6.0) — `WeierstrassCurve.map_ψ`

Internal use count (within NagellLutz, excluding the declaring file): **≥3** load-bearing rewrites
- `LutzNagell/ZSMul.lean:100` — `simp_rw [polyEval_apply, ← map_ψ, map_specialize]`
- `LutzNagell/ZSMul.lean:558` — `rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, …]`
- `LutzNagell/DivisionPolynomialOmega.lean:114` — `…, map_Ψ₂Sq, map_ψ]; simp`
- `LutzNagell/DivisionPolynomialOmega.lean:123` — `…, map_φ, map_ω, map_ψ]; simp`
- `LutzNagell/DivisionPolynomial.lean:504` — `rw [← map_ψ, map_baseChange]` (inside `baseChange_ψ`)
- `LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:57` — `simp only [… , ← WeierstrassCurve.map_ψ] at hX`
- (`ZSMul.lean:25` is a docstring mention, not a use.)

| Caller file:line                          | Usage pattern (one-line excerpt)                                   |
|-------------------------------------------|--------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:100                 | `simp_rw [polyEval_apply, ← map_ψ, map_specialize]`                |
| LutzNagell/ZSMul.lean:558                 | `rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, …]`        |
| LutzNagell/DivisionPolynomialOmega.lean:114 | `map_Ψ₂Sq, map_ψ]; simp`                                          |
| LutzNagell/DivisionPolynomialOmega.lean:123 | `… map_φ, map_ω, map_ψ]; simp`                                    |
| LutzNagell/DivisionPolynomial.lean:504    | `rw [← map_ψ, map_baseChange]`  (proves `baseChange_ψ`)            |
| LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:57 | `simp only […, ← WeierstrassCurve.map_ψ] at hX`      |

The lemma is genuinely used (≥3 sites, no inline re-derivation) — so it is *not* dead code; it is a
real, depended-on API surface. But that API surface is mathlib's `map_ψ` re-created locally.
Note: the sibling `HasseWeil` project consumes mathlib's own `WeierstrassCurve.map_ψ` directly
(e.g. `GenericPointZsmul.lean:648`, `PencilComapWitnesses.lean:480`) — confirming the upstream
lemma is the established, reused one and this copy is the redundant twin.

Inline-derivation grep: none — the statement is not re-proved by hand elsewhere.

---

### Composition check (Phase 6)

`map_ψ` is the base-case-bearing naturality lemma for `ψ`; it is proved by unfolding `ψ` to the
underlying `normEDS` and applying `map_normEDS`. That is the very content mathlib already packages
into its own `map_ψ`. The point is not "compose mathlib primitives to reprove it" — it is that
mathlib *already ships the finished lemma*. So this is not a composition case; it is a direct
duplicate.

Conclusion: **n/a — supplanted by NO-mathlib-has-it** (mathlib has the finished lemma, not merely
the building blocks).

---

## Verdict: `WeierstrassCurve.map_ψ`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): division polynomials are standard (Silverman/Washington); their
  base-change naturality is folklore-automatic and matches the Lean statement exactly — the lit
  target is the maximally general `CommRing`-hom form, which mathlib already states.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL**; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.map_ψ`**
  (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`); identical form,
  same namespace, same `@[simp]`.
- Composition check (Phase 6): n/a — mathlib has the finished lemma.

**Rationale.**
The declaration is byte-identical in statement (and namespace, and `@[simp]` status) to mathlib's
`WeierstrassCurve.map_ψ`. It exists in the NagellLutz project only because
`LutzNagell/DivisionPolynomial.lean` is, by its own module docstring, "a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`" — forked solely to import the
project's own `EllipticDivisibilitySequence` (its own `normEDS`/`complEDS`) instead of mathlib's,
so as to avoid name collisions. The entire `section Map` (eleven `map_*` lemmas) is duplicated
verbatim. There is no new mathematical content and no generalisation: the lit search confirms the
mathlib form is already the maximally general, correct statement of this naturality fact.

The only subtlety: inside this project `W.ψ` resolves to the *forked* `ψ` (built on the forked
`normEDS`), so the project cannot literally `exact WeierstrassCurve.map_ψ` from mathlib — the two
`ψ`s are different constants. But that is an artifact of the fork, not evidence of novelty: mathlib
unquestionably already has this exact lemma about its own `ψ`, and the sibling `HasseWeil` project
uses mathlib's `WeierstrassCurve.map_ψ` directly. So the correct disposition is convergence back
onto mathlib's `DivisionPolynomial.Basic`, not upstreaming a duplicate. This is a textbook
`NO-mathlib-has-it`.

**WHY not (refactor-actionable).**
Mathlib already has it: `WeierstrassCurve.map_ψ` at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`, with the identical
type `(n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f)`. Were the project not forking the file,
the project's form would follow in **0 lines** (`exact WeierstrassCurve.map_ψ f n`, or just the
mathlib lemma firing as the `@[simp]` lemma it already is).

```lean
-- if the project used mathlib's ψ, this lemma is literally the mathlib one:
example (f : R →+* S) (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) :=
  WeierstrassCurve.map_ψ f n
```

Existing mathlib decl:  `WeierstrassCurve.map_ψ`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:536`
Call sites in our project (from Phase 6.0): **6** (across `ZSMul.lean`, `DivisionPolynomialOmega.lean`,
`DivisionPolynomial.lean`, `PIDIntegralMultiple.lean`).

**Refactor plan.** This single lemma is *not* independently removable — it is one line of an
en-bloc fork of `DivisionPolynomial.Basic`. The real refactor is at the file level, and it is the
same disposition the AINTLIB consolidation effort applies to every forked-mathlib track:
1. The blocker is the deliberate import swap: `LutzNagell/DivisionPolynomial.lean` imports
   `LutzNagell.EllipticDivisibilitySequence` (its own `normEDS`) instead of
   `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Resolve the `normEDS`/`complEDS` name-clash
   that motivated the fork (e.g. by reconverging the forked `EllipticDivisibilitySequence` onto
   mathlib's, or namespacing the project's variant) so the project can import mathlib's
   `DivisionPolynomial.Basic` directly.
2. Once mathlib's `Basic` is imported, **delete the entire duplicated `section Map`
   (lines ≈412–467), `map_ψ` included**, and let mathlib's `@[simp] WeierstrassCurve.map_ψ` (and its
   ten siblings) serve the 6 call sites unchanged — they already call the lemmas by the
   bare/`WeierstrassCurve.`-qualified names that mathlib also provides, so most sites need **no
   edit** beyond the import change.
3. This is a cross-project cleanup ticket (it touches the fork as a whole), not a one-lemma edit;
   it belongs to the AINTLIB `lane:cleanup`/dedup track, and should be filed against the whole
   `DivisionPolynomial`/`EllipticDivisibilitySequence` fork rather than this lemma alone.

**Next action.** Do **not** upstream. File a cleanup/dedup ticket to reconverge NagellLutz's
forked `DivisionPolynomial` + `EllipticDivisibilitySequence` onto the mathlib originals; on
success, delete the duplicated `section Map` (this `map_ψ` among them). No mathlib PR — the lemma
is already in mathlib.

---

## Next step

File an AINTLIB cleanup/dedup ticket to reconverge the NagellLutz `DivisionPolynomial` /
`EllipticDivisibilitySequence` fork onto mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.
DivisionPolynomial.Basic` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`; then delete the
duplicated `section Map` (including `map_ψ`) and let mathlib's identical `@[simp]
WeierstrassCurve.map_ψ` serve the existing call sites. No mathlib contribution — mathlib already
has this lemma verbatim.
