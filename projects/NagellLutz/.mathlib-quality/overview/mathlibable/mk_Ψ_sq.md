# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`

> Step-9 (`/overview`) mathlibable assessment, single declaration.
> **Local build stale** — reasoned from source + mathlib source read directly from
> `.lake/packages/mathlib` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`).
> Verdict reached at Phase 5 (mathlib search): this is a **verbatim fork** of an existing
> mathlib lemma — identical statement, identical proof, identical namespace. Phases 3/4/6 are
> recorded for completeness but are moot given the exact hit.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale (reasoned from source; mathlib read from `.lake/packages/mathlib`)
- decl `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:261`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Bivariate/univariate division polynomials `Ψₙ, ΨSqₙ, Φₙ, ψₙ, φₙ` for a
  Weierstrass curve — a fork of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`,
  re-imported (via `LutzNagell.EllipticDivisibilitySequence`) to avoid the mathlib EDS version.

### Qualified-name verification
- Declared as `lemma Affine.CoordinateRing.mk_Ψ_sq` **inside** `namespace WeierstrassCurve`
  (opened at `DivisionPolynomial.lean:27`, closed `:511`), under
  `variable (W : WeierstrassCurve R)` with `[CommRing R]`.
- ⇒ true qualified name = **`WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`**. The parsed
  qualified name in the prompt is **correct**.

---

### Statement (Phase 1)

`mk_Ψ_sq` states: for a Weierstrass curve `W` over a commutative ring `R` and any integer `n`, the
image of the bivariate `n`-division polynomial `Ψₙ ∈ R[X][Y]` in the affine coordinate ring
`R[W] = R[X][Y]/⟨W.polynomial⟩` squares to the image of the *constant* polynomial `C (ΨSqₙ)`, where
`ΨSqₙ ∈ R[X]` is the univariate "`Ψ`-squared" polynomial:

$$\bigl(\,\overline{\Psi_n}\,\bigr)^2 \;=\; \overline{\,\Psi^{\mathrm{Sq}}_n\,}\qquad\text{in } R[W].$$

Mathematically this is the standard fact (Silverman, *AEC* III, exercises on division polynomials)
that `ψₙ²` is a *polynomial in `x` alone* once one works modulo the curve equation `y² + a₁xy + a₃y =
x³ + …`: the only obstruction to `Ψₙ` being univariate is one factor of `ψ₂ = 2y + a₁x + a₃`, whose
square `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆ = Ψ₂Sq` is univariate modulo `W.polynomial`. The lemma is the
coordinate-ring shadow of `mk_ψ₂_sq` lifted through the `Even/Odd` case split in the definitions of
`Ψ` and `ΨSq`.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — base ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `(n : ℤ)` — division-polynomial index.

Hypotheses: none beyond the above.

Conclusion (Lean): `mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)`, an equality in
`W.toAffine.CoordinateRing = AdjoinRoot W.toAffine.polynomial`. (`mk W` is
`AdjoinRoot.mk W.toAffine.polynomial`, the quotient map `R[X][Y] → R[W]`.)

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal helper identity (one `simp_rw`) bridging `Ψ`/`ΨSq` in the coordinate ring; not a
named theorem, not a new structure, not a `## Main results` entry. (Lit width is exhaustive
regardless — but see Phase 5: an exact-name mathlib hit short-circuits the question.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → **n/a**. (A lemma introduces no defeq /
typeclass-search path; the one-liner negative-signal analysis does not apply.)

---

### Literature search (Phase 3)

This decl's source *is* mathlib's source (verbatim — see Phase 5), so the literature question is
fully settled by the mathlib hit; the standard-form analysis below is recorded for completeness.

| #  | Channel                          | Query                                                                              | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" "ψ_n^2" polynomial in x elliptic curve                       | yes  | `ψₙ²` is a polynomial in `x` (univariate) for all `n` | Silverman *AEC*; standard div-poly fact |
|  2 | WebSearch (general form)         | division polynomials Weierstrass curve over a ring `ψ_n` recursion                  | yes  | defined over any base ring via the universal Weierstrass curve | matches mathlib's `CommRing R` generality |
|  3 | WebSearch (named-after/aliases)  | "Ψ_n" "Ψ^2" coordinate ring elliptic divisibility division polynomial             | yes  | same identity; "even part carries the `2y+a₁x+a₃` factor" | the bivariate `Ψₙ` vs univariate `ψₙ`/`ΨSqₙ` split is exactly Best/mathlib's formulation |
|  4 | ChatGPT MCP                      | (MCP reported down per task note) standard form + generality + history of `ψₙ²`-is-univariate | n/a | fallback to #1–#3 + Silverman | MCP unavailable; covered by WebSearch + the direct mathlib read, which is dispositive |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "division polynomial"  | n/a  | (no PDFs there; refs are local-only per CLAUDE.md)   | sibling overview reports confirm the fork lineage |
|  6 | nLab                             | "division polynomial"                                                              | n/a  | nLab has no dedicated div-poly page                  | not a categorical concept |
|  7 | nCatLab                          | —                                                                                  | n/a  | —                                                    | not categorical |
|  8 | Stacks Project                   | division polynomial / coordinate ring of plane curve                              | n/a  | Stacks has no elliptic-division-polynomial entry     | not the right granularity |
|  9 | MathOverflow / MSE               | "ψ_n^2 is a polynomial in x" elliptic curve                                       | yes  | confirms #1 (folklore; many MSE answers)             | generality = any field/ring |
| 10 | recent arXiv (last 5y)           | elliptic divisibility sequence division polynomial coordinate ring                | yes  | matches mathlib's `Ψ/ΨSq/Φ/ψ/φ` API (the file's design doc) | the mathlib file header cites this lineage |

### Literature summary (Phase 3)

Concept identified as: **the `n`-division polynomial `ψₙ` and the fact that `ψₙ²` is univariate
(a polynomial in `x`) once reduced modulo the Weierstrass relation** — encoded here as
`(mk Ψₙ)² = mk (C ΨSqₙ)`.
Sources agree on the standard form: **yes** (Silverman *AEC* III; the mathlib div-poly file design).
Most general standard form: division polynomials over an arbitrary commutative base ring `R` (the
universal Weierstrass curve), exactly mathlib's `[CommRing R]` setting.
Generality dimensions where the literature varies: base structure (field in Silverman ⊂ comm ring in
mathlib — mathlib is already at the more general end).
Disagreement with the literature: **none**.

---

### Generality analysis (Phase 4)

Literature-standard form: stated over any `[CommRing R]` — which is exactly the Lean form.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | comm ring (universal Weierstrass curve) | NO | div-poly recursion + coordinate ring need a comm ring; this is already maximal |
| 2 | `(n : ℤ)`              | integer index     | integer index            | NO | `Ψₙ` is defined for all `n ∈ ℤ` (odd/even split); `ℤ` is the natural index |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is, verbatim, mathlib's own form).
Weakening opportunities: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

Moot — the declaration **is** the current mathlib idiom (same library, same `Ψ/ΨSq/mk` API). No
reformulation question arises.

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | bundled hyps → typeclasses | no | already typeclass-based (`[CommRing R]`) |
| 2 | sequences → filters | no | finite algebraic identity; no limit |
| 3 | construction → universal property | no | it's an equation in a fixed ring |
| 4 | set+closure → bundled substructure | no | n/a |
| 5 | vector-space/metric/field → weaken typeclass | no | already at `CommRing` |
| 6 | 1-categorical → higher-categorical | no | n/a |
| 7 | concrete index → general monoid | no | `ℤ` is the intrinsic index of the div-poly recursion |

Modern idiom available: **no** — it is the modern mathlib form.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no defeq / instance path introduced).

---

### Mathlib search-status: `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq` (Phase 5)

[A] Lean-Finder       "division polynomial squared coordinate ring" — n/a (index stale); covered by [D]
[B] Loogle            `WeierstrassCurve.Ψ, AdjoinRoot.mk, HPow.hPow` — superseded by the exact [D] hit
[C] LeanSearch        "psi_n squared equals Psi-squared in elliptic-curve coordinate ring" — superseded by [D]
[D] **Grep mathlib src**  `grep -rn "mk_Ψ_sq" .lake/packages/mathlib/Mathlib/` →
    **EXACT HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338`
[E] Name pattern      `Affine.CoordinateRing.mk_Ψ_sq` → same single hit as [D]

**Both forms searched** (user form = literature-standard form = mathlib form — all identical).

Side-by-side (mathlib `Basic.lean:338-340` vs fork `DivisionPolynomial.lean:261-263`):

```lean
-- mathlib  Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338
lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]

-- fork  projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:261
lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]
```

Both sit inside `namespace WeierstrassCurve` (mathlib opens it at `Basic.lean:104`, fork at
`DivisionPolynomial.lean:27`) with the same `variable (W : WeierstrassCurve R) [CommRing R]`.
⇒ **byte-for-byte identical**: statement, proof, namespace, qualified name.

Concluded: **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`; identical form**
(a verbatim fork, not a specialisation).

---

### Call sites — `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring file): assessed via grep below.

```
grep -rn "mk_Ψ_sq" projects/NagellLutz/ --include="*.lean"
```
Within the fork file itself, `mk_Ψ_sq` is consumed downstream by `mk_φ` (the `φ`-in-coordinate-ring
lemma), exactly as in mathlib (`Basic.lean:483` uses `mk_Ψ_sq` inside the proof of `mk_φ`). This is a
genuine internal-API node — but a node that already exists upstream. Inline-derivation grep: the
identity is not re-derived elsewhere; it is simply the fork's copy of the mathlib lemma.

Composability signal: the lemma is real API (used by `mk_φ`), but the API is **mathlib's** — so the
right move is to consume the mathlib lemma, not to maintain a private clone.

### Composition check (Phase 6)

Not applicable as a *contribution* question: mathlib does not merely have building blocks, it has the
**exact lemma**. (For the record, the one-line "composition" is `exact
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq n` against the mathlib decl.)

Conclusion: the question is resolved at Phase 5; no composition analysis needed.

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): standard division-polynomial fact (`ψₙ²` univariate), already at comm-ring generality.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's own form; 0 weakenings.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`** at
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338` — **byte-for-byte identical** statement + proof + namespace.
- Composition check (Phase 6): n/a — exact-name hit; `exact …mk_Ψ_sq n` is the ≤1-line follow.

**Rationale:**

This is not a specialisation, a near-miss, or a re-derivation — it is a **verbatim copy** of an
existing mathlib lemma. The NagellLutz `DivisionPolynomial.lean` file is, by its own module
docstring and by the project's sibling overview reports (`preΨ'_three.md`, `map_redInvarNum.md`), a
re-imported fork of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, pulled in to
sidestep the mathlib *EDS* version. `mk_Ψ_sq` rode along in that fork. Statement, proof tactic block,
enclosing `namespace WeierstrassCurve`, variable context, and fully-qualified name all match
`Basic.lean:338` exactly. Mathlib unquestionably already has it.

**WHY not (refactor-actionable):**
Mathlib already contains this declaration under the identical qualified name. The fork exists only to
detach the file from mathlib's `EllipticDivisibilitySequence`; `mk_Ψ_sq` itself carries no NagellLutz
modification and contributes nothing new. Any consumer (here, the fork's own `mk_φ`) should use the
mathlib lemma directly once the file again depends on `Mathlib.…DivisionPolynomial.Basic`.

Existing mathlib decl:        `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338`
Our form follows in ≤1 line (they are the same lemma):
```lean
example (W : WeierstrassCurve R) (n : ℤ) :
    mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) :=
  WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq n
```

Call sites in NagellLutz: the fork's `mk_φ` (mirroring mathlib `Basic.lean:483`), plus any internal
`Ψ/Φ`-coordinate-ring lemmas in the same file.

**Refactor plan.** This is a whole-fork dedup question, not a single-lemma swap. The local copy of
`mk_Ψ_sq` (and its siblings in `DivisionPolynomial.lean`) duplicates
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`. The fork was introduced **only**
to avoid mathlib's `EllipticDivisibilitySequence`; if that coupling can be broken without forking the
*division-polynomial* file too, then:
1. Delete the duplicated `Ψ/ΨSq/Φ/ψ/φ` block (including `mk_Ψ_sq` at line 261) from
   `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean`.
2. `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` instead.
3. At each internal call site (e.g. the fork's `mk_φ`), no argument-order change is needed — the
   mathlib lemma has the identical signature `(n : ℤ)`.

If the fork genuinely cannot drop the `EllipticDivisibilitySequence` coupling (the documented reason
for its existence), this lemma still must **not** be proposed for mathlib — mathlib has it. The
correct cleanup-ticket framing is "de-duplicate the DivisionPolynomial fork against upstream", owned
by the NagellLutz producer; it is not a mathlib contribution.

**Next action:** do **not** open a mathlib PR. Delete `mk_Ψ_sq` (and, ideally, the surrounding
forked `Ψ/ΨSq/Φ/ψ/φ` block) from `DivisionPolynomial.lean` and consume
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` directly; if the fork must persist
for the EDS-decoupling reason, file a NagellLutz dev ticket to minimise the fork, but record `mk_Ψ_sq`
as already-upstream (NO-mathlib-has-it) so it is never mistaken for a contribution.

---

## Next step

Do not open a mathlib PR. Treat as fork-dedup: delete the local `mk_Ψ_sq` (line 261) and prefer the
upstream `WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq` at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:338`; if the fork is load-bearing
for EDS decoupling, file a NagellLutz dev ticket to shrink it.
