# Mathlibable assessment: `smulX_ne_smulX`

- **Qualified name:** `WeierstrassCurve.Universal.Affine.smulX_ne_smulX`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:206`
- **Project:** NagellLutz (Nagell–Lutz; division polynomials; elliptic divisibility sequences)
- **Date:** 2026-06-22
- **Verdict:** **NO-mathlib-has-it** (mathlib already has the general form; this is project-internal `smulX`-bootstrap scaffolding)

---

## 1. Exact statement (from source)

```lean
namespace WeierstrassCurve      -- line 76
namespace Universal             -- line 86
namespace Affine                -- line 157

/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2   -- line 164

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by   -- line 206
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption
```

The companion `smulX_eq_smulX_iff` (line 217) packages it as an iff:
`smulX m = smulX n ↔ m = n ∨ m = -n`.

**Confirmed qualified name** matches the prompt's parsed guess
`WeierstrassCurve.Universal.Affine.smulX_ne_smulX`.

### Mathematical content
`smulX n = φₙ(X,Y) / ψₙ(X,Y)²` is the X-coordinate of the multiple `n·(X,Y)` of the
universal point on the universal Weierstrass curve (coefficients `a₁…a₆` are independent
indeterminates; `Universal.Field` is the fraction field of the universal coordinate ring).
The lemma says: **the X-coordinate of `n·P` is injective in `n` modulo sign** — distinct
multiples (other than `±` pairs) have distinct X-coordinates.

The proof is the textbook **difference-of-X-coordinates** identity
`smulX m − smulX n = ψ_{n+m}·ψ_{n−m} / (ψ_n·ψ_m)²` (`smulX_sub_smulX`, line 186),
combined with `ψᵤ_ne_zero` (over the universal/generic base, `ψ_k ≠ 0 ⇔ k ≠ 0`):
the numerator `ψ_{n+m}ψ_{n−m}` is nonzero exactly when `n+m ≠ 0` and `n−m ≠ 0`,
i.e. `m ≠ -n` and `m ≠ n`.

---

## 2. Literature search

- The identity `x(mP) − x(nP) = ψ_{m+n}ψ_{m−n} / (ψ_m ψ_n)²` is the **standard division-polynomial
  identity**, appearing verbatim in the standard references (MIT 18.783 isogeny-kernel lecture
  notes; Stange and others on elliptic divisibility sequences). The folklore EDS recurrence
  `w_{m+n}w_{m−n} = w_{m+1}w_{m−1}w_n² − w_{n+1}w_{n−1}w_m²` is the same object.
- The consequence — "the X-coordinate of `nP` determines `n` up to sign for a non-torsion point;
  the terms `ψ_k` are all nonzero" — is **well-known folklore**, not a separately-named theorem.
  Searches (Silverman; Washington; Stange; primitive-divisor / EDS literature) surface the
  identity and the non-vanishing for infinite-order points, but no theorem with this name.

Sources consulted: MIT 18.783 notes (ocw.mit.edu), arXiv EDS surveys (1909.12654, math/0409540),
Wikipedia "Divisibility sequence". ChatGPT MCP was unavailable (Codex error); reasoned from source
+ web + mathlib source, as instructed.

---

## 3. Mathlib search (five methods)

`smulX`, `ψᵤ`, and the universal-field construction are **entirely absent from mathlib**:
`grep -r "smulX"` over the pinned mathlib package returns **zero** hits outside `.lake` build
artefacts. The whole `smulX`/`smulY`/`ψᵤ`/`Universal.Field` apparatus is a **bespoke project
construction** (file author: Junyan Xu), layered on top of mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (`IsEllSequence`, `preNormEDS`, `normEDS`) and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` (`φ`, `ψ`, `ω`). Those mathlib files
provide only the *abstract sequence/polynomial* machinery — nothing about X-coordinates of
multiples, injectivity, or the universal point.

**However, the abstract mathematical content of this lemma is ALREADY in mathlib**, as the
group-theoretic statement about points (not the `smulX` algebraic surrogate):

- **`WeierstrassCurve.Affine.Point.X_eq_iff`**
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:639`):
  ```lean
  lemma X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
      x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h₂
  ```
  "Two nonsingular affine points over a field share an X-coordinate **iff** they are equal or
  negatives." Its contrapositive is exactly: `P ≠ Q ∧ P ≠ -Q → x(P) ≠ x(Q)`.
- **`WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff`** (line 881) and
  `eq_or_eq_neg_of_xRep_eq_xRep` (line 872): the same fact in `xRep` form.

`smulX_ne_smulX` is the **specialization of `X_eq_iff` to `P = m·(X,Y)`, `Q = n·(X,Y)`** on the
universal curve, where (because the universal point has infinite order, no relations)
`m·P = n·P ⟺ m = n` and `m·P = -(n·P) ⟺ m = -n`.

---

## 4. Generality analysis

The literature-standard / mathlib-standard form is the **general** statement `X_eq_iff`
(arbitrary nonsingular points over a field). `smulX_ne_smulX` is *strictly less general*:
it is hard-wired to the universal curve and to the `φ/ψ²` algebraic surrogate `smulX`, with the
"only `±n` collide" exception arising from the genericity hypothesis `ψ_k ≠ 0 ⇔ k ≠ 0`
(infinite order of the universal point). There is no weaker hypothesis set under which it
generalizes to a new mathlib-worthy statement — the general statement already exists one level up.

---

## 5. Composition check — and why it cannot simply be replaced here

In principle `smulX_ne_smulX` is the contrapositive of `X_eq_iff` once you know
`smulX n = (n • P).x`. So why does the project prove it the "hard" computational way?

**Dependency ordering (decisive):**

| line | declaration |
|---|---|
| 164 | `def smulX` (algebraic: `φₙ/ψₙ²`) |
| **206** | **`smulX_ne_smulX`** ← this lemma |
| 217 | `smulX_eq_smulX_iff` (uses 206) |
| 338 | `open Affine.Point` |
| **344** | `theorem zsmul_point_eq_smulX_smulY` — the **bridge** identifying `smulX n` with `(n • P).x` |
| **360** | inside that proof: `have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)` |

At line 206 the identification `smulX n = (n • P).x` is **not yet available** — establishing it is
exactly what `zsmul_point_eq_smulX_smulY` (line 344) does, by strong induction, and **that proof
consumes `smulX_ne_smulX`** (line 360) to show consecutive multiples have distinct X-coordinates so
the *addition* formula (not the doubling formula) applies. Invoking `X_eq_iff` here would be
**circular**. `smulX_ne_smulX` is therefore a genuine **bootstrap lemma**: an intermediate,
purely-algebraic computational step needed to *construct* the `n•P = (φₙ/ψₙ² , …)` formula — not a
reusable general result.

Downstream uses are exactly these two internal call sites (line 219 in `smulX_eq_smulX_iff`; line
360 in the bridge proof). It is also **duplicated inside AINTLIB** at
`HasseWeil/Auxiliary/DivisionPolynomial.lean:282` (an internal-dedup concern, orthogonal to
mathlib-ability).

---

## 6. Verdict

**NO-mathlib-has-it.**

- The general mathematical content is already in mathlib as
  `WeierstrassCurve.Affine.Point.X_eq_iff` / `xRep_eq_xRep_iff`
  ("two affine points share an X-coordinate iff equal or negatives").
- `smulX_ne_smulX` is a project-internal **bootstrap specialization** to the universal point and to
  the `smulX = φₙ/ψₙ²` surrogate, proved by the standard division-polynomial difference identity
  *before* (and in service of) the `Point`-level identification that would otherwise supply it.
  It is `smulX`-specific scaffolding, not a standalone result, and would never be ported as-is.
- Tied to the bespoke `smulX`/`ψᵤ`/`Universal.Field` construction, which is itself project-local
  and not in mathlib.

No new mathlib declaration is warranted: the reusable statement exists, and this lemma's role is an
intermediate step toward the very bridge that connects `smulX` to it.
