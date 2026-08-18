# Mathlibable assessment — `EllSequence.compl₂EDS_eq_redInvarNum_sub`

**Verdict: NO-composable-from-mathlib**

> One-line: a `ring` rearrangement of the local definition `redInvarNum` introduced two lines above — zero mathematical content, not a candidate for mathlib.

---

## 1. The declaration (verified from source)

File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1367`
Qualified name (verified): **`EllSequence.compl₂EDS_eq_redInvarNum_sub`**
(opened `namespace EllSequence` at L1356, inside `section Complement`/`section Divisibility`/`section NormEDS`; no further enclosing namespace. The prompt's guessed name is correct.)

Context (`variable (b c d : R) (m : ℤ)`, `[CommRing R]`):

```lean
/-- The numerator of the reduced invariant expression
`(W(m-1)²W(m+2)+W(m-2)W(m+1)²+W₂²W(m)³)/W₂` for a normalised EDS W,
obtained by cancelling `W₃W₂ = b*c` from `invarNum`. -/
def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

lemma compl₂EDS_eq_redInvarNum_sub :
    compl₂EDS b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * compl₂EDSAux b c d m := by
  rw [redInvarNum]; ring
```

The lemma simply solves the **defining equation of `redInvarNum`** (stated on the immediately preceding line, L1364–1365) for its first summand `compl₂EDS`. Proof: unfold the definition and `ring`.

Mathematically: from `R = A + B + C` conclude `A = R − B − C`. It is the additive-rearrangement identity, instantiated at a local definition. No EDS theory is used in the proof; `compl₂EDS`, `compl₂EDSAux`, `normEDS` are opaque to it.

## 2. Literature search

WebSearch over the EDS / division-polynomial / Nagell–Lutz corpus (arXiv 1108.3051, 0802.2651, math/0404412, eprint 2008/444, Stange's division-polynomial papers, the Sept-2025 Nagell–Lutz-over-imaginary-quadratic-fields paper, Wikipedia EDS & Nagell–Lutz, arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings"): EDS and division polynomials are standard, but **"reduced invariant", `redInvarNum`, `redInvarDenom`, `invarNum`, `compl₂EDSAux`, and the `*_eq_redInvarNum_sub` rearrangement are not named results in the literature** — they are bespoke AINTLIB scaffolding for formalising the `ω`-coordinate recurrence (`ω n = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2`) in a `ring`-friendly, division-free form. There is no literature object this lemma "is".

The decomposition `invarNum = redInvarNum · b` exists only to cancel the factor `W₃W₂ = b·c` from the classical invariant so the `ω`-recurrence can be proved over an arbitrary `CommRing` without passing to fractions. The target lemma is the trivial algebraic step inside that program.

## 3. Mathlib search (five methods)

The project **forks and extends** `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

- **Base API present in mathlib** (`.lake/packages/mathlib/.../EllipticDivisibilitySequence.lean`, 547 lines): `preNormEDS`, `normEDS`, `complEDS₂` (mathlib's spelling of the fork's `compl₂EDS`), `complEDS'`, `complEDS`, `normEDS_mul_complEDS₂`, `complEDS₂_mul_b`, `map_complEDS₂`, … Confirmed by `grep` + the mathlib4_docs page.
- **Absent from the entire mathlib tree** (`grep -rn` over `.lake/packages/mathlib/Mathlib` — empty result): `invarNum`, `invarDenom`, `redInvarNum`, `redInvarDenom`, `compl₂EDSAux`/`complEDSAux₂`, `redInvar_normEDS`, and any `*_eq_redInvarNum_sub`. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` contain no `invarNum`/`EllSequence`/`redInvar` usage either — mathlib's `ω` is defined via `ψ₂ₙ/ψₙ`, not via this reduced-invariant decomposition.
- Method 4 (name guess `redInvarNum`, `compl₂EDS_eq_redInvarNum`): the *definition* `redInvarNum` it references is itself fork-local, so no possible mathlib lemma can state this identity — the names on the RHS don't exist upstream.
- Duplicated within AINTLIB: `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:855` carries the twin `complEDS₂_eq_redInvarNum_sub` (mathlib spelling). Both projects fork the same upstream development; this confirms it is fork infrastructure, not upstream content.

**Conclusion:** not in mathlib, and cannot be — its statement is phrased entirely in terms of fork-local definitions (`redInvarNum`, `compl₂EDS`, `compl₂EDSAux`) absent upstream.

## 4. Generality analysis

Already maximally general for what it is: stated over an arbitrary `[CommRing R]`, all variables free, no `nonZeroDivisors`/`Nontrivial`/domain hypotheses (the `omit … in` strips every EDS hypothesis). There is no weaker assumption to drop. Generalising further is meaningless — the content is `A = (A+B+C) − B − C`, which already holds in any additive group / `Ring`.

## 5. Composition check (≤ 3 mathlib calls)

Trivially yes. Given the definition `redInvarNum := compl₂EDS + normEDS^3*b + 2*compl₂EDSAux`, the goal is discharged by **one** tactic: `simp only [redInvarNum]; ring` (or `linear_combination`). It is a single `ring` call after unfolding one local definition. No new mathlib lemma is needed or warranted — `ring`/`linear_combination` are exactly mathlib's primitives for this, and the project already uses them here. It is a sub-`O(1)` consequence of its own preceding `def`.

## 6. Five-bucket verdict

**NO-composable-from-mathlib.**

Rationale:
- It is not a theorem about EDS; it is the additive rearrangement of a definition (`redInvarNum`) stated on the line directly above it, proved by `ring`.
- It **cannot** be "in mathlib" (so not NO-mathlib-has-it): its statement names fork-local definitions (`redInvarNum`, `compl₂EDS`, `compl₂EDSAux`) that do not exist upstream. It is structurally a private bridge step — used exactly once, at `DivisionPolynomialOmega.lean:84`, to rewrite `ψc` in the proof of `WeierstrassCurve.ω_spec`.
- It is recovered from mathlib's `ring` in a single call once the local `def` is in scope, so it is "composable from mathlib" in the strict sense the bucket names. Really it is an unfold-and-`ring` artifact that should stay inline / `private` in the fork. It carries no standalone mathematical value and should **not** be PR'd to mathlib.

If the surrounding reduced-invariant `ω`-recurrence development (`redInvarNum`, `redInvarDenom`, `redInvar_normEDS`, the `ω` family) is ever upstreamed as a whole — which would be a genuine, citable contribution (a `CommRing`-level, fraction-free `ω`-coordinate recurrence) — then `redInvarNum` would land as a `def` and this rearrangement would travel with it as a one-line `private`/inline helper, **not** as a standalone public lemma.

### Evidence pointers
- Statement + proof: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1362-1370`
- Sole use site: `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:84` (proof of `WeierstrassCurve.ω_spec`)
- AINTLIB twin: `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:855` (`complEDS₂_eq_redInvarNum_sub`)
- Mathlib base (extended-from): `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — has `complEDS₂`/`normEDS`, **lacks** the whole `invarNum`/`redInvarNum` layer.
