# Mathlibable assessment: `WeierstrassCurve.map_ΨSq`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `WeierstrassCurve.map_ΨSq`

**Source:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:445`

---

## 1. Exact statement (from source)

```lean
@[simp]
lemma map_ΨSq (n : ℤ) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]
```

Context (`DivisionPolynomial.lean`):
- `namespace WeierstrassCurve` (line 27) → so the parsed qualified name `WeierstrassCurve.map_ΨSq` is **correct (VERIFIED)**.
- `variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)` (line 29)
- `section Map` (line 412) with `variable (f : R →+* S)` (line 418).
- `ΨSq` is defined at line 164: `noncomputable def ΨSq (n : ℤ) : R[X] := W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1`.

**Mathematical content:** the naturality / commutation lemma stating that forming the univariate
"squared division polynomial" `ΨSqₙ ∈ R[X]` commutes with applying a ring homomorphism
`f : R →+* S` to the coefficients — i.e. `ΨSqₙ` of the base-changed curve `W.map f` is the
coefficient-image `(ΨSqₙ).map f`. A routine functoriality statement, not a theorem of independent
mathematical interest.

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

The project file's own module docstring states it outright:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full
> documentation."

The upstream lemma in this very checkout
(`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:522`):

```lean
@[simp]
lemma map_ΨSq (n : ℤ) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]
```

This is **identical**:
- same namespace `WeierstrassCurve`;
- same `variable (f : R →+* S)` in the upstream `section Map` (Basic.lean:489, :495);
- same `ΨSq` definition (Basic.lean:242, byte-for-byte the same);
- same statement;
- same proof term;
- same `@[simp]` attribute;
- same author (`Authors: David Kurniadi Angdinata` — the original mathlib EC division-polynomial
  author — in both file headers).

Search methods used:
1. **grep over `.lake/packages/mathlib`** — found `def ΨSq` (Basic.lean:242) and
   `lemma map_ΨSq` (Basic.lean:522). Direct hit.
2. **Web / mathlib4 docs** — `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
   is confirmed as the canonical upstream module housing `WeierstrassCurve.ΨSq` and its `map_*`
   naturality lemmas.
3. **Cross-repo grep** — other AINTLIB projects (`HasseWeil/...`) already call
   `WeierstrassCurve.map_ΨSq` directly, treating it as the standard (mathlib) name; this fork
   shadows it only inside `NagellLutz` to dodge the EDS name clash.

No more general form is needed: the upstream lemma *is* this lemma at full generality
(arbitrary `CommRing R`, `CommRing S`, arbitrary ring hom `f`).

## 3. Generality analysis

The statement is already maximally general for its setting: `R`, `S` arbitrary commutative rings,
`f` an arbitrary ring homomorphism, `n : ℤ` arbitrary. There is no weaker hypothesis to drop and
no stronger conclusion to reach — it is the canonical functoriality square for `ΨSq`. Mathlib's
copy carries the same generality.

## 4. Composition check

Not relevant to the verdict (mathlib already has the exact decl), but for completeness: the lemma
is itself a one-line `simp` composition (`ΨSq` unfold + `coe_mapRingHom` + `apply_ite`/`Polynomial.map`
naturality). In a context that imports mathlib's `DivisionPolynomial.Basic`, it would be a
0-call result — just `WeierstrassCurve.map_ΨSq` itself, or even `by simp`.

## 5. Why this exists in the project anyway

This is a deliberate, documented **fork**, not new mathematics. `NagellLutz` re-imports a copy of
`DivisionPolynomial.Basic` against its own `EllipticDivisibilitySequence` (which redefines
`normEDS`/`complEDS`) to avoid ambient name collisions. `map_ΨSq` rides along as part of that copy.
The right consolidation action is **deduplication against mathlib**, not upstreaming.

## Recommended action

- **Do not** PR to mathlib — it is already there (`WeierstrassCurve.map_ΨSq`, Basic.lean:522).
- Consolidation / cleanup: if the EDS name-clash that forced the fork can be resolved (e.g. by
  namespacing the project's EDS or by upstreaming the project's EDS changes), the entire copied
  `DivisionPolynomial.lean` — including `map_ΨSq` — should be deleted in favour of mathlib's
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

## Evidence pointers

- Project decl: `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:445`
- Project fork notice: `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:11-16`
- Mathlib decl (identical): `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:522`
- Mathlib `ΨSq` def: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:242`
- mathlib4 docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html
