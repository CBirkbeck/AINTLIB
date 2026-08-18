# Mathlibable assessment: `normEDS_mul_complEDS₂`

**Verdict: NO-mathlib-has-it** — already in mathlib, verbatim, with the same name.

**One-line rationale:** Identical statement, identical proof, identical qualified name already in
the pinned mathlib — the project file is a fork of the very mathlib file that contains it.

- **Declaration:** `normEDS_mul_complEDS₂`
- **Qualified name:** `normEDS_mul_complEDS₂` (root namespace — see below)
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:925`
- **Date:** 2026-06-21
- **Pinned mathlib:** rev `09b373db6e247a35cfa5e44578c09a20e7c97271` (2026-06-21)

---

## 1. The statement (from source)

```lean
lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]
```

Context: `variable (b c d : R)` with `[CommRing R]`, inside `section NormEDS` under the file's
top-level `@[expose] public section` (`open scoped nonZeroDivisors` only). The enclosing
`namespace EllSequence` (line 90) is closed at line 597 (`end EllSequence`), and
`namespace IsEllSequence` (643) is closed at 702, so line 925 sits in the **root namespace**. Hence
the true qualified name is simply `normEDS_mul_complEDS₂` — the parsed name is correct.

**Mathematical content.** For the canonical normalised EDS `W = normEDS b c d` and its 2-complement
sequence `Wᶜ₂ = complEDS₂ b c d`, this is the witnessing identity `W(k) · Wᶜ₂(k) = W(2k)`. It is the
key lemma immediately powering `normEDS_dvd_normEDS_two_mul : normEDS b c d k ∣ normEDS b c d (2*k)`
(the divisibility half of "elliptic *divisibility* sequence").

---

## 2. Mathlib search — IT IS ALREADY THERE (exact match)

This project file is a **fork of the mathlib file**
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical Apache header, same author
"David Kurniadi Angdinata", same module docstring listing `complEDS₂`/`normEDS`). The fork extends
the upstream file with new `EllSequence`/`Param` machinery (the `transf`, `Rel₄OfValid`, `Perm`
sections, `IsEllDivSequence.normEDS` without the `hb` hypothesis, etc.), but the `normEDS` /
`complEDS₂` block is carried over unchanged.

The declaration exists in the **pinned mathlib** at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`:

```lean
lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]
```

**`diff` of the project lines (925–928) against the mathlib lines (321–324): IDENTICAL — no diff.**
Same statement, same proof term, same root-namespace placement (mathlib: root namespace, inside
`section NormEDS`, under `variable (b c d : R)` / `[CommRing R]`). The supporting names it depends on
(`normEDS`, `complEDS₂`, `preNormEDS_mul_complEDS₂`) and its consumer
`normEDS_dvd_normEDS_two_mul` are likewise present upstream at the same spots (mathlib lines
246–339 carry the whole block: `complEDS₂_zero/one/two/three/four/neg`,
`preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`,
`complEDS₂_mul_b`, `normEDS_even/odd`).

Search methods applied:
1. **grep of the pinned mathlib EDS file** → exact hit; line-for-line `diff` shows no difference.
2. **Web / mathlib4 docs** → the public module
   `Mathlib.NumberTheory.EllipticDivisibilitySequence` documents `complEDS₂` (the 2-complement
   sequence witnessing `W(k) ∣ W(2k)`) and `normEDS`; the witnessing relation
   `W(k) · Wᶜ₂(k) = W(2k)` is exactly this lemma.
3. **loogle / leansearch (mathlib index)** not needed — a verbatim source match in the *pinned*
   mathlib is dispositive.

Cross-check: the **HasseWeil** project in this same monorepo *consumes* `normEDS_mul_complEDS₂`
(calls at lines 621, 719, 769 of its `Auxiliary/EllipticDivisibilitySequence.lean`) rather than
redefining it — consistent with it being shared/upstream API.

---

## 3. Generality / composition analysis

Not load-bearing for the verdict (the identical lemma is already in mathlib), but for completeness:

- **Generality.** Already stated at the natural generality: any `CommRing R`, arbitrary `b c d : R`,
  all `k : ℤ`. There is no weaker typeclass or wider index type to move to — `normEDS`/`complEDS₂`
  are themselves `CommRing`-level definitions and the identity is closed by `ring1` after unfolding
  the parity `if`. Nothing to generalise.
- **Composition.** Not an ad-hoc ≤3-call consequence (the proof rewrites through
  `preNormEDS_mul_complEDS₂` and the `if Even` parity bookkeeping), but irrelevant: the assembled
  lemma itself *is* the upstream API surface.

---

## 4. Verdict

**NO-mathlib-has-it.**

`normEDS_mul_complEDS₂` is present in mathlib (the exact rev this repo pins,
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`) with an **identical statement,
identical proof, and identical qualified name**. The project file is a fork of that upstream file
and re-includes the declaration unchanged. There is nothing to contribute upstream; the
consolidation action is to **drop the local copy and import
`Mathlib.NumberTheory.EllipticDivisibilitySequence`**, keeping only the genuinely new
`EllSequence`/`Param`/`IsEllDivSequence.normEDS`-without-`hb` additions the fork layers on top.

### Evidence required for this bucket
- **Mathlib name:** `normEDS_mul_complEDS₂` in `Mathlib.NumberTheory.EllipticDivisibilitySequence`.
- **Proof of identity:** `diff` of source lines 925–928 vs mathlib lines 321–324 returns no
  differences; both reside in the root namespace inside `section NormEDS` over `[CommRing R]`,
  `variable (b c d : R)`.

---

### Sources
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- Pinned mathlib source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (rev `09b373db`)
