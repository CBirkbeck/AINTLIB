# Mathlibable assessment — `complEDS₂_two`

**Verdict: `NO-mathlib-has-it`**
**Qualified name: `complEDS₂_two`** (root namespace — no enclosing `namespace`; `section PreNormEDS` does not change the namespace)
**One-line rationale:** Byte-for-byte already in mathlib (`Mathlib.NumberTheory.EllipticDivisibilitySequence`); the project file is a verbatim fork.

---

## 1. The declaration under review

Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:857`

```lean
@[simp]
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]
```

Context (file-level `variable {R : Type u} [CommRing R]` at line 85; `section PreNormEDS` at line 704 with `variable (b c d : R)` at line 706):

Full elaborated signature:
```
complEDS₂_two : ∀ {R : Type u} [inst : CommRing R] (b c d : R), complEDS₂ b c d 2 = d
```

where (line 844):
```lean
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
```

Mathematically: `complEDS₂` is the 2-complement sequence `Wᶜ₂` of a normalised EDS, the witness to
`W(k) ∣ W(2k)` (i.e. `W(k) · Wᶜ₂(k) = W(2k)`). This lemma is the trivial evaluation `Wᶜ₂(2) = d`, one
of a family of base-case `simp` evaluations (`complEDS₂_zero/one/two/three/four`) used to bootstrap the
divisibility theory of division polynomials. It is a one-line `simp`-closed initial-value computation,
not an independent mathematical result.

## 2. Mathlib search (five-method) — DIRECT HIT

The NagellLutz project explicitly forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` (and the
`AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` files). The forked source is therefore the first
place to look — and it contains this exact declaration.

Vendored mathlib pin: `leanprover/lean4:v4.31.0-rc2`, mathlib `d90090f`.

File: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`

```
246:def complEDS₂ (k : ℤ) : R :=
247:  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
248:    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
...
258:@[simp]
259:lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
260:  simp [complEDS₂]
```

Surrounding namespace/section context in the mathlib file is identical to the project's:
- `variable {R : Type u} [CommRing R]` (line 75)
- `variable (b c d : R)` (line 118)
- `section PreNormEDS` (line 120) — root namespace, no enclosing `namespace`.

A `diff` of the project's `complEDS₂` block (def `complEDS₂` through `preNormEDS_mul_complEDS₂`,
lines 844–877) against the mathlib block (lines 246–279) returns **IDENTICAL**. The statement, the
proof (`simp [complEDS₂]`), the `@[simp]` attribute, the docstring on `complEDS₂`, and the qualified
name all match character-for-character.

Methods 1–5 of the standard search collapse to a single observation: this is not a "similar" lemma or a
"more general form" question — it is the *same declaration* already present in the pinned mathlib.
(`grep -rln complEDS₂` outside the project finds only the mathlib copy and two HasseWeil auxiliary
forks; no third-party reimplementation question arises.)

## 3. Generality analysis

Not applicable as a gating question, since mathlib already has the identical statement at the identical
generality (any `CommRing R`, arbitrary `b c d : R`). There is no weaker hypothesis to seek and no more
general mathlib form that would subsume it differently — it *is* the mathlib form.

## 4. Composition check

Moot: we do not need to compose mathlib primitives to *recover* the lemma, because the lemma itself is
literally in mathlib (and even if one wished to, it is `simp [complEDS₂]` — a one-step unfold-and-reduce
that the upstream `@[simp]` evaluation lemmas already discharge).

## 5. Literature search

Not required for this verdict. The decision is settled by an exact-identity match against the pinned
mathlib, not by a literature-standard-form judgment. (For background: `complEDS₂` originates from David
Kurniadi Angdinata's mathlib EDS / division-polynomial development; the `Wᶜ₂` complement-sequence
machinery underlies the divisibility property `W(k) ∣ W(2k)` of elliptic divisibility sequences.)

## 6. Verdict

**`NO-mathlib-has-it`.**

`complEDS₂_two` is present verbatim in `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(`.lake/packages/mathlib/.../EllipticDivisibilitySequence.lean:259`), with the same name, statement,
proof, attribute, and namespace as the project's copy at `EllipticDivisibilitySequence.lean:857`. The
NagellLutz file is a fork of that mathlib module; this declaration should be dropped in favour of the
upstream one (import `Mathlib.NumberTheory.EllipticDivisibilitySequence`), not contributed.
