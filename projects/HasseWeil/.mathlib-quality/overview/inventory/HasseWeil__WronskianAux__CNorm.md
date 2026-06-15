# Inventory: ./HasseWeil/WronskianAux/CNorm.lean

**File purpose**: **Documentation-only file** (no declarations). It records the `C`-normalization simp
pattern that the `WronskianAux.lean` `linear_combination` proofs rely on: `Polynomial.derivative_pow`
emits `C ((n : ℕ) : R)` (a `Nat.cast`), whereas the other side of an identity has `C (OfNat.ofNat n : R)`;
`ring` treats `C (Nat.cast n)` and `C (OfNat.ofNat n)` as distinct atoms, blocking cancellation. The
documented fix is to include `Polynomial.C_ofNat` (not `@[simp]` in mathlib) together with `Nat.cast_ofNat`
(already `@[simp]`) in the `simp only` normalization step at each call site, atomizing every numeric `C k`
to the polynomial literal `(k : Polynomial R)`.

**Imports**: `Mathlib.Algebra.Polynomial.Basic`

**Total declarations**: **0.** The entire file body is the module docstring; there are no `def`/`lemma`/
`theorem`/`instance`/`attribute` declarations. (grep-confirmed: 0 declarations.)

**Imported by**: `HasseWeil/WronskianAux.lean` (the sole importer).

---

## Declarations

*(none)*

The file exists purely to (a) carry the explanatory docstring and (b) provide a stable import anchor for
the `WronskianAux.lean` proofs. The simp lemmas it describes (`Polynomial.C_ofNat`, `Nat.cast_ofNat`) are
**mathlib lemmas** — they are *referenced in prose* here and *used inline* in `WronskianAux.lean`'s
`simp only` blocks (and in `OmegaPullbackCoeff.lean`'s `wronskian_Φ_ΨSq_three/four`); they are **not**
re-declared, aliased, or bundled into a named simp set in this file.

---

## File Summary

- **Role in proof**: indirect / documentation. It does not contribute any term to the dependency graph of
  the main theorem; it only documents a tactic idiom and is imported by `WronskianAux.lean`.
- **(a) Dead/unused declarations**: not applicable — the file has no declarations. The file itself is
  *imported* (so not a dead module), but it ships **zero reusable content**.
- **(b) Scratch/superseded sub-routes**: none.
- **(c) Hand-rolled vs mathlib**: explicitly defers to mathlib (`Polynomial.C_ofNat`, `Nat.cast_ofNat`) —
  good; no re-implementation.
- **(d) Moral duplication**: none.
- **(e) Under-general statements**: not applicable.
- **Cleanup flags / recommendation**: Since the file declares nothing, consider either
  (i) **promoting it to actual content** — define a named simp set, e.g.
  `@[simp] aux_attr` or a `Polynomial.cNorm` simp lemma list, so call sites can write `simp [cNorm]` instead
  of repeating `simp only [Polynomial.C_ofNat, …, Nat.cast_ofNat]`; **or**
  (ii) **folding the docstring into `WronskianAux.lean`** and dropping the file + its import.
  Either removes a 0-declaration module. Note the docstring's own remark that `simp only` does not pick up
  `Nat.cast_ofNat` automatically (so it must be listed explicitly) is a useful gotcha worth preserving
  wherever it lands. No `sorry`, no `maxHeartbeats`.
