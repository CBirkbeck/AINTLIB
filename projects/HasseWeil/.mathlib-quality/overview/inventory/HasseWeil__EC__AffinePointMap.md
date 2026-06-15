# Inventory: ./HasseWeil/EC/AffinePointMap.lean

**Module**: `HasseWeil.Affine.Point` (two reopenings of this namespace)
**Import**: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`
**Total lines**: 132
**Total declarations**: 6 (2 defs, 3 theorems/lemmas, 1 instance-like def)

---

## Phase 0a — general injective ring hom

Variables: `{R S : Type*} [CommRing R] [CommRing S] {W : WeierstrassCurve R}`, `(f : R →+* S)`, `(hf : Function.Injective f)`

---

### `noncomputable def map`

- **Type**: `W.toAffine.Point → (W.map f).toAffine.Point`
- **What**: The natural map sending a point on `W` over `R` to the corresponding point on `W.map f` over `S`, by applying `f` to both coordinates. Sends `.zero` to `.zero` and `.some x y h` to `.some (f x) (f y) _`.
- **How**: The nonsingularity hypothesis on `(f x, f y)` is obtained by applying `WeierstrassCurve.Affine.map_nonsingular` (mathlib), which states that under an injective ring hom, nonsingularity is preserved.
- **Hypotheses**: `f` must be injective (needed for `map_nonsingular`). `R`, `S` commutative rings.
- **Uses from project**: none
- **Used by**: `map_zero`, `map_some`, `map_add`, `map_neg`, `mapAddMonoidHom`, `map_zsmul` (all in this file)
- **Visibility**: public
- **Lines**: 41–43, proof length 1 line (pattern match, definitional)
- **Notes**: `noncomputable` due to classical logic in mathlib's `Point`; no `set_option maxHeartbeats`; no sorry.

---

### `@[simp] theorem map_zero`

- **Type**: `map f hf (.zero : W.toAffine.Point) = .zero`
- **What**: `map` sends the identity element `.zero` to `.zero`; this is a simp lemma.
- **How**: By `rfl` — the match branch is definitionally equal.
- **Hypotheses**: same variables as `map`.
- **Uses from project**: `map`
- **Used by**: `mapAddMonoidHom` (via `map_zero'` field)
- **Visibility**: public
- **Lines**: 45, proof length 1 (`:= rfl`)
- **Notes**: Tagged `@[simp]`.

---

### `@[simp] theorem map_some`

- **Type**: `map f hf (.some x y h) = .some (f x) (f y) ((WeierstrassCurve.Affine.map_nonsingular _ _ hf).mpr h)`
- **What**: `map` sends a nonsingular affine point `(x, y)` to `(f x, f y)` on `W.map f`; this is a simp lemma.
- **How**: By `rfl` — definitional.
- **Hypotheses**: `h : W.toAffine.Nonsingular x y`, `hf : Function.Injective f`.
- **Uses from project**: `map`
- **Used by**: `map_add`, `map_neg`, `mapAddMonoidHom` (indirectly)
- **Visibility**: public
- **Lines**: 47–50, proof length 1 (`:= rfl`)
- **Notes**: Tagged `@[simp]`.

---

## Phase 0b — field case (additive structure)

Variables: `{F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F'] {W : WeierstrassCurve F}`, `(f : F →+* F')`

Note: `hf` is not separately stated here; `f.injective` is used inline, as field homs are injective.

---

### `theorem map_add`

- **Type**: `∀ (P Q : W.toAffine.Point), map f f.injective (P + Q) = map f f.injective P + map f f.injective Q`
- **What**: `map f` is a group homomorphism with respect to the elliptic curve group law. Case analysis covers: zero + P, P + zero, and the `some + some` cases (with and without Y-coordinate cancellation).
- **How**: The proof uses `WeierstrassCurve.Affine.Point.add_of_Y_eq` and `WeierstrassCurve.Affine.Point.add_some` (mathlib) for the point-addition case split; it uses `WeierstrassCurve.Affine.map_negY`, `map_slope`, `map_addX`, `map_addY` (all mathlib equivariance lemmas) to show `f` commutes with each piece of the addition formula.
- **Hypotheses**: `F`, `F'` fields with decidable equality; `f : F →+* F'` a ring hom (hence injective as a field hom).
- **Uses from project**: `map`, `map_zero`, `map_some`
- **Used by**: `mapAddMonoidHom` (via `map_add'` field)
- **Visibility**: public
- **Lines**: 72–104, proof length ~33 lines
- **Notes**: **Proof > 30 lines** (lines 74–104). No sorry. No `set_option maxHeartbeats`. Uses `by_cases` and `rintro` for the negation-pair case.

---

### `theorem map_neg`

- **Type**: `∀ (P : W.toAffine.Point), -map f f.injective P = map f f.injective (-P)`
- **What**: `map f` commutes with negation of points: the negation of the image equals the image of the negation.
- **How**: Case split on whether `P` is zero or `some x y h`. For the `some` case, uses `WeierstrassCurve.Affine.map_negY f x y` (mathlib) to show `f` commutes with the `negY` function that defines point negation.
- **Hypotheses**: Same field variables as Phase 0b.
- **Uses from project**: `map`, `map_some`
- **Used by**: unused directly in this file (but logically supports `mapAddMonoidHom`)
- **Visibility**: public
- **Lines**: 107–115, proof length ~9 lines
- **Notes**: No sorry. No `maxHeartbeats`. Uses `congr 1` and `exact`.

---

### `noncomputable def mapAddMonoidHom`

- **Type**: `W.toAffine.Point →+ (W.map f).toAffine.Point`
- **What**: Packages `map f f.injective` as an `AddMonoidHom`, providing the additive monoid homomorphism structure.
- **How**: Direct construction via the `AddMonoidHom` record, filling `map_zero'` with `map_zero` and `map_add'` with `map_add`.
- **Hypotheses**: Same field variables as Phase 0b.
- **Uses from project**: `map`, `map_zero`, `map_add`
- **Used by**: `map_zsmul`
- **Visibility**: public
- **Lines**: 119–124, proof length ~5 lines (record literal)
- **Notes**: `noncomputable`. No sorry. No `maxHeartbeats`.

---

### `theorem map_zsmul`

- **Type**: `∀ (n : ℤ) (P : W.toAffine.Point), map f f.injective (n • P) = n • map f f.injective P`
- **What**: `map f` commutes with integer scalar multiplication on elliptic curve points.
- **How**: Directly from `AddMonoidHom.map_zsmul` applied to `mapAddMonoidHom f`, since any additive monoid hom commutes with `zsmul`.
- **Hypotheses**: Same field variables as Phase 0b.
- **Uses from project**: `mapAddMonoidHom`
- **Used by**: unused in this file (publicly exported for other files)
- **Visibility**: public
- **Lines**: 127–129, proof length 1 (`:= (mapAddMonoidHom f).map_zsmul P n`)
- **Notes**: No sorry. No `maxHeartbeats`.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 6 |
| `def` / `noncomputable def` | 2 (`map`, `mapAddMonoidHom`) |
| Theorems/lemmas | 4 (`map_zero`, `map_some`, `map_add`, `map_neg`, `map_zsmul`) — 5 counting `map_zsmul` |
| Instances | 0 |
| `sorry` | none |
| `set_option maxHeartbeats` | none |
| Proofs > 30 lines | `map_add` (~33 lines) |
| Key API (used by 3+) | `map` (used by all 5 downstream decls), `map_some` (used by `map_add`, `map_neg`, `mapAddMonoidHom`) |
| Unused in file | `map_neg`, `map_zsmul` |
