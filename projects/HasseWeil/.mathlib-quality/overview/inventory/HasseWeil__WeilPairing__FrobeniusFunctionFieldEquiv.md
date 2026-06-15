# Inventory: ./HasseWeil/WeilPairing/FrobeniusFunctionFieldEquiv.lean

**File**: `HasseWeil/WeilPairing/FrobeniusFunctionFieldEquiv.lean`
**Total lines**: 267
**Total declarations**: 15 (1 abbrev, 3 defs, 11 theorems/lemmas)
**Sorries**: none
**`set_option maxHeartbeats`**: none

## Summary

This file constructs the arithmetic Frobenius automorphism `σ : K̄(E) ≃+* K̄(E)` of the function field of an elliptic curve over an algebraic closure of a finite field, and proves that it q-powers the K̄-constants. It is axiom-clean (`[propext, Classical.choice, Quot.sound]`). The file is a pure leaf (no sorry, no maxHeartbeats bumps), serving as the elementary coefficient-Frobenius leaf for `FrobeniusGaloisData` consumed by `FrobeniusConjugation.lean`, `FrobeniusDivisorGalois.lean`, and `FrobeniusGaloisScaling.lean`.

---

## Declarations

### `theorem coordRingMap_algebraMap_base`
- **Type**: `{R S : Type*} [CommRing R] [CommRing S] (W' : WeierstrassCurve.Affine R) (f : R →+* S) (a : R) : CoordinateRing.map W' f (algebraMap R W'.CoordinateRing a) = algebraMap S (W'.map f).toAffine.CoordinateRing (f a)`
- **What**: Shows that `CoordinateRing.map f` commutes with `algebraMap` on base constants: applying a ring homomorphism to the base field then embedding is the same as embedding then mapping. This is the coordinate-ring shadow of "a field map acts on the constant coefficients."
- **How**: Unfolds `algebraMap` as `(AdjoinRoot.of polynomial) ∘ (algebraMap R R[X])`, rewrites via `CoordinateRing.map_mk`, uses `Polynomial.map_C` + `coe_mapRingHom` to simplify the polynomial, and verifies both sides are `AdjoinRoot.mk` applied to `C (C (f a))`.
- **Hypotheses**: `R`, `S` are commutative rings; `W'` is an affine Weierstrass curve over `R`; `f : R →+* S` is a ring homomorphism.
- **Uses from project**: none
- **Used by**: `ffFrobEquivRaw_algebraMap` (calls it at line 229)
- **Visibility**: public
- **Lines**: 72–89, proof ~17 lines
- **Notes**: Generic (no base-change specialisation); lives outside the `BaseChange` section.

---

### `noncomputable abbrev coeffFrobEquiv`
- **Type**: `coeffFrobEquiv : AlgebraicClosure K ≃+* AlgebraicClosure K`
- **What**: The q-power coefficient Frobenius `a ↦ a^q` on `K̄ = AlgebraicClosure K`, as a ring equivalence. Defined as the `toRingEquiv` of `FiniteField.frobeniusAlgEquivOfAlgebraic K K̄`.
- **How**: Direct abbreviation of `(FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toRingEquiv`.
- **Hypotheses**: `K` is a finite field (with `[Field K] [Fintype K] [DecidableEq K]`).
- **Uses from project**: none
- **Used by**: `coeffFrobEquiv_apply`, `crFrobEquiv`, `ffFrobEquivRaw`, `map_coeffFrobEquiv_eq`, `ffFrobCast`, `ffFrobEquivRaw_algebraMap`, `ffFrobCast_algebraMap`; also heavily used by `FrobeniusConjugation.lean`, `FrobeniusDivisorGalois.lean`
- **Visibility**: public
- **Lines**: 102–103, 1-line body
- **Notes**: `noncomputable`, `abbrev` (not `def`) so it unfolds transparently.

---

### `@[simp] theorem coeffFrobEquiv_apply`
- **Type**: `(a : AlgebraicClosure K) : coeffFrobEquiv (K := K) a = a ^ Fintype.card K`
- **What**: Evaluates the coefficient Frobenius: `coeffFrobEquiv a = a ^ #K`.
- **How**: Unfolds `coeffFrobEquiv` as the `frobeniusAlgEquivOfAlgebraic` and rewrites with `FiniteField.coe_frobeniusAlgEquivOfAlgebraic`.
- **Hypotheses**: Same as `coeffFrobEquiv`.
- **Uses from project**: none
- **Used by**: `ffFrobEquivRaw_algebraMap` (line 231)
- **Visibility**: public, `@[simp]`
- **Lines**: 105–109, proof 3 lines

---

### `theorem frobeniusGalois_baseChange_map_eq`
- **Type**: `(W.baseChange (AlgebraicClosure K)).map (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom.toRingHom = W.baseChange (AlgebraicClosure K)`
- **What**: The Frobenius `e` fixes the Weierstrass curve `W.baseChange K̄`: mapping the base-changed curve along `e` (which is a K-algebra map, hence fixes `algebraMap K K̄`) returns the same curve.
- **How**: Uses `WeierstrassCurve.map_map` to reduce to a coefficient-level identity, then `AlgEquiv.commutes` to show `e.toAlgHom ∘ algebraMap K K̄ = algebraMap K K̄` pointwise.
- **Hypotheses**: `W` is an elliptic curve over finite field `K`.
- **Uses from project**: none
- **Used by**: `map_coeffFrobEquiv_eq`
- **Visibility**: public
- **Lines**: 114–125, proof ~10 lines

---

### `theorem coordRingMap_surjective`
- **Type**: `(e : AlgebraicClosure K ≃+* AlgebraicClosure K) : Function.Surjective (CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine (e : AlgebraicClosure K →+* AlgebraicClosure K))`
- **What**: `CoordinateRing.map e` is surjective when `e` is a ring equivalence: every element `mk q` in the target is hit by `mk (q.map (mapRingHom e.symm))`.
- **How**: Uses `AdjoinRoot.mk_surjective` to get a representative polynomial, then constructs a preimage via `q.map (mapRingHom e.symm)` and verifies round-trip via `Polynomial.map_map` + a `Polynomial.ringHom_ext` argument showing `(mapRingHom e) ∘ (mapRingHom e.symm) = id`.
- **Hypotheses**: `W` has an isElliptic base-changed curve; `e : K̄ ≃+* K̄` is a ring equiv.
- **Uses from project**: none
- **Used by**: `coordRingMap_bijective`
- **Visibility**: public
- **Lines**: 128–149, proof ~21 lines

---

### `theorem coordRingMap_bijective`
- **Type**: `(e : AlgebraicClosure K ≃+* AlgebraicClosure K) : Function.Bijective (CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine (e : AlgebraicClosure K →+* AlgebraicClosure K))`
- **What**: `CoordinateRing.map e` is bijective for a ring equivalence `e`, combining injectivity (from `CoordinateRing.map_injective`) and surjectivity (from `coordRingMap_surjective`).
- **How**: Direct combination of `CoordinateRing.map_injective` (using `EquivLike.injective e`) and `coordRingMap_surjective W e`.
- **Hypotheses**: Same as `coordRingMap_surjective`.
- **Uses from project**: `coordRingMap_surjective`
- **Used by**: `crFrobEquiv`
- **Visibility**: public
- **Lines**: 151–157, proof 3 lines (term-mode)

---

### `noncomputable def crFrobEquiv`
- **Type**: `crFrobEquiv W : (W.baseChange K̄).toAffine.CoordinateRing ≃+* ((W.baseChange K̄).map coeffFrobEquiv).toAffine.CoordinateRing`
- **What**: Packages the bijective `CoordinateRing.map (coeffFrobEquiv)` as a proper ring isomorphism, via `RingEquiv.ofBijective`.
- **How**: `RingEquiv.ofBijective _ (coordRingMap_bijective W (coeffFrobEquiv K))`.
- **Hypotheses**: `W` is an isElliptic curve over a finite field `K`.
- **Uses from project**: `coordRingMap_bijective`, `coeffFrobEquiv`
- **Used by**: `crFrobEquiv_apply`, `ffFrobEquivRaw`, `ffFrobEquivRaw_algebraMap` (via `crFrobEquiv_apply`)
- **Visibility**: public
- **Lines**: 161–165, 1-line body

---

### `@[simp] theorem crFrobEquiv_apply`
- **Type**: `(z : (W.baseChange K̄).toAffine.CoordinateRing) : crFrobEquiv W z = CoordinateRing.map (W.baseChange K̄).toAffine coeffFrobEquiv z`
- **What**: Evaluates `crFrobEquiv` as plain `CoordinateRing.map coeffFrobEquiv`.
- **How**: `rfl` (definitional equality).
- **Hypotheses**: Same as `crFrobEquiv`.
- **Uses from project**: `crFrobEquiv`, `coeffFrobEquiv`
- **Used by**: `ffFrobEquivRaw_algebraMap`
- **Visibility**: public, `@[simp]`
- **Lines**: 167–170, proof is `rfl`

---

### `noncomputable def ffFrobEquivRaw`
- **Type**: `ffFrobEquivRaw W : (W.baseChange K̄).toAffine.FunctionField ≃+* ((W.baseChange K̄).map coeffFrobEquiv).toAffine.FunctionField`
- **What**: Lifts `crFrobEquiv` from the coordinate ring to the fraction field (function field), giving the raw Frobenius `K̄(E) ≃+* K̄(E.map e)` (before the codomain-cast back to `K̄(E)`).
- **How**: `IsFractionRing.ringEquivOfRingEquiv (crFrobEquiv W)`.
- **Hypotheses**: Same as `crFrobEquiv`.
- **Uses from project**: `crFrobEquiv`
- **Used by**: `frobeniusFunctionFieldEquiv`, `ffFrobEquivRaw_algebraMap`; also used by `FrobeniusConjugation.lean`
- **Visibility**: public
- **Lines**: 174–178, 1-line body

---

### `theorem map_coeffFrobEquiv_eq`
- **Type**: `(W.baseChange K̄).map (coeffFrobEquiv : K̄ →+* K̄) = W.baseChange K̄`
- **What**: The Weierstrass curve equality `(W.baseChange K̄).map e = W.baseChange K̄`, rephrased for `coeffFrobEquiv` as a `RingEquiv`-coerced ring hom.
- **How**: Calls `frobeniusGalois_baseChange_map_eq W` and uses `convert ... using 2` to match the coercion form.
- **Hypotheses**: Same as `frobeniusGalois_baseChange_map_eq`.
- **Uses from project**: `frobeniusGalois_baseChange_map_eq`
- **Used by**: `ffFrobCast`, `ffFrobCast_algebraMap`; also used by `FrobeniusDivisorGalois.lean`, `FrobeniusConjugation.lean`
- **Visibility**: public
- **Lines**: 183–188, proof ~5 lines

---

### `noncomputable def ffFrobCast`
- **Type**: `ffFrobCast W : ((W.baseChange K̄).map coeffFrobEquiv).toAffine.FunctionField ≃+* (W.baseChange K̄).toAffine.FunctionField`
- **What**: The codomain cast `K̄(E.map e) ≃+* K̄(E)` using `RingEquiv.cast` along the curve equality `map_coeffFrobEquiv_eq`, returning the Frobenius's codomain to `K̄(E)`.
- **How**: `RingEquiv.cast (R := fun V => V.toAffine.FunctionField) (map_coeffFrobEquiv_eq W)`.
- **Hypotheses**: Same as `map_coeffFrobEquiv_eq`.
- **Uses from project**: `map_coeffFrobEquiv_eq`
- **Used by**: `frobeniusFunctionFieldEquiv`, `ffFrobCast_algebraMap`; also used by `FrobeniusConjugation.lean`
- **Visibility**: public
- **Lines**: 191–196, 2-line body

---

### `noncomputable def frobeniusFunctionFieldEquiv`
- **Type**: `frobeniusFunctionFieldEquiv W : (W.baseChange K̄).toAffine.FunctionField ≃+* (W.baseChange K̄).toAffine.FunctionField`
- **What**: The arithmetic Frobenius automorphism `σ` of `K̄(E)`: the q-power Frobenius on K̄-coefficients lifted to a ring automorphism of the function field. Acts as `a ↦ a^q` on constants, fixes the 𝔽_q-rational generators.
- **How**: Composition `(ffFrobEquivRaw W).trans (ffFrobCast W)` — fraction-field lift followed by codomain cast. The `RingEquiv.cast` approach (not `▸`) avoids whnf timeout on the curve-indexed `FunctionField`.
- **Hypotheses**: `K` finite field; `W` an isElliptic Weierstrass curve over `K`; the base-changed curve `W.baseChange K̄` is also isElliptic.
- **Uses from project**: `ffFrobEquivRaw`, `ffFrobCast`
- **Used by**: `frobeniusFunctionFieldEquiv_algebraMap`; externally used by `FrobeniusConjugation.lean`, `FrobeniusGaloisScaling.lean`
- **Visibility**: public
- **Lines**: 203–206, 1-line body

---

### `theorem ffFrobEquivRaw_algebraMap`
- **Type**: `(a : K̄) : ffFrobEquivRaw W (algebraMap K̄ (W.baseChange K̄).toAffine.FunctionField a) = algebraMap K̄ ((W.baseChange K̄).map coeffFrobEquiv).toAffine.FunctionField (a ^ Fintype.card K)`
- **What**: The raw Frobenius `ffFrobEquivRaw` sends the base constant `algebraMap a` to `algebraMap (a^q)` in the mapped function field.
- **How**: Uses `IsScalarTower.algebraMap_apply` to factor the algebraMap through the coordinate ring, then `IsFractionRing.ringEquivOfRingEquiv_algebraMap` to push through the fraction-field lift, then `crFrobEquiv_apply` + `coordRingMap_algebraMap_base` at the coordinate-ring level, and finally `coeffFrobEquiv_apply` to get `a^#K`.
- **Hypotheses**: Same as `frobeniusFunctionFieldEquiv`.
- **Uses from project**: `ffFrobEquivRaw`, `crFrobEquiv_apply`, `coordRingMap_algebraMap_base`, `coeffFrobEquiv_apply`, `coeffFrobEquiv`
- **Used by**: `frobeniusFunctionFieldEquiv_algebraMap`
- **Visibility**: public
- **Lines**: 214–231, proof ~17 lines

---

### `theorem ffFrobCast_algebraMap`
- **Type**: `(b : K̄) : ffFrobCast W (algebraMap K̄ ((W.baseChange K̄).map coeffFrobEquiv).toAffine.FunctionField b) = algebraMap K̄ (W.baseChange K̄).toAffine.FunctionField b`
- **What**: The codomain cast `ffFrobCast` fixes base constants: `RingEquiv.cast` along the curve equality acts as the identity on `algebraMap b`.
- **How**: Unfolds `ffFrobCast`, then proves a helper `key` that for any `V` and `h : V = W.baseChange K̄`, the cast sends `algebraMap b` to `algebraMap b` — discharged by `subst h; rfl` — then applies it via `map_coeffFrobEquiv_eq W`.
- **Hypotheses**: Same as `frobeniusFunctionFieldEquiv`.
- **Uses from project**: `ffFrobCast`, `map_coeffFrobEquiv_eq`
- **Used by**: `frobeniusFunctionFieldEquiv_algebraMap`
- **Visibility**: public
- **Lines**: 236–250, proof ~14 lines

---

### `theorem frobeniusFunctionFieldEquiv_algebraMap`
- **Type**: `(a : K̄) : frobeniusFunctionFieldEquiv W (algebraMap K̄ (W.baseChange K̄).toAffine.FunctionField a) = algebraMap K̄ (W.baseChange K̄).toAffine.FunctionField (a ^ Fintype.card K)`
- **What**: The main result: the arithmetic Frobenius `σ` q-powers the K̄-constants, `σ(algebraMap a) = algebraMap (a^#K)`. This is the "elementary leaf" of `FrobeniusGaloisData`.
- **How**: Expands `frobeniusFunctionFieldEquiv` as `ffFrobEquivRaw.trans ffFrobCast`, uses `RingEquiv.trans_apply`, then chains `ffFrobEquivRaw_algebraMap` (raw lift q-powers) with `ffFrobCast_algebraMap` (cast fixes constants).
- **Hypotheses**: Same as `frobeniusFunctionFieldEquiv`.
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `ffFrobEquivRaw_algebraMap`, `ffFrobCast_algebraMap`
- **Used by**: unused within this file (leaf theorem for external consumers); externally used by `FrobeniusConjugation.lean` (lines 242, 329, 331, 477) and `FrobeniusGaloisScaling.lean` (line 308)
- **Visibility**: public
- **Lines**: 256–262, proof ~6 lines

---

## Cross-reference summary

| Declaration | Used by (internal) |
|---|---|
| `coordRingMap_algebraMap_base` | `ffFrobEquivRaw_algebraMap` |
| `coeffFrobEquiv` | `coeffFrobEquiv_apply`, `crFrobEquiv`, `ffFrobEquivRaw`, `map_coeffFrobEquiv_eq`, `ffFrobCast`, `ffFrobEquivRaw_algebraMap`, `ffFrobCast_algebraMap` |
| `coeffFrobEquiv_apply` | `ffFrobEquivRaw_algebraMap` |
| `frobeniusGalois_baseChange_map_eq` | `map_coeffFrobEquiv_eq` |
| `coordRingMap_surjective` | `coordRingMap_bijective` |
| `coordRingMap_bijective` | `crFrobEquiv` |
| `crFrobEquiv` | `crFrobEquiv_apply`, `ffFrobEquivRaw` |
| `crFrobEquiv_apply` | `ffFrobEquivRaw_algebraMap` |
| `ffFrobEquivRaw` | `frobeniusFunctionFieldEquiv`, `ffFrobEquivRaw_algebraMap` |
| `map_coeffFrobEquiv_eq` | `ffFrobCast`, `ffFrobCast_algebraMap` |
| `ffFrobCast` | `frobeniusFunctionFieldEquiv`, `ffFrobCast_algebraMap` |
| `frobeniusFunctionFieldEquiv` | `frobeniusFunctionFieldEquiv_algebraMap` |
| `ffFrobEquivRaw_algebraMap` | `frobeniusFunctionFieldEquiv_algebraMap` |
| `ffFrobCast_algebraMap` | `frobeniusFunctionFieldEquiv_algebraMap` |
| `frobeniusFunctionFieldEquiv_algebraMap` | unused internally (external leaf) |

**Key API** (used by 3+ others in this file): `coeffFrobEquiv` (used by 7 declarations).
