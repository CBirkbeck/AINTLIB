# Inventory: ./HasseWeil/Curves/PicZeroPushforward.lean

**File**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Lines**: 132
**Imports**: `HasseWeil.Curves.PicZero`, `HasseWeil.EC.IsogenyAG`
**Namespace**: `HasseWeil.EC.Isogeny`
**Total declarations**: 7 (2 defs, 5 lemmas/theorems, 0 instances)

---

## Variable context

```
{F : Type*} [Field F] [DecidableEq F]
{W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
```

All declarations in this file live under these variables.

---

### `noncomputable def pushforwardProjectiveDivisor`

- **Type**: `(φ : Isogeny W₁ W₂) → (cd : φ.toCurveMap.CoordHom) → ProjectiveDivisor ⟨W₁⟩ →+ ProjectiveDivisor ⟨W₂⟩`
- **What**: Defines the additive-monoid-hom pushforward of projective divisors `Σ nᵢ(Pᵢ)` to `Σ nᵢ(φ(Pᵢ))`, where the point map is `φ.toPointMap cd` composed with `.toProjectiveSmoothPoint`.
- **How**: One-liner using `Finsupp.mapDomain.addMonoidHom` applied to the point-reindexing function; all additive-hom structure is free from the `Finsupp` API.
- **Hypotheses**: An isogeny `φ : Isogeny W₁ W₂` with a coordinate-ring witness `cd : φ.toCurveMap.CoordHom`.
- **Uses from project**: `Isogeny.toPointMap`, `Affine.Point.toProjectiveSmoothPoint`, `ProjectiveSmoothPoint.toAffinePoint`
- **Used by**: `pushforwardProjectiveDivisor_apply`, `pushforwardProjectiveDivisor_zero`, `pushforwardProjectiveDivisor_add`, `pushforwardProjectiveDivisor_single`, `degree_pushforwardProjectiveDivisor`, `pushforwardDegZero`, `pushforwardProjectiveDivisor_kappaDivisor`
- **Visibility**: public
- **Lines**: 36–42, proof length: 1 line (definitional)
- **Notes**: Key API export — used by `HomProperty.lean` in `IsogenyAG`.

---

### `@[simp] theorem pushforwardProjectiveDivisor_apply`

- **Type**: `pushforwardProjectiveDivisor φ cd D = Finsupp.mapDomain (fun P => (φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint) D`
- **What**: Unfolds the definition of `pushforwardProjectiveDivisor` to expose the underlying `Finsupp.mapDomain` computation.
- **How**: Proved by `rfl` — the definition is definitionally equal to the RHS.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor`
- **Used by**: `pushforwardProjectiveDivisor_single`, `degree_pushforwardProjectiveDivisor`, `pushforwardProjectiveDivisor_kappaDivisor`
- **Visibility**: public (simp lemma)
- **Lines**: 43–48, proof length: 1 line
- **Notes**: None.

---

### `@[simp] theorem pushforwardProjectiveDivisor_zero`

- **Type**: `pushforwardProjectiveDivisor φ cd 0 = 0`
- **What**: The pushforward of the zero divisor is zero, i.e., the hom preserves the additive identity.
- **How**: Immediate from `AddMonoidHom.map_zero` applied to `pushforwardProjectiveDivisor φ cd`.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor`
- **Used by**: unused in file (but exported for callers)
- **Visibility**: public (simp lemma)
- **Lines**: 50–53, proof length: 1 line
- **Notes**: None.

---

### `@[simp] theorem pushforwardProjectiveDivisor_add`

- **Type**: `pushforwardProjectiveDivisor φ cd (D₁ + D₂) = pushforwardProjectiveDivisor φ cd D₁ + pushforwardProjectiveDivisor φ cd D₂`
- **What**: The pushforward is additive, i.e., it is a homomorphism of divisor groups.
- **How**: Immediate from `AddMonoidHom.map_add` applied to `pushforwardProjectiveDivisor φ cd`.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor`
- **Used by**: unused in file (but exported for callers)
- **Visibility**: public (simp lemma)
- **Lines**: 55–60, proof length: 1 line
- **Notes**: None.

---

### `@[simp] theorem pushforwardProjectiveDivisor_single`

- **Type**: `pushforwardProjectiveDivisor φ cd (Finsupp.single P n) = Finsupp.single ((φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint) n`
- **What**: The pushforward of a single-point divisor `n·(P)` is the single-point divisor `n·(φ(P))`.
- **How**: Uses `pushforwardProjectiveDivisor_apply` to unfold and then `Finsupp.mapDomain_single` from mathlib.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor_apply`, `pushforwardProjectiveDivisor`
- **Used by**: unused in file (but exported for callers)
- **Visibility**: public (simp lemma)
- **Lines**: 62–70, proof length: 2 lines
- **Notes**: None.

---

### `theorem degree_pushforwardProjectiveDivisor`

- **Type**: `ProjectiveDivisor.degree (pushforwardProjectiveDivisor φ cd D) = ProjectiveDivisor.degree D`
- **What**: The total degree of a projective divisor is preserved by the pushforward; the point-reindexing does not change the sum of multiplicities.
- **How**: Uses `pushforwardProjectiveDivisor_apply` to expose `Finsupp.mapDomain`, then applies `Finsupp.sum_mapDomain_index` with trivial linearity witnesses `(fun _ => rfl)` and `(fun _ _ _ => rfl)`.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor_apply`, `Curves.ProjectiveDivisor.degree`
- **Used by**: `pushforwardDegZero`
- **Visibility**: public
- **Lines**: 76–84, proof length: 4 lines
- **Notes**: None.

---

### `noncomputable def pushforwardDegZero`

- **Type**: `(φ : Isogeny W₁ W₂) → (cd : φ.toCurveMap.CoordHom) → ProjectiveDivisor.degZero ⟨W₁⟩ →+ ProjectiveDivisor.degZero ⟨W₂⟩`
- **What**: Restricts the divisor pushforward to the degree-zero subgroup `Div⁰`, producing an additive-group hom on `Div⁰(W₁) → Div⁰(W₂)`.
- **How**: Built by the anonymous constructor for `AddMonoidHom` on subtype; the `toFun` wraps `pushforwardProjectiveDivisor` and uses `degree_pushforwardProjectiveDivisor` + `ProjectiveDivisor.mem_degZero` to verify degree zero is preserved; `map_zero'` and `map_add'` delegate to the underlying hom.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `pushforwardProjectiveDivisor`, `degree_pushforwardProjectiveDivisor`, `Curves.ProjectiveDivisor.mem_degZero`, `Curves.ProjectiveDivisor.degZero`
- **Used by**: unused in file (exported; used in `HomProperty.lean`)
- **Visibility**: public
- **Lines**: 88–106, proof length: 18 lines (across `toFun`/`map_zero'`/`map_add'` fields)
- **Notes**: None.

---

### `theorem pushforwardProjectiveDivisor_kappaDivisor`

- **Type**: `pushforwardProjectiveDivisor φ cd (Curves.kappaDivisor W₁ P) = Curves.kappaDivisor W₂ (φ.toPointMap cd P)`
- **What**: The divisor-level diagram commutes: pushing the point-to-class divisor `κ(P) = (P) − (O)` through `φ` gives `κ(φ(P)) = (φ(P)) − (O)` on `W₂`. This is the precursor to the Pic⁰-level functoriality (T-PIC-D-001).
- **How**: Establishes `φ(0) = 0` via `Isogeny.toPointMap_zero`, unfolds `kappaDivisor` via `unfold`, then applies `simp` with `pushforwardProjectiveDivisor_single`, the simp lemmas `toProjectiveSmoothPoint_toAffinePoint`, `toAffinePoint_infinity`, and `toProjectiveSmoothPoint_zero`.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `Isogeny.toPointMap_zero`, `pushforwardProjectiveDivisor_single`, `Curves.kappaDivisor`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`, `Curves.ProjectiveSmoothPoint.toAffinePoint_infinity`, `Affine.Point.toProjectiveSmoothPoint_zero`
- **Used by**: unused in file (exported; used in `HomProperty.lean`)
- **Visibility**: public
- **Lines**: 120–131, proof length: 10 lines
- **Notes**: Comment in the docstring correctly identifies this as the divisor-level fact needed for T-PIC-D-001.

---

## Summary statistics

| Category | Count |
|---|---|
| `noncomputable def` | 2 |
| `@[simp] theorem` / `theorem` | 5 |
| `instance` | 0 |
| **Total** | **7** |

- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none
- **Key API** (used by 3+ others in file): `pushforwardProjectiveDivisor` (used by all 5 theorems and `pushforwardDegZero`)
- **Unused in file** (dead-code candidates): `pushforwardProjectiveDivisor_zero`, `pushforwardProjectiveDivisor_add`, `pushforwardProjectiveDivisor_single`, `pushforwardDegZero`, `pushforwardProjectiveDivisor_kappaDivisor` (all used by callers in other files, notably `HomProperty.lean`)
