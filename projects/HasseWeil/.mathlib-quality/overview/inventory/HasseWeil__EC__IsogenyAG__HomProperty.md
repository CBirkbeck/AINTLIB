# Inventory: ./HasseWeil/EC/IsogenyAG/HomProperty.lean

**File**: `HasseWeil/EC/IsogenyAG/HomProperty.lean`
**Lines**: 1–229
**Imports**: `HasseWeil.Curves.PicZero`, `HasseWeil.Curves.PicZeroPushforward`
**Namespace**: `HasseWeil.EC.Isogeny`

**Summary**: Witness-parametric proof of Silverman III.4.8 (isogenies are group homomorphisms on K-rational points). The argument factors through Pic⁰: build σ̄ : Pic⁰(E) → E·Point and φ_∗ : Pic⁰(E₁) → Pic⁰(E₂) from open witnesses (T-PIC-A-002, T-PIC-C-003, T-III-3-003), observe diagram commutativity via a divisor-level identity, and derive additivity by a calc chain through κ ∘ σ̄ = id.

No sorries, no `set_option maxHeartbeats`, 5 declarations total (2 defs, 3 theorems, 0 instances).

---

## Declarations

---

### `noncomputable def picZeroSumOfWitness`

- **Type**:
  ```
  (W : Affine F) [W.IsElliptic]
  (h_van : ∀ D : ProjectiveDivisor ⟨W⟩, D ∈ projPrincipalSubgroup → projectiveDivisorSum W D = 0)
  → PicProj₀ ⟨W⟩ →+ W.Point
  ```
- **What**: Descends the divisor sum map σ̄ to the Pic⁰ level; constructs the additive group homomorphism PicProj₀(W) → W.Point from the restricted map on degree-zero divisors, given the witness that σ vanishes on principal divisors (T-PIC-A-002).
- **How**: Forms the restricted hom via `projectiveDivisorSumHom W` composed with the `degZero` subtype inclusion, then lifts through `QuotientAddGroup.lift` using `h_van` to show the principal subgroup maps to zero.
- **Hypotheses**: W is an elliptic curve; h_van = the witness that σ vanishes on any principal projective divisor.
- **Uses from project**: `Curves.projectiveDivisorSumHom`, `Curves.ProjectiveDivisor.degZero`, `SmoothPlaneCurve.projPrincipalSubgroup`, `Curves.projectiveDivisorSum`.
- **Used by**: `picZeroSumOfWitness_apply_mk`, `picZeroSumOfWitness_picZeroOfPoint`, `AddHomProperty_of_picZero_witnesses`.
- **Visibility**: public
- **Lines**: 50–70, proof inline (~5 lines in the `fun D hD =>` branch)
- **Notes**: noncomputable; key API exported to `NoFinitePolesBridge.lean`, `AFConditional.lean`, `MillerAllChar.lean`.

---

### `@[simp] theorem picZeroSumOfWitness_apply_mk`

- **Type**:
  ```
  picZeroSumOfWitness W h_van (QuotientAddGroup.mk D) = projectiveDivisorSum W D.val
  ```
- **What**: simp lemma unfolding the action of `picZeroSumOfWitness` on a quotient representative: applying σ̄ at `[D]` equals σ(D.val).
- **How**: Proved by `rfl` — follows immediately from the `QuotientAddGroup.lift` definition.
- **Hypotheses**: Same as `picZeroSumOfWitness`.
- **Uses from project**: `picZeroSumOfWitness` (from this file), `Curves.projectiveDivisorSum`.
- **Used by**: `picZeroSumOfWitness_picZeroOfPoint`, `AddHomProperty_of_picZero_witnesses` (indirectly via simp in AFConditional/MillerAllChar).
- **Visibility**: public (simp tagged)
- **Lines**: 72–80, proof length: 1 line (`rfl`)
- **Notes**: None.

---

### `@[simp] theorem picZeroSumOfWitness_picZeroOfPoint`

- **Type**:
  ```
  picZeroSumOfWitness W h_van (picZeroOfPoint W P) = P
  ```
- **What**: The composition σ̄ ∘ κ = id at the Pic⁰ level; applying `picZeroSumOfWitness` to the Pic⁰ class of a point P recovers P.
- **How**: Unfolds `picZeroOfPoint`, applies `picZeroSumOfWitness_apply_mk`, then uses the divisor-level identity `Curves.projectiveDivisorSum_kappaDivisor W P` (which says σ((P)−(O)) = P).
- **Hypotheses**: Same as `picZeroSumOfWitness`; P a rational point of W.
- **Uses from project**: `picZeroSumOfWitness_apply_mk` (this file), `Curves.picZeroOfPoint`, `Curves.projectiveDivisorSum_kappaDivisor`.
- **Used by**: `AddHomProperty_of_picZero_witnesses` (via `h_easy_W₁`, `h_easy_W₂`).
- **Visibility**: public (simp tagged)
- **Lines**: 84–93, proof length: 4 lines
- **Notes**: Key "easy direction" of the κ/σ̄ inverse pair. Used extensively in `AFConditional.lean`, `MillerAllChar.lean`, `NoFinitePolesBridge.lean`.

---

### `noncomputable def pushforwardPicZeroOfWitness`

- **Type**:
  ```
  (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
  (h_pres : ∀ D : ProjectiveDivisor ⟨W₁⟩, D ∈ projPrincipalSubgroup → pushforwardProjectiveDivisor φ cd D ∈ projPrincipalSubgroup)
  → PicProj₀ ⟨W₁⟩ →+ PicProj₀ ⟨W₂⟩
  ```
- **What**: Descends the divisor pushforward φ_∗ to the Pic⁰ level; constructs an additive hom PicProj₀(W₁) → PicProj₀(W₂) given the witness that φ_∗ maps principal divisors to principal divisors (T-PIC-C-003).
- **How**: Composes `QuotientAddGroup.mk'` with `pushforwardDegZero φ cd` to get a hom into the quotient, then lifts through `QuotientAddGroup.lift`. In the well-definedness check, rewrites via `QuotientAddGroup.mk'_apply` and `QuotientAddGroup.eq_zero_iff`, then applies `h_pres`.
- **Hypotheses**: φ is an isogeny with CoordHom `cd`; h_pres = the witness that pushforward preserves principal divisors.
- **Uses from project**: `pushforwardProjectiveDivisor` (from PicZeroPushforward), `pushforwardDegZero` (from PicZeroPushforward), `SmoothPlaneCurve.projPrincipalSubgroup`.
- **Used by**: `picZeroOfPoint_pushforwardPicZero`, `AddHomProperty_of_picZero_witnesses`.
- **Visibility**: public
- **Lines**: 102–128, proof inline (~10 lines in well-definedness branch)
- **Notes**: noncomputable; closes T-PIC-C-004 witness-parametrically.

---

### `theorem picZeroOfPoint_pushforwardPicZero`

- **Type**:
  ```
  (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) (h_pres : ...) (P : W₁.Point) :
  picZeroOfPoint W₂ (φ.toPointMap cd P) = pushforwardPicZeroOfWitness φ cd h_pres (picZeroOfPoint W₁ P)
  ```
- **What**: The Pic⁰-level diagram commutes: κ(φP) = φ_∗(κP), i.e., the κ maps and the pushforward form a commutative square.
- **How**: Both sides reduce to `QuotientAddGroup.mk` of Subtype-wrapped divisors. Equality follows by `congr 1; Subtype.ext` reducing to divisor-level equality, which is `pushforwardProjectiveDivisor_kappaDivisor φ cd P` (from PicZeroPushforward).
- **Hypotheses**: φ an isogeny with CoordHom; h_pres the preserves-principal witness; P a rational point of W₁.
- **Uses from project**: `pushforwardPicZeroOfWitness` (this file), `Curves.picZeroOfPoint`, `pushforwardProjectiveDivisor_kappaDivisor` (from PicZeroPushforward).
- **Used by**: `AddHomProperty_of_picZero_witnesses`.
- **Visibility**: public
- **Lines**: 135–151, proof length: 6 lines
- **Notes**: Closes T-PIC-D-001 witness-parametrically.

---

### `theorem AddHomProperty_of_picZero_witnesses`

- **Type**:
  ```
  (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
  (h_van_W₁ : ...) (h_van_W₂ : ...) (h_pres : ...) (h_inj_W₁ : ∀ D, picZeroOfPoint W₁ (picZeroSumOfWitness W₁ h_van_W₁ D) = D)
  → φ.AddHomProperty cd
  ```
- **What**: The universal witness-parametric closure of Silverman III.4.8: given witnesses for σ-vanishing-on-principals (for both curves), pushforward-preserves-principals, and κ-injectivity (equivalently κ ∘ σ̄ = id), concludes that φ is a group homomorphism on rational points.
- **How**: Sets up sb1, sb2 (σ̄ at Pic⁰), pushPic (φ_∗ at Pic⁰). Derives sb1-injectivity from h_inj_W₁ (κ ∘ σ̄ = id gives left inverse). Derives κ-additivity (κ(P+Q) = κP + κQ) using sb1-injectivity and the easy direction (sb1 ∘ κ = id) and sb1 being a hom. Then a calc chain: φ(P+Q) = sb2(κ(φ(P+Q))) = sb2(pushPic(κ(P+Q))) = sb2(pushPic(κP+κQ)) = sb2(pushPic(κP)+pushPic(κQ)) = φP+φQ, using `picZeroOfPoint_pushforwardPicZero` for the diagram commute step and `h_easy_W₂` to cancel at the end.
- **Hypotheses**: φ an isogeny with CoordHom; witnesses h_van_W₁, h_van_W₂ (T-PIC-A-002 for both curves), h_pres (T-PIC-C-003), h_inj_W₁ (T-III-3-003, κ ∘ σ̄ = id on W₁).
- **Uses from project**: `picZeroSumOfWitness` (this file), `pushforwardPicZeroOfWitness` (this file), `picZeroSumOfWitness_picZeroOfPoint` (this file), `picZeroOfPoint_pushforwardPicZero` (this file), `Curves.picZeroOfPoint`, `Isogeny.AddHomProperty`.
- **Used by**: `AFConditional.lean` (externally, as the main theorem instantiated with the three witnesses).
- **Visibility**: public
- **Lines**: 165–229, proof length: ~65 lines
- **Notes**: Proof > 30 lines. This is the main theorem of the file. The calc chain faithfully formalizes the Silverman III.4.8 diagram argument.

---

## Cross-Reference Summary

| Declaration | Used by (in file) | Used by (external files) |
|---|---|---|
| `picZeroSumOfWitness` | `picZeroSumOfWitness_apply_mk`, `picZeroSumOfWitness_picZeroOfPoint`, `AddHomProperty_of_picZero_witnesses` | `NoFinitePolesBridge`, `AFConditional`, `MillerAllChar` |
| `picZeroSumOfWitness_apply_mk` | `picZeroSumOfWitness_picZeroOfPoint` | `AFConditional` |
| `picZeroSumOfWitness_picZeroOfPoint` | `AddHomProperty_of_picZero_witnesses` | `NoFinitePolesBridge`, `AFConditional`, `MillerAllChar` |
| `pushforwardPicZeroOfWitness` | `picZeroOfPoint_pushforwardPicZero`, `AddHomProperty_of_picZero_witnesses` | (none found) |
| `picZeroOfPoint_pushforwardPicZero` | `AddHomProperty_of_picZero_witnesses` | (none found) |
| `AddHomProperty_of_picZero_witnesses` | (none in file) | `AFConditional` |
