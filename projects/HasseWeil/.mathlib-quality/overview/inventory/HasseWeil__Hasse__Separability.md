# Inventory: ./HasseWeil/Hasse/Separability.lean

**Total lines**: 436  
**Namespace**: `HasseWeil` (top level), `HasseWeil.Isogeny` (lines 249–336), `HasseWeil.Conditional` (lines 410–434)  
**Module header**: Witness-parametric Silverman III.5.5 and V.1.2

---

## Declarations

### `theorem isSeparable_iff_of_coeff_witness`
- **Type**: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] (β : Isogeny W.toAffine W.toAffine) (c : F) (h_coeff : omegaPullbackCoeff W β = algebraMap F _ c) (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) : β.IsSeparable ↔ c ≠ 0`
- **What**: The core witness-parametric separability criterion: given that the ω-pullback coefficient of β equals the algebraMap image of some scalar c, and that IsSeparable ↔ coefficient ≠ 0, concludes IsSeparable ↔ c ≠ 0 in the base field.
- **How**: Two rewrites: `h_sep_iff`, then `h_coeff`, then `map_ne_zero_iff` with injectivity of `algebraMap`. The argument is a chain of iff-substitutions using field injectivity.
- **Hypotheses**: β is an isogeny on an elliptic curve, h_coeff gives the algebraMap form of the ω-pullback coefficient, h_sep_iff is the T-II-4-004 separability criterion for β.
- **Uses from project**: `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: `m_plus_n_frob_isSeparable_iff_of_witness`, `oneSubFrobenius_isSeparable_of_witness` (both in this file)
- **Visibility**: public
- **Lines**: 67–76, proof ~3 lines
- **Notes**: Foundational wrapper; proof is a 1-line rewrite chain.

---

### `theorem m_plus_n_frob_isSeparable_iff_of_witness`
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (m : ℤ) (β : Isogeny W.toAffine W.toAffine) (h_coeff : omegaPullbackCoeff W β = algebraMap K _ m) (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) : β.IsSeparable ↔ (m : K) ≠ 0`
- **What**: Specializes `isSeparable_iff_of_coeff_witness` to the case where the coefficient witness is an integer cast `(m : K)`, implementing Silverman III.5.5 for m + n·π type isogenies.
- **How**: Direct application of `isSeparable_iff_of_coeff_witness` with `c := (m : K)`.
- **Hypotheses**: Same as `isSeparable_iff_of_coeff_witness`, with c specialized to an integer cast.
- **Uses from project**: `isSeparable_iff_of_coeff_witness` (this file), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: `mulByInt_isSeparable_of_witness` (this file)
- **Visibility**: public
- **Lines**: 91–100, proof ~1 line (term-mode)
- **Notes**: Silverman III.5.5 reference.

---

### `theorem oneSubFrobenius_isSeparable_of_witness`
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (β : Isogeny W.toAffine W.toAffine) (h_coeff : omegaPullbackCoeff W β = 1) (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) : β.IsSeparable`
- **What**: Witness-parametric V.1.2: if the ω-pullback coefficient of β is 1 and the T-II-4-004 criterion holds, then β is separable. Implements Silverman V.1.2 (1 − π is separable) in witness form.
- **How**: Rewrites h_coeff via `map_one` to get algebraMap form, applies `isSeparable_iff_of_coeff_witness` with c = 1, then closes by `one_ne_zero`.
- **Hypotheses**: h_coeff = the III.5.3+III.5.2 combination giving coefficient 1; h_sep_iff = T-II-4-004 for β.
- **Uses from project**: `isSeparable_iff_of_coeff_witness` (this file), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: Used externally by `HasseWeil/Hasse/OneSubFrobenius.lean`
- **Visibility**: public
- **Lines**: 113–124, proof ~5 lines
- **Notes**: Silverman V.1.2 reference; directly called by OneSubFrobenius.lean.

---

### `theorem pullbackKaehler_invariantDifferential_of_coeff_witness`
- **Type**: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] (α : Isogeny W.toAffine W.toAffine) (c : F) (h_coeff : omegaPullbackCoeff W α = algebraMap F _ c) : α.pullbackKaehler (invariantDifferential W.toAffine) = c • invariantDifferential W.toAffine`
- **What**: If the ω-pullback coefficient of α equals `algebraMap F _ c`, then the Kähler pullback of ω is `c • ω`. Witness-parametric form of Silverman III.5.1/III.5.3.
- **How**: One `rw` using `Isogeny.pullbackKaehler_invariantDifferential` (InvariantDifferentialPullback.lean), then h_coeff, then `algebraMap_smul`.
- **Hypotheses**: h_coeff connects the ω-pullback coefficient to an algebraMap scalar.
- **Uses from project**: `omegaPullbackCoeff` (OmegaPullbackCoeff.lean), `Isogeny.pullbackKaehler_invariantDifferential` (InvariantDifferentialPullback.lean), `invariantDifferential` (Curves/Differentials.lean)
- **Used by**: `mulByInt_pullbackKaehler_invariantDifferential_of_witness`, `translation_pullbackKaehler_invariantDifferential_of_witness` (this file); externally by `HasseWeil/BridgeFrobenius.lean`
- **Visibility**: public
- **Lines**: 146–154, proof ~1 line
- **Notes**: Key reusable engine; called by 3 other declarations in this file.

---

### `theorem mulByInt_pullbackKaehler_invariantDifferential_of_witness`
- **Type**: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] (m : ℤ) (h_coeff : omegaPullbackCoeff W (mulByInt W.toAffine m) = algebraMap F _ m) : (mulByInt W.toAffine m).pullbackKaehler (invariantDifferential W.toAffine) = (m : F) • invariantDifferential W.toAffine`
- **What**: Witness-parametric Silverman III.5.3: `[m]*ω = m·ω`. Instantiation of the pullback-coefficient witness at the multiplication-by-m isogeny.
- **How**: Direct application of `pullbackKaehler_invariantDifferential_of_coeff_witness` with the multiplication-by-m isogeny and c = (m : F).
- **Hypotheses**: h_coeff = the T-III-5-003 fact that `omegaPullbackCoeff [m] = algebraMap _ m`.
- **Uses from project**: `pullbackKaehler_invariantDifferential_of_coeff_witness` (this file), `mulByInt` (Basic.lean), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 159–168, proof ~2 lines (term-mode)
- **Notes**: Dead code candidate within this file; may be used by external files.

---

### `theorem translation_pullbackKaehler_invariantDifferential_of_witness`
- **Type**: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] (τ : Isogeny W.toAffine W.toAffine) (h_coeff : omegaPullbackCoeff W τ = 1) : τ.pullbackKaehler (invariantDifferential W.toAffine) = invariantDifferential W.toAffine`
- **What**: Witness-parametric Silverman III.5.1 (translation invariance): if the ω-pullback coefficient is 1, then τ*ω = ω.
- **How**: Rewrites h_coeff via `map_one` to algebraMap form, then applies `pullbackKaehler_invariantDifferential_of_coeff_witness` with c = 1 and `one_smul`.
- **Hypotheses**: h_coeff = the characterizing property of translations on invariant differentials.
- **Uses from project**: `pullbackKaehler_invariantDifferential_of_coeff_witness` (this file), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 174–185, proof ~4 lines
- **Notes**: Dead code candidate within this file; Silverman III.5.1 reference.

---

### `theorem mulByInt_isSeparable_of_witness`
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (m : ℤ) (hm : (m : K) ≠ 0) (h_coeff : ...) (h_sep_iff : ...) : (mulByInt W.toAffine m).IsSeparable`
- **What**: Witness-parametric Silverman III.5.4: `[m]` is separable when m ≠ 0 in K.
- **How**: Applies `m_plus_n_frob_isSeparable_iff_of_witness` and closes with `hm`.
- **Hypotheses**: m ≠ 0 in K; h_coeff = T-III-5-003; h_sep_iff = T-II-4-004 for [m].
- **Uses from project**: `m_plus_n_frob_isSeparable_iff_of_witness` (this file), `mulByInt` (Basic.lean), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 201–210, proof ~1 line (term-mode)
- **Notes**: Dead code candidate within this file; Silverman III.5.4. Note: `TorsionSeparable.lean` has its own `mulByInt_isSeparable` routed differently.

---

### `theorem omegaPullbackCoeff_mulByNat_p_eq_zero`
- **Type**: `(p : ℕ) [CharP k p] [Fact (Nat.Prime p)] (E : WeierstrassCurve k) [E.toAffine.IsElliptic] : omegaPullbackCoeff E (mulByInt E.toAffine (p : ℤ)) = 0`
- **What**: In characteristic p, the ω-pullback coefficient of [p] vanishes. This is the T-FROB-OMEGA-ZERO fact (preamble to Silverman III.6.1 Case 2).
- **How**: Applies `omegaPullbackCoeff_mulByInt` (OmegaPullbackCoeff.lean) at m = p, then uses `CharP.cast_eq_zero` to get (p : k) = 0, and `map_zero` to conclude the algebraMap image is 0.
- **Hypotheses**: Characteristic p, prime p.
- **Uses from project**: `omegaPullbackCoeff_mulByInt` (OmegaPullbackCoeff.lean), `mulByInt` (Basic.lean), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: `mulByInt_p_omega_pullback_eq_zero`, `Conditional.mulByNat_p_not_isSeparable_of_algKaehler_witness` (this file)
- **Visibility**: public
- **Lines**: 223–232, proof ~6 lines
- **Notes**: T-FROB-OMEGA-ZERO. Note that `[Fact (Nat.Prime p)]` notation differs slightly from the alias below (`[Fact p.Prime]`).

---

### `theorem mulByInt_p_omega_pullback_eq_zero`
- **Type**: `(p : ℕ) [CharP k p] [Fact p.Prime] (E : WeierstrassCurve k) [E.toAffine.IsElliptic] : omegaPullbackCoeff E (mulByInt E.toAffine (p : ℤ)) = 0`
- **What**: Dispatch-board alias (T01, R27) for `omegaPullbackCoeff_mulByNat_p_eq_zero`, using the alternative `Fact p.Prime` notation. Foundational ticket TIER 1.
- **How**: One-liner delegating to `omegaPullbackCoeff_mulByNat_p_eq_zero`.
- **Hypotheses**: Same as `omegaPullbackCoeff_mulByNat_p_eq_zero`.
- **Uses from project**: `omegaPullbackCoeff_mulByNat_p_eq_zero` (this file), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean)
- **Used by**: `mulByInt_p_not_isSeparable` (this file)
- **Visibility**: public
- **Lines**: 237–241, proof ~1 line (term-mode)
- **Notes**: T01 / R27 ticket alias; minor redundancy with `omegaPullbackCoeff_mulByNat_p_eq_zero`.

---

### `noncomputable def Isogeny.inseparableDegree`
- **Type**: `(φ : Isogeny W₁ W₂) : ℕ` defined as `φ.degree / φ.sepDegree`
- **What**: The inseparable degree of a `HasseWeil.Isogeny`, defined as total degree divided by separable degree. Parallel of `HasseWeil.EC.Isogeny.inseparableDegree` for the `HasseWeil.Isogeny` type. Implements Silverman II.2.10.
- **How**: Term-mode definition, ℕ-division `φ.degree / φ.sepDegree`.
- **Hypotheses**: None beyond the isogeny.
- **Uses from project**: `Isogeny.degree`, `Isogeny.sepDegree` (IsogenyKernel.lean or Basic.lean)
- **Used by**: `Isogeny.inseparableDegree_eq_one_iff_isSeparable`, `Isogeny.inseparableDegree_isPow_of_charP`, `mulByInt_p_inseparableDegree_eq_pow` (this file)
- **Visibility**: public
- **Lines**: 256–257, 1-line definition
- **Notes**: Silverman II.2.10; possibly overlaps with `HasseWeil.EC.Isogeny.inseparableDegree` in InseparableDegree.lean.

---

### `theorem Isogeny.inseparableDegree_eq_one_iff_isSeparable`
- **Type**: `(φ : Isogeny W₁ W₂) (hfin : FiniteDimensional W₂.FunctionField W₁.FunctionField) : φ.inseparableDegree = 1 ↔ φ.IsSeparable`
- **What**: The inseparable degree equals 1 iff the isogeny is separable. Implements Silverman II.2.10 equivalence via the multiplicativity `deg = sepDeg × finInsepDeg`.
- **How**: Rewrites `IsSeparable` as `sepDegree = degree` via `isSeparable_iff_sepDegree_eq_degree` (IsogenyKernel.lean), then uses `Field.finSepDegree_mul_finInsepDegree` (mathlib) to establish the multiplicativity, and Nat.div_self / Dvd argument to conclude.
- **Hypotheses**: FiniteDimensional (function field extension); elliptic curve.
- **Uses from project**: `Isogeny.inseparableDegree` (this file), `isSeparable_iff_sepDegree_eq_degree` (EC/IsogenyKernel.lean), `Isogeny.sepDegree`, `Isogeny.degree`
- **Used by**: `mulByInt_p_inseparableDegree_eq_pow` (this file)
- **Visibility**: public
- **Lines**: 262–295, proof ~33 lines
- **Notes**: Proof > 30 lines; uses mathlib `Field.finSepDegree_mul_finInsepDegree` and `Field.instNeZeroFinSepDegree`.

---

### `theorem Isogeny.inseparableDegree_isPow_of_charP`
- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] (α : Isogeny W.toAffine W.toAffine) (h_deg_pos : 0 < α.degree) : ∃ e : ℕ, α.inseparableDegree = p ^ e`
- **What**: In characteristic p, the inseparable degree of any positive-degree isogeny is a power of p. Parallel of `InseparableDegree.inseparableDegree_isPow_of_charP` for the `HasseWeil.Isogeny` type.
- **How**: Transfers CharP to the function field via `charP_of_injective_algebraMap`, constructs ExpChar instance, uses `FiniteDimensional.of_finrank_pos`, then invokes mathlib's `finInsepDegree_eq_pow` (PurelyInseparable/Basic.lean) and relates to `inseparableDegree` via `Field.finSepDegree_mul_finInsepDegree`.
- **Hypotheses**: p prime, characteristic p on K, degree > 0.
- **Uses from project**: `Isogeny.inseparableDegree` (this file), `Isogeny.degree`, `Isogeny.sepDegree`, `Isogeny.toAlgebra`
- **Used by**: `mulByInt_p_inseparableDegree_eq_pow` (this file)
- **Visibility**: public
- **Lines**: 300–334, proof ~34 lines
- **Notes**: Proof > 30 lines; uses mathlib `finInsepDegree_eq_pow`, `charP_of_injective_algebraMap`, `ExpChar.prime`. Suspicious duplication with `Curves/InseparableDegree.lean`'s `inseparableDegree_isPow_of_charP` (lines 129+).

---

### `theorem mulByInt_p_not_isSeparable` (T02)
- **Type**: `(p : ℕ) [CharP k p] [Fact p.Prime] (E : WeierstrassCurve k) [E.toAffine.IsElliptic] : ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable`
- **What**: T02 (R27): in characteristic p, [p] is inseparable. This is the contrapositive of Silverman II.4.2(c) applied to T01 (vanishing of the ω-pullback coefficient of [p]).
- **How**: Takes the separability assumption `h_sep`, applies `isogeny_omegaCoeff_ne_zero_of_isSeparable` (Differentials.lean) to get the coefficient is nonzero, and then contradicts that with `mulByInt_p_omega_pullback_eq_zero` (T01, this file) which says it is zero.
- **Hypotheses**: CharP k p, prime p, elliptic curve.
- **Uses from project**: `isogeny_omegaCoeff_ne_zero_of_isSeparable` (Curves/Differentials.lean), `mulByInt_p_omega_pullback_eq_zero` (this file), `mulByInt` (Basic.lean)
- **Used by**: `mulByInt_p_inseparableDegree_eq_pow` (this file)
- **Visibility**: public
- **Lines**: 347–353, proof ~4 lines
- **Notes**: T02 / R27 ticket.

---

### `theorem mulByInt_p_inseparableDegree_eq_pow` (T03)
- **Type**: `(p : ℕ) [CharP k p] [Fact p.Prime] (E : WeierstrassCurve k) [E.toAffine.IsElliptic] : ∃ e : ℕ, 1 ≤ e ∧ (mulByInt E.toAffine (p : ℤ)).inseparableDegree = p ^ e`
- **What**: T03 (R27): in characteristic p, the inseparable degree of [p] is p^e for some e ≥ 1 (genuinely inseparable, not just degree-1 separable).
- **How**: Applies `Isogeny.inseparableDegree_isPow_of_charP` (this file) to get e with inseparableDegree = p^e; then uses T02 (`mulByInt_p_not_isSeparable`) with `inseparableDegree_eq_one_iff_isSeparable` (this file) to rule out e = 0 via `interval_cases e`.
- **Hypotheses**: CharP k p, prime p, elliptic curve.
- **Uses from project**: `Isogeny.inseparableDegree_isPow_of_charP` (this file), `mulByInt_degree_pos` (Basic.lean), `mulByInt_p_not_isSeparable` (this file), `Isogeny.inseparableDegree_eq_one_iff_isSeparable` (this file), `mulByInt` (Basic.lean), `Isogeny.inseparableDegree` (this file)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 365–389, proof ~24 lines
- **Notes**: T03 / R27 ticket. Dead code candidate within this file (no internal callers).

---

### `theorem Conditional.mulByNat_p_not_isSeparable_of_algKaehler_witness`
- **Type**: `(p : ℕ) [CharP k p] [Fact (Nat.Prime p)] (E : WeierstrassCurve k) [E.toAffine.IsElliptic] (h_alg : (mulByInt E.toAffine (p : ℤ)).IsSeparable ↔ Function.Injective (mulByInt E.toAffine (p : ℤ)).pullbackKaehler) : ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable`
- **What**: Witness-parametric T-FROB-INSEP (namespaced `Conditional`): in char p, [p] is inseparable, given the algebra-Kähler bridge `IsSeparable [p] ↔ pullbackKaehler [p] injective` (T-II-4-004 / Silverman II.4.2(c)) as a hypothesis.
- **How**: Applies `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler` (Curves/Differentials.lean) with h_alg to get the coefficient-based iff, then uses `omegaPullbackCoeff_mulByNat_p_eq_zero` (this file) to derive a contradiction.
- **Hypotheses**: CharP k p, prime p, elliptic curve, and the h_alg algebra-Kähler bridge witness (T-II-4-004).
- **Uses from project**: `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler` (Curves/Differentials.lean), `omegaPullbackCoeff_mulByNat_p_eq_zero` (this file), `mulByInt` (Basic.lean)
- **Used by**: unused in file
- **Visibility**: public (within `Conditional` namespace, per anti-drift protocol)
- **Lines**: 423–432, proof ~5 lines
- **Notes**: `Conditional` namespace per anti-drift gate 1 (PROTOCOL.md 2026-05-08). Dead code candidate within this file.

---

## Summary of Cross-References

### Key project declarations used (from other files)
- `omegaPullbackCoeff` — OmegaPullbackCoeff.lean (used everywhere)
- `omegaPullbackCoeff_mulByInt` — OmegaPullbackCoeff.lean (used in `omegaPullbackCoeff_mulByNat_p_eq_zero`)
- `Isogeny.pullbackKaehler_invariantDifferential` — InvariantDifferentialPullback.lean
- `invariantDifferential` — Curves/Differentials.lean
- `mulByInt` — Basic.lean
- `mulByInt_degree_pos` — Basic.lean
- `isSeparable_iff_sepDegree_eq_degree` — EC/IsogenyKernel.lean
- `isogeny_omegaCoeff_ne_zero_of_isSeparable` — Curves/Differentials.lean
- `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler` — Curves/Differentials.lean
- `Field.finSepDegree_mul_finInsepDegree` — mathlib
- `finInsepDegree_eq_pow` — mathlib (PurelyInseparable/Basic.lean)
- `charP_of_injective_algebraMap` — mathlib
- `ExpChar.prime` — mathlib

### Key API (used by 3+ declarations in this file)
- `isSeparable_iff_of_coeff_witness` (used by 3: `m_plus_n_frob_isSeparable_iff_of_witness`, `oneSubFrobenius_isSeparable_of_witness`, implicitly via `mulByInt_isSeparable_of_witness`)
- `pullbackKaehler_invariantDifferential_of_coeff_witness` (used by 3: `mulByInt_pullbackKaehler_invariantDifferential_of_witness`, `translation_pullbackKaehler_invariantDifferential_of_witness`, and implicitly via `mulByInt_pullbackKaehler_invariantDifferential_of_witness`)
- `omegaPullbackCoeff_mulByNat_p_eq_zero` (used by 2 direct callers: `mulByInt_p_omega_pullback_eq_zero`, `Conditional.mulByNat_p_not_isSeparable_of_algKaehler_witness`)
- `Isogeny.inseparableDegree` (used by 3: `inseparableDegree_eq_one_iff_isSeparable`, `inseparableDegree_isPow_of_charP`, `mulByInt_p_inseparableDegree_eq_pow`)

### Declarations unused within this file (dead-code candidates for this file)
- `mulByInt_pullbackKaehler_invariantDifferential_of_witness`
- `translation_pullbackKaehler_invariantDifferential_of_witness`
- `mulByInt_isSeparable_of_witness`
- `mulByInt_p_inseparableDegree_eq_pow`
- `Conditional.mulByNat_p_not_isSeparable_of_algKaehler_witness`
