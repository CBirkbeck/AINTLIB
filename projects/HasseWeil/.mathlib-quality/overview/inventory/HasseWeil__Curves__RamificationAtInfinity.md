# Inventory: ./HasseWeil/Curves/RamificationAtInfinity.lean

**File summary:** 648 lines. Establishes the abstract ramification-at-infinity identity `[K(C) : k(f)] = Σ_P e(P)·f(P)` by packaging Mathlib's `Ideal.sum_ramification_inertia` behind a bespoke type-synonym `LinfAt` and record structure `Sinf`. No sorries, no `set_option maxHeartbeats`.

---

## Declarations

---

### `noncomputable def polyToFieldOfInv`
- **Type**: `{L : Type*} [Field L] [Algebra k L] (f : L) : Polynomial k →ₐ[k] L`
- **What**: The canonical `k`-algebra map `Polynomial k → L` sending `X ↦ f⁻¹`; the algebraic incarnation of "u = 1/f is the uniformizer at infinity".
- **How**: One-liner wrapping `Polynomial.aeval f⁻¹`.
- **Hypotheses**: `L` is a field, `k`-algebra.
- **Uses from project**: none
- **Used by**: `polyToFieldOfInv_X`, `polyToFieldOfInv_C`, `polyToFieldOfInv_injective_of_transcendental`, `polyToFieldOfInv_algebraMap_eq`, `polyToFieldOfInv_ne_zero_of_ne_zero`, `LinfAt.algebraPolynomial`, `algebraMap_polynomial_apply`, `isScalarTower_k_polynomial`, `isScalarTower_polynomial_fractionRing`, `ratFunToFieldOfInv`, `Sinf.ofIntegralClosure`
- **Visibility**: public
- **Lines**: 66–68; proof length: 1 line (term-mode)
- **Notes**: none

---

### `@[simp] theorem polyToFieldOfInv_X`
- **Type**: `polyToFieldOfInv (k := k) f Polynomial.X = f⁻¹`
- **What**: The simp lemma computing `polyToFieldOfInv f` at `X`, giving `f⁻¹`.
- **How**: `Polynomial.aeval_X f⁻¹`.
- **Hypotheses**: `L` field, `k`-algebra.
- **Uses from project**: `polyToFieldOfInv`
- **Used by**: unused in file (simp lemma, consumed via simp in external files)
- **Visibility**: public
- **Lines**: 70–73; 1 line
- **Notes**: none

---

### `@[simp] theorem polyToFieldOfInv_C`
- **Type**: `polyToFieldOfInv (k := k) f (Polynomial.C c) = algebraMap k L c`
- **What**: Simp lemma: constant polynomials map to the algebraMap value.
- **How**: `Polynomial.aeval_C f⁻¹ c`.
- **Hypotheses**: `L` field, `k`-algebra.
- **Uses from project**: `polyToFieldOfInv`
- **Used by**: `polyToFieldOfInv_algebraMap_eq`, `isScalarTower_k_polynomial` (via `polyToFieldOfInv_algebraMap_eq`)
- **Visibility**: public
- **Lines**: 74–77; 1 line
- **Notes**: none

---

### `theorem polyToFieldOfInv_injective_of_transcendental`
- **Type**: `{f : L} (hf : Transcendental k f⁻¹) : Function.Injective (polyToFieldOfInv (k := k) f)`
- **What**: If `f⁻¹` is transcendental over `k` then the evaluation map is injective.
- **How**: Uses `transcendental_iff_injective` from Mathlib.
- **Hypotheses**: `f⁻¹` transcendental over `k`.
- **Uses from project**: `polyToFieldOfInv`
- **Used by**: `polyToFieldOfInv_ne_zero_of_ne_zero`, `ratFunToFieldOfInv`, `Sinf.ofIntegralClosure`
- **Visibility**: public
- **Lines**: 79–84; 3 lines
- **Notes**: Key API — used by 3 other declarations in this file.

---

### `@[simp] theorem polyToFieldOfInv_algebraMap_eq`
- **Type**: `polyToFieldOfInv (k := k) f (algebraMap k _ c) = algebraMap k L c`
- **What**: The map commutes with `algebraMap k`; constants from `k` are preserved.
- **How**: `Polynomial.algebraMap_eq` + `polyToFieldOfInv_C`.
- **Hypotheses**: none beyond field/algebra.
- **Uses from project**: `polyToFieldOfInv_C`
- **Used by**: `isScalarTower_k_polynomial` (body uses `polyToFieldOfInv_algebraMap_eq`)
- **Visibility**: public
- **Lines**: 110–113; 2 lines
- **Notes**: none

---

### `theorem polyToFieldOfInv_ne_zero_of_ne_zero`
- **Type**: `(hf : Transcendental k f⁻¹) {p : Polynomial k} (hp : p ≠ 0) : polyToFieldOfInv (k := k) f p ≠ 0`
- **What**: If `f⁻¹` is transcendental, the evaluation of any nonzero polynomial is nonzero.
- **How**: Injectivity (`polyToFieldOfInv_injective_of_transcendental`) + `map_zero`.
- **Hypotheses**: `f⁻¹` transcendental, `p ≠ 0`.
- **Uses from project**: `polyToFieldOfInv_injective_of_transcendental`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 117–123; 4 lines
- **Notes**: Dead code candidate within this file (may be used externally).

---

### `noncomputable def ratFunToFieldOfInv`
- **Type**: `{f : L} (hf : Transcendental k f⁻¹) : FractionRing (Polynomial k) →ₐ[k] L`
- **What**: Lifts `polyToFieldOfInv f` to the fraction field, sending the formal indeterminate to `f⁻¹`; exists because the polynomial map is injective under transcendence.
- **How**: `IsFractionRing.liftAlgHom` applied to `polyToFieldOfInv_injective_of_transcendental`.
- **Hypotheses**: `f⁻¹` transcendental over `k`.
- **Uses from project**: `polyToFieldOfInv`, `polyToFieldOfInv_injective_of_transcendental`
- **Used by**: `ratFunToFieldOfInv_injective`, `LinfAt.algebraFractionRing`, `algebraMap_fractionRing_apply`, `isScalarTower_polynomial_fractionRing`, `isScalarTower_k_fractionRing`
- **Visibility**: public
- **Lines**: 137–143; 5 lines (term-mode)
- **Notes**: Key API — used by 5 other declarations.

---

### `theorem ratFunToFieldOfInv_injective`
- **Type**: `(hf : Transcendental k f⁻¹) : Function.Injective (ratFunToFieldOfInv hf)`
- **What**: The lifted rational-function map is injective (algebra map between fields).
- **How**: `.toRingHom.injective` on the `AlgHom`.
- **Hypotheses**: `f⁻¹` transcendental.
- **Uses from project**: `ratFunToFieldOfInv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 146–149; 2 lines
- **Notes**: Dead code candidate within this file.

---

### `def LinfAt`
- **Type**: `{L : Type*} [Field L] [Algebra k L] (_f : L) : Type _`
- **What**: A type synonym for `L`, indexed by `f`, used to install an alternate `Polynomial k`-algebra structure (via `X ↦ f⁻¹`) without conflicting with the project's existing `X ↦ coordX` instance.
- **How**: Definitional alias `= L`; `@[nolint unusedArguments]` for the phantom `_f`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: all of `LinfAt.algebraPolynomial`, `LinfAt.algebraFractionRing`, `LinfAt.isScalarTower_*`, `Sinf` fields, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`, `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 165–166; definitional (0 proof lines)
- **Notes**: Central design: the entire file's algebra-tower avoidance pivots on this synonym.

---

### `instance (anonymous) : Field (LinfAt (k := k) f)`
- **Type**: `Field (LinfAt (k := k) f)`
- **What**: Transports the `Field L` instance to the type synonym `LinfAt f`.
- **How**: `‹Field L›` (instance copy).
- **Hypotheses**: `[Field L]`.
- **Uses from project**: `LinfAt`
- **Used by**: implicitly by everything in `LinfAt` namespace
- **Visibility**: public (in `LinfAt` namespace)
- **Lines**: 170–171; 1 line
- **Notes**: none

---

### `instance (anonymous) : Algebra k (LinfAt (k := k) f)`
- **Type**: `Algebra k (LinfAt (k := k) f)`
- **What**: Transports the `Algebra k L` instance to `LinfAt f`.
- **How**: `‹Algebra k L›`.
- **Hypotheses**: `[Algebra k L]`.
- **Uses from project**: `LinfAt`
- **Used by**: implicitly by everything using `LinfAt`
- **Visibility**: public (in `LinfAt` namespace)
- **Lines**: 172–173; 1 line
- **Notes**: none

---

### `noncomputable instance LinfAt.algebraPolynomial`
- **Type**: `Algebra (Polynomial k) (LinfAt (k := k) f)`
- **What**: The alternate `Polynomial k`-algebra structure on `LinfAt f` sending `X ↦ f⁻¹`.
- **How**: `.toRingHom.toAlgebra` on `polyToFieldOfInv`.
- **Hypotheses**: `[Field L] [Algebra k L]`.
- **Uses from project**: `polyToFieldOfInv`
- **Used by**: `algebraMap_polynomial_apply`, `isScalarTower_k_polynomial`, `LinfAt.algebraFractionRing`, `isScalarTower_polynomial_fractionRing`, `isScalarTower_k_fractionRing`, `Sinf` fields, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Visibility**: public
- **Lines**: 179–182; 1 line (term-mode instance)
- **Notes**: none

---

### `theorem algebraMap_polynomial_apply`
- **Type**: `(algebraMap (Polynomial k) (LinfAt (k := k) f) p : L) = polyToFieldOfInv (k := k) f p`
- **What**: Explicitly confirms that the `algebraMap` from `Polynomial k` to `LinfAt f` computes as `polyToFieldOfInv`.
- **How**: `rfl`.
- **Hypotheses**: standard.
- **Uses from project**: `polyToFieldOfInv`, `LinfAt.algebraPolynomial`
- **Used by**: unused in file (definitional bridge for external use)
- **Visibility**: public
- **Lines**: 186–190; 1 line
- **Notes**: Dead code candidate within this file.

---

### `instance LinfAt.isScalarTower_k_polynomial`
- **Type**: `IsScalarTower k (Polynomial k) (LinfAt (k := k) f)`
- **What**: The `k → Polynomial k → LinfAt f` tower commutes.
- **How**: `IsScalarTower.of_algebraMap_eq` + `polyToFieldOfInv_algebraMap_eq`.
- **Hypotheses**: standard.
- **Uses from project**: `LinfAt.algebraPolynomial`, `polyToFieldOfInv_algebraMap_eq`
- **Used by**: `isScalarTower_polynomial_fractionRing`, `isScalarTower_k_fractionRing` (transitively)
- **Visibility**: public
- **Lines**: 194–203; ~8 lines
- **Notes**: none

---

### `noncomputable instance LinfAt.algebraFractionRing`
- **Type**: `[hf : Fact (Transcendental k f⁻¹)] : Algebra (FractionRing (Polynomial k)) (LinfAt (k := k) f)`
- **What**: The `FractionRing (Polynomial k)`-algebra structure on `LinfAt f`, parametrised by a `Fact` of transcendence.
- **How**: `.toRingHom.toAlgebra` on `ratFunToFieldOfInv`.
- **Hypotheses**: `Fact (Transcendental k f⁻¹)`.
- **Uses from project**: `ratFunToFieldOfInv`
- **Used by**: `algebraMap_fractionRing_apply`, `isScalarTower_polynomial_fractionRing`, `isScalarTower_k_fractionRing`, `Sinf.ofIntegralClosure`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Visibility**: public
- **Lines**: 225–230; 2 lines (term-mode)
- **Notes**: `Fact` encoding required to prevent universe-polymorphism / instance-resolution conflicts.

---

### `theorem algebraMap_fractionRing_apply`
- **Type**: `(algebraMap (FractionRing (Polynomial k)) (LinfAt (k := k) f) q : L) = ratFunToFieldOfInv hf.out q`
- **What**: Confirms the algebra map computes as `ratFunToFieldOfInv`.
- **How**: `rfl`.
- **Hypotheses**: `Fact (Transcendental k f⁻¹)`.
- **Uses from project**: `LinfAt.algebraFractionRing`, `ratFunToFieldOfInv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 234–241; 1 line
- **Notes**: Dead code candidate within this file.

---

### `instance LinfAt.isScalarTower_polynomial_fractionRing`
- **Type**: `[Fact (Transcendental k f⁻¹)] : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) (LinfAt (k := k) f)`
- **What**: The `Polynomial k → FractionRing → LinfAt f` tower commutes.
- **How**: `IsScalarTower.of_algebraMap_eq`; the two maps agree because `ratFunToFieldOfInv` is built as `liftAlgHom` extending `polyToFieldOfInv`; checked by `AlgHom.ext` + `simp`.
- **Hypotheses**: `Fact (Transcendental k f⁻¹)`.
- **Uses from project**: `ratFunToFieldOfInv`, `polyToFieldOfInv`, `LinfAt.algebraPolynomial`, `LinfAt.algebraFractionRing`
- **Used by**: `Sinf.ofIntegralClosure`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Visibility**: public
- **Lines**: 246–267; ~18 lines
- **Notes**: None; proof establishes the universal-property coherence of `IsFractionRing.liftAlgHom`.

---

### `instance LinfAt.isScalarTower_k_fractionRing`
- **Type**: `[Fact (Transcendental k f⁻¹)] : IsScalarTower k (FractionRing (Polynomial k)) (LinfAt (k := k) f)`
- **What**: The `k → FractionRing (Polynomial k) → LinfAt f` tower commutes.
- **How**: `IsScalarTower.of_algebraMap_eq` + `AlgHom.commutes` on `ratFunToFieldOfInv`.
- **Hypotheses**: `Fact (Transcendental k f⁻¹)`.
- **Uses from project**: `ratFunToFieldOfInv`, `LinfAt.algebraFractionRing`
- **Used by**: `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Visibility**: public
- **Lines**: 272–283; ~9 lines
- **Notes**: none

---

### `structure Sinf`
- **Type**: `{L : Type*} [Field L] [Algebra k L] (f : L) : Type _` (structure with 9 fields)
- **What**: A record packaging the integral closure of `Polynomial k` inside `LinfAt f` together with all typeclasses needed by `Ideal.sum_ramification_inertia` — bypasses a Lean 4 `Meta.SynthInstance.tryResolve` negative-cache anomaly on `↥(integralClosure …)` coercions.
- **How**: Record with fields: `carrier`, `commRing`, `isDomain`, `isDedekindDomain`, `algPoly`, `algLinfAt`, `isFractionRing`, `isScalarTower`, `moduleFinite`, `isTorsionFree`.
- **Hypotheses**: none (fields carry the hypotheses).
- **Uses from project**: `LinfAt`
- **Used by**: `Sinf.ofIntegralClosure`, `xIdeal_isMaximal`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`, `Sinf.ordAt`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `Sinf.kappa`, `Sinf.algBaseFromCarrier`, `Sinf.inertiaDeg_eq_finrank_kappa`, `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`, `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 320–342; 0 proof lines (structure definition)
- **Notes**: Central design decision: explicit record avoids Lean 4 typeclass synthesis failure on `integralClosure` Subalgebra coercions (commit 538ff64 documented in file).

---

### `noncomputable def Sinf.ofIntegralClosure`
- **Type**: `[Fact (Transcendental k f⁻¹)] [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)] [Algebra.IsSeparable (FractionRing (Polynomial k)) (LinfAt (k := k) f)] : Sinf (k := k) f`
- **What**: Canonical constructor of `Sinf` from Mathlib's `integralClosure` Subalgebra; synthesises all record fields from the finite-separable hypotheses.
- **How**: Uses `IsIntegralClosure.isFractionRing_of_finite_extension`, `IsIntegralClosure.finite`, `Subalgebra.instIsTorsionFree`, and `polyToFieldOfInv_injective_of_transcendental` (for `FaithfulSMul`). Runs under `set_option backward.isDefEq.respectTransparency false`.
- **Hypotheses**: `L/k(f)` finite + separable + `f⁻¹` transcendental.
- **Uses from project**: `LinfAt`, `Sinf`, `polyToFieldOfInv_injective_of_transcendental`, `LinfAt.algebraPolynomial`, `LinfAt.algebraFractionRing`, `LinfAt.isScalarTower_polynomial_fractionRing`
- **Used by**: unused in file (consumed by `GapSpines.lean`)
- **Visibility**: public
- **Lines**: 357–382; ~24 lines
- **Notes**: Proof longer than 20 lines; uses `set_option backward.isDefEq.respectTransparency false` (scoped to `section SinfConstruction`, justified by comment referencing Mathlib `NormalClosure` pattern).

---

### `noncomputable abbrev xIdeal`
- **Type**: `Ideal (Polynomial k)`
- **What**: The ideal `(X)` in `Polynomial k`; under `X ↦ f⁻¹`, this is the "point at infinity" prime.
- **How**: `Ideal.span {Polynomial.X}`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `xIdeal_isMaximal`, `xIdeal_ne_bot`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`, `quotientXAlgEquiv`, `Sinf.ordAt`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `Sinf.kappa`, `Sinf.inertiaDeg_eq_finrank_kappa`, `finrank_residue_eq_finrank_k`, `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`, `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 395–396; 1 line (abbrev)
- **Notes**: Key API — used by essentially every theorem in the closing sections.

---

### `instance xIdeal_isMaximal`
- **Type**: `(xIdeal (k := k)).IsMaximal`
- **What**: The ideal `(X) ⊂ k[X]` is maximal (since `k[X]/(X) ≅ k` is a field).
- **How**: `Ideal.span_singleton_prime` + `Polynomial.prime_X` + maximality criterion.
- **Hypotheses**: `[Field k]`.
- **Uses from project**: `xIdeal`
- **Used by**: `finrank_eq_sum_ramificationIdx_mul_inertiaDeg` (implicitly via Mathlib's `Ideal.sum_ramification_inertia`), `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`
- **Visibility**: public
- **Lines**: 398–402; 4 lines
- **Notes**: none

---

### `theorem xIdeal_ne_bot`
- **Type**: `(xIdeal (k := k)) ≠ ⊥`
- **What**: `(X)` is not the zero ideal.
- **How**: `Ideal.span_singleton_eq_bot` + `Polynomial.X_ne_zero`.
- **Hypotheses**: `[Field k]`.
- **Uses from project**: `xIdeal`
- **Used by**: `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Visibility**: public
- **Lines**: 404–407; 3 lines
- **Notes**: none

---

### `theorem finrank_eq_sum_ramificationIdx_mul_inertiaDeg`
- **Type**: `[Fact (Transcendental k f⁻¹)] [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)] (data : Sinf (k := k) f) : ∑ P ∈ primesOverFinset (xIdeal) data.carrier, ramificationIdx * inertiaDeg = Module.finrank (FractionRing (Polynomial k)) (LinfAt (k := k) f)`
- **What**: The abstract fundamental ramification–inertia identity: `Σ e(P)·f(P) = [L : k(f)]` for primes over `(X)`.
- **How**: Direct application of `Ideal.sum_ramification_inertia` from Mathlib after installing all `Sinf` fields via `letI`.
- **Hypotheses**: `L/k(f)` finite, `f⁻¹` transcendental, Sinf data package.
- **Uses from project**: `Sinf`, `xIdeal`, `xIdeal_ne_bot`, `LinfAt`, `LinfAt.algebraFractionRing`, `LinfAt.isScalarTower_k_fractionRing`, `LinfAt.isScalarTower_polynomial_fractionRing`
- **Used by**: `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 416–438; ~20 lines
- **Notes**: none

---

### `noncomputable def quotientXAlgEquiv`
- **Type**: `(Polynomial k ⧸ xIdeal (k := k)) ≃ₐ[k] k`
- **What**: The canonical `k`-algebra isomorphism `k[X]/(X) ≅ k` (evaluation at 0).
- **How**: `Ideal.quotientEquivAlgOfEq` (rewriting `(X) = (X − 0)`) composed with `Polynomial.quotientSpanXSubCAlgEquiv 0`.
- **Hypotheses**: `[Field k]`.
- **Uses from project**: `xIdeal`
- **Used by**: `finrank_residue_eq_finrank_k`
- **Visibility**: public
- **Lines**: 466–472; 5 lines
- **Notes**: none

---

### `noncomputable def Sinf.ordAt`
- **Type**: `(data : Sinf (k := k) f) : Ideal data.carrier → ℤ`
- **What**: Defines `ordAt P` as `-(ramificationIdx (algebraMap …) (xIdeal) P)`, the order of `f` at `P` (negative of the ramification index gives the pole order).
- **How**: Definitional; sign convention bridges ramification index (natural number) to order-at-P (integer, negative at poles).
- **Hypotheses**: `Sinf` data.
- **Uses from project**: `Sinf`, `xIdeal`
- **Used by**: `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 476–484; 3 lines
- **Notes**: none

---

### `theorem Sinf.toNat_neg_ordAt_eq_ramificationIdx`
- **Type**: `∀ P : Ideal data.carrier, (-(data.ordAt P)).toNat = Ideal.ramificationIdx … P`
- **What**: `(-ordAt P).toNat = ramificationIdx P` — the round-trip from integer order back to the natural ramification index.
- **How**: `simp [Sinf.ordAt]`.
- **Hypotheses**: `Sinf` data.
- **Uses from project**: `Sinf.ordAt`, `Sinf`
- **Used by**: `finrank_eq_weighted_poleDegree_of_nonconstant`
- **Visibility**: public
- **Lines**: 487–499; 5 lines
- **Notes**: none

---

### `abbrev Sinf.kappa`
- **Type**: `(data : Sinf (k := k) f) : Ideal data.carrier → Type _`
- **What**: The residue field `κ(P) = data.carrier ⧸ P` at a prime `P` of the Sinf carrier.
- **How**: `fun P => data.carrier ⧸ P` (abbreviation).
- **Hypotheses**: `Sinf` data.
- **Uses from project**: `Sinf`
- **Used by**: `Sinf.inertiaDeg_eq_finrank_kappa`, `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective` (in statement via kappa-like quotient)
- **Visibility**: public
- **Lines**: 504–509; 2 lines (abbrev)
- **Notes**: none

---

### `@[reducible] noncomputable def Sinf.algBaseFromCarrier`
- **Type**: `(data : Sinf (k := k) f) : Algebra k data.carrier`
- **What**: The `k`-algebra structure on `data.carrier` obtained by composing `k → Polynomial k → carrier`; not a global instance.
- **How**: `.comp` of the two `algebraMap`s, then `.toAlgebra`.
- **Hypotheses**: `Sinf` data.
- **Uses from project**: `Sinf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 515–525; 6 lines
- **Notes**: Dead code candidate within this file; `@[reducible]` suggests it was intended for use at call sites via `letI`.

---

### `theorem Sinf.inertiaDeg_eq_finrank_kappa`
- **Type**: `∀ (P : Ideal data.carrier) [P.LiesOver (xIdeal (k := k))], Ideal.inertiaDeg (xIdeal) P = Module.finrank (Polynomial k ⧸ xIdeal) (data.kappa P)`
- **What**: Bridge 3: inertia degree at `P` over `(X)` equals the residue-field `(k[X]/(X))`-finrank.
- **How**: `Ideal.inertiaDeg_algebraMap` from Mathlib.
- **Hypotheses**: `P` lies over `xIdeal`, `Sinf` data.
- **Uses from project**: `Sinf`, `Sinf.kappa`, `xIdeal`
- **Used by**: unused in file (consumed externally by `L6Witnesses.lean`)
- **Visibility**: public
- **Lines**: 531–542; 5 lines
- **Notes**: Dead code candidate within this file.

---

### `theorem finrank_residue_eq_finrank_k`
- **Type**: `Module.finrank (Polynomial k ⧸ xIdeal (k := k)) M = Module.finrank k M`
- **What**: The `(k[X]/(X))`-finrank of a free module `M` equals its `k`-finrank, since `k[X]/(X) ≅ k`.
- **How**: `Module.finrank_mul_finrank` + `quotientXAlgEquiv.toLinearEquiv.finrank_eq` + `Module.finrank_self`.
- **Hypotheses**: `M` free over `Polynomial k ⧸ xIdeal`, compatible scalar tower `k → k[X]/(X) → M`.
- **Uses from project**: `xIdeal`, `quotientXAlgEquiv`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 547–556; 8 lines
- **Notes**: Dead code candidate within this file.

---

### `theorem Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`
- **Type**: `(data : Sinf (k := k) f) (P : Ideal data.carrier) [P.IsPrime] [P.LiesOver (xIdeal)] (h_surj : Function.Surjective (algebraMap (Polynomial k ⧸ xIdeal) (data.carrier ⧸ P))) : Ideal.inertiaDeg (xIdeal) P = 1`
- **What**: If the structure map `k[X]/(X) → carrier/P` (i.e., `k → κ(P)`) is surjective, then the inertia degree equals 1; the abstract `surjective ⟹ inertiaDeg = 1` bridge for the V.1.3 residual.
- **How**: Upper bound: `finrank_le_one` applied to `1` using surjectivity; lower bound: `Ideal.inertiaDeg_pos` transported via `Ideal.inertiaDeg_algebraMap`.
- **Hypotheses**: `P` prime, lies over `xIdeal`, residue map surjective, `Sinf` data (needs `moduleFinite`, `isDomain`).
- **Uses from project**: `Sinf`, `xIdeal`, `xIdeal_isMaximal`
- **Used by**: unused in file (consumed by `L6Witnesses.lean` line 3827)
- **Visibility**: public
- **Lines**: 575–609; **34 lines**
- **Notes**: Long proof (>30 lines); no sorry; the key closing lemma for the V.1.3 inertia-degree residual.

---

### `theorem finrank_eq_weighted_poleDegree_of_nonconstant`
- **Type**: `[Fact (Transcendental k f⁻¹)] [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)] (data : Sinf (k := k) f) : Module.finrank (FractionRing (Polynomial k)) (LinfAt (k := k) f) = ∑ P ∈ primesOverFinset (xIdeal) data.carrier, (-(data.ordAt P)).toNat * Ideal.inertiaDeg (xIdeal) P`
- **What**: The abstract closing corollary: `[L : k(f)] = Σ_P (-ord_P f) · inertiaDeg P`; combines the ramification-inertia identity with the sign bridge for `ordAt`.
- **How**: `finrank_eq_sum_ramificationIdx_mul_inertiaDeg` + `Finset.sum_congr` + `Sinf.toNat_neg_ordAt_eq_ramificationIdx`.
- **Hypotheses**: `f⁻¹` transcendental, `L/k(f)` finite, `Sinf` data.
- **Uses from project**: `Sinf`, `xIdeal`, `LinfAt`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `Sinf.ordAt`
- **Used by**: unused in file (consumed by `PoleDivisorFallback.lean` and `OpenLemmas.lean`)
- **Visibility**: public
- **Lines**: 619–644; ~24 lines
- **Notes**: The main deliverable of this file for external callers.

---

## Cross-reference summary

**keyApi** (used by ≥3 other declarations within this file):
- `polyToFieldOfInv`: used by `polyToFieldOfInv_X`, `polyToFieldOfInv_C`, `polyToFieldOfInv_injective_of_transcendental`, `polyToFieldOfInv_algebraMap_eq`, `polyToFieldOfInv_ne_zero_of_ne_zero`, `ratFunToFieldOfInv`, `LinfAt.algebraPolynomial`, and more.
- `polyToFieldOfInv_injective_of_transcendental`: used by `polyToFieldOfInv_ne_zero_of_ne_zero`, `ratFunToFieldOfInv`, `Sinf.ofIntegralClosure`.
- `ratFunToFieldOfInv`: used by `ratFunToFieldOfInv_injective`, `LinfAt.algebraFractionRing`, `algebraMap_fractionRing_apply`, `isScalarTower_polynomial_fractionRing`, `isScalarTower_k_fractionRing`.
- `LinfAt`: used by essentially all `LinfAt.*` instances and `Sinf` fields.
- `xIdeal`: used by `xIdeal_isMaximal`, `xIdeal_ne_bot`, `quotientXAlgEquiv`, `Sinf.ordAt`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `Sinf.kappa`, `Sinf.inertiaDeg_eq_finrank_kappa`, `finrank_residue_eq_finrank_k`, `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`, `finrank_eq_weighted_poleDegree_of_nonconstant`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`.
- `Sinf`: used by `Sinf.ofIntegralClosure`, `finrank_eq_sum_ramificationIdx_mul_inertiaDeg`, `Sinf.ordAt`, `Sinf.toNat_neg_ordAt_eq_ramificationIdx`, `Sinf.kappa`, `Sinf.algBaseFromCarrier`, `Sinf.inertiaDeg_eq_finrank_kappa`, `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective`, `finrank_eq_weighted_poleDegree_of_nonconstant`.
