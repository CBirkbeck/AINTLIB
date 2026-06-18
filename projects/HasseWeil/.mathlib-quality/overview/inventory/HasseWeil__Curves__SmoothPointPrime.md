# Inventory: ./HasseWeil/Curves/SmoothPointPrime.lean

**File summary**: 682 lines. Two thematic sections: (1) a short SmoothPoint ↔ HeightOneSpectrum bijection bridge (lines 35–71, 4 declarations inside `SmoothPlaneCurve`); (2) a large A2–A4 Dedekind-domain ideal factorisation / ClassGroup ≃ Finsupp-quotient development (lines 89–681, 40 declarations at top level in `HasseWeil.Curves`). No `sorry`, no `set_option maxHeartbeats`.

---

## Section 1: SmoothPlaneCurve namespace (lines 35–71)

---

### `theorem toHeightOneSpectrum_injective`

- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → Function.Injective (SmoothPoint.toHeightOneSpectrum (C := C))`
- **What**: The map sending each smooth F-rational point to its associated height-one prime of `C.CoordinateRing` is injective.
- **How**: Applies `C.maximalIdealAt_injective` (from `NormValuation.lean`) to the equation of underlying ideals obtained by `congrArg`.
- **Hypotheses**: `C.CoordinateRing` is integrally closed (which gives Dedekind domain structure).
- **Uses from project**: `SmoothPoint.toHeightOneSpectrum`, `C.maximalIdealAt_injective`
- **Used by**: `smoothPointEquivHeightOneSpectrum` (line 63)
- **Visibility**: public
- **Lines**: 35–41, proof 4 lines
- **Notes**: none

---

### `theorem toHeightOneSpectrum_surjective`

- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] → Function.Surjective (SmoothPoint.toHeightOneSpectrum (C := C))`
- **What**: Under algebraic closure of the base field and the elliptic hypothesis, every height-one prime of `C.CoordinateRing` arises from a smooth point.
- **How**: Uses `v.isPrime.isMaximal v.ne_bot` (Dedekind domain: every nonzero prime is maximal) then `C.exists_smoothPoint_of_isMaximal` (from `NormValuation.lean`) and `IsDedekindDomain.HeightOneSpectrum.ext`.
- **Hypotheses**: `F` algebraically closed; `C.toAffine` is elliptic; `C.CoordinateRing` integrally closed.
- **Uses from project**: `C.exists_smoothPoint_of_isMaximal`
- **Used by**: `smoothPointEquivHeightOneSpectrum` (line 64)
- **Visibility**: public
- **Lines**: 46–54, proof 5 lines
- **Notes**: none

---

### `noncomputable def smoothPointEquivHeightOneSpectrum`

- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] → C.SmoothPoint ≃ IsDedekindDomain.HeightOneSpectrum C.CoordinateRing`
- **What**: Packages the injective + surjective lemmas into a bijective equivalence between smooth points and height-one primes.
- **How**: `Equiv.ofBijective` applied to `toHeightOneSpectrum_injective` and `toHeightOneSpectrum_surjective`.
- **Hypotheses**: Same as surjectivity: `F` algebraically closed, `C` elliptic, coordinate ring integrally closed.
- **Uses from project**: `toHeightOneSpectrum_injective`, `toHeightOneSpectrum_surjective`
- **Used by**: `smoothPointEquivHeightOneSpectrum_apply_asIdeal` (line 69)
- **Visibility**: public
- **Lines**: 59–64, proof 2 lines (term-mode)
- **Notes**: none

---

### `@[simp] theorem smoothPointEquivHeightOneSpectrum_apply_asIdeal`

- **Type**: `[IsAlgClosed F] [C.toAffine.IsElliptic] [IsIntegrallyClosed C.CoordinateRing] (P : C.SmoothPoint) → (C.smoothPointEquivHeightOneSpectrum P).asIdeal = C.maximalIdealAt P`
- **What**: Evaluating the bijection on a smooth point and extracting the underlying ideal recovers `maximalIdealAt P` (definitional equality).
- **How**: `rfl`.
- **Hypotheses**: Same as `smoothPointEquivHeightOneSpectrum`.
- **Uses from project**: `smoothPointEquivHeightOneSpectrum`, `C.maximalIdealAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–70, proof 1 line
- **Notes**: none

---

## Section 2: A2–A4 Dedekind domain / ClassGroup Finsupp development (lines 89–681)

---

### `noncomputable def Ideal.toHeightOneFinsuppNonzero`

- **Type**: `[CommRing R] [IsDomain R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ 0) → IsDedekindDomain.HeightOneSpectrum R →₀ ℕ`
- **What**: Packages the unique prime factorisation of a nonzero ideal `I` as a finitely-supported function on `HeightOneSpectrum R`, with value `Associates.count (Associates.mk v.asIdeal) (Associates.mk I).factors` at each prime `v`.
- **How**: Uses `Finsupp.onFinset` with support derived from `Ideal.finite_factors hI`; the membership condition uses `Associates.count_ne_zero_iff_dvd`.
- **Hypotheses**: Dedekind domain; `I ≠ 0`.
- **Uses from project**: none
- **Used by**: `Ideal.toHeightOneFinsuppNonzero_apply`, `Ideal.toHeightOneFinsuppNonzero_mul`, `Ideal.toHeightOneFinsuppNonzero_one`, `Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero`
- **Visibility**: public
- **Lines**: 89–99, proof (by tactic) ~11 lines
- **Notes**: A2.1 in the Pic⁰ chain commentary.

---

### `@[simp] theorem Ideal.toHeightOneFinsuppNonzero_apply`

- **Type**: `(hI : I ≠ 0) (v : HeightOneSpectrum R) → Ideal.toHeightOneFinsuppNonzero hI v = (Associates.mk v.asIdeal).count (Associates.mk I).factors`
- **What**: The Finsupp value at `v` is the Associates count, unfolding the definition.
- **How**: `rfl` (after `classical`).
- **Hypotheses**: Dedekind domain.
- **Uses from project**: `Ideal.toHeightOneFinsuppNonzero`
- **Used by**: `Ideal.toHeightOneFinsuppNonzero_mul`, `Ideal.toHeightOneFinsuppNonzero_one`, `Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero`
- **Visibility**: public
- **Lines**: 101–108, proof 3 lines
- **Notes**: Key simp lemma used by the `_mul` and `_one` theorems.

---

### `theorem Ideal.toHeightOneFinsuppNonzero_mul`

- **Type**: `(hI : I ≠ 0) (hJ : J ≠ 0) → Ideal.toHeightOneFinsuppNonzero (mul_ne_zero hI hJ) = Ideal.toHeightOneFinsuppNonzero hI + Ideal.toHeightOneFinsuppNonzero hJ`
- **What**: The Finsupp factorisation of `I·J` is the pointwise sum of those of `I` and `J` (multiplicativity of factorisation).
- **How**: Applies `toHeightOneFinsuppNonzero_apply` and then `Associates.count_mul` with `Associates.mk_mul_mk`.
- **Hypotheses**: Dedekind domain; `I, J ≠ 0`.
- **Uses from project**: `Ideal.toHeightOneFinsuppNonzero_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 116–127, proof 7 lines
- **Notes**: A2.2. Unused within file; exported for future use.

---

### `theorem Ideal.toHeightOneFinsuppNonzero_one`

- **Type**: `Ideal.toHeightOneFinsuppNonzero (one_ne_zero : (1 : Ideal R) ≠ 0) = 0`
- **What**: The unit ideal has empty factorisation (zero Finsupp).
- **How**: Applies `toHeightOneFinsuppNonzero_apply`, then `Associates.mk_one`, `Associates.factors_one`, and `Associates.count_zero`.
- **Hypotheses**: Dedekind domain.
- **Uses from project**: `Ideal.toHeightOneFinsuppNonzero_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 131–139, proof 8 lines
- **Notes**: A2.3. Unused within file.

---

### `noncomputable def Ideal.fromHeightOneFinsupp`

- **Type**: `(f : HeightOneSpectrum R →₀ ℕ) → Ideal R`
- **What**: Reverse map: given a finitely-supported multiplicity function on height-one primes, returns the ideal `∏ v.asIdeal ^ (f v)` (finite product over support).
- **How**: `f.prod (fun v n => v.asIdeal ^ n)`.
- **Hypotheses**: Dedekind domain.
- **Uses from project**: none
- **Used by**: `Ideal.fromHeightOneFinsupp_zero`, `Ideal.fromHeightOneFinsupp_add`, `Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero`, `Ideal.fromHeightOneFinsupp_ne_zero`
- **Visibility**: public
- **Lines**: 148–151, term-mode definition
- **Notes**: A2.4 reverse direction.

---

### `@[simp] theorem Ideal.fromHeightOneFinsupp_zero`

- **Type**: `Ideal.fromHeightOneFinsupp (0 : HeightOneSpectrum R →₀ ℕ) = 1`
- **What**: The empty Finsupp maps to the unit ideal (empty product = 1).
- **How**: `Finsupp.prod_zero_index`.
- **Hypotheses**: Dedekind domain.
- **Uses from project**: `Ideal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 154–157, proof 1 line
- **Notes**: Unused within file.

---

### `theorem Ideal.fromHeightOneFinsupp_add`

- **Type**: `(f g : HeightOneSpectrum R →₀ ℕ) → Ideal.fromHeightOneFinsupp (f + g) = Ideal.fromHeightOneFinsupp f * Ideal.fromHeightOneFinsupp g`
- **What**: Addition on Finsupps corresponds to multiplication of ideals (i.e., the reverse map is a monoid homomorphism).
- **How**: `Finsupp.prod_add_index'` with `pow_zero` and `pow_add` witnesses.
- **Hypotheses**: Dedekind domain.
- **Uses from project**: `Ideal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 160–170, proof 10 lines
- **Notes**: Unused within file.

---

### `theorem Finsupp.prod_eq_finprod_of_zero_eq_one`

- **Type**: `(f : α →₀ M) (g : α → M → N) (h_zero : ∀ a, g a 0 = 1) → f.prod g = ∏ᶠ a, g a (f a)`
- **What**: For any Finsupp `f` and function `g` with trivial off-support values, the Finsupp product equals the corresponding finprod (bridge lemma).
- **How**: Uses `Finsupp.prod` definition, `finprod_eq_prod_of_mulSupport_subset`, and the membership condition `Function.mem_mulSupport` + `Finsupp.mem_support_iff`.
- **Hypotheses**: `M` has zero; `N` is a commutative monoid; `g a 0 = 1` for all `a`.
- **Uses from project**: none
- **Used by**: `Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero`
- **Visibility**: public
- **Lines**: 181–193, proof 12 lines
- **Notes**: General-purpose helper; file comments flag it as a possible mathlib upstream contribution candidate.

---

### `theorem Ideal.fromHeightOneFinsupp_toHeightOneFinsuppNonzero`

- **Type**: `(hI : I ≠ 0) → Ideal.fromHeightOneFinsupp (Ideal.toHeightOneFinsuppNonzero hI) = I`
- **What**: The round-trip `fromHeightOneFinsupp ∘ toHeightOneFinsuppNonzero = id`: reconstructing an ideal from its prime Finsupp factorisation recovers the original ideal.
- **How**: Bridges via `Finsupp.prod_eq_finprod_of_zero_eq_one` to convert `Finsupp.prod` to `finprod`, then applies mathlib's `Ideal.finprod_heightOneSpectrum_factorization` and `toHeightOneFinsuppNonzero_apply`.
- **Hypotheses**: Dedekind domain; `I ≠ 0`.
- **Uses from project**: `Finsupp.prod_eq_finprod_of_zero_eq_one`, `Ideal.toHeightOneFinsuppNonzero`, `Ideal.fromHeightOneFinsupp`, `Ideal.toHeightOneFinsuppNonzero_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 200–210, proof 10 lines
- **Notes**: A2.5 forward isomorphism. Unused within file; expected to be used by callers.

---

### `noncomputable def FractionalIdeal.fromHeightOneFinsupp`

- **Type**: `(f : HeightOneSpectrum R →₀ ℤ) → FractionalIdeal R⁰ K`
- **What**: Integer-coefficient version of the reverse Finsupp-to-ideal map: `f.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n)` using `zpow`.
- **How**: Term-mode `Finsupp.prod`.
- **Hypotheses**: Dedekind domain `R`, fraction field `K`.
- **Uses from project**: none
- **Used by**: `FractionalIdeal.fromHeightOneFinsupp_zero`, `FractionalIdeal.fromHeightOneFinsupp_add`, `FractionalIdeal.count_fromHeightOneFinsupp`
- **Visibility**: public
- **Lines**: 217–221, term-mode definition
- **Notes**: A3 reverse; integer (ℤ) exponents for fractional ideals.

---

### `@[simp] theorem FractionalIdeal.fromHeightOneFinsupp_zero`

- **Type**: `FractionalIdeal.fromHeightOneFinsupp (R := R) (K := K) (0 : HeightOneSpectrum R →₀ ℤ) = 1`
- **What**: Empty Finsupp maps to the unit fractional ideal.
- **How**: `Finsupp.prod_zero_index`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 224–229, proof 1 line
- **Notes**: Unused within file.

---

### `theorem FractionalIdeal.fromHeightOneFinsupp_add`

- **Type**: `(f g : HeightOneSpectrum R →₀ ℤ) → FractionalIdeal.fromHeightOneFinsupp (f + g) = FractionalIdeal.fromHeightOneFinsupp f * FractionalIdeal.fromHeightOneFinsupp g`
- **What**: Addition on Finsupps corresponds to multiplication of fractional ideals.
- **How**: `Finsupp.prod_add_index'` with `zpow_zero` and `zpow_add₀` (using `FractionalIdeal.coeIdeal_ne_zero` to verify nonzero denominators for `zpow_add₀`).
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 233–248, proof 16 lines
- **Notes**: Unused within file.

---

### `theorem FractionalIdeal.count_fromHeightOneFinsupp`

- **Type**: `(v : HeightOneSpectrum R) (f : HeightOneSpectrum R →₀ ℤ) → FractionalIdeal.count K v (FractionalIdeal.fromHeightOneFinsupp f) = f v`
- **What**: The height-one count of `fromHeightOneFinsupp f` at `v` recovers `f v` (the Finsupp is a left inverse of `count`).
- **How**: Unfolds definition and directly applies mathlib's `FractionalIdeal.count_finsuppProd`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 253–260, proof 3 lines
- **Notes**: Unused within file; foundational for the A4 round-trip.

---

### `theorem Ideal.fromHeightOneFinsupp_ne_zero`

- **Type**: `(f : HeightOneSpectrum R →₀ ℕ) → Ideal.fromHeightOneFinsupp f ≠ 0`
- **What**: Any ideal built from a height-one prime Finsupp is nonzero (because each prime ideal is nonzero and powers of nonzero ideals are nonzero in a domain).
- **How**: Unfolds `Finsupp.prod` and applies `Finset.prod_ne_zero_iff.mpr` with `pow_ne_zero _ v.ne_bot`.
- **Hypotheses**: Dedekind domain.
- **Uses from project**: `Ideal.fromHeightOneFinsupp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 271–278, proof 6 lines
- **Notes**: Unused within file; supplanted by `FractionalIdeal.fromFinsupp_ne_zero` at the fractional ideal level.

---

### `noncomputable def FractionalIdeal.unitsToHeightOneFinsupp`

- **Type**: `(I : (FractionalIdeal R⁰ K)ˣ) → IsDedekindDomain.HeightOneSpectrum R →₀ ℤ`
- **What**: Packages the integer-valued height-one prime count of an invertible fractional ideal as a Finsupp, with finite support derived from `FractionalIdeal.finite_factors`.
- **How**: `Finsupp.onFinset` using `Filter.eventually_cofinite.mp` to extract the finite set.
- **Hypotheses**: Dedekind domain with fraction field; `I` a unit in `FractionalIdeal R⁰ K`.
- **Uses from project**: none
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsupp_apply`, `FractionalIdeal.unitsToHeightOneFinsupp_mul`, `FractionalIdeal.unitsToHeightOneFinsupp_one`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`, `FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 288–300, proof ~12 lines
- **Notes**: A4 foundational map; heavily used within the file.

---

### `@[simp] theorem FractionalIdeal.unitsToHeightOneFinsupp_apply`

- **Type**: `(I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) → FractionalIdeal.unitsToHeightOneFinsupp I v = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K)`
- **What**: Evaluates the Finsupp at `v`: it equals the height-one count at `v`.
- **How**: `rfl` (after `classical`).
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp`
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsupp_mul`, `FractionalIdeal.unitsToHeightOneFinsupp_one`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom` (transitively), `FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 302–310, proof 3 lines
- **Notes**: Key simp lemma; used by ≥6 other declarations.

---

### `theorem FractionalIdeal.unitsToHeightOneFinsupp_mul`

- **Type**: `(I J : (FractionalIdeal R⁰ K)ˣ) → FractionalIdeal.unitsToHeightOneFinsupp (I * J) = FractionalIdeal.unitsToHeightOneFinsupp I + FractionalIdeal.unitsToHeightOneFinsupp J`
- **What**: The count Finsupp is additive under multiplication of unit fractional ideals.
- **How**: Applies `unitsToHeightOneFinsupp_apply` and `FractionalIdeal.count_mul` (using `Units.ne_zero`).
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp_apply`
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom` (map_mul')
- **Visibility**: public
- **Lines**: 315–328, proof 12 lines
- **Notes**: none

---

### `theorem FractionalIdeal.unitsToHeightOneFinsupp_one`

- **Type**: `FractionalIdeal.unitsToHeightOneFinsupp (1 : (FractionalIdeal R⁰ K)ˣ) = 0`
- **What**: The unit (trivial) fractional ideal has zero count Finsupp.
- **How**: Applies `unitsToHeightOneFinsupp_apply` and `FractionalIdeal.count_one`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp_apply`
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom` (map_one')
- **Visibility**: public
- **Lines**: 332–340, proof 8 lines
- **Notes**: none

---

### `noncomputable def FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`

- **Type**: `(FractionalIdeal R⁰ K)ˣ →* Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)`
- **What**: Packages `unitsToHeightOneFinsupp` as a `MonoidHom` via `Multiplicative.ofAdd`, using `_mul` and `_one` for the axioms.
- **How**: Inline proofs using `unitsToHeightOneFinsupp_one` and `unitsToHeightOneFinsupp_mul`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp`, `FractionalIdeal.unitsToHeightOneFinsupp_one`, `FractionalIdeal.unitsToHeightOneFinsupp_mul`
- **Used by**: `FractionalIdeal.classToFinsuppQuotient`, `FractionalIdeal.principalToHeightOneFinsuppMonoidHom`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`, `FractionalIdeal.classToFinsuppQuotient_injective`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective`, `FractionalIdeal.classToFinsuppQuotient_surjective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 345–359, proof ~15 lines
- **Notes**: Key API used by ≥7 other declarations.

---

### `theorem FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply`

- **Type**: `(x : Kˣ) (v : HeightOneSpectrum R) → FractionalIdeal.unitsToHeightOneFinsupp (toPrincipalIdeal R K x) v = FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K))`
- **What**: The count Finsupp of the principal fractional ideal generated by a unit `x ∈ Kˣ` equals the count of the corresponding `spanSingleton`.
- **How**: Directly by `unitsToHeightOneFinsupp_apply` and `coe_toPrincipalIdeal`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp_apply`
- **Used by**: `FractionalIdeal.principalToHeightOneFinsuppMonoidHom_apply`
- **Visibility**: public
- **Lines**: 365–371, proof 2 lines
- **Notes**: none

---

### `theorem FractionalIdeal.count_spanSingleton_mk'`

- **Type**: `(hn : n ≠ 0) (d : ↥R⁰) (v : HeightOneSpectrum R) → FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d)) = (Associates count numerator ideal at v) - (Associates count denominator ideal at v)`
- **What**: Computes the height-one count of the span of a fraction `n/d ∈ K` as the difference of Associates counts on numerator and denominator principal ideals.
- **How**: Uses `FractionalIdeal.count_well_defined` after rewriting `spanSingleton(n/d)` as `spanSingleton(d)⁻¹ * coe(Ideal.span {n})` via `mk'_eq_div` and `coeIdeal_span_singleton`/`spanSingleton_mul_spanSingleton`.
- **Hypotheses**: `R` Dedekind domain with fraction field `K`; `n ≠ 0`, `d ∈ R⁰`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 377–401, proof ~24 lines
- **Notes**: Unused within file; moderately long proof.

---

### `noncomputable def FractionalIdeal.principalToHeightOneFinsuppMonoidHom`

- **Type**: `Kˣ →* Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)`
- **What**: Composition of `toPrincipalIdeal R K` with `unitsToHeightOneFinsuppMonoidHom`; sends a unit of `K` to the count Finsupp of its associated principal fractional ideal.
- **How**: Term-mode `MonoidHom.comp`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`
- **Used by**: `FractionalIdeal.principalToHeightOneFinsuppMonoidHom_apply`, `FractionalIdeal.principalImageSubgroup`
- **Visibility**: public
- **Lines**: 406–410, term-mode definition
- **Notes**: none

---

### `theorem FractionalIdeal.principalToHeightOneFinsuppMonoidHom_apply`

- **Type**: `(x : Kˣ) (v : HeightOneSpectrum R) → Multiplicative.toAdd (FractionalIdeal.principalToHeightOneFinsuppMonoidHom x) v = FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K))`
- **What**: Evaluating `principalToHeightOneFinsuppMonoidHom` at `(x, v)` yields the count of the principal span.
- **How**: Reduces via `show` to `unitsToHeightOneFinsupp_toPrincipalIdeal_apply`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsupp_toPrincipalIdeal_apply`, `FractionalIdeal.principalToHeightOneFinsuppMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 414–422, proof 4 lines
- **Notes**: Unused within file.

---

### `noncomputable def FractionalIdeal.principalImageSubgroup`

- **Type**: `Subgroup (Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ))`
- **What**: The range of `principalToHeightOneFinsuppMonoidHom`; this is the subgroup of principal divisors in the Finsupp-quotient picture.
- **How**: Term-mode `.range`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.principalToHeightOneFinsuppMonoidHom`
- **Used by**: `FractionalIdeal.principalImageSubgroup_normal`, `FractionalIdeal.classToFinsuppQuotient`, `ClassGroup.toFinsuppQuotient`, `FractionalIdeal.classToFinsuppQuotient_injective`, `FractionalIdeal.classToFinsuppMulEquiv`, `ClassGroup.toFinsuppMulEquiv`, `FractionalIdeal.classToFinsuppMulEquiv_mk`
- **Visibility**: public
- **Lines**: 427–431, term-mode definition
- **Notes**: Key subgroup; used as the target of ≥7 declarations.

---

### `instance FractionalIdeal.principalImageSubgroup_normal`

- **Type**: `(FractionalIdeal.principalImageSubgroup (R := R) (K := K)).Normal`
- **What**: The principal image subgroup is normal (automatic since the ambient Multiplicative group is commutative).
- **How**: `Subgroup.normal_of_comm`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.principalImageSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 434–438, proof 1 line
- **Notes**: Unused within file; needed for well-definedness of quotient group constructions elsewhere.

---

### `noncomputable def FractionalIdeal.classToFinsuppQuotient`

- **Type**: `(FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range →* Multiplicative (HeightOneSpectrum R →₀ ℤ) ⧸ FractionalIdeal.principalImageSubgroup`
- **What**: Descends `unitsToHeightOneFinsuppMonoidHom` to a well-defined group homomorphism on the affine ClassGroup quotient, landing in the Finsupp-quotient.
- **How**: `QuotientGroup.lift` verifying the kernel containment: a principal element `toPrincipalIdeal x` maps into `principalImageSubgroup`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`, `FractionalIdeal.principalImageSubgroup`
- **Used by**: `ClassGroup.toFinsuppQuotient`, `FractionalIdeal.classToFinsuppQuotient_injective`, `FractionalIdeal.classToFinsuppQuotient_surjective`, `FractionalIdeal.classToFinsuppQuotient_bijective`, `FractionalIdeal.classToFinsuppMulEquiv`, `FractionalIdeal.classToFinsuppMulEquiv_mk`
- **Visibility**: public
- **Lines**: 445–457, proof ~12 lines
- **Notes**: Central A4 descent morphism; used by 6 other declarations.

---

### `noncomputable def ClassGroup.toFinsuppQuotient`

- **Type**: `(K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] → ClassGroup R →* Multiplicative (HeightOneSpectrum R →₀ ℤ) ⧸ principalImageSubgroup`
- **What**: Composes `classToFinsuppQuotient` with `ClassGroup.equiv K` to produce the abstract ClassGroup-to-Finsupp-quotient morphism (fraction-field-independent form).
- **How**: `MonoidHom.comp`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.classToFinsuppQuotient`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 463–469, term-mode definition
- **Notes**: Unused within file.

---

### `theorem FractionalIdeal.eq_of_count_eq`

- **Type**: `(hI : I ≠ 0) (hJ : J ≠ 0) (h : ∀ v, FractionalIdeal.count K v I = FractionalIdeal.count K v J) → I = J`
- **What**: Two nonzero fractional ideals are equal if their height-one count functions agree everywhere.
- **How**: Reconstructs each via `FractionalIdeal.finprod_heightOneSpectrum_factorization'` and uses `finprod_congr`.
- **Hypotheses**: Dedekind domain with fraction field; both ideals nonzero.
- **Uses from project**: none
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`
- **Visibility**: public
- **Lines**: 474–483, proof 6 lines
- **Notes**: none

---

### `theorem FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`

- **Type**: `Function.Injective (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom (R := R) (K := K))`
- **What**: The MonoidHom sending invertible fractional ideals to count Finsupps is injective.
- **How**: Uses `Multiplicative.ofAdd.injective` to unwrap, `DFunLike.congr_fun` on the Finsupp equality, and `eq_of_count_eq` + `Units.ext` to conclude equality of the units.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.eq_of_count_eq`, `FractionalIdeal.unitsToHeightOneFinsupp_apply`
- **Used by**: `FractionalIdeal.classToFinsuppQuotient_injective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 488–501, proof 13 lines
- **Notes**: none

---

### `theorem FractionalIdeal.classToFinsuppQuotient_injective`

- **Type**: `Function.Injective (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K))`
- **What**: The descended quotient map from the affine ClassGroup to the Finsupp-quotient is injective (trivial kernel).
- **How**: Uses `MonoidHom.ker_eq_bot_iff`, `QuotientGroup.induction_on`, unpacks `principalImageSubgroup` membership to find `x` with `principalToHeightOneFinsuppMonoidHom x = unitsToHeightOneFinsupp I`, applies `unitsToHeightOneFinsuppMonoidHom_injective` to get `I = toPrincipalIdeal x`, and concludes `[I] = 1`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`, `FractionalIdeal.principalImageSubgroup`, `FractionalIdeal.classToFinsuppQuotient`
- **Used by**: `FractionalIdeal.classToFinsuppQuotient_bijective`, `FractionalIdeal.classToFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 508–534, proof ~27 lines
- **Notes**: Proof is moderately long (~27 lines).

---

### `theorem FractionalIdeal.fromFinsupp_ne_zero`

- **Type**: `(f : HeightOneSpectrum R →₀ ℤ) → f.prod (fun w n => (w.asIdeal : FractionalIdeal R⁰ K) ^ n) ≠ 0`
- **What**: The fractional ideal built from any Finsupp (via `zpow` products over height-one primes) is nonzero.
- **How**: Unfolds `Finsupp.prod` and applies `Finset.prod_ne_zero_iff.mpr` with `zpow_ne_zero` + `FractionalIdeal.coeIdeal_ne_zero`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: none
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 538–545, proof 6 lines
- **Notes**: none

---

### `theorem FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective`

- **Type**: `Function.Surjective (FractionalIdeal.unitsToHeightOneFinsuppMonoidHom (R := R) (K := K))`
- **What**: The MonoidHom sending invertible fractional ideals to count Finsupps is surjective: any Finsupp arises from `Units.mk0` applied to the corresponding zpow product.
- **How**: For given `mf`, constructs `I_f = (toAdd mf).prod (asIdeal · ^ ·)`, lifts to a unit via `Units.mk0 I_f (fromFinsupp_ne_zero ...)`, then shows `count_finsuppProd` gives the correct count.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.fromFinsupp_ne_zero`
- **Used by**: `FractionalIdeal.classToFinsuppQuotient_surjective`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 551–568, proof 18 lines
- **Notes**: none

---

### `theorem FractionalIdeal.classToFinsuppQuotient_surjective`

- **Type**: `Function.Surjective (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K))`
- **What**: The quotient map is surjective; follows from the composition of two surjections (`mk'` and `unitsToHeightOneFinsuppMonoidHom_surjective`).
- **How**: `QuotientGroup.lift_surjective_of_surjective` applied to `(mk'_surjective).comp unitsToHeightOneFinsuppMonoidHom_surjective`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective`, `FractionalIdeal.classToFinsuppQuotient`
- **Used by**: `FractionalIdeal.classToFinsuppQuotient_bijective`, `FractionalIdeal.classToFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 574–581, proof 4 lines
- **Notes**: none

---

### `theorem FractionalIdeal.classToFinsuppQuotient_bijective`

- **Type**: `Function.Bijective (FractionalIdeal.classToFinsuppQuotient (R := R) (K := K))`
- **What**: The quotient map is bijective (combines injective + surjective).
- **How**: `⟨classToFinsuppQuotient_injective, classToFinsuppQuotient_surjective⟩`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.classToFinsuppQuotient_injective`, `FractionalIdeal.classToFinsuppQuotient_surjective`
- **Used by**: `FractionalIdeal.classToFinsuppMulEquiv`
- **Visibility**: public
- **Lines**: 586–592, proof 3 lines
- **Notes**: none

---

### `noncomputable def FractionalIdeal.classToFinsuppMulEquiv`

- **Type**: `(FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) ⧸ principalImageSubgroup`
- **What**: The bijective quotient map is a `MulEquiv` (packaged via `MulEquiv.ofBijective`).
- **How**: `MulEquiv.ofBijective classToFinsuppQuotient classToFinsuppQuotient_bijective`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.classToFinsuppQuotient`, `FractionalIdeal.classToFinsuppQuotient_bijective`
- **Used by**: `ClassGroup.toFinsuppMulEquiv`, `FractionalIdeal.classToFinsuppMulEquiv_mk`
- **Visibility**: public
- **Lines**: 598–605, term-mode definition
- **Notes**: none

---

### `noncomputable def ClassGroup.toFinsuppMulEquiv`

- **Type**: `(K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] → ClassGroup R ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) ⧸ principalImageSubgroup`
- **What**: The abstract ClassGroup is multiplicatively equivalent to the Finsupp-modulo-principal-Finsupps quotient.
- **How**: Transitive composition `(ClassGroup.equiv K).trans FractionalIdeal.classToFinsuppMulEquiv`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.classToFinsuppMulEquiv`, `FractionalIdeal.principalImageSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 610–616, term-mode definition
- **Notes**: Unused within file; top-level result of the A4 chain.

---

### `noncomputable def FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`

- **Type**: `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ)`
- **What**: The unit-level bijection (without quotients): invertible fractional ideals are multiplicatively equivalent to the Finsupp group.
- **How**: `MulEquiv.ofBijective unitsToHeightOneFinsuppMonoidHom ⟨injective, surjective⟩`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_injective`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom_surjective`
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 621–628, term-mode definition
- **Notes**: none

---

### `@[simp] theorem FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply`

- **Type**: `(I : (FractionalIdeal R⁰ K)ˣ) → FractionalIdeal.unitsToHeightOneFinsuppMulEquiv I = Multiplicative.ofAdd (FractionalIdeal.unitsToHeightOneFinsupp I)`
- **What**: Evaluating the unit-level MulEquiv is the same as applying `unitsToHeightOneFinsupp` wrapped in `ofAdd`.
- **How**: `rfl`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`, `FractionalIdeal.unitsToHeightOneFinsupp`
- **Used by**: `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`
- **Visibility**: public
- **Lines**: 632–638, proof 1 line
- **Notes**: none

---

### `theorem FractionalIdeal.classToFinsuppMulEquiv_mk`

- **Type**: `(I : (FractionalIdeal R⁰ K)ˣ) → FractionalIdeal.classToFinsuppMulEquiv (QuotientGroup.mk I) = QuotientGroup.mk' principalImageSubgroup (unitsToHeightOneFinsuppMonoidHom I)`
- **What**: On representative elements (`mk`), the affine MulEquiv acts by applying `unitsToHeightOneFinsuppMonoidHom` and then taking the quotient class.
- **How**: `rfl` (definitional equality from `QuotientGroup.lift`).
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.classToFinsuppMulEquiv`, `FractionalIdeal.principalImageSubgroup`, `FractionalIdeal.unitsToHeightOneFinsuppMonoidHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 643–651, proof 1 line
- **Notes**: Unused within file.

---

### `theorem FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_symm_apply`

- **Type**: `(mf : Multiplicative (HeightOneSpectrum R →₀ ℤ)) → unitsToHeightOneFinsuppMulEquiv.symm mf = Units.mk0 ((toAdd mf).prod (fun w n => (w.asIdeal : FractionalIdeal R⁰ K) ^ n)) (fromFinsupp_ne_zero (toAdd mf))`
- **What**: Explicit description of the inverse of the unit-level MulEquiv: it sends a Multiplicative Finsupp `mf` to the unit `Units.mk0` of the corresponding zpow-product fractional ideal.
- **How**: Applies `unitsToHeightOneFinsuppMulEquiv.injective` to reduce to the forward direction, uses `MulEquiv.apply_symm_apply`, then confirms equality using `count_finsuppProd` and `unitsToHeightOneFinsuppMulEquiv_apply`.
- **Hypotheses**: Dedekind domain with fraction field.
- **Uses from project**: `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv`, `FractionalIdeal.fromFinsupp_ne_zero`, `FractionalIdeal.unitsToHeightOneFinsupp_apply`, `FractionalIdeal.unitsToHeightOneFinsuppMulEquiv_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 656–679, proof ~23 lines
- **Notes**: Unused within file.

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 44 |
| `noncomputable def` | 13 |
| `theorem` | 28 |
| `instance` | 1 |
| `@[simp]` theorems | 6 |
| `sorry` | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 0 |
